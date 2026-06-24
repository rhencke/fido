(** ============================================================================
    unified.v — ONE authoritative closed-world operational semantics.

    The external review's DECISIVE finding: there were several semantic systems (the [IO]/[World]
    monad, the [cmd.v] effect evaluator, the rich [rstep] concurrency calculus, the bounded [rstepC],
    the session reductions) but NO single authoritative operational configuration covering an ORDINARY
    program that combines goroutines + channels + heap mutation + panic + defer + output.

    This file builds exactly that: a SINGLE command language [UCmd] carrying ALL the admitted effects,
    a SINGLE configuration [UConfig], and a SINGLE small-step relation [ustep].  It REUSES concurrency.v's
    trace / happens-before / race-freedom machinery — that theory is TRACE-based (it reasons about the
    [KWrite]/[KRead] events and [hbt], not about [Cmd]/[rstep]), so it is calculus-agnostic and the
    ownership/race results PORT onto [ustep] by proving only that [ustep] preserves the ownership
    discipline (a later slice — see [UPrivateDisc] below).

    Effects and how each is carried:
      - heap        [UWrite]/[URead]   -> [uc_heap] + [KWrite]/[KRead] trace events (drives race-freedom)
      - channels    [USend]/[URecv]/[UClose] -> [uc_bufs] + [KSend]/[KRecv]/[KClose] (the [rstep] rules)
      - goroutines  [USpawn]           -> [uc_live] + [KSpawn]/[KStart] (the go-before-start hb edge)
      - OUTPUT      [UOut]             -> [uc_out] (an append-only log; output is not a memory race)
      - DEFER       [UDfr]             -> [uc_defers] (per-goroutine LIFO stack, run at return)
      - PANIC       [UPan]             -> [uc_panic] (per-goroutine status; defers STILL run — review P0)

    The defer/panic interaction is the faithful one (the cmd.v P0 fix, now operational + concurrent): a
    deferred action runs at function-scope RETURN in LIFO order, AND a panic does NOT cancel the
    remaining defers — it records the active panic and unwinding CONTINUES.  See [ustep_ret_defer] /
    [ustep_pan_defer]. *)

From Fido Require Import preamble concurrency.
From Stdlib Require Import List Lia Arith.
Import ListNotations.

(** THE unified command language — every admitted effect, one syntax.  (Values are [nat] and locations
    [nat], exactly as the rich [rstep] calculus, so the trace/race machinery applies verbatim; [UOut]
    carries the rich [GoAny] payload since output is observed, not raced.) *)
Inductive UCmd : Type :=
  | URet   : UCmd                                  (* return / done *)
  | UOut   : list GoAny -> UCmd -> UCmd            (* print xs; then k     — OUTPUT *)
  | UPan   : GoAny -> UCmd                          (* panic v              — PANIC (no continuation) *)
  | UDfr   : UCmd -> UCmd -> UCmd                   (* defer d; then k      — DEFER *)
  | USend  : nat -> nat -> UCmd -> UCmd            (* ch <- v; then k *)
  | URecv  : nat -> (nat -> UCmd) -> UCmd          (* x := <-ch; then k x *)
  | UWrite : nat -> nat -> UCmd -> UCmd            (* *l = v; then k *)
  | URead  : nat -> (nat -> UCmd) -> UCmd          (* x := *l; then k x *)
  | USpawn : UCmd -> UCmd -> UCmd                  (* go child(); then k *)
  | UClose : nat -> UCmd -> UCmd.                  (* close(ch); then k *)

(** THE unified configuration — one closed world holding every effect's state. *)
Record UConfig := mkUCfg {
  uc_prog   : nat -> UCmd ;               (* each goroutine's program *)
  uc_bufs   : nat -> list (nat * nat) ;   (* channel -> FIFO of (value, send-position) *)
  uc_heap   : nat -> nat ;                (* location -> value *)
  uc_live   : nat -> bool ;               (* which goroutines exist *)
  uc_trace  : Trace ;                     (* memory/sync events — the race-freedom substrate *)
  uc_out    : list (nat * list GoAny) ;   (* OUTPUT log: (goroutine, printed values), in order *)
  uc_defers : nat -> list UCmd ;          (* per-goroutine DEFER stack (head = most-recent = runs first) *)
  uc_panic  : nat -> option GoAny         (* per-goroutine PANIC status (Some v = panicking with v) *)
}.

(** THE single small-step relation.  Concurrency/heap/channel rules mirror [rstep] (so the embedding in
    the next slice is rule-for-rule); the genuinely NEW rules are output, panic, defer-register, and the
    defer-running RETURN/PANIC rules that make defer + panic operational and faithful. *)
Inductive ustep : UConfig -> UConfig -> Prop :=
  (* ---- heap ---- *)
  | ustep_write : forall p b h lv tr o df pa tid l v k,
      lv tid = true -> p tid = UWrite l v k ->
      ustep (mkUCfg p b h lv tr o df pa)
            (mkUCfg (upd p tid k) b (upd h l v) lv (tr ++ [mkEv tid (KWrite l)]) o df pa)
  | ustep_read : forall p b h lv tr o df pa tid l f,
      lv tid = true -> p tid = URead l f ->
      ustep (mkUCfg p b h lv tr o df pa)
            (mkUCfg (upd p tid (f (h l))) b h lv (tr ++ [mkEv tid (KRead l)]) o df pa)
  (* ---- channels ---- *)
  | ustep_send : forall p b h lv tr o df pa tid c v k,
      lv tid = true -> p tid = USend c v k -> closedb tr c = false ->
      ustep (mkUCfg p b h lv tr o df pa)
            (mkUCfg (upd p tid k) (upd b c (b c ++ [(v, length tr)])) h lv
                    (tr ++ [mkEv tid (KSend c)]) o df pa)
  | ustep_recv : forall p b h lv tr o df pa tid c f v s brest,
      lv tid = true -> p tid = URecv c f -> b c = (v, s) :: brest ->
      ustep (mkUCfg p b h lv tr o df pa)
            (mkUCfg (upd p tid (f v)) (upd b c brest) h lv
                    (tr ++ [mkEv tid (KRecv c s)]) o df pa)
  | ustep_close : forall p b h lv tr o df pa tid c k,
      lv tid = true -> p tid = UClose c k -> closedb tr c = false ->
      ustep (mkUCfg p b h lv tr o df pa)
            (mkUCfg (upd p tid k) b h lv (tr ++ [mkEv tid (KClose c)]) o df pa)
  (* ---- goroutines ---- *)
  | ustep_spawn : forall p b h lv tr o df pa tid child k cid,
      lv tid = true -> p tid = USpawn child k -> lv cid = false ->
      ustep (mkUCfg p b h lv tr o df pa)
            (mkUCfg (upd (upd p tid k) cid child) b h (upd lv cid true)
                    (tr ++ [mkEv tid (KSpawn cid); mkEv cid (KStart (length tr))]) o
                    (upd df cid nil) (upd pa cid None))   (* a fresh goroutine has no defers, no panic *)
  (* ---- OUTPUT: append to the log, no memory event ---- *)
  | ustep_out : forall p b h lv tr o df pa tid xs k,
      lv tid = true -> p tid = UOut xs k ->
      ustep (mkUCfg p b h lv tr o df pa)
            (mkUCfg (upd p tid k) b h lv tr (o ++ [(tid, xs)]) df pa)
  (* ---- DEFER: register d on the goroutine's LIFO stack (front = runs first) ---- *)
  | ustep_defer : forall p b h lv tr o df pa tid d k,
      lv tid = true -> p tid = UDfr d k ->
      ustep (mkUCfg p b h lv tr o df pa)
            (mkUCfg (upd p tid k) b h lv tr o (upd df tid (d :: df tid)) pa)
  (* ---- RETURN: run the next deferred action (LIFO); when none, the goroutine is done ---- *)
  | ustep_ret_defer : forall p b h lv tr o df pa tid d ds,
      lv tid = true -> p tid = URet -> df tid = d :: ds ->
      ustep (mkUCfg p b h lv tr o df pa)
            (mkUCfg (upd p tid d) b h lv tr o (upd df tid ds) pa)
  | ustep_ret_done : forall p b h lv tr o df pa tid,
      lv tid = true -> p tid = URet -> df tid = [] ->
      ustep (mkUCfg p b h lv tr o df pa)
            (mkUCfg p b h (upd lv tid false) tr o df pa)
  (* ---- PANIC: record the active panic; the remaining defers STILL run (review P0).  Only when the
         defer stack is empty does the goroutine actually die — panicking. ---- *)
  | ustep_pan_defer : forall p b h lv tr o df pa tid v d ds,
      lv tid = true -> p tid = UPan v -> df tid = d :: ds ->
      ustep (mkUCfg p b h lv tr o df pa)
            (mkUCfg (upd p tid d) b h lv tr o (upd df tid ds) (upd pa tid (Some v)))
  | ustep_pan_done : forall p b h lv tr o df pa tid v,
      lv tid = true -> p tid = UPan v -> df tid = [] ->
      ustep (mkUCfg p b h lv tr o df pa)
            (mkUCfg p b h (upd lv tid false) tr o df (upd pa tid (Some v))).

Inductive usteps : UConfig -> UConfig -> Prop :=
  | usteps_refl : forall cfg, usteps cfg cfg
  | usteps_step : forall a b c, ustep a b -> usteps b c -> usteps a c.

Lemma usteps_trans : forall a b c, usteps a b -> usteps b c -> usteps a c.
Proof.
  intros a b c H. induction H; intros Hbc; [exact Hbc|].
  eapply usteps_step; [exact H | apply IHusteps; exact Hbc].
Qed.

(** ---- SANITY: the new effects are operational and faithful ---- *)

(** OUTPUT is recorded (no longer erased — the old [run_io] no-op the review flagged): printing [xs]
    appends [(tid, xs)] to the log. *)
Lemma ustep_out_records : forall p b h lv tr o df pa tid xs k,
  lv tid = true -> p tid = UOut xs k ->
  ustep (mkUCfg p b h lv tr o df pa)
        (mkUCfg (upd p tid k) b h lv tr (o ++ [(tid, xs)]) df pa).
Proof. intros. apply ustep_out; assumption. Qed.

(** DEFER + PANIC, operational and faithful: a panicking goroutine with a pending defer does NOT skip
    it — it records the panic and steps INTO the deferred action (which then runs to its own return).
    This is the cmd.v P0 fix, now in the concurrent operational semantics. *)
Lemma ustep_panic_runs_deferred : forall p b h lv tr o df pa tid v d ds,
  lv tid = true -> p tid = UPan v -> df tid = d :: ds ->
  ustep (mkUCfg p b h lv tr o df pa)
        (mkUCfg (upd p tid d) b h lv tr o (upd df tid ds) (upd pa tid (Some v))).
Proof. intros. apply ustep_pan_defer; assumption. Qed.

(** A memory step appends EXACTLY one [KWrite]/[KRead] event — the hook by which concurrency.v's
    trace-based race-freedom ([Owned]/[LocPrivate]/[TraceRaceFree]) ports onto [ustep] in the next
    slice (only [UPrivateDisc]-preservation remains to prove; the trace theory is reused verbatim). *)
Lemma ustep_write_event : forall p b h lv tr o df pa tid l v k,
  lv tid = true -> p tid = UWrite l v k ->
  uc_trace (mkUCfg (upd p tid k) b (upd h l v) lv (tr ++ [mkEv tid (KWrite l)]) o df pa)
    = uc_trace (mkUCfg p b h lv tr o df pa) ++ [mkEv tid (KWrite l)].
Proof. reflexivity. Qed.

(** ============================================================================
    SLICE 2 — PORTING RACE-FREEDOM ONTO THE UNIFIED SEMANTICS.

    The reviewer's ask: "port the ownership, session, race, and liveness results onto that single
    semantics."  Here is race-freedom, ported with NO re-proving of the trace theory: concurrency.v's
    [TraceOwned_app] / [LocPrivate] / [locprivate_race_free] are trace-based and reused verbatim; only
    the [UPrivateDisc]-preservation across [ustep] is new (the U-analogues of [MemFree]/[OnlyAcc] and the
    per-rule preservation).  The new effects are handled exactly: OUTPUT/PANIC touch no memory; a
    deferred action carries the SAME ownership constraint (so running it at return is owner-safe). *)

(* A [UMemFree] command touches NO shared memory — channels/spawn/output/panic/defer of memory-free
   children only.  Vacuously [UOnlyAcc] for ANY owner. *)
Inductive UMemFree : UCmd -> Prop :=
  | UMF_ret   : UMemFree URet
  | UMF_out   : forall xs k, UMemFree k -> UMemFree (UOut xs k)
  | UMF_pan   : forall v, UMemFree (UPan v)
  | UMF_dfr   : forall d k, UMemFree d -> UMemFree k -> UMemFree (UDfr d k)
  | UMF_send  : forall c v k, UMemFree k -> UMemFree (USend c v k)
  | UMF_recv  : forall c f, (forall v, UMemFree (f v)) -> UMemFree (URecv c f)
  | UMF_spawn : forall child k, UMemFree child -> UMemFree k -> UMemFree (USpawn child k)
  | UMF_close : forall c k, UMemFree k -> UMemFree (UClose c k).

(* [UOnlyAcc P c]: every memory access [c] makes (now AND in its deferred actions / continuations)
   is to a location satisfying [P]; spawned children are [UMemFree]. *)
Inductive UOnlyAcc (P : nat -> Prop) : UCmd -> Prop :=
  | UOA_ret   : UOnlyAcc P URet
  | UOA_out   : forall xs k, UOnlyAcc P k -> UOnlyAcc P (UOut xs k)
  | UOA_pan   : forall v, UOnlyAcc P (UPan v)
  | UOA_dfr   : forall d k, UOnlyAcc P d -> UOnlyAcc P k -> UOnlyAcc P (UDfr d k)
  | UOA_send  : forall c v k, UOnlyAcc P k -> UOnlyAcc P (USend c v k)
  | UOA_recv  : forall c f, (forall v, UOnlyAcc P (f v)) -> UOnlyAcc P (URecv c f)
  | UOA_write : forall l v k, P l -> UOnlyAcc P k -> UOnlyAcc P (UWrite l v k)
  | UOA_read  : forall l f, P l -> (forall v, UOnlyAcc P (f v)) -> UOnlyAcc P (URead l f)
  | UOA_spawn : forall child k, UMemFree child -> UOnlyAcc P k -> UOnlyAcc P (USpawn child k)
  | UOA_close : forall c k, UOnlyAcc P k -> UOnlyAcc P (UClose c k).

Lemma umemfree_onlyacc : forall c, UMemFree c -> forall P, UOnlyAcc P c.
Proof.
  intros c H. induction H; intros P;
    [ apply UOA_ret | apply UOA_out; auto | apply UOA_pan
    | apply UOA_dfr; auto | apply UOA_send; auto | apply UOA_recv; auto
    | apply UOA_spawn; auto | apply UOA_close; auto ].
Qed.

Lemma uoa_out_inv   : forall P xs k, UOnlyAcc P (UOut xs k) -> UOnlyAcc P k.
Proof. intros P xs k H; inversion H; subst; assumption. Qed.
Lemma uoa_dfr_inv   : forall P d k, UOnlyAcc P (UDfr d k) -> UOnlyAcc P d /\ UOnlyAcc P k.
Proof. intros P d k H; inversion H; subst; split; assumption. Qed.
Lemma uoa_send_inv  : forall P c v k, UOnlyAcc P (USend c v k) -> UOnlyAcc P k.
Proof. intros P c v k H; inversion H; subst; assumption. Qed.
Lemma uoa_recv_inv  : forall P c f, UOnlyAcc P (URecv c f) -> forall v, UOnlyAcc P (f v).
Proof. intros P c f H; inversion H; subst; assumption. Qed.
Lemma uoa_write_inv : forall P l v k, UOnlyAcc P (UWrite l v k) -> P l /\ UOnlyAcc P k.
Proof. intros P l v k H; inversion H; subst; split; assumption. Qed.
Lemma uoa_read_inv  : forall P l f, UOnlyAcc P (URead l f) -> P l /\ (forall v, UOnlyAcc P (f v)).
Proof. intros P l f H; inversion H; subst; split; assumption. Qed.
Lemma uoa_spawn_inv : forall P child k, UOnlyAcc P (USpawn child k) -> UMemFree child /\ UOnlyAcc P k.
Proof. intros P child k H; inversion H; subst; split; assumption. Qed.
Lemma uoa_close_inv : forall P c k, UOnlyAcc P (UClose c k) -> UOnlyAcc P k.
Proof. intros P c k H; inversion H; subst; assumption. Qed.

Lemma uonlyacc_upd : forall own (p : nat -> UCmd) tid (cont : UCmd) (lv : nat -> bool) g,
  (forall g', lv g' = true -> UOnlyAcc (fun l => own l = g') (p g')) ->
  UOnlyAcc (fun l => own l = tid) cont ->
  lv g = true ->
  UOnlyAcc (fun l => own l = g) (upd p tid cont g).
Proof.
  intros own p tid cont lv g Hprog Hcont Hg.
  destruct (Nat.eq_dec g tid) as [->|Hne].
  - rewrite upd_same. exact Hcont.
  - rewrite (upd_other p tid cont g Hne). exact (Hprog g Hg).
Qed.

(** The ownership discipline on a UNIFIED config: every memory access in the trace is by the
    location's owner; every live goroutine's PROGRAM and every action on its DEFER STACK only-access
    locations it owns (the defer-stack clause is what makes running a deferred action at return
    owner-safe, so the panic/defer machinery stays race-free). *)
Definition UPrivateDisc (own : nat -> nat) (cfg : UConfig) : Prop :=
  (forall i l, acc_loc_at (uc_trace cfg) i = Some l -> tid_at (uc_trace cfg) i = own l)
  /\ (forall g, uc_live cfg g = true -> UOnlyAcc (fun l => own l = g) (uc_prog cfg g))
  /\ (forall g, uc_live cfg g = true -> Forall (UOnlyAcc (fun l => own l = g)) (uc_defers cfg g)).

Lemma uprivate_disc_step : forall own cfg cfg',
  ustep cfg cfg' -> UPrivateDisc own cfg -> UPrivateDisc own cfg'.
Proof.
  intros own cfg cfg' Hstep HPD. unfold UPrivateDisc in HPD |- *.
  destruct HPD as [Htr [Hprog Hdf]].
  destruct Hstep as
    [ p b h lv tr o df pa tid l v k Hlv Hp
    | p b h lv tr o df pa tid l f Hlv Hp
    | p b h lv tr o df pa tid c v k Hlv Hp Hcl
    | p b h lv tr o df pa tid c f v s brest Hlv Hp Hbc
    | p b h lv tr o df pa tid c k Hlv Hp Hcl
    | p b h lv tr o df pa tid child k cid Hlv Hp Hcid
    | p b h lv tr o df pa tid xs k Hlv Hp
    | p b h lv tr o df pa tid d k Hlv Hp
    | p b h lv tr o df pa tid d ds Hlv Hp Hdfeq
    | p b h lv tr o df pa tid Hlv Hp Hdfeq
    | p b h lv tr o df pa tid v d ds Hlv Hp Hdfeq
    | p b h lv tr o df pa tid v Hlv Hp Hdfeq ];
    cbn [uc_trace uc_prog uc_live uc_defers] in Htr, Hprog, Hdf |- *.
  - (* write: owner access (own l = tid), cont k *)
    pose proof (Hprog tid Hlv) as HO. rewrite Hp in HO. apply uoa_write_inv in HO. destruct HO as [Hown HOk].
    split; [| split].
    + apply (TraceOwned_app own tr (mkEv tid (KWrite l)) Htr). intros l' [Hw|Hr]; cbn in *;
        [ injection Hw as Heq; subst l'; symmetry; exact Hown | discriminate ].
    + intros g Hg. exact (uonlyacc_upd own p tid k lv g Hprog HOk Hg).
    + exact Hdf.
  - (* read: owner access, cont f (h l) *)
    pose proof (Hprog tid Hlv) as HO. rewrite Hp in HO. apply uoa_read_inv in HO. destruct HO as [Hown HOf].
    split; [| split].
    + apply (TraceOwned_app own tr (mkEv tid (KRead l)) Htr). intros l' [Hw|Hr]; cbn in *;
        [ discriminate | injection Hr as Heq; subst l'; symmetry; exact Hown ].
    + intros g Hg. exact (uonlyacc_upd own p tid (f (h l)) lv g Hprog (HOf (h l)) Hg).
    + exact Hdf.
  - (* send: KSend (not memory), cont k *)
    pose proof (Hprog tid Hlv) as HO. rewrite Hp in HO. apply uoa_send_inv in HO.
    split; [| split].
    + apply (TraceOwned_app own tr (mkEv tid (KSend c)) Htr). intros l' [Hw|Hr]; cbn in *; discriminate.
    + intros g Hg. exact (uonlyacc_upd own p tid k lv g Hprog HO Hg).
    + exact Hdf.
  - (* recv: KRecv, cont f v *)
    pose proof (Hprog tid Hlv) as HO. rewrite Hp in HO.
    split; [| split].
    + apply (TraceOwned_app own tr (mkEv tid (KRecv c s)) Htr). intros l' [Hw|Hr]; cbn in *; discriminate.
    + intros g Hg. exact (uonlyacc_upd own p tid (f v) lv g Hprog (uoa_recv_inv _ _ _ HO v) Hg).
    + exact Hdf.
  - (* close: KClose, cont k *)
    pose proof (Hprog tid Hlv) as HO. rewrite Hp in HO. apply uoa_close_inv in HO.
    split; [| split].
    + apply (TraceOwned_app own tr (mkEv tid (KClose c)) Htr). intros l' [Hw|Hr]; cbn in *; discriminate.
    + intros g Hg. exact (uonlyacc_upd own p tid k lv g Hprog HO Hg).
    + exact Hdf.
  - (* spawn: child is UMemFree (OnlyAcc any owner); fresh child has [] defers; KSpawn/KStart not memory *)
    pose proof (Hprog tid Hlv) as HO. rewrite Hp in HO. apply uoa_spawn_inv in HO. destruct HO as [HMF HOk].
    split; [| split].
    + replace (tr ++ [mkEv tid (KSpawn cid); mkEv cid (KStart (length tr))])
        with ((tr ++ [mkEv tid (KSpawn cid)]) ++ [mkEv cid (KStart (length tr))])
        by (rewrite <- app_assoc; reflexivity).
      apply (TraceOwned_app own (tr ++ [mkEv tid (KSpawn cid)]) (mkEv cid (KStart (length tr)))).
      * apply (TraceOwned_app own tr (mkEv tid (KSpawn cid)) Htr). intros l' [Hw|Hr]; cbn in *; discriminate.
      * intros l' [Hw|Hr]; cbn in *; discriminate.
    + intros g Hg. destruct (Nat.eq_dec g cid) as [->|Hgc].
      * rewrite upd_same. exact (umemfree_onlyacc child HMF (fun l => own l = cid)).
      * rewrite (upd_other (upd p tid k) cid child g Hgc).
        rewrite (upd_other lv cid true g Hgc) in Hg.
        exact (uonlyacc_upd own p tid k lv g Hprog HOk Hg).
    + intros g Hg. destruct (Nat.eq_dec g cid) as [->|Hgc].
      * rewrite upd_same. apply Forall_nil.
      * rewrite (upd_other df cid nil g Hgc). rewrite (upd_other lv cid true g Hgc) in Hg. exact (Hdf g Hg).
  - (* output: trace + defers unchanged, cont k *)
    pose proof (Hprog tid Hlv) as HO. rewrite Hp in HO. apply uoa_out_inv in HO.
    split; [exact Htr | split; [| exact Hdf]].
    intros g Hg. exact (uonlyacc_upd own p tid k lv g Hprog HO Hg).
  - (* defer-register: cont k; push d (UOnlyAcc) onto the stack *)
    pose proof (Hprog tid Hlv) as HO. rewrite Hp in HO. apply uoa_dfr_inv in HO. destruct HO as [HOd HOk].
    split; [exact Htr | split].
    + intros g Hg. exact (uonlyacc_upd own p tid k lv g Hprog HOk Hg).
    + intros g Hg. destruct (Nat.eq_dec g tid) as [->|Hgt].
      * rewrite upd_same. apply Forall_cons; [exact HOd | exact (Hdf tid Hlv)].
      * rewrite (upd_other df tid (d :: df tid) g Hgt). exact (Hdf g Hg).
  - (* return-runs-defer: prog := d (head of stack, UOnlyAcc), stack := tail *)
    pose proof (Hdf tid Hlv) as HFd. rewrite Hdfeq in HFd.
    split; [exact Htr | split].
    + intros g Hg. exact (uonlyacc_upd own p tid d lv g Hprog (Forall_inv HFd) Hg).
    + intros g Hg. destruct (Nat.eq_dec g tid) as [->|Hgt].
      * rewrite upd_same. exact (Forall_inv_tail HFd).
      * rewrite (upd_other df tid ds g Hgt). exact (Hdf g Hg).
  - (* return-done: goroutine dies; prog/defers unchanged, only [lv tid] flips false *)
    split; [exact Htr | split].
    + intros g Hg. destruct (Nat.eq_dec g tid) as [->|Hgt];
        [ rewrite upd_same in Hg; discriminate | rewrite (upd_other lv tid false g Hgt) in Hg; exact (Hprog g Hg) ].
    + intros g Hg. destruct (Nat.eq_dec g tid) as [->|Hgt];
        [ rewrite upd_same in Hg; discriminate | rewrite (upd_other lv tid false g Hgt) in Hg; exact (Hdf g Hg) ].
  - (* panic-runs-defer: like return-runs-defer (panic status is irrelevant to ownership) *)
    pose proof (Hdf tid Hlv) as HFd. rewrite Hdfeq in HFd.
    split; [exact Htr | split].
    + intros g Hg. exact (uonlyacc_upd own p tid d lv g Hprog (Forall_inv HFd) Hg).
    + intros g Hg. destruct (Nat.eq_dec g tid) as [->|Hgt].
      * rewrite upd_same. exact (Forall_inv_tail HFd).
      * rewrite (upd_other df tid ds g Hgt). exact (Hdf g Hg).
  - (* panic-done: goroutine dies panicking; like return-done *)
    split; [exact Htr | split].
    + intros g Hg. destruct (Nat.eq_dec g tid) as [->|Hgt];
        [ rewrite upd_same in Hg; discriminate | rewrite (upd_other lv tid false g Hgt) in Hg; exact (Hprog g Hg) ].
    + intros g Hg. destruct (Nat.eq_dec g tid) as [->|Hgt];
        [ rewrite upd_same in Hg; discriminate | rewrite (upd_other lv tid false g Hgt) in Hg; exact (Hdf g Hg) ].
Qed.

Lemma uprivate_disc_steps : forall own a b, usteps a b -> UPrivateDisc own a -> UPrivateDisc own b.
Proof.
  intros own a b H. induction H as [cfg | a b c Hab Hbc IH]; intros HPD; [exact HPD|].
  apply IH. exact (uprivate_disc_step own _ _ Hab HPD).
Qed.

Lemma uprivate_disc_locprivate : forall own cfg,
  UPrivateDisc own cfg -> LocPrivate (uc_trace cfg).
Proof.
  intros own cfg [Htr _] i j [l [Hi Hj]]. rewrite (Htr i l Hi), (Htr j l Hj). reflexivity.
Qed.

(** RACE-FREEDOM, PORTED: a unified-semantics program whose goroutines only touch their OWN locations
    (and spawn memory-free children) runs RACE-FREE for EVERY reachable interleaving — now over the ONE
    semantics carrying channels + heap + spawn + OUTPUT + PANIC + DEFER together.  Reuses
    concurrency.v's [locprivate_race_free] verbatim. *)
Theorem uprivate_disc_reachable_race_free : forall own cfg0 cfg,
  UPrivateDisc own cfg0 -> usteps cfg0 cfg ->
  LocPrivate (uc_trace cfg) /\ TraceRaceFree (uc_trace cfg).
Proof.
  intros own cfg0 cfg HPD Hsteps.
  pose proof (uprivate_disc_locprivate own cfg (uprivate_disc_steps own cfg0 cfg Hsteps HPD)) as HLP.
  split; [exact HLP | exact (locprivate_race_free _ HLP)].
Qed.
