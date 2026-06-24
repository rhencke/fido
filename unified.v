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
            (mkUCfg p b h (upd lv tid false) tr o df (upd pa tid (Some v)))
  (* ---- faithful CLOSED-CHANNEL panics: send/close on a closed channel PANICS (Go), modelled by
         transitioning the goroutine to [UPan] (the defer/death machinery above then runs); a recv on a
         CLOSED, drained channel returns the zero value (binds 0), exactly [rstep_recv_closed]. ---- *)
  | ustep_send_closed : forall p b h lv tr o df pa tid c v k,
      lv tid = true -> p tid = USend c v k -> closedb tr c = true ->
      ustep (mkUCfg p b h lv tr o df pa)
            (mkUCfg (upd p tid (UPan rt_send_closed)) b h lv tr o df pa)
  | ustep_close_closed : forall p b h lv tr o df pa tid c k,
      lv tid = true -> p tid = UClose c k -> closedb tr c = true ->
      ustep (mkUCfg p b h lv tr o df pa)
            (mkUCfg (upd p tid (UPan rt_close_closed)) b h lv tr o df pa)
  | ustep_recv_closed : forall p b h lv tr o df pa tid c f pos e,
      lv tid = true -> p tid = URecv c f -> b c = [] ->
      nth_error tr pos = Some e -> e_kind e = KClose c ->
      ustep (mkUCfg p b h lv tr o df pa)
            (mkUCfg (upd p tid (f 0)) b h lv (tr ++ [mkEv tid (KRecv c pos)]) o df pa).

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
    | p b h lv tr o df pa tid v Hlv Hp Hdfeq
    | p b h lv tr o df pa tid c v k Hlv Hp Hcl
    | p b h lv tr o df pa tid c k Hlv Hp Hcl
    | p b h lv tr o df pa tid c f pos e Hlv Hp Hbc Hpos Hek ];
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
  - (* send-on-closed: prog becomes UPan (no memory, UOnlyAcc trivially); trace/defers unchanged *)
    split; [exact Htr | split; [| exact Hdf]].
    intros g Hg. exact (uonlyacc_upd own p tid (UPan rt_send_closed) lv g Hprog (UOA_pan _ _) Hg).
  - (* close-on-closed: prog becomes UPan *)
    split; [exact Htr | split; [| exact Hdf]].
    intros g Hg. exact (uonlyacc_upd own p tid (UPan rt_close_closed) lv g Hprog (UOA_pan _ _) Hg).
  - (* recv-on-closed: cont f 0; event KRecv (not memory) *)
    pose proof (Hprog tid Hlv) as HO. rewrite Hp in HO.
    split; [| split].
    + apply (TraceOwned_app own tr (mkEv tid (KRecv c pos)) Htr). intros l' [Hw|Hr]; cbn in *; discriminate.
    + intros g Hg. exact (uonlyacc_upd own p tid (f 0) lv g Hprog (uoa_recv_inv _ _ _ HO 0) Hg).
    + exact Hdf.
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

(** ============================================================================
    SLICE 3 — LIVENESS / DEADLOCK, ported onto the unified semantics.

    With panics now operational (send/close-on-closed -> [UPan]; recv-on-closed -> zero), the ONLY way a
    live goroutine fails to step is a receive on an empty, still-OPEN channel — a genuine wait for a
    sender.  So [ustep]'s progress and deadlock characterization is clean: a config is STUCK exactly when
    every live goroutine is so blocked.  Output, defer-register, defer/panic-at-return, write, read,
    spawn all step unconditionally; send steps (async) or panics; close steps or panics; recv steps when
    buffered or closed.  This is the rich-calculus [rstuck_blocked]/[ready_can_step] re-homed on the ONE
    semantics that ALSO carries panic + defer + output. *)
Definition ucan_step (cfg : UConfig) : Prop := exists cfg', ustep cfg cfg'.
Definition UFreshAvail (cfg : UConfig) : Prop := exists cid, uc_live cfg cid = false.
Definition ublocked (cfg : UConfig) (tid : nat) : Prop :=
  exists c f, uc_prog cfg tid = URecv c f
              /\ uc_bufs cfg c = [] /\ closedb (uc_trace cfg) c = false.

(** PROGRESS: a live goroutine that is NOT blocked-on-empty-open-recv means the whole config can step. *)
Theorem uready_can_step : forall cfg tid,
  UFreshAvail cfg -> uc_live cfg tid = true -> ~ ublocked cfg tid -> ucan_step cfg.
Proof.
  intros cfg tid [cid Hcid] Hlive Hnblk. destruct cfg as [p b h lv tr o df pa].
  cbn [uc_prog uc_bufs uc_trace uc_live] in *.
  destruct (p tid) as [ | xs k | v | d k | c v k | c f | l v k | l f | child k | c k ] eqn:Hp.
  - (* URet *) destruct (df tid) as [|d ds] eqn:E.
    + eexists. eapply ustep_ret_done; [exact Hlive | exact Hp | exact E].
    + eexists. eapply ustep_ret_defer; [exact Hlive | exact Hp | exact E].
  - eexists. eapply ustep_out; [exact Hlive | exact Hp].
  - (* UPan *) destruct (df tid) as [|d ds] eqn:E.
    + eexists. eapply ustep_pan_done; [exact Hlive | exact Hp | exact E].
    + eexists. eapply ustep_pan_defer; [exact Hlive | exact Hp | exact E].
  - eexists. eapply ustep_defer; [exact Hlive | exact Hp].
  - (* USend *) destruct (closedb tr c) eqn:Ecl.
    + eexists. eapply ustep_send_closed; [exact Hlive | exact Hp | exact Ecl].
    + eexists. eapply ustep_send; [exact Hlive | exact Hp | exact Ecl].
  - (* URecv *) destruct (b c) as [|[v s] rest] eqn:Eb.
    + destruct (closedb tr c) eqn:Ecl.
      * destruct (closedb_true_witness _ _ Ecl) as [pos [e [Hpos Hek]]].
        eexists. eapply ustep_recv_closed; [exact Hlive | exact Hp | exact Eb | exact Hpos | exact Hek].
      * exfalso. apply Hnblk. exists c, f. split; [exact Hp | split; [exact Eb | exact Ecl]].
    + eexists. eapply ustep_recv; [exact Hlive | exact Hp | exact Eb].
  - eexists. eapply ustep_write; [exact Hlive | exact Hp].
  - eexists. eapply ustep_read; [exact Hlive | exact Hp].
  - eexists. eapply ustep_spawn; [exact Hlive | exact Hp | exact Hcid].
  - (* UClose *) destruct (closedb tr c) eqn:Ecl.
    + eexists. eapply ustep_close_closed; [exact Hlive | exact Hp | exact Ecl].
    + eexists. eapply ustep_close; [exact Hlive | exact Hp | exact Ecl].
Qed.

(** DEADLOCK CHARACTERIZATION (the converse): a STUCK config — one that cannot step yet has a live
    goroutine — has EVERY live goroutine blocked on an empty, open channel.  No spurious "stuck": a
    would-be panic (send/close on closed) is a STEP, not a deadlock; only a real wait-for-sender is. *)
Theorem ustuck_blocked : forall cfg,
  UFreshAvail cfg -> ~ ucan_step cfg ->
  forall tid, uc_live cfg tid = true -> ublocked cfg tid.
Proof.
  intros cfg [cid Hcid] Hnstep tid Hlive. destruct cfg as [p b h lv tr o df pa].
  cbn [uc_prog uc_bufs uc_trace uc_live] in *.
  destruct (p tid) as [ | xs k | v | d k | c v k | c f | l v k | l f | child k | c k ] eqn:Hp.
  - exfalso. apply Hnstep. destruct (df tid) as [|d ds] eqn:E.
    + eexists. eapply ustep_ret_done; [exact Hlive | exact Hp | exact E].
    + eexists. eapply ustep_ret_defer; [exact Hlive | exact Hp | exact E].
  - exfalso. apply Hnstep. eexists. eapply ustep_out; [exact Hlive | exact Hp].
  - exfalso. apply Hnstep. destruct (df tid) as [|d ds] eqn:E.
    + eexists. eapply ustep_pan_done; [exact Hlive | exact Hp | exact E].
    + eexists. eapply ustep_pan_defer; [exact Hlive | exact Hp | exact E].
  - exfalso. apply Hnstep. eexists. eapply ustep_defer; [exact Hlive | exact Hp].
  - exfalso. apply Hnstep. destruct (closedb tr c) eqn:Ecl.
    + eexists. eapply ustep_send_closed; [exact Hlive | exact Hp | exact Ecl].
    + eexists. eapply ustep_send; [exact Hlive | exact Hp | exact Ecl].
  - (* URecv: the only blocking shape *) destruct (b c) as [|[v s] rest] eqn:Eb.
    + destruct (closedb tr c) eqn:Ecl.
      * exfalso. apply Hnstep. destruct (closedb_true_witness _ _ Ecl) as [pos [e [Hpos Hek]]].
        eexists. eapply ustep_recv_closed; [exact Hlive | exact Hp | exact Eb | exact Hpos | exact Hek].
      * exists c, f. split; [exact Hp | split; [exact Eb | exact Ecl]].
    + exfalso. apply Hnstep. eexists. eapply ustep_recv; [exact Hlive | exact Hp | exact Eb].
  - exfalso. apply Hnstep. eexists. eapply ustep_write; [exact Hlive | exact Hp].
  - exfalso. apply Hnstep. eexists. eapply ustep_read; [exact Hlive | exact Hp].
  - exfalso. apply Hnstep. eexists. eapply ustep_spawn; [exact Hlive | exact Hp | exact Hcid].
  - exfalso. apply Hnstep. destruct (closedb tr c) eqn:Ecl.
    + eexists. eapply ustep_close_closed; [exact Hlive | exact Hp | exact Ecl].
    + eexists. eapply ustep_close; [exact Hlive | exact Hp | exact Ecl].
Qed.

(** ============================================================================
    SLICE 4 — the unified semantics, DEMONSTRATED on concrete all-effects executions.

    These are the "ordinary program combining the effects, machine-checked" the review asked for:
    concrete [usteps] runs exercising panic + defer + output (and heap), proving the unified semantics
    behaves faithfully — in particular the defer/panic interaction that was the cmd.v P0 bug, now
    operational AND in the concurrent step relation. *)

(** THE P0 FIX, OPERATIONAL + CONCURRENT: goroutine 0 PANICS with a deferred [print xv] pending.  The
    deferred print STILL happens (it appears in [uc_out]), THEN the goroutine dies with the panic [pv]
    recorded.  Pre-fix, the deferred print was provably dropped. *)
Lemma unified_panic_runs_defer : forall (xv pv : GoAny),
  exists cfg',
    usteps (mkUCfg (fun t => if Nat.eqb t 0 then UPan pv else URet)
                   (fun _ => nil) (fun _ => 0) (fun t => Nat.eqb t 0) nil
                   nil (fun t => if Nat.eqb t 0 then UOut (xv :: nil) URet :: nil else nil)
                   (fun _ => None))
           cfg'
    /\ uc_out cfg' = (0, xv :: nil) :: nil      (* the deferred print HAPPENED *)
    /\ uc_live cfg' 0 = false                   (* the goroutine died *)
    /\ uc_panic cfg' 0 = Some pv.               (* ...with the panic recorded *)
Proof.
  intros xv pv. eexists. split.
  - eapply usteps_step.
    { apply (ustep_pan_defer _ _ _ _ _ _ _ _ 0 pv (UOut (xv :: nil) URet) nil); reflexivity. }
    eapply usteps_step.
    { apply (ustep_out _ _ _ _ _ _ _ _ 0 (xv :: nil) URet); reflexivity. }
    eapply usteps_step.
    { apply (ustep_ret_done _ _ _ _ _ _ _ _ 0); reflexivity. }
    apply usteps_refl.
  - cbn. repeat split; reflexivity.
Qed.

(** HEAP write-then-read in the unified semantics: goroutine 0 writes [loc 0 := 7] then reads it back,
    binding 7 — the mutable-heap effect, with the [KWrite]/[KRead] events that drive race-freedom. *)
Lemma unified_heap_write_read : forall (k : nat -> UCmd),
  exists cfg',
    usteps (mkUCfg (fun t => if Nat.eqb t 0 then UWrite 0 7 (URead 0 k) else URet)
                   (fun _ => nil) (fun _ => 0) (fun t => Nat.eqb t 0) nil
                   nil (fun _ => nil) (fun _ => None))
           cfg'
    /\ uc_prog cfg' 0 = k 7                      (* the read bound the written value 7 *)
    /\ uc_heap cfg' 0 = 7.
Proof.
  intros k. eexists. split.
  - eapply usteps_step.
    { apply (ustep_write _ _ _ _ _ _ _ _ 0 0 7 (URead 0 k)); reflexivity. }
    eapply usteps_step.
    { apply (ustep_read _ _ _ _ _ _ _ _ 0 0 k); reflexivity. }
    apply usteps_refl.
  - cbn. split; reflexivity.
Qed.

(** CHANNEL send+recv in the unified semantics: goroutine 0 sends 5 on channel 0 (async buffer), then
    receives it back, binding 5 — the channel effect, with [KSend]/[KRecv] synchronisation events. *)
Lemma unified_chan_send_recv : forall (k : nat -> UCmd),
  exists cfg',
    usteps (mkUCfg (fun t => if Nat.eqb t 0 then USend 0 5 (URecv 0 k) else URet)
                   (fun _ => nil) (fun _ => 0) (fun t => Nat.eqb t 0) nil
                   nil (fun _ => nil) (fun _ => None))
           cfg'
    /\ uc_prog cfg' 0 = k 5.                     (* the recv bound the sent value 5 *)
Proof.
  intros k. eexists. split.
  - eapply usteps_step.
    { apply (ustep_send _ _ _ _ _ _ _ _ 0 0 5 (URecv 0 k)); reflexivity. }
    eapply usteps_step.
    { apply (ustep_recv _ _ _ _ _ _ _ _ 0 0 k 5 0 nil); reflexivity. }
    apply usteps_refl.
  - cbn. reflexivity.
Qed.

(** OUTPUT is recorded IN PROGRAM ORDER — closing review #6 #12's "[run_io] erases output" on the
    AUTHORITATIVE semantics: [print x; print y] yields the log [(0,[x]); (0,[y])], faithfully and ordered
    (the shallow [run_io] made differently-printing programs provably equal; [ustep]'s [uc_out] does not). *)
Lemma unified_output_ordered : forall (x y : GoAny),
  exists cfg',
    usteps (mkUCfg (fun t => if Nat.eqb t 0 then UOut (x :: nil) (UOut (y :: nil) URet) else URet)
                   (fun _ => nil) (fun _ => 0) (fun t => Nat.eqb t 0) nil
                   nil (fun _ => nil) (fun _ => None))
           cfg'
    /\ uc_out cfg' = (0, x :: nil) :: (0, y :: nil) :: nil.
Proof.
  intros x y. eexists. split.
  - eapply usteps_step.
    { apply (ustep_out _ _ _ _ _ _ _ _ 0 (x :: nil) (UOut (y :: nil) URet)); reflexivity. }
    eapply usteps_step.
    { apply (ustep_out _ _ _ _ _ _ _ _ 0 (y :: nil) URet); reflexivity. }
    apply usteps_refl.
  - cbn. reflexivity.
Qed.

(** ============================================================================
    SLICE 6 — the review's exact ask, machine-checked: ONE ordinary program combining the effects.

    A single goroutine that MUTATES the heap, SENDS on a channel and RECEIVES it back, DEFERS a print,
    then PANICS — exercising heap + channel + defer + panic + output TOGETHER in the ONE semantics.  The
    review said no authoritative semantics covered such a program; here is one, run end to end: the
    deferred print STILL happens at the panic (the P0 fix), the heap holds its write, the channel
    round-trips, and the goroutine dies with the panic recorded. *)
Lemma unified_all_effects : forall (msg boom : GoAny),
  exists cfg',
    usteps (mkUCfg
              (fun t => if Nat.eqb t 0
                        then UWrite 0 9 (USend 0 5 (URecv 0 (fun _ =>
                               UDfr (UOut (msg :: nil) URet) (UPan boom))))
                        else URet)
              (fun _ => nil) (fun _ => 0) (fun t => Nat.eqb t 0) nil
              nil (fun _ => nil) (fun _ => None))
           cfg'
    /\ uc_heap cfg' 0 = 9               (* the heap write landed *)
    /\ uc_out cfg' = (0, msg :: nil) :: nil   (* the deferred print happened, despite the panic *)
    /\ uc_panic cfg' 0 = Some boom      (* the panic was recorded *)
    /\ uc_live cfg' 0 = false.          (* the goroutine died *)
Proof.
  intros msg boom. eexists. split.
  - eapply usteps_step.
    { apply (ustep_write _ _ _ _ _ _ _ _ 0 0 9
               (USend 0 5 (URecv 0 (fun _ => UDfr (UOut (msg :: nil) URet) (UPan boom))))); reflexivity. }
    eapply usteps_step.
    { apply (ustep_send _ _ _ _ _ _ _ _ 0 0 5
               (URecv 0 (fun _ => UDfr (UOut (msg :: nil) URet) (UPan boom)))); reflexivity. }
    eapply usteps_step.
    { apply (ustep_recv _ _ _ _ _ _ _ _ 0 0 (fun _ => UDfr (UOut (msg :: nil) URet) (UPan boom))
               5 1 nil); reflexivity. }
    eapply usteps_step.
    { apply (ustep_defer _ _ _ _ _ _ _ _ 0 (UOut (msg :: nil) URet) (UPan boom)); reflexivity. }
    eapply usteps_step.
    { apply (ustep_pan_defer _ _ _ _ _ _ _ _ 0 boom (UOut (msg :: nil) URet) nil); reflexivity. }
    eapply usteps_step.
    { apply (ustep_out _ _ _ _ _ _ _ _ 0 (msg :: nil) URet); reflexivity. }
    eapply usteps_step.
    { apply (ustep_ret_done _ _ _ _ _ _ _ _ 0); reflexivity. }
    apply usteps_refl.
  - cbn. repeat split; reflexivity.
Qed.

(** ============================================================================
    SLICE 7 — observable behaviour is APPEND-ONLY: output and the trace only ever GROW under [ustep].

    A structural faithfulness property the shallow [run_io] could not have (it erased output): every
    step EXTENDS the output log and the event trace by a suffix — nothing already emitted is ever lost,
    overwritten, or reordered.  (Reinforces review #6 #12 on the authoritative semantics.) *)
Lemma ustep_out_grows : forall cfg cfg', ustep cfg cfg' -> exists s, uc_out cfg' = uc_out cfg ++ s.
Proof.
  intros cfg cfg' H. destruct H; cbn [uc_out];
    first [ exists (@nil (nat * list GoAny)); rewrite app_nil_r; reflexivity | eexists; reflexivity ].
Qed.

Lemma ustep_trace_grows : forall cfg cfg', ustep cfg cfg' -> exists s, uc_trace cfg' = uc_trace cfg ++ s.
Proof.
  intros cfg cfg' H. destruct H; cbn [uc_trace];
    first [ exists (@nil Ev); rewrite app_nil_r; reflexivity | eexists; reflexivity ].
Qed.

Lemma usteps_out_grows : forall cfg cfg', usteps cfg cfg' -> exists s, uc_out cfg' = uc_out cfg ++ s.
Proof.
  intros cfg cfg' H. induction H as [c | a b c Hab Hbc IH].
  - exists nil. rewrite app_nil_r. reflexivity.
  - destruct (ustep_out_grows a b Hab) as [s1 H1]. destruct IH as [s2 H2].
    exists (s1 ++ s2). rewrite H2, H1, app_assoc. reflexivity.
Qed.

Lemma usteps_trace_grows : forall cfg cfg', usteps cfg cfg' -> exists s, uc_trace cfg' = uc_trace cfg ++ s.
Proof.
  intros cfg cfg' H. induction H as [c | a b c Hab Hbc IH].
  - exists nil. rewrite app_nil_r. reflexivity.
  - destruct (ustep_trace_grows a b Hab) as [s1 H1]. destruct IH as [s2 H2].
    exists (s1 ++ s2). rewrite H2, H1, app_assoc. reflexivity.
Qed.
