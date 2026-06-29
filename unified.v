(** ============================================================================
    unified.v — the single unified (PROOF-ONLY) closed-world operational semantics for the model fragments.
    ⚠️ NOT the certified-emission path's semantics — a future GoSem must bridge or retire it before behavioral
    safety enters certified emission (see ARCHITECTURE.md).  "Authoritative" below means authoritative AMONG the
    proof-only model fragments (it unifies them), never Fido's certified-path semantics.

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
From Stdlib Require Import List Lia Arith FunctionalExtensionality.
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
  | UClose : nat -> UCmd -> UCmd                   (* close(ch); then k *)
  | USelect : list (nat * (nat -> UCmd)) -> UCmd.  (* select over recv cases (channel, value-binding cont) *)

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
(** Channel CAPACITY (review #8 P0-7): [ucap c] is channel [c]'s capacity — [None] = unbounded, [Some n] =
    a buffer holding at most [n].  [uroom ucap b c] is "[c] has room for one more send": always for unbounded,
    else iff the FIFO is shorter than the capacity.  A send STEPS only with room; a full-buffer send BLOCKS
    (it is a [ublocked] shape), exactly Go's buffered-channel semantics — so [ustep_send] is no longer the
    UNBOUNDED append the review flagged.  The relation is parametrised by [ucap]; the [rstep] embedding
    instantiates it to [fun _ => None] (unbounded), matching the unbounded [rstep] buffer. *)
Definition uroom (ucap : nat -> option nat) (b : nat -> list (nat * nat)) (c : nat) : bool :=
  match ucap c with
  | None   => true
  | Some n => Nat.ltb (length (b c)) n
  end.

Section UStepCap.
Variable ucap : nat -> option nat.

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
      lv tid = true -> p tid = USend c v k -> closedb tr c = false -> uroom ucap b c = true ->
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
            (mkUCfg (upd p tid (f 0)) b h lv (tr ++ [mkEv tid (KRecv c pos)]) o df pa)
  (* ---- SELECT: any ready case (buffered, or closed-drained) may fire — genuinely nondeterministic ---- *)
  | ustep_select : forall p b h lv tr o df pa tid cases c f v s brest,
      lv tid = true -> p tid = USelect cases ->
      In (c, f) cases -> b c = (v, s) :: brest ->
      ustep (mkUCfg p b h lv tr o df pa)
            (mkUCfg (upd p tid (f v)) (upd b c brest) h lv
                    (tr ++ [mkEv tid (KRecv c s)]) o df pa)
  | ustep_select_closed : forall p b h lv tr o df pa tid cases c f pos e,
      lv tid = true -> p tid = USelect cases ->
      In (c, f) cases -> b c = [] -> nth_error tr pos = Some e -> e_kind e = KClose c ->
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
  | UMF_close : forall c k, UMemFree k -> UMemFree (UClose c k)
  | UMF_select : forall cases, (forall c f, In (c, f) cases -> forall v, UMemFree (f v)) ->
                   UMemFree (USelect cases).

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
  | UOA_close : forall c k, UOnlyAcc P k -> UOnlyAcc P (UClose c k)
  | UOA_select : forall cases, (forall c f, In (c, f) cases -> forall v, UOnlyAcc P (f v)) ->
                   UOnlyAcc P (USelect cases).

Lemma umemfree_onlyacc : forall c, UMemFree c -> forall P, UOnlyAcc P c.
Proof.
  intros c H. induction H as
    [ | xs k Hk IHk | v | d k Hd IHd Hk2 IHk2 | c0 v0 k Hk IHk | c0 f Hf IHf
    | child k Hc IHc Hk2 IHk2 | c0 k Hk IHk | cases Hcs IHcs ]; intros P.
  - apply UOA_ret.
  - apply UOA_out; apply IHk.
  - apply UOA_pan.
  - apply UOA_dfr; [apply IHd | apply IHk2].
  - apply UOA_send; apply IHk.
  - apply UOA_recv; intros v; apply IHf.
  - apply UOA_spawn; [exact Hc | apply IHk2].
  - apply UOA_close; apply IHk.
  - apply UOA_select; intros c1 f1 Hin v; exact (IHcs c1 f1 Hin v P).
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
Lemma uoa_select_inv : forall P cases, UOnlyAcc P (USelect cases) ->
  forall c f, In (c, f) cases -> forall v, UOnlyAcc P (f v).
Proof. intros P cases H; inversion H; subst; assumption. Qed.

(* Select readiness for the unified calculus (mirrors concurrency.v's [sel_ready_cl]): the FIRST case
   whose channel is non-empty ([USR_buf]) or closed-drained ([USR_closed]); [None] iff every case is
   empty-and-open — the only genuinely blocking select. *)
Inductive USelReady : Type :=
  | USR_buf    (c : nat) (f : nat -> UCmd) (v s : nat)
  | USR_closed (c : nat) (f : nat -> UCmd).
Fixpoint usel_ready_cl (b : nat -> list (nat * nat)) (tr : Trace)
                       (cases : list (nat * (nat -> UCmd))) : option USelReady :=
  match cases with
  | nil => None
  | (c, f) :: rest =>
      match b c with
      | (v, s) :: _ => Some (USR_buf c f v s)
      | nil => if closedb tr c then Some (USR_closed c f) else usel_ready_cl b tr rest
      end
  end.
Lemma usel_ready_cl_buf : forall b tr cases c f v s,
  usel_ready_cl b tr cases = Some (USR_buf c f v s) ->
  In (c, f) cases /\ exists rest, b c = (v, s) :: rest.
Proof.
  induction cases as [|[c0 f0] rest IH]; intros c f v s H; cbn in H; [discriminate|].
  destruct (b c0) as [|[v0 s0] brest] eqn:Hb0.
  - destruct (closedb tr c0) eqn:Hcl0; [discriminate|].
    destruct (IH _ _ _ _ H) as [Hin Hex]. split; [right; exact Hin | exact Hex].
  - injection H as -> -> -> ->. split; [left; reflexivity | exists brest; exact Hb0].
Qed.
Lemma usel_ready_cl_closed : forall b tr cases c f,
  usel_ready_cl b tr cases = Some (USR_closed c f) ->
  In (c, f) cases /\ b c = nil /\ closedb tr c = true.
Proof.
  induction cases as [|[c0 f0] rest IH]; intros c f H; cbn in H; [discriminate|].
  destruct (b c0) as [|[v0 s0] brest] eqn:Hb0.
  - destruct (closedb tr c0) eqn:Hcl0.
    + injection H as -> ->. split; [left; reflexivity | split; [exact Hb0 | exact Hcl0]].
    + destruct (IH _ _ H) as [Hin [Hbc Hclc]]. split; [right; exact Hin | split; [exact Hbc | exact Hclc]].
  - discriminate.
Qed.
Lemma usel_ready_cl_none : forall b tr cases,
  usel_ready_cl b tr cases = None ->
  forall c f, In (c, f) cases -> b c = nil /\ closedb tr c = false.
Proof.
  induction cases as [|[c0 f0] rest IH]; intros H c f Hin; cbn in H; [inversion Hin|].
  destruct (b c0) as [|[v0 s0] brest] eqn:Hb0.
  - destruct (closedb tr c0) eqn:Hcl0; [discriminate|].
    destruct Hin as [Heq | Hin].
    + injection Heq as Hc Hf. subst c0. split; [exact Hb0 | exact Hcl0].
    + exact (IH H c f Hin).
  - discriminate.
Qed.

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
    | p b h lv tr o df pa tid c f pos e Hlv Hp Hbc Hpos Hek
    | p b h lv tr o df pa tid cases c f v s brest Hlv Hp Hin Hbc
    | p b h lv tr o df pa tid cases c f pos e Hlv Hp Hin Hbc Hpos Hek ];
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
  - (* select (buffered case (c,f) fires): cont f v; event KRecv (not memory) *)
    pose proof (Hprog tid Hlv) as HO. rewrite Hp in HO.
    split; [| split].
    + apply (TraceOwned_app own tr (mkEv tid (KRecv c s)) Htr). intros l' [Hw|Hr]; cbn in *; discriminate.
    + intros g Hg. exact (uonlyacc_upd own p tid (f v) lv g Hprog (uoa_select_inv _ _ HO c f Hin v) Hg).
    + exact Hdf.
  - (* select-closed (case (c,f) closed-drained): cont f 0; event KRecv (not memory) *)
    pose proof (Hprog tid Hlv) as HO. rewrite Hp in HO.
    split; [| split].
    + apply (TraceOwned_app own tr (mkEv tid (KRecv c pos)) Htr). intros l' [Hw|Hr]; cbn in *; discriminate.
    + intros g Hg. exact (uonlyacc_upd own p tid (f 0) lv g Hprog (uoa_select_inv _ _ HO c f Hin 0) Hg).
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
  (exists c f, uc_prog cfg tid = URecv c f
               /\ uc_bufs cfg c = [] /\ closedb (uc_trace cfg) c = false)
  \/ (exists cases, uc_prog cfg tid = USelect cases
                    /\ usel_ready_cl (uc_bufs cfg) (uc_trace cfg) cases = None)
  \/ (exists c v k, uc_prog cfg tid = USend c v k        (* blocked on a FULL buffer (review #8 P0-4/P0-7) *)
                    /\ closedb (uc_trace cfg) c = false /\ uroom ucap (uc_bufs cfg) c = false).

(** PROGRESS: a live goroutine that is NOT blocked-on-empty-open-recv means the whole config can step. *)
Theorem uready_can_step : forall cfg tid,
  UFreshAvail cfg -> uc_live cfg tid = true -> ~ ublocked cfg tid -> ucan_step cfg.
Proof.
  intros cfg tid [cid Hcid] Hlive Hnblk. destruct cfg as [p b h lv tr o df pa].
  cbn [uc_prog uc_bufs uc_trace uc_live] in *.
  destruct (p tid) as [ | xs k | v | d k | c v k | c f | l v k | l f | child k | c k | cases ] eqn:Hp.
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
    + destruct (uroom ucap b c) eqn:Er.
      * eexists. eapply ustep_send; [exact Hlive | exact Hp | exact Ecl | exact Er].
      * exfalso. apply Hnblk. right. right. exists c, v, k. split; [exact Hp | split; [exact Ecl | exact Er]].
  - (* URecv *) destruct (b c) as [|[v s] rest] eqn:Eb.
    + destruct (closedb tr c) eqn:Ecl.
      * destruct (closedb_true_witness _ _ Ecl) as [pos [e [Hpos Hek]]].
        eexists. eapply ustep_recv_closed; [exact Hlive | exact Hp | exact Eb | exact Hpos | exact Hek].
      * exfalso. apply Hnblk. left. exists c, f. split; [exact Hp | split; [exact Eb | exact Ecl]].
    + eexists. eapply ustep_recv; [exact Hlive | exact Hp | exact Eb].
  - eexists. eapply ustep_write; [exact Hlive | exact Hp].
  - eexists. eapply ustep_read; [exact Hlive | exact Hp].
  - eexists. eapply ustep_spawn; [exact Hlive | exact Hp | exact Hcid].
  - (* UClose *) destruct (closedb tr c) eqn:Ecl.
    + eexists. eapply ustep_close_closed; [exact Hlive | exact Hp | exact Ecl].
    + eexists. eapply ustep_close; [exact Hlive | exact Hp | exact Ecl].
  - (* USelect *) destruct (usel_ready_cl b tr cases) as [[c f v s | c f]|] eqn:Esel.
    + destruct (usel_ready_cl_buf _ _ _ _ _ _ _ Esel) as [Hin [rest Hb]].
      eexists. eapply ustep_select; [exact Hlive | exact Hp | exact Hin | exact Hb].
    + destruct (usel_ready_cl_closed _ _ _ _ _ Esel) as [Hin [Hb Hcl]].
      destruct (closedb_true_witness _ _ Hcl) as [pos [e [Hpos Hek]]].
      eexists. eapply ustep_select_closed; [exact Hlive | exact Hp | exact Hin | exact Hb | exact Hpos | exact Hek].
    + exfalso. apply Hnblk. right. left. exists cases. split; [exact Hp | exact Esel].
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
  destruct (p tid) as [ | xs k | v | d k | c v k | c f | l v k | l f | child k | c k | cases ] eqn:Hp.
  - exfalso. apply Hnstep. destruct (df tid) as [|d ds] eqn:E.
    + eexists. eapply ustep_ret_done; [exact Hlive | exact Hp | exact E].
    + eexists. eapply ustep_ret_defer; [exact Hlive | exact Hp | exact E].
  - exfalso. apply Hnstep. eexists. eapply ustep_out; [exact Hlive | exact Hp].
  - exfalso. apply Hnstep. destruct (df tid) as [|d ds] eqn:E.
    + eexists. eapply ustep_pan_done; [exact Hlive | exact Hp | exact E].
    + eexists. eapply ustep_pan_defer; [exact Hlive | exact Hp | exact E].
  - exfalso. apply Hnstep. eexists. eapply ustep_defer; [exact Hlive | exact Hp].
  - (* USend *) destruct (closedb tr c) eqn:Ecl.
    + exfalso. apply Hnstep. eexists. eapply ustep_send_closed; [exact Hlive | exact Hp | exact Ecl].
    + destruct (uroom ucap b c) eqn:Er.
      * exfalso. apply Hnstep. eexists. eapply ustep_send; [exact Hlive | exact Hp | exact Ecl | exact Er].
      * (* full buffer: a blocking shape *) right. right. exists c, v, k. split; [exact Hp | split; [exact Ecl | exact Er]].
  - (* URecv: a blocking shape *) destruct (b c) as [|[v s] rest] eqn:Eb.
    + destruct (closedb tr c) eqn:Ecl.
      * exfalso. apply Hnstep. destruct (closedb_true_witness _ _ Ecl) as [pos [e [Hpos Hek]]].
        eexists. eapply ustep_recv_closed; [exact Hlive | exact Hp | exact Eb | exact Hpos | exact Hek].
      * left. exists c, f. split; [exact Hp | split; [exact Eb | exact Ecl]].
    + exfalso. apply Hnstep. eexists. eapply ustep_recv; [exact Hlive | exact Hp | exact Eb].
  - exfalso. apply Hnstep. eexists. eapply ustep_write; [exact Hlive | exact Hp].
  - exfalso. apply Hnstep. eexists. eapply ustep_read; [exact Hlive | exact Hp].
  - exfalso. apply Hnstep. eexists. eapply ustep_spawn; [exact Hlive | exact Hp | exact Hcid].
  - exfalso. apply Hnstep. destruct (closedb tr c) eqn:Ecl.
    + eexists. eapply ustep_close_closed; [exact Hlive | exact Hp | exact Ecl].
    + eexists. eapply ustep_close; [exact Hlive | exact Hp | exact Ecl].
  - (* USelect: the OTHER blocking shape (no ready case) *)
    destruct (usel_ready_cl b tr cases) as [[c f v s | c f]|] eqn:Esel.
    + exfalso. apply Hnstep. destruct (usel_ready_cl_buf _ _ _ _ _ _ _ Esel) as [Hin [rest Hb]].
      eexists. eapply ustep_select; [exact Hlive | exact Hp | exact Hin | exact Hb].
    + exfalso. apply Hnstep. destruct (usel_ready_cl_closed _ _ _ _ _ Esel) as [Hin [Hb Hcl]].
      destruct (closedb_true_witness _ _ Hcl) as [pos [e [Hpos Hek]]].
      eexists. eapply ustep_select_closed; [exact Hlive | exact Hp | exact Hin | exact Hb | exact Hpos | exact Hek].
    + right. left. exists cases. split; [exact Hp | exact Esel].
Qed.

End UStepCap.

(** Make the capacity [ucap] IMPLICIT on the constructors (a section [Variable] generalises explicit, unlike
    an inductive parameter) — so the positional [apply (ustep_X _ … )] proofs and the [embed] cases infer it
    from the goal, while the RELATION [ustep ucap …] keeps it explicit for statements. *)
Arguments ustep_write {ucap}.   Arguments ustep_read {ucap}.
Arguments ustep_send {ucap}.    Arguments ustep_recv {ucap}.
Arguments ustep_close {ucap}.   Arguments ustep_spawn {ucap}.
Arguments ustep_out {ucap}.     Arguments ustep_defer {ucap}.
Arguments ustep_ret_defer {ucap}.  Arguments ustep_ret_done {ucap}.
Arguments ustep_pan_defer {ucap}.  Arguments ustep_pan_done {ucap}.
Arguments ustep_send_closed {ucap}.  Arguments ustep_close_closed {ucap}.
Arguments ustep_recv_closed {ucap}.  Arguments ustep_select {ucap}.
Arguments ustep_select_closed {ucap}.
Arguments usteps_refl {ucap}.   Arguments usteps_step {ucap}.

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
    usteps (fun _ => None) (mkUCfg (fun t => if Nat.eqb t 0 then UPan pv else URet)
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
    usteps (fun _ => None) (mkUCfg (fun t => if Nat.eqb t 0 then UWrite 0 7 (URead 0 k) else URet)
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
    usteps (fun _ => None) (mkUCfg (fun t => if Nat.eqb t 0 then USend 0 5 (URecv 0 k) else URet)
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
    usteps (fun _ => None) (mkUCfg (fun t => if Nat.eqb t 0 then UOut (x :: nil) (UOut (y :: nil) URet) else URet)
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
    usteps (fun _ => None) (mkUCfg
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
Lemma ustep_out_grows : forall {ucap} cfg cfg', ustep ucap cfg cfg' -> exists s, uc_out cfg' = uc_out cfg ++ s.
Proof.
  intros ucap cfg cfg' H. destruct H; cbn [uc_out];
    first [ exists (@nil (nat * list GoAny)); rewrite app_nil_r; reflexivity | eexists; reflexivity ].
Qed.

Lemma ustep_trace_grows : forall {ucap} cfg cfg', ustep ucap cfg cfg' -> exists s, uc_trace cfg' = uc_trace cfg ++ s.
Proof.
  intros ucap cfg cfg' H. destruct H; cbn [uc_trace];
    first [ exists (@nil Ev); rewrite app_nil_r; reflexivity | eexists; reflexivity ].
Qed.

Lemma usteps_out_grows : forall {ucap} cfg cfg', usteps ucap cfg cfg' -> exists s, uc_out cfg' = uc_out cfg ++ s.
Proof.
  intros ucap cfg cfg' H. induction H as [c | a b c Hab Hbc IH].
  - exists nil. rewrite app_nil_r. reflexivity.
  - destruct (ustep_out_grows a b Hab) as [s1 H1]. destruct IH as [s2 H2].
    exists (s1 ++ s2). rewrite H2, H1, app_assoc. reflexivity.
Qed.

Lemma usteps_trace_grows : forall {ucap} cfg cfg', usteps ucap cfg cfg' -> exists s, uc_trace cfg' = uc_trace cfg ++ s.
Proof.
  intros ucap cfg cfg' H. induction H as [c | a b c Hab Hbc IH].
  - exists nil. rewrite app_nil_r. reflexivity.
  - destruct (ustep_trace_grows a b Hab) as [s1 H1]. destruct IH as [s2 H2].
    exists (s1 ++ s2). rewrite H2, H1, app_assoc. reflexivity.
Qed.

(** ============================================================================
    SLICE 9 — THE EMBEDDING: the rich value-carrying calculus [rstep] IS a fragment of [ustep].

    This is the formal answer to the architectural finding ("no single authoritative semantics over
    goroutines+channels+heap+panic+defer+output").  We give a structure-preserving map [embed_cmd :
    concurrency.Cmd -> UCmd] / [embed_cfg : RConfig -> UConfig] and prove a FORWARD SIMULATION: every
    [rstep] is mirrored, rule-for-rule, by a [ustep] on the embedded configurations
    ([rstep_embeds]), lifted to runs ([rsteps_embeds]).  Because the embedding is the IDENTITY on the
    trace ([embed_cfg_trace]), every trace-based result already proved for [rstep] runs (well-formed
    traces, happens-before, the ownership/race-freedom discipline) is — verbatim — a statement about
    [ustep] runs.  So [ustep] is not a competing semantics: the rich calculus is literally [ustep]
    restricted to the panic/defer/output-free sub-language, and [ustep] only ADDS the missing effects.

    The one boundary subtlety: [embed_cmd] must commute with [upd] on the program map (and, at a spawn,
    with the constant defer/panic maps).  These are pointwise equalities of FUNCTIONS, discharged by
    [functional_extensionality] — already part of the project's trust base (builtins.v [run_io_inj]),
    and NOT in [main_effect]'s cone, so [EXPECTED_ASSUMPTIONS.txt] stays empty and the axiom gate is
    unaffected.  ([Print Assumptions rstep_embeds] therefore shows [functional_extensionality]; this is
    the same funext the END-TO-END TRUST BASE already discloses, introduced nowhere new logically.) *)

(* The select cases carry value-binding continuations ([nat -> Cmd]) inside a [list].  Coq's guard
   checker cannot see a recursive [embed_cmd] call through either [List.map] OR a mutual companion
   fixpoint ([f v] is rejected as "not a subterm of rest").  The canonical idiom that IS accepted: an
   INLINED local fixpoint over the case list, in the [CSelect] branch — there the checker tracks that
   [xs]'s elements are subterms of [cs], hence of [c], so [embed_cmd (f v)] is a guarded call to the
   enclosing [embed_cmd]. *)
Fixpoint embed_cmd (c : Cmd) : UCmd :=
  match c with
  | CRet         => URet
  | CSend ch v k => USend ch v (embed_cmd k)
  | CRecv ch f   => URecv ch (fun v => embed_cmd (f v))
  | CWrite l v k => UWrite l v (embed_cmd k)
  | CRead l f    => URead l (fun v => embed_cmd (f v))
  | CSpawn ch k  => USpawn (embed_cmd ch) (embed_cmd k)
  | CSelect cs   =>
      USelect ((fix emb_cs (xs : list (nat * (nat -> Cmd))) : list (nat * (nat -> UCmd)) :=
                  match xs with
                  | []              => []
                  | (ch, f) :: rest => (ch, fun v => embed_cmd (f v)) :: emb_cs rest
                  end) cs)
  | CClose ch k  => UClose ch (embed_cmd k)
  end.

(* A STANDALONE companion (no longer mutual — [embed_cmd] is already a closed constant here, so its
   call inside is not a recursive call and needs no guard).  It is CONVERTIBLE to the [CSelect]
   branch's inlined fix, so [embed_cmd (CSelect cs)] reduces to [USelect (embed_cases cs)] — letting
   the select rules reason about [In] over this named form. *)
Fixpoint embed_cases (cs : list (nat * (nat -> Cmd))) : list (nat * (nat -> UCmd)) :=
  match cs with
  | []             => []
  | (ch, f) :: rest => (ch, fun v => embed_cmd (f v)) :: embed_cases rest
  end.

Lemma embed_cmd_select : forall cs, embed_cmd (CSelect cs) = USelect (embed_cases cs).
Proof. reflexivity. Qed.

Definition embed_cfg (cfg : RConfig) : UConfig :=
  mkUCfg (fun t => embed_cmd (rc_prog cfg t))
         (rc_bufs cfg) (rc_heap cfg) (rc_live cfg) (rc_trace cfg)
         nil (fun _ => nil) (fun _ => None).

(** [embed_cmd] commutes with a single-slot program update — the only non-definitional step. *)
Lemma embed_upd_prog : forall (p : nat -> Cmd) (tid : nat) (k : Cmd),
  (fun t => embed_cmd (upd p tid k t)) = upd (fun t => embed_cmd (p t)) tid (embed_cmd k).
Proof.
  intros p tid k. apply functional_extensionality. intro t.
  destruct (Nat.eq_dec t tid) as [-> | Hne].
  - rewrite !upd_same. reflexivity.
  - rewrite !(upd_other _ _ _ _ Hne). reflexivity.
Qed.

(** A spawn resets the fresh child's defer/panic to the empty maps — which the constant embedded maps
    already are; [upd c nil/None] of a constant map is that same constant map (pointwise). *)
Lemma upd_const_nil : forall cid : nat, upd (fun _ : nat => @nil UCmd) cid nil = (fun _ => nil).
Proof.
  intro cid. apply functional_extensionality. intro x.
  destruct (Nat.eq_dec x cid) as [-> | Hne].
  - rewrite upd_same. reflexivity.
  - rewrite (upd_other _ _ _ _ Hne). reflexivity.
Qed.

Lemma upd_const_none : forall cid : nat, upd (fun _ : nat => @None GoAny) cid None = (fun _ => None).
Proof.
  intro cid. apply functional_extensionality. intro x.
  destruct (Nat.eq_dec x cid) as [-> | Hne].
  - rewrite upd_same. reflexivity.
  - rewrite (upd_other _ _ _ _ Hne). reflexivity.
Qed.

(** [In] is preserved under [embed_cases] — needed for the two select rules. *)
Lemma in_embed_cases : forall cs c f,
  In (c, f) cs -> In (c, fun v => embed_cmd (f v)) (embed_cases cs).
Proof.
  induction cs as [ | [ch g] rest IH ]; cbn; intros c f H; [ contradiction | ].
  destruct H as [Heq | Hin].
  - injection Heq; intros Hg Hch; subst. left; reflexivity.
  - right. apply IH. exact Hin.
Qed.

(** THE forward simulation: every [rstep] is a [ustep] on the embedded configs — rule for rule. *)
Theorem rstep_embeds : forall cfg cfg', rstep cfg cfg' -> ustep (fun _ => None) (embed_cfg cfg) (embed_cfg cfg').
Proof.
  intros cfg cfg' H. destruct H as
    [ p b h lv tr tid c v k Hlv Hp Hcl
    | p b h lv tr tid c f v s brest Hlv Hp Hbc
    | p b h lv tr tid l v k Hlv Hp
    | p b h lv tr tid l f Hlv Hp
    | p b h lv tr tid child k cid Hlv Hp Hcid
    | p b h lv tr tid cases c f v s brest Hlv Hp Hin Hbc
    | p b h lv tr tid c k Hlv Hp Hcl
    | p b h lv tr tid c f pos e Hlv Hp Hbc Hpos Hek
    | p b h lv tr tid cases c f pos e Hlv Hp Hin Hbc Hpos Hek ].
  - (* send *)
    unfold embed_cfg; cbn [rc_prog rc_bufs rc_heap rc_live rc_trace].
    rewrite (embed_upd_prog p tid k).
    apply ustep_send; [ exact Hlv | cbn beta; rewrite Hp; reflexivity | exact Hcl | reflexivity ].
  - (* recv *)
    unfold embed_cfg; cbn [rc_prog rc_bufs rc_heap rc_live rc_trace].
    rewrite (embed_upd_prog p tid (f v)).
    apply ustep_recv with (f := fun w => embed_cmd (f w)) (v := v);
      [ exact Hlv | cbn beta; rewrite Hp; reflexivity | exact Hbc ].
  - (* write *)
    unfold embed_cfg; cbn [rc_prog rc_bufs rc_heap rc_live rc_trace].
    rewrite (embed_upd_prog p tid k).
    apply ustep_write; [ exact Hlv | cbn beta; rewrite Hp; reflexivity ].
  - (* read *)
    unfold embed_cfg; cbn [rc_prog rc_bufs rc_heap rc_live rc_trace].
    rewrite (embed_upd_prog p tid (f (h l))).
    apply ustep_read with (f := fun w => embed_cmd (f w));
      [ exact Hlv | cbn beta; rewrite Hp; reflexivity ].
  - (* spawn — also resets the child's (constant) defer/panic maps *)
    assert (HT : embed_cfg (mkRCfg (upd (upd p tid k) cid child) b h (upd lv cid true)
                    (tr ++ [mkEv tid (KSpawn cid); mkEv cid (KStart (length tr))]))
               = mkUCfg (upd (upd (fun t => embed_cmd (p t)) tid (embed_cmd k)) cid (embed_cmd child))
                        b h (upd lv cid true)
                        (tr ++ [mkEv tid (KSpawn cid); mkEv cid (KStart (length tr))])
                        nil (upd (fun _ => nil) cid nil) (upd (fun _ => None) cid None)).
    { unfold embed_cfg; cbn [rc_prog rc_bufs rc_heap rc_live rc_trace]. f_equal.
      - rewrite (embed_upd_prog (upd p tid k) cid child), (embed_upd_prog p tid k). reflexivity.
      - symmetry. apply upd_const_nil.
      - symmetry. apply upd_const_none. }
    rewrite HT. unfold embed_cfg; cbn [rc_prog rc_bufs rc_heap rc_live rc_trace].
    apply ustep_spawn; [ exact Hlv | cbn beta; rewrite Hp; reflexivity | exact Hcid ].
  - (* select *)
    unfold embed_cfg; cbn [rc_prog rc_bufs rc_heap rc_live rc_trace].
    rewrite (embed_upd_prog p tid (f v)).
    apply ustep_select with (cases := embed_cases cases) (c := c) (f := fun w => embed_cmd (f w)) (v := v);
      [ exact Hlv | cbn beta; rewrite Hp; reflexivity
      | apply in_embed_cases; exact Hin | exact Hbc ].
  - (* close *)
    unfold embed_cfg; cbn [rc_prog rc_bufs rc_heap rc_live rc_trace].
    rewrite (embed_upd_prog p tid k).
    apply ustep_close; [ exact Hlv | cbn beta; rewrite Hp; reflexivity | exact Hcl ].
  - (* recv from a closed, drained channel *)
    unfold embed_cfg; cbn [rc_prog rc_bufs rc_heap rc_live rc_trace].
    rewrite (embed_upd_prog p tid (f 0)).
    apply ustep_recv_closed with (c := c) (f := fun w => embed_cmd (f w)) (pos := pos) (e := e);
      [ exact Hlv | cbn beta; rewrite Hp; reflexivity | exact Hbc | exact Hpos | exact Hek ].
  - (* select on a closed, drained case *)
    unfold embed_cfg; cbn [rc_prog rc_bufs rc_heap rc_live rc_trace].
    rewrite (embed_upd_prog p tid (f 0)).
    apply ustep_select_closed with (cases := embed_cases cases) (c := c) (f := fun w => embed_cmd (f w)) (pos := pos) (e := e);
      [ exact Hlv | cbn beta; rewrite Hp; reflexivity
      | apply in_embed_cases; exact Hin | exact Hbc | exact Hpos | exact Hek ].
Qed.

(** Lifted to runs: an [rsteps] execution embeds into a [usteps] execution. *)
Theorem rsteps_embeds : forall cfg cfg', rsteps cfg cfg' -> usteps (fun _ => None) (embed_cfg cfg) (embed_cfg cfg').
Proof.
  intros cfg cfg' H. induction H as [c | a b c Hab Hbc IH].
  - apply usteps_refl.
  - eapply usteps_step; [ apply rstep_embeds; exact Hab | exact IH ].
Qed.

(** The embedding is the IDENTITY on the trace — so every trace-based safety result about [rstep]
    runs is, verbatim, a result about the corresponding [ustep] runs. *)
Lemma embed_cfg_trace : forall cfg, uc_trace (embed_cfg cfg) = rc_trace cfg.
Proof. intro cfg. reflexivity. Qed.

(** Capstone: a rich-calculus run is mirrored step-for-step by the unified semantics with an IDENTICAL
    trace.  This is the formal sense in which [ustep] is THE one authoritative semantics — [rstep]'s
    every behaviour (and thus every theorem stated over [rstep]'s traces) lives inside it. *)
Corollary rsteps_trace_embeds : forall cfg cfg', rsteps cfg cfg' ->
  usteps (fun _ => None) (embed_cfg cfg) (embed_cfg cfg') /\ uc_trace (embed_cfg cfg') = rc_trace cfg'.
Proof.
  intros cfg cfg' H. split.
  - apply rsteps_embeds; exact H.
  - apply embed_cfg_trace.
Qed.

(** The BOUNDED-CAPACITY calculus is a fragment too: [rstepC]'s [rstepsC_embed] already shows every
    bounded run is an unbounded [rsteps] run (a guarded send is a plain send; a cap-0 rendezvous is
    send-then-recv), so composing with [rsteps_embeds] subsumes the capacity-aware calculus into
    [ustep] as well — closing the 2026-06-24 review's #2/#3 ("capacity rendezvous in a detached
    calculus").  BOTH prior operational systems are now provably fragments of the one semantics. *)
Corollary rstepsC_embeds : forall cap cfg cfg', rstepsC cap cfg cfg' ->
  usteps (fun _ => None) (embed_cfg cfg) (embed_cfg cfg').
Proof. intros cap cfg cfg' H. apply rsteps_embeds. exact (rstepsC_embed _ _ _ H). Qed.

(** ============================================================================
    SLICE 10 — SESSIONS, OPERATIONALLY: a protocol is REALIZED by a [ustep] run.

    The 2026-06-24 review's finding #10: the session theory (concurrency.v [PSess]/[PEmits]/
    [psess_emits_proto]) is "primarily about protocol SYNTAX" — it reads the send/recv sequence off a
    session TERM's structure ([PEmits]) but never ties it to an EXECUTION.  Here we give a protocol an
    OPERATIONAL meaning on the one authoritative semantics.  [proto_ucmd] compiles a [Proto] to a
    [UCmd]: each [PSend] is a [USend] on an open channel [cs]; each [PRecv] is a [URecv] on a channel
    [cr] that is already CLOSED + drained — Go's "the partner has finished and closed", so every recv
    is READY and yields the zero value (no rendezvous bookkeeping needed).  [proto_ucmd_realizes] then
    proves: the [ustep] run of [proto_ucmd ... p] runs to completion and emits a trace whose SEND/RECV
    polarity sequence is EXACTLY the protocol's ([proto_polarity p]).  Composed with the syntactic
    [psess_full_emits_proto], this is the port: a session-typed term's behavioural spec ([PEmits]) is
    realized, step-for-step, by a concrete execution of the unified semantics. *)

(** The send/recv polarity sequence a protocol prescribes (send = [true]). *)
Fixpoint proto_polarity (p : Proto) : list bool :=
  match p with
  | builtins.PSend _ p' => true  :: proto_polarity p'
  | builtins.PRecv _ p' => false :: proto_polarity p'
  | PEnd                 => []
  end.

(** The polarity an event contributes (only channel send/recv are communication). *)
Definition ev_polarity (e : Ev) : option bool :=
  match e_kind e with KSend _ => Some true | KRecv _ _ => Some false | _ => None end.

Fixpoint trace_polarity (tr : Trace) : list bool :=
  match tr with
  | []        => []
  | e :: rest => match ev_polarity e with Some b => b :: trace_polarity rest | None => trace_polarity rest end
  end.

Lemma trace_polarity_app : forall t1 t2, trace_polarity (t1 ++ t2) = trace_polarity t1 ++ trace_polarity t2.
Proof.
  induction t1 as [ | e rest IH ]; intro t2; cbn; [ reflexivity | ].
  destruct (ev_polarity e); cbn; rewrite IH; reflexivity.
Qed.

(** Compile a protocol to a unified-semantics program: send on [cs], recv on the pre-closed [cr]. *)
Fixpoint proto_ucmd (cs cr val : nat) (p : Proto) : UCmd :=
  match p with
  | builtins.PSend _ p' => USend cs val (proto_ucmd cs cr val p')
  | builtins.PRecv _ p' => URecv cr (fun _ => proto_ucmd cs cr val p')
  | PEnd                 => URet
  end.

(** THE operational realization: the [ustep] run of [proto_ucmd ... p] for goroutine [tid] terminates
    ([URet]) having emitted EXACTLY the protocol's send/recv polarity sequence, given only that [cs] is
    open and [cr] is closed+drained in the starting state.  (Carried through the induction: appending
    [KSend cs]/[KRecv cr] never closes [cs], never fills [cr], and preserves [cr]'s close at [pos].) *)
Theorem proto_ucmd_realizes :
  forall (p : Proto) (cs cr val tid pos : nat) (prg : nat -> UCmd)
         (b : nat -> list (nat * nat)) (h : nat -> nat) (lv : nat -> bool)
         (tr : Trace) (o : list (nat * list GoAny)) (df : nat -> list UCmd)
         (pa : nat -> option GoAny) (ecl : Ev),
    cs <> cr ->
    lv tid = true ->
    b cr = [] ->
    closedb tr cs = false ->
    nth_error tr pos = Some ecl -> e_kind ecl = KClose cr ->
    prg tid = proto_ucmd cs cr val p ->
    exists cfg',
      usteps (fun _ => None) (mkUCfg prg b h lv tr o df pa) cfg'
      /\ uc_prog cfg' tid = URet
      /\ trace_polarity (uc_trace cfg') = trace_polarity tr ++ proto_polarity p.
Proof.
  induction p as [ A p' IH | A p' IH | ]; intros cs cr val tid pos prg b h lv tr o df pa ecl
    Hne Hlv Hbcr Hcs Hpos Hek Hprg.
  - (* PSend: a send on the open [cs] fires, then recurse *)
    pose (prg' := upd prg tid (proto_ucmd cs cr val p')).
    pose (b'   := upd b cs (b cs ++ [(val, length tr)])).
    assert (Hstep : ustep (fun _ => None) (mkUCfg prg b h lv tr o df pa)
                          (mkUCfg prg' b' h lv (tr ++ [mkEv tid (KSend cs)]) o df pa)).
    { apply ustep_send; [ exact Hlv | rewrite Hprg; reflexivity | exact Hcs | reflexivity ]. }
    assert (Hcr' : b' cr = []) by (unfold b'; rewrite (upd_other _ _ _ _ (not_eq_sym Hne)); exact Hbcr).
    assert (Hcs' : closedb (tr ++ [mkEv tid (KSend cs)]) cs = false)
      by (rewrite closedb_app, Hcs; reflexivity).
    assert (Hpos' : nth_error (tr ++ [mkEv tid (KSend cs)]) pos = Some ecl)
      by (rewrite nth_error_app_old by (eapply nth_error_lt; exact Hpos); exact Hpos).
    assert (Hprg' : prg' tid = proto_ucmd cs cr val p') by (unfold prg'; rewrite upd_same; reflexivity).
    destruct (IH cs cr val tid pos prg' b' h lv (tr ++ [mkEv tid (KSend cs)]) o df pa ecl
                 Hne Hlv Hcr' Hcs' Hpos' Hek Hprg') as [cfg' [Hrun [Hdone Htr]]].
    exists cfg'. split; [ eapply usteps_step; [ exact Hstep | exact Hrun ] | split; [ exact Hdone | ] ].
    rewrite Htr, trace_polarity_app. cbn. rewrite <- app_assoc. reflexivity.
  - (* PRecv: a recv on the closed+drained [cr] fires (yields zero), then recurse *)
    pose (prg' := upd prg tid (proto_ucmd cs cr val p')).
    assert (Hstep : ustep (fun _ => None) (mkUCfg prg b h lv tr o df pa)
                          (mkUCfg prg' b h lv (tr ++ [mkEv tid (KRecv cr pos)]) o df pa)).
    { apply ustep_recv_closed with (c := cr) (f := fun _ => proto_ucmd cs cr val p') (pos := pos) (e := ecl);
        [ exact Hlv | rewrite Hprg; reflexivity | exact Hbcr | exact Hpos | exact Hek ]. }
    assert (Hcs' : closedb (tr ++ [mkEv tid (KRecv cr pos)]) cs = false)
      by (rewrite closedb_app, Hcs; reflexivity).
    assert (Hpos' : nth_error (tr ++ [mkEv tid (KRecv cr pos)]) pos = Some ecl)
      by (rewrite nth_error_app_old by (eapply nth_error_lt; exact Hpos); exact Hpos).
    assert (Hprg' : prg' tid = proto_ucmd cs cr val p') by (unfold prg'; rewrite upd_same; reflexivity).
    destruct (IH cs cr val tid pos prg' b h lv (tr ++ [mkEv tid (KRecv cr pos)]) o df pa ecl
                 Hne Hlv Hbcr Hcs' Hpos' Hek Hprg') as [cfg' [Hrun [Hdone Htr]]].
    exists cfg'. split; [ eapply usteps_step; [ exact Hstep | exact Hrun ] | split; [ exact Hdone | ] ].
    rewrite Htr, trace_polarity_app. cbn. rewrite <- app_assoc. reflexivity.
  - (* PEnd: already at URet, no step, no events *)
    exists (mkUCfg prg b h lv tr o df pa).
    split; [ apply usteps_refl | split ].
    + cbn [uc_prog]. rewrite Hprg. reflexivity.
    + cbn [uc_trace]. rewrite app_nil_r. reflexivity.
Qed.

(** [proto_polarity] is [proto_steps] with the value-types erased to polarities — the bridge to the
    syntactic session theory, whose [PEmits] sequence is in [StepKind]. *)
Definition step_polarity (sk : StepKind) : bool :=
  match sk with PKSend _ => true | PKRecv _ => false end.

Lemma proto_polarity_steps : forall p, proto_polarity p = map step_polarity (proto_steps p).
Proof. induction p as [ A p' IH | A p' IH | ]; cbn; [ rewrite IH | rewrite IH | ]; reflexivity. Qed.

(** THE PORT: a COMPLETE session-typed term ([PSess i PEnd A]) — the forge-proof extracted [Sess] —
    has its syntactic communication spec ([PEmits s steps], hence [steps = proto_steps i]) REALIZED by
    a concrete [ustep] execution: running [proto_ucmd] for protocol [i] terminates having emitted a
    trace whose send/recv polarity sequence is precisely [map step_polarity steps].  The session
    indices are no longer "just syntax" — they are a behavioural spec the unified semantics enacts. *)
Corollary psess_realized_operationally :
  forall (i : Proto) (A : Type) (s : PSess i PEnd A) (steps : list StepKind)
         (cs cr val tid pos : nat) (prg : nat -> UCmd)
         (b : nat -> list (nat * nat)) (h : nat -> nat) (lv : nat -> bool)
         (tr : Trace) (o : list (nat * list GoAny)) (df : nat -> list UCmd)
         (pa : nat -> option GoAny) (ecl : Ev),
    PEmits s steps ->
    cs <> cr -> lv tid = true -> b cr = [] -> closedb tr cs = false ->
    nth_error tr pos = Some ecl -> e_kind ecl = KClose cr ->
    prg tid = proto_ucmd cs cr val i ->
    exists cfg',
      usteps (fun _ => None) (mkUCfg prg b h lv tr o df pa) cfg'
      /\ uc_prog cfg' tid = URet
      /\ trace_polarity (uc_trace cfg') = trace_polarity tr ++ map step_polarity steps.
Proof.
  intros i A s steps cs cr val tid pos prg b h lv tr o df pa ecl Hem
         Hne Hlv Hbcr Hcs Hpos Hek Hprg.
  apply psess_full_emits_proto in Hem. subst steps.
  destruct (proto_ucmd_realizes i cs cr val tid pos prg b h lv tr o df pa ecl
              Hne Hlv Hbcr Hcs Hpos Hek Hprg) as [cfg' [Hrun [Hdone Htr]]].
  exists cfg'. split; [ exact Hrun | split; [ exact Hdone | ] ].
  rewrite Htr, proto_polarity_steps. reflexivity.
Qed.

(** ============================================================================
    REVIEW #8 P0-7 REGRESSION — [ustep_send] is no longer the UNBOUNDED append.
    A send onto a FULL bounded channel ([Some n], buffer already length n) has NO room, so it does NOT
    step — instead the goroutine is [ublocked] on a full buffer (Go's buffered-send-blocks).  Contrast: an
    [None] (unbounded) channel always has room.  These witness that [ustep_send]'s new [uroom] premise
    actually bites (the capacity is enforced, not vacuous). *)
Example uroom_full_no_room  : uroom (fun _ => Some 1) (fun _ => [(7, 0)]) 0 = false.
Proof. reflexivity. Qed.
Example uroom_unbounded_ok  : uroom (fun _ => None) (fun _ => [(7, 0)]) 0 = true.
Proof. reflexivity. Qed.
Example full_send_is_ublocked :
  ublocked (fun _ => Some 1)
           (mkUCfg (fun _ => USend 0 9 URet) (fun _ => [(7, 0)]) (fun _ => 0)
                   (fun t => Nat.eqb t 0) nil nil (fun _ => nil) (fun _ => None)) 0.
Proof. right. right. exists 0, 9, URet. cbn. split; [ reflexivity | split; reflexivity ]. Qed.
