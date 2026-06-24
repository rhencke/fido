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
                    (tr ++ [mkEv tid (KSpawn cid); mkEv cid (KStart (length tr))]) o df pa)
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
