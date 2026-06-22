(** Trace-based happens-before for ARBITRARY executions.

    The Phase 1..4 model in [builtins.v] proves the go-mem ordering RULES are a
    consistent strict partial order and defeat data races — but on HAND-BUILT event
    sets ([ChEvent], [mp_hb], [fork_hb], …).  This module ties happens-before to an
    ACTUAL EXECUTION TRACE: a list of events produced by interleaving goroutines,
    where synchronisation is recorded by BACK-POINTERS — a receive carries the trace
    position of the send that produced its value; a goroutine's first step carries
    the position of the [go] that spawned it.  These back-pointers are exactly what a
    real run records.

    CENTRAL THEOREM ([hbt_irrefl]): for ANY well-formed trace, happens-before
    (program order ∪ synchronisation) is a STRICT PARTIAL ORDER — because the TRACE
    POSITION (the interleaving order) is a LINEAR EXTENSION of it: you cannot
    synchronise with the future.  This GENERALISES the bespoke [ev_ts] timestamp to
    arbitrary executions and arbitrary goroutine/channel topologies — the missing
    bridge between the abstract rules and real operations.  Axiom-free. *)
From Fido Require Import preamble.
From Stdlib Require Import List Lia Arith.
Require Import Stdlib.Numbers.Cyclic.Int63.PrimInt63.   (* [int] (Go int64) — the keystone value carrier *)
Import ListNotations.

Inductive EvKind :=
  | KSend  (chan : nat)
  | KRecv  (chan : nat) (from : nat)   (* the value's producer is at trace position [from]: a
                                          matched SEND, or — for a recv that returns the zero value
                                          because the channel is closed and drained — the CLOSE. *)
  | KSpawn (child : nat)
  | KStart (parent : nat)              (* this goroutine was spawned at position [parent] *)
  | KWrite (loc : nat)
  | KRead  (loc : nat)
  | KClose (chan : nat).               (* close(ch): per the Go memory model, a close happens-before
                                          a recv that returns zero because the channel is closed. *)

Record Ev := mkEv { e_tid : nat; e_kind : EvKind }.
Definition Trace := list Ev.

Definition tid_at (t : Trace) (i : nat) : nat :=
  match nth_error t i with Some e => e_tid e | None => 0 end.

(** A trace is WELL-FORMED when every back-pointer points to an EARLIER event of the
    right kind: a receive's [from] is an earlier send on the same channel; a start's
    [parent] is an earlier spawn OF THAT SAME GOROUTINE (the spawn's [child] = this
    start's own [e_tid]).  A real execution always satisfies this — you receive a value
    already sent, and a goroutine runs after the [go] that spawned IT.  (Break #8 fix:
    the child-identity clause was missing, so a [KStart] could point at a [KSpawn] of a
    DIFFERENT child — forging a spawn happens-before edge to an unrelated goroutine.) *)
Definition WfTrace (t : Trace) : Prop :=
  forall i e, nth_error t i = Some e ->
    match e_kind e with
    | KRecv c from =>
        from < i /\ exists e', nth_error t from = Some e' /\
                              (e_kind e' = KSend c \/ e_kind e' = KClose c)
    | KStart parent =>
        parent < i /\ exists e', nth_error t parent = Some e' /\ e_kind e' = KSpawn (e_tid e)
    | _ => True
    end.

(** Program order: same goroutine, strictly earlier in the trace. *)
Definition po (t : Trace) (i j : nat) : Prop :=
  i < j /\ j < length t /\ tid_at t i = tid_at t j.

(** Synchronisation: the matched-pair edges, read off the back-pointers. *)
Definition sync (t : Trace) (i j : nat) : Prop :=
  exists e, nth_error t j = Some e /\
    match e_kind e with
    | KRecv _ from => from = i
    | KStart parent => parent = i
    | _ => False
    end.

(** Happens-before = transitive closure of program order ∪ synchronisation. *)
Inductive hbt (t : Trace) : nat -> nat -> Prop :=
  | hbt_po    : forall i j, po t i j -> hbt t i j
  | hbt_sync  : forall i j, sync t i j -> hbt t i j
  | hbt_trans : forall i j k, hbt t i j -> hbt t j k -> hbt t i k.

Lemma po_forward : forall t i j, po t i j -> i < j.
Proof. intros t i j [H _]. exact H. Qed.

(** A synchronisation edge always points FORWARD — its source is the back-pointer,
    which well-formedness places strictly earlier. *)
Lemma sync_forward : forall t i j, WfTrace t -> sync t i j -> i < j.
Proof.
  intros t i j Hwf [e [Hj Hk]].
  specialize (Hwf j e Hj).
  destruct (e_kind e) as [c|c from0|ch|parent0|l|l|c]; cbn in Hwf, Hk; try contradiction.
  - (* KRecv *) destruct Hwf as [Hlt _]. subst from0. exact Hlt.
  - (* KStart *) destruct Hwf as [Hlt _]. subst parent0. exact Hlt.
Qed.

(** THE BRIDGE: happens-before is contained in the trace order. *)
Theorem hbt_forward : forall t i j, WfTrace t -> hbt t i j -> i < j.
Proof.
  intros t i j Hwf H.
  induction H as [i j Hpo | i j Hsy | i j k Hij IHij Hjk IHjk].
  - apply po_forward in Hpo; exact Hpo.
  - apply (sync_forward t i j Hwf Hsy).
  - lia.
Qed.

(** Hence — for ANY well-formed trace — happens-before is a STRICT PARTIAL ORDER:
    irreflexive (the trace position is a linear extension) and transitive. *)
Theorem hbt_irrefl : forall t i, WfTrace t -> ~ hbt t i i.
Proof. intros t i Hwf H. apply (hbt_forward t i i Hwf) in H. lia. Qed.

Theorem hbt_transitive : forall t i j k, hbt t i j -> hbt t j k -> hbt t i k.
Proof. intros t i j k. apply hbt_trans. Qed.

(** ---- A concrete execution: message passing (write → send ⤳ recv → read) ----
    Thread 0 writes x (loc 0) then sends on chan 0; thread 1 receives (matched send
    at position 1) then reads x.  This is the [mp_hb] example, now as an ACTUAL
    interleaved trace whose synchronisation is the recorded recv→send back-pointer. *)
Definition mp_trace : Trace :=
  [ mkEv 0 (KWrite 0)     (* pos 0: thread 0 writes x      *)
  ; mkEv 0 (KSend 0)      (* pos 1: thread 0 sends on c0   *)
  ; mkEv 1 (KRecv 0 1)    (* pos 2: thread 1 recvs c0 (from = pos 1) *)
  ; mkEv 1 (KRead 0) ].   (* pos 3: thread 1 reads x       *)

Lemma nth_error_lt : forall (t : Trace) i e, nth_error t i = Some e -> i < length t.
Proof.
  intros t i e H. apply nth_error_Some. intro Hn. rewrite H in Hn. discriminate.
Qed.

Lemma mp_trace_wf : WfTrace mp_trace.
Proof.
  intros i e H.
  destruct i as [|[|[|[|i]]]].
  - cbn in H; inversion H; subst; cbn; exact I.
  - cbn in H; inversion H; subst; cbn; exact I.
  - cbn in H; inversion H; subst; cbn.
    split; [lia | exists (mkEv 0 (KSend 0)); split; [reflexivity | left; reflexivity]].
  - cbn in H; inversion H; subst; cbn; exact I.
  - apply nth_error_lt in H; cbn in H; lia.
Qed.

(** The write is happens-before the read, through the channel handoff. *)
Lemma mp_trace_hb_0_3 : hbt mp_trace 0 3.
Proof.
  apply hbt_trans with (j := 1).
  - apply hbt_po. unfold po, tid_at; cbn. repeat split; lia.
  - apply hbt_trans with (j := 2).
    + apply hbt_sync. unfold sync. exists (mkEv 1 (KRecv 0 1)). cbn. split; reflexivity.
    + apply hbt_po. unfold po, tid_at; cbn. repeat split; lia.
Qed.

(** ---- Data races on a trace, and race freedom ---- *)
Definition tr_acc (t : Trace) (i : nat) : option Access :=
  match nth_error t i with
  | Some e => match e_kind e with
              | KWrite l => Some (AWrite l) | KRead l => Some (ARead l) | _ => None end
  | None => None
  end.

(** A data race: two cross-goroutine conflicting memory accesses, unordered by
    happens-before. *)
Definition TraceRace (t : Trace) (i j : nat) : Prop :=
  tid_at t i <> tid_at t j /\
  (exists ai aj, tr_acc t i = Some ai /\ tr_acc t j = Some aj /\ conflict ai aj) /\
  ~ hbt t i j /\ ~ hbt t j i.

Definition TraceRaceFree (t : Trace) : Prop := forall i j, ~ TraceRace t i j.

Lemma tr_acc_lt : forall t i ai, tr_acc t i = Some ai -> i < length t.
Proof.
  intros t i ai H. unfold tr_acc in H.
  destruct (nth_error t i) eqn:E; [apply nth_error_lt in E; exact E | discriminate H].
Qed.

(** Ordered ⇒ not a race (the whole defence is happens-before ordering). *)
Theorem trace_ordered_no_race : forall t i j, hbt t i j -> ~ TraceRace t i j.
Proof. intros t i j Hhb [_ [_ [Hno _]]]. exact (Hno Hhb). Qed.

(** A trace with AT MOST ONE memory access (all accessing positions coincide) is race-free: a data
    race needs TWO distinct-goroutine conflicting accesses, so a single access can never form a racing
    pair.  This dispatches the PRE-HANDOFF phases of a single-writer handoff program (before the reader
    reads, only the writer has touched memory) — a brick of the Keller-style inductive-invariant proof
    that EVERY interleaving of the typed pointer handoff is race-free (limit #2, slice 2-A). *)
Lemma le1_mem_access_race_free : forall t,
  (forall i j, tr_acc t i <> None -> tr_acc t j <> None -> i = j) ->
  TraceRaceFree t.
Proof.
  intros t H i j [Htid [[ai [aj [Hai [Haj _]]]] _]].
  assert (Hij : i = j) by (apply H; [rewrite Hai; discriminate | rewrite Haj; discriminate]).
  subst j. apply Htid. reflexivity.
Qed.

(** The message-passing PROGRAM is whole-trace race-free: its only conflicting
    cross-goroutine pair (the write/read of x) is ordered by the channel handoff. *)
Theorem mp_trace_race_free : TraceRaceFree mp_trace.
Proof.
  intros i j [Htid [[ai [aj [Hai [Haj _]]]] [Hnij Hnji]]].
  pose proof (tr_acc_lt _ _ _ Hai) as Hi. pose proof (tr_acc_lt _ _ _ Haj) as Hj.
  cbn in Hi, Hj.
  destruct i as [|[|[|[|i]]]]; try lia;
  destruct j as [|[|[|[|j]]]]; try lia;
    cbn in Hai, Haj, Htid;
    try discriminate Hai; try discriminate Haj;
    try (apply Htid; reflexivity).
  - apply Hnij. exact mp_trace_hb_0_3.   (* i=0 (write), j=3 (read) *)
  - apply Hnji. exact mp_trace_hb_0_3.   (* i=3 (read),  j=0 (write) *)
Qed.

(** ── CLOSED-CHANNEL RECEIVE (trace-core foundation) ──────────────────────────
    A recv from a CLOSED, drained channel returns the zero value immediately (Go).  Per the Go
    memory model, "the closing of a channel happens before a receive that returns a zero value
    because the channel is closed" — so such a recv's producer is the CLOSE, not a send.  The
    trace core now expresses this: a [KClose] event, and a [KRecv]'s back-pointer may point at a
    [KClose] of that channel (not only a [KSend]).  WfTrace/hb/race-freedom are all preserved
    (proven above); these witnesses show the model represents the closed recv FAITHFULLY.
    (The operational [step]/[rstep] rule that GENERATES such a trace — a config closed-flag + a
    recv-on-closed-drained step — is the follow-on slice.) ── *)
Definition closed_recv_trace : Trace :=
  [ mkEv 0 (KClose 5)       (* pos 0: thread 0 closes channel 5            *)
  ; mkEv 1 (KRecv 5 0) ].   (* pos 1: thread 1 recvs zero from CLOSED ch 5; from = pos 0 (the close) *)

Lemma closed_recv_wf : WfTrace closed_recv_trace.
Proof.
  intros i e H. destruct i as [|[|i]].
  - cbn in H; inversion H; subst; cbn; exact I.    (* KClose: no obligation *)
  - cbn in H; inversion H; subst; cbn.             (* KRecv whose producer is the CLOSE *)
    split; [lia | exists (mkEv 0 (KClose 5)); split; [reflexivity | right; reflexivity]].
  - apply nth_error_lt in H. cbn in H. lia.
Qed.

(** The close (pos 0) HAPPENS-BEFORE the closed receive (pos 1) — the Go-memory-model edge, here a
    [sync] edge read off the recv's back-pointer (which points at the close). *)
Lemma closed_recv_hb : hbt closed_recv_trace 0 1.
Proof.
  apply hbt_sync. unfold sync. exists (mkEv 1 (KRecv 5 0)). cbn. split; reflexivity.
Qed.

(** ============================================================================
    OPERATIONAL SEMANTICS: well-formed traces are GENERATED, not assumed.

    A fixed pool of goroutines (each a list of channel/memory actions) interleaves;
    every step APPENDS an event to the trace.  A send records its own trace position
    in the channel's FIFO buffer; a receive pulls the front position as its
    back-pointer.  The invariant [BufOk] (every buffered position is an EARLIER send
    of that channel) is preserved by every step, so EVERY reachable trace is
    well-formed — turning [WfTrace] from a hypothesis into a THEOREM about execution
    ([reachable_wf]).  Composed with [hbt_irrefl] ([reachable_hb_strict]): the
    happens-before of ANY real execution is a strict partial order.  Goroutine SPAWN
    is modelled — [PSpawn]/[step_spawn] grow a DYNAMIC pool tracked by [cfg_live]
    (only spawned goroutines run; initially just [main]).  (The fork EDGE / [KStart]
    is a deliberate follow-up — already proven abstractly by [fork_hb] in builtins.v
    — so cross-goroutine ordering here still flows through channel synchronisation.)
    ============================================================================ *)
Inductive PAct :=
  | PSend (c:nat) | PRecv (c:nat) | PWrite (l:nat) | PRead (l:nat)
  | PSpawn (child:nat)   (* spawn goroutine [child] (its body pre-registered in cfg_prog) *)
  | PSelect (cs:list nat)
  | PClose (c:nat).      (* close(c): records a KClose event.  A recv/select on a CLOSED, drained
                            channel is then READY (yields the zero value) — see step_recv_closed /
                            step_select_closed.  Closed-state is read off the trace (the KClose
                            event), so no config field is needed. *)
  (* [select] over RECEIVE cases [cs]: receive on ANY ONE channel in [cs] that is ready.
     This is the AUTHORITATIVE select model (the sequential [run_io] [select_recv2] is a
     non-authoritative ch1-priority interpreter — see the select code review).  Its
     [step_select] rule below fires for EVERY ready channel, so a config with two ready
     cases has TWO successors: select is genuinely NONDETERMINISTIC here (Go's
     pseudo-random choice), and a safety property must hold for ALL of them.  When NO case
     is ready it has no [step] at all — so empty-select is a LOCAL non-step that contributes
     to global deadlock [Stuck], NEVER a fabricated value.  (Scope: every case shares the
     post-select continuation [rest]; per-case branch BODIES are the orthogonal goto-dispatch
     dimension — [select2] in builtins.v — not what the choice/blocking review flagged.) *)

Definition upd {A} (f : nat -> A) (k : nat) (v : A) : nat -> A :=
  fun x => if Nat.eqb x k then v else f x.

Lemma upd_same : forall {A} (f : nat -> A) k v, upd f k v k = v.
Proof. intros A f k v. unfold upd. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma upd_other : forall {A} (f : nat -> A) k v x, x <> k -> upd f k v x = f x.
Proof. intros A f k v x H. unfold upd. apply Nat.eqb_neq in H. rewrite H. reflexivity. Qed.

(* Keep [upd] from being unfolded by [cbn]/[simpl] in the proofs below — reason about
   it only through [upd_same] / [upd_other]. *)
Global Opaque upd.

Record Config := mkCfg {
  cfg_prog  : nat -> list PAct;   (* goroutine id -> remaining actions *)
  cfg_bufs  : nat -> list nat;    (* channel -> FIFO of sender trace-positions *)
  cfg_live  : nat -> bool;        (* which goroutines have been spawned (are runnable) *)
  cfg_trace : Trace               (* events emitted so far, in order *)
}.

(** One interleaving step: some LIVE goroutine runs its head action, appending an
    event.  A spawn marks the child live ([upd lv child true]). *)
Inductive step : Config -> Config -> Prop :=
  | step_send : forall p b lv tr tid c rest,
      lv tid = true -> p tid = PSend c :: rest ->
      step (mkCfg p b lv tr)
           (mkCfg (upd p tid rest) (upd b c (b c ++ [length tr])) lv
                  (tr ++ [mkEv tid (KSend c)]))
  | step_recv : forall p b lv tr tid c rest s brest,
      lv tid = true -> p tid = PRecv c :: rest -> b c = s :: brest ->
      step (mkCfg p b lv tr)
           (mkCfg (upd p tid rest) (upd b c brest) lv
                  (tr ++ [mkEv tid (KRecv c s)]))
  | step_write : forall p b lv tr tid l rest,
      lv tid = true -> p tid = PWrite l :: rest ->
      step (mkCfg p b lv tr)
           (mkCfg (upd p tid rest) b lv (tr ++ [mkEv tid (KWrite l)]))
  | step_read : forall p b lv tr tid l rest,
      lv tid = true -> p tid = PRead l :: rest ->
      step (mkCfg p b lv tr)
           (mkCfg (upd p tid rest) b lv (tr ++ [mkEv tid (KRead l)]))
  | step_spawn : forall p b lv tr tid child rest,
      lv tid = true -> p tid = PSpawn child :: rest ->
      step (mkCfg p b lv tr)
           (mkCfg (upd p tid rest) b (upd lv child true)
                  (tr ++ [mkEv tid (KSpawn child)]))
  (* select: the chosen channel [c] must be one of the cases ([In c cs]) AND ready
     ([b c = s :: brest]).  Like [step_recv] but over a SET of channels — every ready
     case yields a distinct step, so [step] is nondeterministic at a select. *)
  | step_select : forall p b lv tr tid cs c rest s brest,
      lv tid = true -> p tid = PSelect cs :: rest ->
      In c cs -> b c = s :: brest ->
      step (mkCfg p b lv tr)
           (mkCfg (upd p tid rest) (upd b c brest) lv
                  (tr ++ [mkEv tid (KRecv c s)]))
  (* close: record a [KClose c] event (no buffer change). *)
  | step_close : forall p b lv tr tid c rest,
      lv tid = true -> p tid = PClose c :: rest ->
      step (mkCfg p b lv tr)
           (mkCfg (upd p tid rest) b lv (tr ++ [mkEv tid (KClose c)]))
  (* recv from a CLOSED, DRAINED channel: READY in Go (yields zero); the [KRecv]'s back-pointer is
     the CLOSE position [pos] (close happens-before the closed-recv, per the Go memory model).  The
     premise [nth_error tr pos = Some e /\ e_kind e = KClose c] reads "c is closed" off the trace. *)
  | step_recv_closed : forall p b lv tr tid c rest pos e,
      lv tid = true -> p tid = PRecv c :: rest ->
      b c = [] -> nth_error tr pos = Some e -> e_kind e = KClose c ->
      step (mkCfg p b lv tr)
           (mkCfg (upd p tid rest) b lv (tr ++ [mkEv tid (KRecv c pos)]))
  (* select whose case channel [c] is CLOSED + drained: that case is READY (zero value) — the
     closed-channel analogue of [step_select], which the sequential model mispredicted. *)
  | step_select_closed : forall p b lv tr tid cs c rest pos e,
      lv tid = true -> p tid = PSelect cs :: rest ->
      In c cs -> b c = [] -> nth_error tr pos = Some e -> e_kind e = KClose c ->
      step (mkCfg p b lv tr)
           (mkCfg (upd p tid rest) b lv (tr ++ [mkEv tid (KRecv c pos)])).

Definition BufOk (cfg : Config) : Prop :=
  forall c s, In s (cfg_bufs cfg c) ->
    s < length (cfg_trace cfg) /\
    exists e', nth_error (cfg_trace cfg) s = Some e' /\ e_kind e' = KSend c.

Definition Inv (cfg : Config) : Prop := WfTrace (cfg_trace cfg) /\ BufOk cfg.

Lemma nth_error_app_old : forall (t : Trace) e i,
  i < length t -> nth_error (t ++ [e]) i = nth_error t i.
Proof. intros t e i H. rewrite nth_error_app1 by exact H. reflexivity. Qed.

Lemma nth_error_app_new : forall (t : Trace) e,
  nth_error (t ++ [e]) (length t) = Some e.
Proof. intros t e. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.

(** Appending an event preserves well-formedness, given the new event's own
    back-pointer (if any) points into the existing trace. *)
Lemma WfTrace_app : forall t e,
  WfTrace t ->
  match e_kind e with
  | KRecv c from => from < length t /\ exists e', nth_error t from = Some e' /\
                                                 (e_kind e' = KSend c \/ e_kind e' = KClose c)
  | KStart parent => parent < length t /\ exists e', nth_error t parent = Some e' /\ e_kind e' = KSpawn (e_tid e)
  | _ => True
  end ->
  WfTrace (t ++ [e]).
Proof.
  intros t e Hwf Hnew i e0 Hi.
  destruct (Nat.lt_ge_cases i (length t)) as [Hlt | Hge].
  - rewrite nth_error_app_old in Hi by exact Hlt.
    specialize (Hwf i e0 Hi).
    destruct (e_kind e0) as [c0|c0 from0|ch0|parent0|l0|l0|c0] eqn:Ek; cbn in Hwf |- *; auto.
    + destruct Hwf as [Hf [e' [He' Hk']]]. split; [exact Hf|].
      exists e'. rewrite nth_error_app_old by lia. split; [exact He'|exact Hk'].
    + destruct Hwf as [Hf [e' [He' Hk']]]. split; [exact Hf|].
      exists e'. rewrite nth_error_app_old by lia. split; [exact He'|exact Hk'].
  - rewrite nth_error_app2 in Hi by lia.
    pose proof (nth_error_lt _ _ _ Hi) as Hb. cbn in Hb.
    assert (Hzero : i - length t = 0) by lia.
    assert (Hieq : i = length t) by lia.
    rewrite Hzero in Hi. cbn in Hi. injection Hi as Hi; subst e0.
    destruct (e_kind e) as [c0|c0 from0|ch0|parent0|l0|l0|c0] eqn:Ek; cbn in Hnew |- *; auto.
    + destruct Hnew as [Hf [e' [He' Hk']]]. split; [rewrite Hieq; exact Hf|].
      exists e'. rewrite nth_error_app_old by exact Hf. split; [exact He'|exact Hk'].
    + destruct Hnew as [Hf [e' [He' Hk']]]. split; [rewrite Hieq; exact Hf|].
      exists e'. rewrite nth_error_app_old by exact Hf. split; [exact He'|exact Hk'].
Qed.

(** Break #8 witness (machine-checked): a [KStart] whose own goroutine ([e_tid = 99]) points back at a
    [KSpawn] of a DIFFERENT child ([KSpawn 1]) is now REJECTED by [WfTrace] — the forged spawn happens-before
    edge to an unrelated goroutine cannot be built.  (Under the old definition this trace was well-formed,
    because the back-pointer only had to hit SOME [KSpawn].) *)
Example forged_start_rejected :
  ~ WfTrace [ mkEv 0 (KSpawn 1); mkEv 99 (KStart 0) ].
Proof.
  intro H. specialize (H 1 (mkEv 99 (KStart 0)) eq_refl). cbn in H.
  destruct H as [_ [e' [He' Hk]]]. cbn in He'. injection He' as He'. subst e'. discriminate Hk.
Qed.

(** Bookkeeping: a buffered position survives a trace-append (still earlier, still a
    send of its channel). *)
Lemma BufOk_pos_app : forall tr c s e,
  s < length tr -> (exists e', nth_error tr s = Some e' /\ e_kind e' = KSend c) ->
  s < length (tr ++ [e]) /\ exists e', nth_error (tr ++ [e]) s = Some e' /\ e_kind e' = KSend c.
Proof.
  intros tr c s e Hlt [e' [He' Hk']].
  split; [rewrite length_app; cbn; lia |].
  exists e'. rewrite nth_error_app_old by exact Hlt. split; [exact He'|exact Hk'].
Qed.

(** Same, for an ARBITRARY-length suffix (the [rstep_spawn] case appends TWO events, not one). *)
Lemma BufOk_pos_app_gen : forall tr suf c s,
  s < length tr -> (exists e', nth_error tr s = Some e' /\ e_kind e' = KSend c) ->
  s < length (tr ++ suf) /\ exists e', nth_error (tr ++ suf) s = Some e' /\ e_kind e' = KSend c.
Proof.
  intros tr suf c s Hlt [e' [He' Hk']].
  split; [rewrite length_app; lia |].
  exists e'. rewrite nth_error_app1 by exact Hlt. split; [exact He'|exact Hk'].
Qed.

(** A trace with NO close event.  Used by the single-channel Keystone: its [OnChan]
    programs never close, so [rstep_recv_closed] — which demands a [KClose] in the
    trace — provably cannot fire there (the bridge stays in the open-channel regime). *)
Definition NoCloseTrace (t : Trace) : Prop :=
  forall pos e, nth_error t pos = Some e -> forall c', e_kind e <> KClose c'.

Lemma NoClose_app : forall t e,
  NoCloseTrace t -> (forall c', e_kind e <> KClose c') -> NoCloseTrace (t ++ [e]).
Proof.
  intros t e Hnc Hnew pos e0 Hpos c'.
  destruct (Nat.lt_ge_cases pos (length t)) as [Hlt | Hge].
  - rewrite nth_error_app_old in Hpos by exact Hlt. exact (Hnc pos e0 Hpos c').
  - rewrite nth_error_app2 in Hpos by lia.
    pose proof (nth_error_lt _ _ _ Hpos) as Hb. cbn in Hb.
    assert (Hz : pos - length t = 0) by lia. rewrite Hz in Hpos. cbn in Hpos.
    injection Hpos as <-. exact (Hnew c').
Qed.

Lemma step_preserves_inv : forall cfg cfg', step cfg cfg' -> Inv cfg -> Inv cfg'.
Proof.
  intros cfg cfg' Hstep [Hwf Hbuf].
  destruct Hstep as
    [ p b lv tr tid c rest Hlv Hp
    | p b lv tr tid c rest s brest Hlv Hp Hbc
    | p b lv tr tid l rest Hlv Hp
    | p b lv tr tid l rest Hlv Hp
    | p b lv tr tid child rest Hlv Hp
    | p b lv tr tid cs c rest s brest Hlv Hp Hin Hbc
    | p b lv tr tid c rest Hlv Hp
    | p b lv tr tid c rest pos e Hlv Hp Hbc Hpos Hek
    | p b lv tr tid cs c rest pos e Hlv Hp Hin Hbc Hpos Hek ];
    split.
  (* ---- send ---- *)
  - apply WfTrace_app; [exact Hwf | cbn; exact I].
  - intros c0 s Hin. cbn [cfg_bufs cfg_trace] in Hin |- *.
    destruct (Nat.eq_dec c0 c) as [Heq|Hne].
    + subst c0. rewrite upd_same in Hin. rewrite in_app_iff in Hin.
      destruct Hin as [Hin | Hin].
      * destruct (Hbuf c s Hin) as [Hlt Hex]. apply BufOk_pos_app; assumption.
      * destruct Hin as [<- | []].
        split; [rewrite length_app; cbn; lia |].
        exists (mkEv tid (KSend c)). rewrite nth_error_app_new. split; reflexivity.
    + rewrite (upd_other _ _ _ _ Hne) in Hin.
      destruct (Hbuf c0 s Hin) as [Hlt Hex]. apply BufOk_pos_app; assumption.
  (* ---- recv ---- *)
  - apply WfTrace_app; [exact Hwf | cbn].
    assert (Hins : In s (b c)) by (rewrite Hbc; left; reflexivity).
    destruct (Hbuf c s Hins) as [Hlt [e' [He' Hk']]].
    split; [exact Hlt | exists e'; split; [exact He' | left; exact Hk']].
  - intros c0 s0 Hin. cbn [cfg_bufs cfg_trace] in Hin |- *.
    destruct (Nat.eq_dec c0 c) as [Heq|Hne].
    + subst c0. rewrite upd_same in Hin.
      assert (Hin' : In s0 (b c)) by (rewrite Hbc; right; exact Hin).
      destruct (Hbuf c s0 Hin') as [Hlt Hex]. apply BufOk_pos_app; assumption.
    + rewrite (upd_other _ _ _ _ Hne) in Hin.
      destruct (Hbuf c0 s0 Hin) as [Hlt Hex]. apply BufOk_pos_app; assumption.
  (* ---- write ---- *)
  - apply WfTrace_app; [exact Hwf | cbn; exact I].
  - intros c0 s Hin. cbn [cfg_bufs cfg_trace] in Hin |- *.
    destruct (Hbuf c0 s Hin) as [Hlt Hex]. apply BufOk_pos_app; assumption.
  (* ---- read ---- *)
  - apply WfTrace_app; [exact Hwf | cbn; exact I].
  - intros c0 s Hin. cbn [cfg_bufs cfg_trace] in Hin |- *.
    destruct (Hbuf c0 s Hin) as [Hlt Hex]. apply BufOk_pos_app; assumption.
  (* ---- spawn (bufs unchanged; KSpawn has no well-formedness obligation) ---- *)
  - apply WfTrace_app; [exact Hwf | cbn; exact I].
  - intros c0 s Hin. cbn [cfg_bufs cfg_trace] in Hin |- *.
    destruct (Hbuf c0 s Hin) as [Hlt Hex]. apply BufOk_pos_app; assumption.
  (* ---- select (receives on the CHOSEN ready channel; identical to recv) ---- *)
  - apply WfTrace_app; [exact Hwf | cbn].
    assert (Hins : In s (b c)) by (rewrite Hbc; left; reflexivity).
    destruct (Hbuf c s Hins) as [Hlt [e' [He' Hk']]].
    split; [exact Hlt | exists e'; split; [exact He' | left; exact Hk']].
  - intros c0 s0 Hin0. cbn [cfg_bufs cfg_trace] in Hin0 |- *.
    destruct (Nat.eq_dec c0 c) as [Heq|Hne].
    + subst c0. rewrite upd_same in Hin0.
      assert (Hin' : In s0 (b c)) by (rewrite Hbc; right; exact Hin0).
      destruct (Hbuf c s0 Hin') as [Hlt Hex]. apply BufOk_pos_app; assumption.
    + rewrite (upd_other _ _ _ _ Hne) in Hin0.
      destruct (Hbuf c0 s0 Hin0) as [Hlt Hex]. apply BufOk_pos_app; assumption.
  (* ---- close (KClose has no WfTrace obligation; bufs unchanged) ---- *)
  - apply WfTrace_app; [exact Hwf | cbn; exact I].
  - intros c0 s Hin1. cbn [cfg_bufs cfg_trace] in Hin1 |- *.
    destruct (Hbuf c0 s Hin1) as [Hlt Hex]. apply BufOk_pos_app; assumption.
  (* ---- recv_closed (KRecv's producer is the CLOSE at [pos]; bufs unchanged) ---- *)
  - apply WfTrace_app; [exact Hwf | cbn].
    split; [exact (nth_error_lt _ _ _ Hpos) | exists e; split; [exact Hpos | right; exact Hek]].
  - intros c0 s Hin1. cbn [cfg_bufs cfg_trace] in Hin1 |- *.
    destruct (Hbuf c0 s Hin1) as [Hlt Hex]. apply BufOk_pos_app; assumption.
  (* ---- select_closed (same closed-recv shape as recv_closed) ---- *)
  - apply WfTrace_app; [exact Hwf | cbn].
    split; [exact (nth_error_lt _ _ _ Hpos) | exists e; split; [exact Hpos | right; exact Hek]].
  - intros c0 s Hin1. cbn [cfg_bufs cfg_trace] in Hin1 |- *.
    destruct (Hbuf c0 s Hin1) as [Hlt Hex]. apply BufOk_pos_app; assumption.
Qed.

Inductive steps : Config -> Config -> Prop :=
  | steps_refl : forall cfg, steps cfg cfg
  | steps_step : forall a b c, step a b -> steps b c -> steps a c.

(* Initially only [main] (goroutine 0) is live; others start dormant until spawned. *)
Definition init_cfg (p : nat -> list PAct) : Config :=
  mkCfg p (fun _ => []) (fun t => Nat.eqb t 0) [].

Lemma init_inv : forall p, Inv (init_cfg p).
Proof.
  intros p. split.
  - intros i e H. apply nth_error_lt in H. cbn in H. lia.
  - intros c s H. cbn in H. contradiction.
Qed.

Lemma steps_preserves_inv : forall a b, steps a b -> Inv a -> Inv b.
Proof.
  intros a b H. induction H; intros Hinv; [exact Hinv|].
  apply IHsteps. exact (step_preserves_inv _ _ H Hinv).
Qed.

(** THE CAPSTONE.  Every reachable execution trace is well-formed... *)
Theorem reachable_wf : forall p cfg, steps (init_cfg p) cfg -> WfTrace (cfg_trace cfg).
Proof.
  intros p cfg H. apply (steps_preserves_inv _ _ H (init_inv p)).
Qed.

(** ...hence the happens-before of ANY real execution (any program, any reachable
    configuration) is a STRICT PARTIAL ORDER — the abstract guarantee, now earned by
    actual execution rather than assumed on a hand-built trace. *)
Corollary reachable_hb_strict : forall p cfg i,
  steps (init_cfg p) cfg -> ~ hbt (cfg_trace cfg) i i.
Proof.
  intros p cfg i H. apply hbt_irrefl. exact (reachable_wf p cfg H).
Qed.

(** ============================================================================
    STEP 2 — general race-freedom under an OWNERSHIP discipline.

    Until now race freedom was proven for hand-built traces (mp_trace_race_free).
    Here it becomes a THEOREM from a structural discipline: if the accesses to each
    memory location form a happens-before CHAIN — any two same-location accesses
    are either directly hb-ordered or separated by an intermediate same-location
    access — then NO conflicting pair is unordered, so the trace is race-free.
    This is the trace-level shadow of OWNERSHIP: a location is touched only by its
    current owner, and ownership transfers only through synchronisation (an
    hb-edge), so accesses to it are serialised by happens-before.
    ============================================================================ *)

(** The memory location accessed at position [i] (None for non-memory events). *)
Definition acc_loc_at (t : Trace) (i : nat) : option nat :=
  match nth_error t i with
  | Some e => match e_kind e with KWrite l => Some l | KRead l => Some l | _ => None end
  | None => None
  end.

Definition same_loc (t : Trace) (i j : nat) : Prop :=
  exists l, acc_loc_at t i = Some l /\ acc_loc_at t j = Some l.

Lemma acc_loc_at_lt : forall t i l, acc_loc_at t i = Some l -> i < length t.
Proof.
  intros t i l H. unfold acc_loc_at in H. destruct (nth_error t i) eqn:E.
  - apply nth_error_lt in E; exact E.
  - discriminate.
Qed.

(** The ownership discipline: accesses to each location form an hb-chain. *)
Definition Owned (t : Trace) : Prop :=
  forall i j, i < j -> same_loc t i j ->
    hbt t i j \/ exists k, i < k < j /\ same_loc t i k /\ same_loc t k j.

(** Under the discipline, EVERY pair of same-location accesses is hb-ordered
    (the local "consecutive accesses ordered" lifts to a global chain). *)
Theorem owned_orders_same_loc : forall t,
  Owned t -> forall i j, i < j -> same_loc t i j -> hbt t i j.
Proof.
  intros t HO.
  assert (Hn : forall n i j, j <= i + n -> i < j -> same_loc t i j -> hbt t i j).
  { induction n as [|n IHn]; intros i j Hbound Hij Hsl; [lia|].
    destruct (HO i j Hij Hsl) as [Hhb | [k [[Hik Hkj] [Hsik Hskj]]]]; [exact Hhb|].
    apply hbt_trans with (j := k).
    - apply IHn; [lia | exact Hik | exact Hsik].
    - apply IHn; [lia | exact Hkj | exact Hskj]. }
  intros i j Hij Hsl. apply (Hn (j - i)); [lia | exact Hij | exact Hsl].
Qed.

(** Bridge: a memory access [tr_acc] pins the location [acc_loc_at] sees. *)
Lemma tr_acc_loc : forall t i a, tr_acc t i = Some a -> acc_loc_at t i = Some (acc_loc a).
Proof.
  intros t i a H. unfold tr_acc, acc_loc_at in *.
  destruct (nth_error t i) as [e|]; [|discriminate].
  destruct (e_kind e); cbn in H; try discriminate; injection H as <-; reflexivity.
Qed.

(** THE STEP-2 THEOREM: an ownership-disciplined trace is race-free. *)
Theorem owned_race_free : forall t, Owned t -> TraceRaceFree t.
Proof.
  intros t HO i j [Htid [[ai [aj [Hai [Haj Hcon]]]] [Hnij Hnji]]].
  apply tr_acc_loc in Hai. apply tr_acc_loc in Haj.
  destruct Hcon as [Hloc _].
  assert (Hsl : same_loc t i j).
  { exists (acc_loc ai). split; [exact Hai | rewrite Haj, Hloc; reflexivity]. }
  destruct (Nat.lt_trichotomy i j) as [Hlt | [Heq | Hgt]].
  - apply Hnij. exact (owned_orders_same_loc t HO i j Hlt Hsl).
  - subst j. apply Htid. reflexivity.
  - apply Hnji. apply (owned_orders_same_loc t HO j i Hgt).
    destruct Hsl as [l [Hi Hj]]. exists l. split; [exact Hj | exact Hi].
Qed.

(** ============================================================================
    RACE-FREEDOM BY A CHECKABLE DISCIPLINE — location PRIVACY discharges [Owned].

    [owned_race_free] takes [Owned] (accesses to each location form an hb-chain) as a HYPOTHESIS.
    Here is a SYNTACTIC, decidable discipline that IMPLIES it — so the ownership premise is
    ESTABLISHED, not assumed (research-plan step 2 "Remaining").  [LocPrivate]: every memory
    location is touched by a SINGLE goroutine (any two same-location accesses share a tid).  Then
    same-location accesses lie in ONE goroutine's PROGRAM ORDER, and [po] ⊆ [hbt], so they are
    hb-ordered — [Owned] holds outright.  This is the no-sharing BASE of the ownership story (a
    location whose owner never changes); ownership TRANSFER across a channel synchronisation is the
    general case (deferred — dynamic [CSpawn] makes a static owner assignment subtle).
    ============================================================================ *)
Definition LocPrivate (t : Trace) : Prop :=
  forall i j, same_loc t i j -> tid_at t i = tid_at t j.

(** Location privacy DISCHARGES the ownership discipline: same-location accesses are program-ordered
    (same goroutine), and program order is happens-before. *)
Theorem locprivate_owned : forall t, LocPrivate t -> Owned t.
Proof.
  intros t HLP i j Hij Hsl. left. apply hbt_po. unfold po.
  split; [exact Hij | split].
  - destruct Hsl as [l [_ Hj]]. exact (acc_loc_at_lt t j l Hj).
  - exact (HLP i j Hsl).
Qed.

(** Hence a location-private trace is RACE-FREE — with [Owned] no longer assumed but EARNED from the
    checkable structural discipline. *)
Theorem locprivate_race_free : forall t, LocPrivate t -> TraceRaceFree t.
Proof. intros t HLP. exact (owned_race_free t (locprivate_owned t HLP)). Qed.

(** Witness (positive): goroutine 0 writes location 0, goroutine 1 writes location 1 — DISJOINT
    locations, so [LocPrivate] holds (no same-location cross-goroutine pair) and the trace is
    race-free with NO [Owned] hypothesis. *)
Definition disjoint_trace : Trace := [mkEv 0 (KWrite 0); mkEv 1 (KWrite 1)].

(* In this trace location [l] is written at position [l] by goroutine [l], so an access of [l] pins
   the accessing goroutine to [l]. *)
Lemma disjoint_loc_tid : forall i l,
  acc_loc_at disjoint_trace i = Some l -> tid_at disjoint_trace i = l.
Proof.
  intros i l H. pose proof (acc_loc_at_lt _ _ _ H) as Hlt. cbn in Hlt.
  unfold disjoint_trace, acc_loc_at, tid_at in *.
  destruct i as [|[|i]]; cbn in *; try lia; congruence.
Qed.

Lemma disjoint_locprivate : LocPrivate disjoint_trace.
Proof.
  intros i j [l [Hi Hj]].
  rewrite (disjoint_loc_tid i l Hi), (disjoint_loc_tid j l Hj). reflexivity.
Qed.

Theorem disjoint_race_free : TraceRaceFree disjoint_trace.
Proof. exact (locprivate_race_free _ disjoint_locprivate). Qed.

(** Witness (negative): the discipline BITES — two goroutines writing the SAME location is NOT
    [LocPrivate] (a real shared-memory conflict the discipline correctly rejects). *)
Definition shared_trace : Trace := [mkEv 0 (KWrite 5); mkEv 1 (KWrite 5)].

Lemma shared_not_locprivate : ~ LocPrivate shared_trace.
Proof.
  intros H. assert (Hsl : same_loc shared_trace 0 1)
    by (exists 5; unfold shared_trace, acc_loc_at; cbn; split; reflexivity).
  specialize (H 0 1 Hsl). unfold shared_trace, tid_at in H. cbn in H. discriminate.
Qed.

(** Combined with reachability: a REACHABLE execution that is location-private is race-free AND has a
    strict-partial-order happens-before — race-freedom earned from a checkable discipline on a
    genuinely-executed trace, no [Owned] assumption. *)
Theorem reachable_locprivate_safe : forall p cfg,
  steps (init_cfg p) cfg -> LocPrivate (cfg_trace cfg) ->
  TraceRaceFree (cfg_trace cfg) /\ (forall i, ~ hbt (cfg_trace cfg) i i).
Proof.
  intros p cfg Hsteps HLP. split.
  - exact (locprivate_race_free _ HLP).
  - intro i. apply hbt_irrefl. exact (reachable_wf p cfg Hsteps).
Qed.

(** ── OWNERSHIP TRANSFER through a channel — the general principle (complements [LocPrivate], the
    no-sharing base).  A location's owner can MOVE between goroutines, provided the handoff goes
    through a synchronisation: access [a] by goroutine A is program-before a SEND, the matching RECV
    is program-before access [b] by goroutine B.  Then [a] →hb→ [b] ([po]·[sync]·[po]), so the two
    cross-goroutine accesses are ORDERED — even a WRITE/WRITE conflict on the handed-off location is
    race-free.  This is exactly the idiomatic Go pattern "pass ownership over a channel". ── *)
Theorem transfer_orders : forall t a s r b,
  po t a s -> sync t s r -> po t r b -> hbt t a b.
Proof.
  intros t a s r b Hpo1 Hsync Hpo2.
  apply hbt_trans with (j := s); [apply hbt_po; exact Hpo1 |].
  apply hbt_trans with (j := r); [apply hbt_sync; exact Hsync | apply hbt_po; exact Hpo2].
Qed.

(** Witness: goroutine 0 writes location 7, HANDS OFF via a send, goroutine 1 receives and then ALSO
    writes location 7.  A genuine write/write conflict on 7 — yet race-FREE, because the transfer
    orders the two writes ([transfer_orders] over the send/recv).  [LocPrivate] would REJECT this
    (two goroutines touch 7); the transfer discipline ACCEPTS it. *)
Definition handoff_trace : Trace :=
  [ mkEv 0 (KWrite 7); mkEv 0 (KSend 0); mkEv 1 (KRecv 0 1); mkEv 1 (KWrite 7) ].

Lemma handoff_loc_pos : forall i l, acc_loc_at handoff_trace i = Some l -> i = 0 \/ i = 3.
Proof.
  intros i l H. pose proof (acc_loc_at_lt _ _ _ H) as Hlt. cbn in Hlt.
  unfold handoff_trace, acc_loc_at in H.
  destruct i as [|[|[|[|i]]]]; cbn in H;
    [ left; reflexivity | discriminate | discriminate | right; reflexivity | lia ].
Qed.

Lemma handoff_owned : Owned handoff_trace.
Proof.
  intros i j Hij [l [Hi Hj]]. left.
  destruct (handoff_loc_pos i l Hi) as [-> | ->];
    destruct (handoff_loc_pos j l Hj) as [-> | ->]; try lia.
  apply (transfer_orders handoff_trace 0 1 2 3).
  - unfold po, tid_at; cbn. repeat split; lia.
  - unfold sync; cbn. exists (mkEv 1 (KRecv 0 1)); cbn. split; reflexivity.
  - unfold po, tid_at; cbn. repeat split; lia.
Qed.

Theorem handoff_race_free : TraceRaceFree handoff_trace.
Proof. exact (owned_race_free _ handoff_owned). Qed.

(** ── A CLOSED-FORM RACE-FREEDOM DISCIPLINE — unifying the TWO bases (LocPrivate no-sharing AND the
    channel/fork HANDOFF) into ONE checkable structural condition. ──
    [Handoff t i j] holds when the accesses at [i] and [j] are EITHER by the SAME goroutine (program
    order alone orders them) OR connected by a SINGLE synchronisation handoff [po]·[sync]·[po] — an
    access program-before a SEND/SPAWN whose matching RECV/START is program-before the other access.
    A trace is [HandoffDisciplined] when EVERY conflicting (same-location) pair [i<j] is a [Handoff].
    This single condition IMPLIES [Owned] (hence race-freedom), via [transfer_orders] for the handoff
    case and program order for the same-goroutine case.  It SUBSUMES both existing bases:
    [locprivate_handoff_disciplined] (no sharing ⇒ same-goroutine disjunct) and the bespoke
    [handoff_owned]/[fork_handoff_owned]/[chan_pub_owned] witnesses (the handoff disjunct).  This is
    the "closed-form transfer discipline as a checkable condition" the per-trace witnesses gestured at:
    future programs earn race-freedom by exhibiting the STRUCTURE, not a hand-built [Owned] proof. *)
Definition Handoff (t : Trace) (i j : nat) : Prop :=
  tid_at t i = tid_at t j \/ exists s r, po t i s /\ sync t s r /\ po t r j.

Definition HandoffDisciplined (t : Trace) : Prop :=
  forall i j, i < j -> same_loc t i j -> Handoff t i j.

Theorem handoff_disciplined_owned : forall t, HandoffDisciplined t -> Owned t.
Proof.
  intros t HD i j Hij Hsl. left.
  destruct (HD i j Hij Hsl) as [Hsame | [s [r [Hpo1 [Hsync Hpo2]]]]].
  - (* same goroutine: i<j of equal tid is in program order *)
    apply hbt_po. unfold po. split; [exact Hij | split; [| exact Hsame]].
    destruct Hsl as [l [_ Hj]]. exact (acc_loc_at_lt _ _ _ Hj).
  - (* cross-goroutine: the single send/spawn handoff orders i before j *)
    exact (transfer_orders t i s r j Hpo1 Hsync Hpo2).
Qed.

Theorem handoff_disciplined_race_free : forall t, HandoffDisciplined t -> TraceRaceFree t.
Proof. intros t HD. exact (owned_race_free t (handoff_disciplined_owned t HD)). Qed.

(** Base 1 subsumed: a LocPrivate trace (every location touched by one goroutine) is trivially
    HandoffDisciplined — every conflicting pair takes the same-goroutine disjunct. *)
Lemma locprivate_handoff_disciplined : forall t, LocPrivate t -> HandoffDisciplined t.
Proof. intros t HLP i j _ Hsl. left. exact (HLP i j Hsl). Qed.

(** Base 2 subsumed: the channel-handoff witness is HandoffDisciplined (the conflicting write/write at
    0/3 take the handoff disjunct s=1,r=2) — so [handoff_race_free] re-derives through the discipline. *)
Lemma handoff_trace_disciplined : HandoffDisciplined handoff_trace.
Proof.
  intros i j Hij [l [Hi Hj]].
  destruct (handoff_loc_pos i l Hi) as [-> | ->];
    destruct (handoff_loc_pos j l Hj) as [-> | ->]; try lia.
  right. exists 1, 2. split; [|split].
  - unfold po, tid_at; cbn. repeat split; lia.
  - unfold sync; cbn. exists (mkEv 1 (KRecv 0 1)); cbn. split; reflexivity.
  - unfold po, tid_at; cbn. repeat split; lia.
Qed.

(** ── MULTI-HOP handoff: ownership transferred through a CHAIN of channels (g0 ⇝ g1 ⇝ g2 ⇝ …). ──
    The single [Handoff] is one [po]·[sync]·[po].  [syncpath t i j] is the TRANSITIVE closure
    [po]·([sync]·[po])* — an access [i], then any number of (program-step to a SEND/SPAWN, hand off to
    the matching RECV/START, program-step on) hops, reaching [j].  Each hop is two [hbt] edges, so a
    whole path is [hbt] ([syncpath_hbt]); hence a [SyncDisciplined] trace (every conflicting pair has a
    path) is [Owned] — race-free.  This STRICTLY generalises [HandoffDisciplined]
    ([handoff_syncpath]: one hop is a path), covering ownership that moves across SEVERAL channels
    before the final access — which a single handoff cannot express. *)
Inductive syncpath (t : Trace) : nat -> nat -> Prop :=
  | sp_po   : forall i j, po t i j -> syncpath t i j
  | sp_step : forall i s r j, po t i s -> sync t s r -> syncpath t r j -> syncpath t i j.

Lemma syncpath_hbt : forall t i j, syncpath t i j -> hbt t i j.
Proof.
  intros t i j H. induction H as [i j Hpo | i s r j Hpo Hsync Hpath IH].
  - apply hbt_po; exact Hpo.
  - apply hbt_trans with (j := s); [apply hbt_po; exact Hpo |].
    apply hbt_trans with (j := r); [apply hbt_sync; exact Hsync | exact IH].
Qed.

Definition SyncDisciplined (t : Trace) : Prop :=
  forall i j, i < j -> same_loc t i j -> syncpath t i j.

Theorem sync_disciplined_owned : forall t, SyncDisciplined t -> Owned t.
Proof. intros t SD i j Hij Hsl. left. apply syncpath_hbt. exact (SD i j Hij Hsl). Qed.

Theorem sync_disciplined_race_free : forall t, SyncDisciplined t -> TraceRaceFree t.
Proof. intros t SD. exact (owned_race_free t (sync_disciplined_owned t SD)). Qed.

(** A single [Handoff] is a one-hop [syncpath], so the multi-hop discipline subsumes the single one. *)
Lemma handoff_syncpath : forall t i j, i < j -> same_loc t i j -> Handoff t i j -> syncpath t i j.
Proof.
  intros t i j Hij Hsl [Hsame | [s [r [Hpo1 [Hsync Hpo2]]]]].
  - apply sp_po. unfold po. split; [exact Hij | split; [| exact Hsame]].
    destruct Hsl as [l [_ Hj]]. exact (acc_loc_at_lt _ _ _ Hj).
  - apply sp_step with (s := s) (r := r); [exact Hpo1 | exact Hsync | apply sp_po; exact Hpo2].
Qed.

Corollary handoff_disciplined_sync : forall t, HandoffDisciplined t -> SyncDisciplined t.
Proof. intros t HD i j Hij Hsl. exact (handoff_syncpath t i j Hij Hsl (HD i j Hij Hsl)). Qed.

(** Witness needing TWO hops: g0 writes loc 7, sends on ch0; g1 receives ch0, sends on ch1; g2
    receives ch1, reads loc 7.  The write (pos 0) and read (pos 5) are race-free ONLY through the
    2-hop chain 0 →po 1 →sync 2 →po 3 →sync 4 →po 5 — a single handoff cannot reach. *)
Definition two_hop_trace : Trace :=
  [ mkEv 0 (KWrite 7); mkEv 0 (KSend 0); mkEv 1 (KRecv 0 1);
    mkEv 1 (KSend 1);  mkEv 2 (KRecv 1 3); mkEv 2 (KRead 7) ].

Lemma two_hop_loc_pos : forall i l, acc_loc_at two_hop_trace i = Some l -> i = 0 \/ i = 5.
Proof.
  intros i l H. pose proof (acc_loc_at_lt _ _ _ H) as Hlt. cbn in Hlt.
  unfold two_hop_trace, acc_loc_at in H.
  destruct i as [|[|[|[|[|[|i]]]]]]; cbn in H;
    [ left; reflexivity | discriminate | discriminate
    | discriminate | discriminate | right; reflexivity | lia ].
Qed.

Lemma two_hop_disciplined : SyncDisciplined two_hop_trace.
Proof.
  intros i j Hij [l [Hi Hj]].
  destruct (two_hop_loc_pos i l Hi) as [-> | ->];
    destruct (two_hop_loc_pos j l Hj) as [-> | ->]; try lia.
  (* 0 ⇝ 5: po 0 1, sync 1 2, po 2 3, sync 3 4, po 4 5 *)
  apply sp_step with (s := 1) (r := 2).
  - unfold po, tid_at; cbn. repeat split; lia.
  - unfold sync; cbn. exists (mkEv 1 (KRecv 0 1)); cbn. split; reflexivity.
  - apply sp_step with (s := 3) (r := 4).
    + unfold po, tid_at; cbn. repeat split; lia.
    + unfold sync; cbn. exists (mkEv 2 (KRecv 1 3)); cbn. split; reflexivity.
    + apply sp_po. unfold po, tid_at; cbn. repeat split; lia.
Qed.

Theorem two_hop_race_free : TraceRaceFree two_hop_trace.
Proof. exact (sync_disciplined_race_free _ two_hop_disciplined). Qed.

(** FORK-edge ownership handoff — the OTHER go-mem synchronisation: "the [go] statement that starts a
    new goroutine is synchronised before the goroutine's execution begins" (go.dev/ref/mem).  Same
    [transfer_orders] shape as the channel handoff, but the sync edge is the SPAWN→START pair
    ([KSpawn] / [KStart], back-pointer = the spawn position) instead of send/recv: goroutine 0 writes
    loc 7, SPAWNS goroutine 1, which STARTS and reads loc 7 — write →hb→ read, so the parent's
    pre-spawn writes are visible to the child and the cross-goroutine accesses are race-free.  Shows
    [transfer_orders] is generic over BOTH go-mem synchronisation mechanisms (channel AND fork). *)
Definition fork_handoff_trace : Trace :=
  [ mkEv 0 (KWrite 7); mkEv 0 (KSpawn 1); mkEv 1 (KStart 1); mkEv 1 (KRead 7) ].

Lemma fork_loc_pos : forall i l, acc_loc_at fork_handoff_trace i = Some l -> i = 0 \/ i = 3.
Proof.
  intros i l H. pose proof (acc_loc_at_lt _ _ _ H) as Hlt. cbn in Hlt.
  unfold fork_handoff_trace, acc_loc_at in H.
  destruct i as [|[|[|[|i]]]]; cbn in H;
    [ left; reflexivity | discriminate | discriminate | right; reflexivity | lia ].
Qed.

Lemma fork_handoff_owned : Owned fork_handoff_trace.
Proof.
  intros i j Hij [l [Hi Hj]]. left.
  destruct (fork_loc_pos i l Hi) as [-> | ->];
    destruct (fork_loc_pos j l Hj) as [-> | ->]; try lia.
  apply (transfer_orders fork_handoff_trace 0 1 2 3).
  - unfold po, tid_at; cbn. repeat split; lia.
  - unfold sync; cbn. exists (mkEv 1 (KStart 1)); cbn. split; reflexivity.
  - unfold po, tid_at; cbn. repeat split; lia.
Qed.

Theorem fork_handoff_race_free : TraceRaceFree fork_handoff_trace.
Proof. exact (owned_race_free _ fork_handoff_owned). Qed.

(** The message-passing trace satisfies the discipline (its only same-location pair,
    the write/read of x, is directly hb-ordered) — so [owned_race_free] re-derives
    its race-freedom from the GENERAL theorem, subsuming [mp_trace_race_free]. *)
Lemma mp_trace_owned : Owned mp_trace.
Proof.
  intros i j Hij [l [Hi Hj]]. left.
  pose proof (acc_loc_at_lt _ _ _ Hi) as Hbi.
  pose proof (acc_loc_at_lt _ _ _ Hj) as Hbj. cbn in Hbi, Hbj.
  destruct i as [|[|[|[|i]]]]; try lia;
  destruct j as [|[|[|[|j]]]]; try lia;
    cbn in Hi, Hj; try discriminate; try lia.
  exact mp_trace_hb_0_3.
Qed.

Example mp_trace_race_free_via_owned : TraceRaceFree mp_trace :=
  owned_race_free mp_trace mp_trace_owned.

(** ============================================================================
    STEP 3a — exact FIFO ordering of channel buffers.

    [WfTrace] only says a receive's back-pointer is SOME earlier send; the [step]
    semantics actually enforces FIFO (a receive pulls the buffer FRONT — the oldest
    unreceived send).  Here that is made a THEOREM: in every reachable config the
    channel buffer is STRICTLY INCREASING in send position ([reachable_sorted]).
    Since a receive pulls the front (the minimum), receives therefore consume sends
    in send order — the exact kth-recv ↔ kth-send pairing, at the buffer level.
    ============================================================================ *)

(** Strictly increasing: each head is below everything after it. *)
Fixpoint Incr (l : list nat) : Prop :=
  match l with [] => True | x :: l' => (forall y, In y l' -> x < y) /\ Incr l' end.

Lemma Incr_tail : forall x l, Incr (x :: l) -> Incr l.
Proof. intros x l H. apply H. Qed.

Lemma Incr_app : forall l y, Incr l -> (forall x, In x l -> x < y) -> Incr (l ++ [y]).
Proof.
  induction l as [|a l IH]; intros y Hi Hlt; cbn.
  - split; [intros z H; destruct H | exact I].
  - cbn in Hi. destruct Hi as [Ha Hl]. split.
    + intros z Hz. apply in_app_or in Hz. destruct Hz as [Hz|Hz].
      * apply Ha; exact Hz.
      * destruct Hz as [<-|[]]. apply Hlt; left; reflexivity.
    + apply IH; [exact Hl | intros x Hx; apply Hlt; right; exact Hx].
Qed.

Definition BufSorted (cfg : Config) : Prop := forall c, Incr (cfg_bufs cfg c).

Lemma step_preserves_sorted : forall cfg cfg',
  step cfg cfg' -> Inv cfg -> BufSorted cfg -> BufSorted cfg'.
Proof.
  intros cfg cfg' Hstep [Hwf Hbuf] Hsort.
  destruct Hstep as
    [ p b lv tr tid c rest Hlv Hp
    | p b lv tr tid c rest s brest Hlv Hp Hbc
    | p b lv tr tid l rest Hlv Hp
    | p b lv tr tid l rest Hlv Hp
    | p b lv tr tid child rest Hlv Hp
    | p b lv tr tid cs c rest s brest Hlv Hp Hin Hbc
    | p b lv tr tid c rest Hlv Hp
    | p b lv tr tid c rest pos e Hlv Hp Hbc Hpos Hek
    | p b lv tr tid cs c rest pos e Hlv Hp Hin Hbc Hpos Hek ];
    intros c0; cbn [cfg_bufs cfg_trace].
  - (* send *) destruct (Nat.eq_dec c0 c) as [->|Hne].
    + rewrite upd_same. apply Incr_app.
      * exact (Hsort c).
      * intros x Hx. destruct (Hbuf c x Hx) as [Hlt _]. exact Hlt.
    + rewrite (upd_other _ _ _ _ Hne). exact (Hsort c0).
  - (* recv *) destruct (Nat.eq_dec c0 c) as [->|Hne].
    + rewrite upd_same. specialize (Hsort c). cbn [cfg_bufs] in Hsort.
      rewrite Hbc in Hsort. apply Incr_tail in Hsort. exact Hsort.
    + rewrite (upd_other _ _ _ _ Hne). exact (Hsort c0).
  - exact (Hsort c0).
  - exact (Hsort c0).
  - exact (Hsort c0).
  - (* select: same as recv (the chosen channel loses its head) *)
    destruct (Nat.eq_dec c0 c) as [->|Hne].
    + rewrite upd_same. specialize (Hsort c). cbn [cfg_bufs] in Hsort.
      rewrite Hbc in Hsort. apply Incr_tail in Hsort. exact Hsort.
    + rewrite (upd_other _ _ _ _ Hne). exact (Hsort c0).
  - exact (Hsort c0).   (* close: bufs unchanged *)
  - exact (Hsort c0).   (* recv_closed: bufs unchanged *)
  - exact (Hsort c0).   (* select_closed: bufs unchanged *)
Qed.

Lemma init_sorted : forall p, BufSorted (init_cfg p).
Proof. intros p c. cbn. exact I. Qed.

Lemma steps_preserves_both : forall a b,
  steps a b -> Inv a -> BufSorted a -> Inv b /\ BufSorted b.
Proof.
  intros a b H. induction H; intros Hinv Hsort; [split; assumption|].
  apply IHsteps.
  - exact (step_preserves_inv _ _ H Hinv).
  - exact (step_preserves_sorted _ _ H Hinv Hsort).
Qed.

Theorem reachable_sorted : forall p cfg, steps (init_cfg p) cfg -> BufSorted cfg.
Proof.
  intros p cfg H. apply (steps_preserves_both _ _ H (init_inv p) (init_sorted p)).
Qed.

(** ============================================================================
    Steps 1+2 combined — the safety capstone, and deadlock representability.
    ============================================================================ *)

(** A REACHABLE execution (any program, any reachable state) that respects the
    ownership discipline has a strict-partial-order happens-before AND is race-free
    — step 1 (reachable_wf) and step 2 (owned_race_free), composed. *)
Corollary reachable_owned_safe : forall p cfg,
  steps (init_cfg p) cfg -> Owned (cfg_trace cfg) ->
  TraceRaceFree (cfg_trace cfg) /\ (forall i, ~ hbt (cfg_trace cfg) i i).
Proof.
  intros p cfg Hsteps HO. split.
  - exact (owned_race_free _ HO).
  - intro i. apply hbt_irrefl. exact (reachable_wf _ _ Hsteps).
Qed.

(** Unlike the (sequential, total) [run_io] model, this operational semantics
    REPRESENTS deadlock: a config that cannot step yet has a live goroutine with
    work left.  Proving deadlock-FREEDOM (progress) is the open liveness frontier;
    showing deadlock is representable is its honest foundation. *)
Definition can_step (cfg : Config) : Prop := exists cfg', step cfg cfg'.
Definition done (cfg : Config) : Prop :=
  forall tid, cfg_live cfg tid = true -> cfg_prog cfg tid = [].
Definition Stuck (cfg : Config) : Prop := ~ can_step cfg /\ ~ done cfg.

(** A single goroutine blocked forever on an empty channel with no sender. *)
Definition block_cfg : Config :=
  mkCfg (fun t => if Nat.eqb t 0 then [PRecv 0] else [])
        (fun _ => []) (fun t => Nat.eqb t 0) [].

Lemma block_stuck : Stuck block_cfg.
Proof.
  split.
  - intros [cfg' Hstep]. inversion Hstep; subst; cbn in *;
      match goal with H : (_ =? 0) = true |- _ => apply Nat.eqb_eq in H; subst end;
      cbn in *; try discriminate;
      (* the recv-on-closed case: the trace is empty, so its [nth_error [] pos = Some e] is absurd *)
      match goal with H : nth_error [] _ = Some _ |- _ =>
        apply nth_error_lt in H; cbn in H; lia end.
  - intros Hdone. specialize (Hdone 0 eq_refl). discriminate Hdone.
Qed.

(** ── SELECT, the AUTHORITATIVE relational semantics: the two code-review findings, proven ──

    These two witnesses are the FIX for the select code review (the sequential [run_io]
    [select_recv2] is a deterministic, blocking-idealised UNDER-APPROXIMATION; here select is
    a first-class operational action whose [step_select] rule is the authoritative truth). *)

(** FINDING 1 — CHOICE IS NONDETERMINISTIC.  A config with TWO ready cases has TWO distinct
    successors (receive ch0 vs receive ch1, distinguishable in the trace).  Go picks
    pseudo-randomly; the sequential ch1-priority interpreter realises only the first — so a
    safety property must hold for BOTH, never just the deterministic one.  ([sel_ready_cfg] is
    a post-send state: positions 0 and 1 are the two earlier sends, so it is [Inv]-valid.) *)
Definition sel_ready_cfg : Config :=
  mkCfg (fun t => if Nat.eqb t 0 then [PSelect [0; 1]] else [])
        (fun c => if Nat.eqb c 0 then [0] else if Nat.eqb c 1 then [1] else [])
        (fun t => Nat.eqb t 0)
        [mkEv 0 (KSend 0); mkEv 0 (KSend 1)].

Theorem select_nondeterministic :
  exists cfg1 cfg2, step sel_ready_cfg cfg1 /\ step sel_ready_cfg cfg2 /\
                    cfg_trace cfg1 <> cfg_trace cfg2.
Proof.
  eexists. eexists. split; [| split].
  - eapply step_select with (tid:=0) (cs:=[0;1]) (c:=0) (s:=0);
      [ reflexivity | reflexivity | left; reflexivity | reflexivity ].
  - eapply step_select with (tid:=0) (cs:=[0;1]) (c:=1) (s:=1);
      [ reflexivity | reflexivity | right; left; reflexivity | reflexivity ].
  - cbn. intro H. inversion H.
Qed.

(** FINDING 2 — EMPTY SELECT IS DEADLOCK, NOT A VALUE.  A goroutine selecting on channels with
    no ready case (and no other goroutine to make one ready) is [Stuck] — exactly like
    [block_cfg], NOT the fabricated [(0, zero)] the sequential interpreter returns.  Blocking
    lives in the GLOBAL transition relation (no enabled step), per the review. *)
Definition sel_block_cfg : Config :=
  mkCfg (fun t => if Nat.eqb t 0 then [PSelect [0; 1]] else [])
        (fun _ => []) (fun t => Nat.eqb t 0) [].

Lemma sel_block_stuck : Stuck sel_block_cfg.
Proof.
  split.
  - intros [cfg' Hstep]. inversion Hstep; subst; cbn in *;
      match goal with H : (_ =? 0) = true |- _ => apply Nat.eqb_eq in H; subst end;
      cbn in *; try discriminate;
      (* select_closed: the trace is empty, so its [nth_error [] pos = Some e] is absurd *)
      match goal with H : nth_error [] _ = Some _ |- _ =>
        apply nth_error_lt in H; cbn in H; lia end.
  - intros Hdone. specialize (Hdone 0 eq_refl). discriminate Hdone.
Qed.

(** CLOSED-CHANNEL READINESS, OPERATIONAL (closes the select review's relational gap end-to-end).
    A recv/select on a CLOSED, drained channel is READY — it STEPS, yielding the zero value — whereas
    on an OPEN empty channel it is stuck ([block_stuck]/[sel_block_stuck] above).  [closed_chan_cfg]
    has channel 5 already closed (a [KClose 5] at trace position 0) and an empty buffer. *)
Definition closed_chan_cfg : Config :=
  mkCfg (fun t => if Nat.eqb t 0 then [PRecv 5] else if Nat.eqb t 1 then [PSelect [5]] else [])
        (fun _ => []) (fun t => orb (Nat.eqb t 0) (Nat.eqb t 1))
        [mkEv 2 (KClose 5)].

(** The recv from the closed, drained channel CAN step (Go: returns zero) — where the buffered
    [step_recv] could not.  The emitted [KRecv 5 0]'s producer is the close (pos 0). *)
Theorem closed_recv_can_step : exists cfg', step closed_chan_cfg cfg'.
Proof.
  eexists. eapply step_recv_closed with (tid := 0) (c := 5) (pos := 0) (e := mkEv 2 (KClose 5));
    [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity ].
Qed.

(** A SELECT whose only case channel is closed+drained is likewise READY (the case fires with zero)
    — the relational fix for the exact bug the sequential model had (it took [default] / fabricated). *)
Theorem closed_select_can_step : exists cfg', step closed_chan_cfg cfg'.
Proof.
  eexists. eapply step_select_closed with (tid := 1) (cs := [5]) (c := 5) (pos := 0) (e := mkEv 2 (KClose 5));
    [ reflexivity | reflexivity | left; reflexivity | reflexivity | reflexivity | reflexivity ].
Qed.

(** And the step keeps the trace well-formed (the closed-recv is a real, sound transition): the
    resulting config still satisfies [Inv] (so its trace's happens-before stays a strict order). *)
Theorem closed_recv_preserves_inv :
  forall cfg', step closed_chan_cfg cfg' -> Inv closed_chan_cfg -> Inv cfg'.
Proof. intros cfg' Hstep Hinv. exact (step_preserves_inv _ _ Hstep Hinv). Qed.

(** ============================================================================
    STEP 1.2 + 1.3 + real memory — a RICH calculus: VALUES, a HEAP, value-dependent
    control (a command TREE with bind), dynamic spawn, AND a refinement showing the
    channel operations implement the [run_io] channel-buffer laws.

    The keystone's substance: a faithful concurrent model of actual Fido programs —
    channels carry VALUES, reads return them, the continuation functions are [bind]
    (control branches on received/read values), the HEAP is real — yet it INHERITS
    the same axiom-free safety theorems (well-formed traces ⇒ hb a strict partial
    order; ownership ⇒ race-free), reusing [WfTrace]/[hbt]/[Owned]/[owned_race_free].
    And [rchan] (its channel value-FIFO) evolves EXACTLY as the [run_io] [chan_buf]
    laws specify, so it is a sound model of Fido's IO channels.
    ============================================================================ *)

(* DECIDABLE "channel [c] is closed": some [KClose c] event sits in the trace (closed-state is read
   off the trace, exactly as [rstep_recv_closed] does — no [RConfig] field).  Defined HERE (before the
   rich calculus) because [rstep_close] is GUARDED by it: closing a channel needs it still OPEN, so a
   double-close has no valid step (Go PANICS on it) — see [rpanicking]. *)
Definition closedb (tr : Trace) (c : nat) : bool :=
  existsb (fun e => match e_kind e with KClose c' => Nat.eqb c' c | _ => false end) tr.

Lemma closedb_true_witness : forall tr c, closedb tr c = true ->
  exists pos e, nth_error tr pos = Some e /\ e_kind e = KClose c.
Proof.
  intros tr c H. unfold closedb in H. apply existsb_exists in H. destruct H as [e [Hin He]].
  destruct (e_kind e) as [c0|c0 from|ch|par|l|l|c0] eqn:Ek; try discriminate.
  apply Nat.eqb_eq in He. subst c0.
  apply In_nth_error in Hin. destruct Hin as [pos Hpos]. exists pos, e. split; [exact Hpos | exact Ek].
Qed.

Lemma closedb_false_not : forall tr c, closedb tr c = false ->
  ~ (exists pos e, nth_error tr pos = Some e /\ e_kind e = KClose c).
Proof.
  intros tr c H [pos [e [Hpos Hek]]].
  assert (Hin : In e tr) by (eapply nth_error_In; exact Hpos).
  assert (Htrue : closedb tr c = true).
  { unfold closedb. apply existsb_exists. exists e. split; [exact Hin | rewrite Hek; apply Nat.eqb_refl]. }
  rewrite H in Htrue. discriminate.
Qed.

(* [Cmd] recurses through [list (nat * (nat -> Cmd))] in [CSelect].  Registering the "All" schemes
   for the nesting types [prod] and [list] FIRST lets Coq build [Cmd]'s full nested induction
   principle (rather than warning that it cannot) — the fix the [register-all] diagnostic recommends. *)
Scheme All for prod.
Scheme All for list.

Inductive Cmd : Type :=
  | CRet   : Cmd
  | CSend  : nat -> nat -> Cmd -> Cmd          (* send value on channel, continue *)
  | CRecv  : nat -> (nat -> Cmd) -> Cmd        (* recv from channel, BIND value, continue *)
  | CWrite : nat -> nat -> Cmd -> Cmd          (* write value to location, continue *)
  | CRead  : nat -> (nat -> Cmd) -> Cmd        (* read location, BIND value, continue *)
  | CSpawn : Cmd -> Cmd -> Cmd                 (* spawn child, continue parent *)
  | CSelect : list (nat * (nat -> Cmd)) -> Cmd  (* select over recv cases — see note below *)
  | CClose : nat -> Cmd -> Cmd.                  (* close(c), then continue.  A recv/select on a
                                                    CLOSED, drained channel becomes READY (binds the
                                                    zero value): rstep_close / rstep_recv_closed /
                                                    rstep_select_closed — the rich-calculus port of
                                                    the simple-calculus closed-channel slice. *)
  (* [select] over recv cases, each a (channel, value-binding continuation) PAIR — the
     AUTHORITATIVE select in the rich value-carrying calculus (the typed [run_io] [select_recv2]
     is a non-authoritative ch1-priority interpreter — see the select code reviews).  Unlike the
     simple-calculus [PSelect] (which shared ONE continuation across cases), each case carries its
     OWN continuation, so [select { case <-ch: A() | case <-ch: B() }] — same channel, distinct
     bodies — is representable and BOTH cases are eligible (Go may pick either).  [rstep_select]
     below fires for EVERY ready case, so select is genuinely NONDETERMINISTIC; when no case is
     ready it has no step, so empty-select is a LOCAL non-step feeding global deadlock [RStuck]. *)

Record RConfig := mkRCfg {
  rc_prog  : nat -> Cmd;
  rc_bufs  : nat -> list (nat * nat);   (* channel -> FIFO of (value, send-position) *)
  rc_heap  : nat -> nat;                 (* location -> value *)
  rc_live  : nat -> bool;
  rc_trace : Trace
}.

Inductive rstep : RConfig -> RConfig -> Prop :=
  | rstep_send : forall p b h lv tr tid c v k,
      lv tid = true -> p tid = CSend c v k -> closedb tr c = false ->
      rstep (mkRCfg p b h lv tr)
            (mkRCfg (upd p tid k) (upd b c (b c ++ [(v, length tr)])) h lv
                    (tr ++ [mkEv tid (KSend c)]))
  | rstep_recv : forall p b h lv tr tid c f v s brest,
      lv tid = true -> p tid = CRecv c f -> b c = (v, s) :: brest ->
      rstep (mkRCfg p b h lv tr)
            (mkRCfg (upd p tid (f v)) (upd b c brest) h lv
                    (tr ++ [mkEv tid (KRecv c s)]))
  | rstep_write : forall p b h lv tr tid l v k,
      lv tid = true -> p tid = CWrite l v k ->
      rstep (mkRCfg p b h lv tr)
            (mkRCfg (upd p tid k) b (upd h l v) lv
                    (tr ++ [mkEv tid (KWrite l)]))
  | rstep_read : forall p b h lv tr tid l f,
      lv tid = true -> p tid = CRead l f ->
      rstep (mkRCfg p b h lv tr)
            (mkRCfg (upd p tid (f (h l))) b h lv
                    (tr ++ [mkEv tid (KRead l)]))
  (* spawn emits BOTH the parent's [KSpawn cid] AND the child's [KStart (length tr)] —
     atomically GROUNDING Go's "the [go] statement happens-before the start of the goroutine's
     execution" (go.dev/ref/mem) in the operational semantics: the [KStart]'s back-pointer is the
     position of the [KSpawn] just emitted ([length tr]), so the fork synchronisation edge ([sync]
     [KStart]->[KSpawn]) is now PRODUCED BY EXECUTION rather than hand-built in a witness trace.
     ([KStart] carries the child [tid], so it joins the child's program order; pinning it right
     after [KSpawn] is one valid linearisation and introduces NO spurious happens-before edge — [hbt]
     is [po] (same-tid) U [sync] only, never global trace order — see [fork_exec_trace] below.) *)
  | rstep_spawn : forall p b h lv tr tid child k cid,
      lv tid = true -> p tid = CSpawn child k -> lv cid = false ->
      rstep (mkRCfg p b h lv tr)
            (mkRCfg (upd (upd p tid k) cid child) b h (upd lv cid true)
                    (tr ++ [mkEv tid (KSpawn cid); mkEv cid (KStart (length tr))]))
  (* select: pick ANY case [(c, f)] in [cases] whose channel [c] is READY ([b c = (v,s)::brest]);
     receive [v], BIND it into THAT case's continuation [f], emit the recv event.  Like
     [rstep_recv] but choosing among a SET of (channel, continuation) cases — so [rstep] is
     nondeterministic at a select, and each successor runs the chosen case's own continuation. *)
  | rstep_select : forall p b h lv tr tid cases c f v s brest,
      lv tid = true -> p tid = CSelect cases ->
      In (c, f) cases -> b c = (v, s) :: brest ->
      rstep (mkRCfg p b h lv tr)
            (mkRCfg (upd p tid (f v)) (upd b c brest) h lv
                    (tr ++ [mkEv tid (KRecv c s)]))
  (* close: record a [KClose c] event (no buffer change).  GUARDED by [closedb tr c = false] — the
     channel must still be OPEN.  A close of an ALREADY-closed channel has no step (Go PANICS): it is
     classified [rpanicking], not a silent re-close.  ([closedb] is permanent — [rsteps_closedb_mono]
     — so once closed the guard never re-opens.) *)
  | rstep_close : forall p b h lv tr tid c k,
      lv tid = true -> p tid = CClose c k -> closedb tr c = false ->
      rstep (mkRCfg p b h lv tr)
            (mkRCfg (upd p tid k) b h lv (tr ++ [mkEv tid (KClose c)]))
  (* recv from a CLOSED, DRAINED channel: READY in Go (binds the zero value [0]); the [KRecv]'s
     back-pointer is the CLOSE position [pos] (close happens-before the closed-recv, per the Go
     memory model).  [nth_error tr pos = Some e /\ e_kind e = KClose c] reads "c is closed". *)
  | rstep_recv_closed : forall p b h lv tr tid c f pos e,
      lv tid = true -> p tid = CRecv c f ->
      b c = [] -> nth_error tr pos = Some e -> e_kind e = KClose c ->
      rstep (mkRCfg p b h lv tr)
            (mkRCfg (upd p tid (f 0)) b h lv (tr ++ [mkEv tid (KRecv c pos)]))
  (* select whose case channel [c] is CLOSED + drained: that case is READY (binds zero) — the
     closed-channel analogue of [rstep_select]. *)
  | rstep_select_closed : forall p b h lv tr tid cases c f pos e,
      lv tid = true -> p tid = CSelect cases ->
      In (c, f) cases -> b c = [] -> nth_error tr pos = Some e -> e_kind e = KClose c ->
      rstep (mkRCfg p b h lv tr)
            (mkRCfg (upd p tid (f 0)) b h lv (tr ++ [mkEv tid (KRecv c pos)])).

Definition RBufOk (cfg : RConfig) : Prop :=
  forall c v s, In (v, s) (rc_bufs cfg c) ->
    s < length (rc_trace cfg) /\
    exists e', nth_error (rc_trace cfg) s = Some e' /\ e_kind e' = KSend c.

Definition RInv (cfg : RConfig) : Prop := WfTrace (rc_trace cfg) /\ RBufOk cfg.

Lemma rstep_preserves_inv : forall cfg cfg', rstep cfg cfg' -> RInv cfg -> RInv cfg'.
Proof.
  intros cfg cfg' Hstep [Hwf Hbuf].
  destruct Hstep as
    [ p b h lv tr tid c v k Hlv Hp _
    | p b h lv tr tid c f v s brest Hlv Hp Hbc
    | p b h lv tr tid l v k Hlv Hp
    | p b h lv tr tid l f Hlv Hp
    | p b h lv tr tid child k cid Hlv Hp Hcid
    | p b h lv tr tid cases c f v s brest Hlv Hp Hin Hbc
    | p b h lv tr tid c k Hlv Hp _
    | p b h lv tr tid c f pos e Hlv Hp Hbc Hpos Hek
    | p b h lv tr tid cases c f pos e Hlv Hp Hin Hbc Hpos Hek ];
    split.
  (* send WfTrace / RBufOk *)
  - apply WfTrace_app; [exact Hwf | cbn; exact I].
  - intros c0 v0 s0 Hin. cbn [rc_bufs rc_trace] in Hin |- *.
    destruct (Nat.eq_dec c0 c) as [->|Hne].
    + rewrite upd_same in Hin. rewrite in_app_iff in Hin. destruct Hin as [Hin | Hin].
      * destruct (Hbuf c v0 s0 Hin) as [Hlt Hex]. apply BufOk_pos_app; assumption.
      * destruct Hin as [Heq | []]. injection Heq as Hv Hs. subst s0.
        split; [rewrite length_app; cbn; lia |].
        exists (mkEv tid (KSend c)). rewrite nth_error_app_new. split; reflexivity.
    + rewrite (upd_other _ _ _ _ Hne) in Hin.
      destruct (Hbuf c0 v0 s0 Hin) as [Hlt Hex]. apply BufOk_pos_app; assumption.
  (* recv WfTrace / RBufOk *)
  - apply WfTrace_app; [exact Hwf | cbn].
    assert (Hins : In (v, s) (b c)) by (rewrite Hbc; left; reflexivity).
    destruct (Hbuf c v s Hins) as [Hlt [e' [He' Hk']]].
    split; [exact Hlt | exists e'; split; [exact He' | left; exact Hk']].
  - intros c0 v0 s0 Hin. cbn [rc_bufs rc_trace] in Hin |- *.
    destruct (Nat.eq_dec c0 c) as [->|Hne].
    + rewrite upd_same in Hin.
      assert (Hin' : In (v0, s0) (b c)) by (rewrite Hbc; right; exact Hin).
      destruct (Hbuf c v0 s0 Hin') as [Hlt Hex]. apply BufOk_pos_app; assumption.
    + rewrite (upd_other _ _ _ _ Hne) in Hin.
      destruct (Hbuf c0 v0 s0 Hin) as [Hlt Hex]. apply BufOk_pos_app; assumption.
  (* write WfTrace / RBufOk *)
  - apply WfTrace_app; [exact Hwf | cbn; exact I].
  - intros c0 v0 s0 Hin. cbn [rc_bufs rc_trace] in Hin |- *.
    destruct (Hbuf c0 v0 s0 Hin) as [Hlt Hex]. apply BufOk_pos_app; assumption.
  (* read WfTrace / RBufOk *)
  - apply WfTrace_app; [exact Hwf | cbn; exact I].
  - intros c0 v0 s0 Hin. cbn [rc_bufs rc_trace] in Hin |- *.
    destruct (Hbuf c0 v0 s0 Hin) as [Hlt Hex]. apply BufOk_pos_app; assumption.
  (* spawn WfTrace / RBufOk: trace appends [KSpawn cid; KStart (length tr)] — TWO events.
     WfTrace via two [WfTrace_app]s; the [KStart]'s obligation points at the [KSpawn] just laid down. *)
  - change ([mkEv tid (KSpawn cid); mkEv cid (KStart (length tr))])
      with ([mkEv tid (KSpawn cid)] ++ [mkEv cid (KStart (length tr))]).
    rewrite app_assoc.
    apply WfTrace_app.
    + apply WfTrace_app; [exact Hwf | cbn; exact I].
    + cbn. split; [rewrite length_app; cbn; lia |].
      exists (mkEv tid (KSpawn cid)).
      rewrite nth_error_app_new. split; reflexivity.
  - intros c0 v0 s0 Hin. cbn [rc_bufs rc_trace] in Hin |- *.
    destruct (Hbuf c0 v0 s0 Hin) as [Hlt Hex]. apply BufOk_pos_app_gen; assumption.
  (* select WfTrace / RBufOk — identical to recv (it receives on the chosen ready channel) *)
  - apply WfTrace_app; [exact Hwf | cbn].
    assert (Hins : In (v, s) (b c)) by (rewrite Hbc; left; reflexivity).
    destruct (Hbuf c v s Hins) as [Hlt [e' [He' Hk']]].
    split; [exact Hlt | exists e'; split; [exact He' | left; exact Hk']].
  - intros c0 v0 s0 Hin0. cbn [rc_bufs rc_trace] in Hin0 |- *.
    destruct (Nat.eq_dec c0 c) as [->|Hne].
    + rewrite upd_same in Hin0.
      assert (Hin' : In (v0, s0) (b c)) by (rewrite Hbc; right; exact Hin0).
      destruct (Hbuf c v0 s0 Hin') as [Hlt Hex]. apply BufOk_pos_app; assumption.
    + rewrite (upd_other _ _ _ _ Hne) in Hin0.
      destruct (Hbuf c0 v0 s0 Hin0) as [Hlt Hex]. apply BufOk_pos_app; assumption.
  (* close WfTrace / RBufOk (KClose has no obligation; bufs unchanged) *)
  - apply WfTrace_app; [exact Hwf | cbn; exact I].
  - intros c0 v0 s0 Hin1. cbn [rc_bufs rc_trace] in Hin1 |- *.
    destruct (Hbuf c0 v0 s0 Hin1) as [Hlt Hex]. apply BufOk_pos_app; assumption.
  (* recv_closed WfTrace / RBufOk (KRecv's producer is the CLOSE at [pos]; bufs unchanged) *)
  - apply WfTrace_app; [exact Hwf | cbn].
    split; [exact (nth_error_lt _ _ _ Hpos) | exists e; split; [exact Hpos | right; exact Hek]].
  - intros c0 v0 s0 Hin1. cbn [rc_bufs rc_trace] in Hin1 |- *.
    destruct (Hbuf c0 v0 s0 Hin1) as [Hlt Hex]. apply BufOk_pos_app; assumption.
  (* select_closed WfTrace / RBufOk (same closed-recv shape) *)
  - apply WfTrace_app; [exact Hwf | cbn].
    split; [exact (nth_error_lt _ _ _ Hpos) | exists e; split; [exact Hpos | right; exact Hek]].
  - intros c0 v0 s0 Hin1. cbn [rc_bufs rc_trace] in Hin1 |- *.
    destruct (Hbuf c0 v0 s0 Hin1) as [Hlt Hex]. apply BufOk_pos_app; assumption.
Qed.

Inductive rsteps : RConfig -> RConfig -> Prop :=
  | rsteps_refl : forall cfg, rsteps cfg cfg
  | rsteps_step : forall a b c, rstep a b -> rsteps b c -> rsteps a c.

Definition rinit_cfg (p : nat -> Cmd) : RConfig :=
  mkRCfg p (fun _ => []) (fun _ => 0) (fun t => Nat.eqb t 0) [].

Lemma rinit_inv : forall p, RInv (rinit_cfg p).
Proof.
  intros p. split.
  - intros i e H. apply nth_error_lt in H. cbn in H. lia.
  - intros c v s H. cbn in H. contradiction.
Qed.

Lemma rsteps_preserves_inv : forall a b, rsteps a b -> RInv a -> RInv b.
Proof.
  intros a b H. induction H; intros Hinv; [exact Hinv|].
  apply IHrsteps. exact (rstep_preserves_inv _ _ H Hinv).
Qed.

(** Every reachable RICH execution trace is well-formed -> hb is a strict order. *)
Theorem reachable_wf_r : forall p cfg, rsteps (rinit_cfg p) cfg -> WfTrace (rc_trace cfg).
Proof. intros p cfg H. apply (rsteps_preserves_inv _ _ H (rinit_inv p)). Qed.

Corollary reachable_hb_strict_r : forall p cfg i,
  rsteps (rinit_cfg p) cfg -> ~ hbt (rc_trace cfg) i i.
Proof. intros p cfg i H. apply hbt_irrefl. exact (reachable_wf_r p cfg H). Qed.

(** Race-freedom under ownership transfers to the rich calculus too. *)
Corollary reachable_owned_safe_r : forall p cfg,
  rsteps (rinit_cfg p) cfg -> Owned (rc_trace cfg) ->
  TraceRaceFree (rc_trace cfg) /\ (forall i, ~ hbt (rc_trace cfg) i i).
Proof.
  intros p cfg Hsteps HO. split.
  - exact (owned_race_free _ HO).
  - intro i. apply hbt_irrefl. exact (reachable_wf_r p cfg Hsteps).
Qed.

(** ---- Grounding Go's "go-before-start" in EXECUTION (concurrency research-plan 1.1) ----
    [fork_handoff_trace] / [fork_handoff_race_free] (defined way above) were HAND-BUILT traces:
    we asserted the events and proved the fork edge made the write/read non-racy.  Now that
    [rstep_spawn] EMITS the child's [KStart], that very trace is PRODUCED BY RUNNING a program:
    [main] writes loc 7, spawns a child, the child reads loc 7.  Executing it yields EXACTLY
    [fork_handoff_trace] ([fork_exec_trace]) — so the fork synchronisation is no longer an
    assertion about a literal but a CONSEQUENCE of the operational semantics, and race-freedom
    then drops out of [reachable_owned_safe_r] ([fork_exec_race_free]).  This is the operational
    analogue of "the [go] statement happens-before the start of the goroutine's execution". *)
Definition fork_child : Cmd := CRead 7 (fun _ => CRet).
Definition fork_prog : nat -> Cmd :=
  fun n => if Nat.eqb n 0 then CWrite 7 99 (CSpawn fork_child CRet) else CRet.

Theorem fork_exec_trace :
  exists cfg, rsteps (rinit_cfg fork_prog) cfg /\ rc_trace cfg = fork_handoff_trace.
Proof.
  unfold rinit_cfg. eexists. split.
  - eapply rsteps_step.
    { eapply rstep_write with (tid := 0); reflexivity. }
    eapply rsteps_step.
    { eapply rstep_spawn with (tid := 0) (cid := 1);
        [ reflexivity | rewrite upd_same; reflexivity | reflexivity ]. }
    eapply rsteps_step.
    { eapply rstep_read with (tid := 1);
        [ rewrite upd_same; reflexivity | rewrite upd_same; reflexivity ]. }
    apply rsteps_refl.
  - cbn. reflexivity.
Qed.

(** The executed trace is race-free AND its happens-before is a strict order — derived purely from
    reachability (WfTrace) + ownership, with the fork edge now grounded in execution. *)
Theorem fork_exec_race_free :
  exists cfg, rsteps (rinit_cfg fork_prog) cfg /\
              TraceRaceFree (rc_trace cfg) /\ (forall i, ~ hbt (rc_trace cfg) i i).
Proof.
  destruct fork_exec_trace as [cfg [Hsteps Htr]].
  exists cfg. split; [exact Hsteps |].
  apply (reachable_owned_safe_r fork_prog cfg Hsteps).
  rewrite Htr. exact fork_handoff_owned.
Qed.

(** ---- Grounding Go's CHANNEL handoff (the recv-from edge) in EXECUTION ----
    The SIBLING of [fork_exec_*]: the OTHER (and primary) go-mem mechanism — "a send on a channel
    happens-before the corresponding receive completes" (go.dev/ref/mem).  [handoff_trace] above was
    HAND-BUILT; here a real program PRODUCES the handoff by running.  Crucially, [main] SPAWNS the
    child FIRST, and only THEN writes loc 7 and sends — so the FORK edge canNOT publish the write
    (the write happens AFTER the spawn), and the cross-goroutine ordering MUST flow through the
    channel send/recv.  This is the canonical "publish a write by passing it over a channel" idiom,
    and the executed trace proves it race-free via the channel edge alone ([transfer_orders] over the
    [KSend]/[KRecv] pair at positions 3->4).  The trace is SIX events (the spawn is unavoidable: a
    real run starts with [main] only and must [go] to get a second goroutine). *)
Definition chan_pub_child : Cmd := CRecv 0 (fun _ => CRead 7 (fun _ => CRet)).
Definition chan_pub_prog : nat -> Cmd :=
  fun n => if Nat.eqb n 0
           then CSpawn chan_pub_child (CWrite 7 99 (CSend 0 42 CRet))
           else CRet.

(* The exact trace a run of [chan_pub_prog] emits: spawn, child-start, then main's write/send, then
   the child's recv (back-pointer 3 = the send) and read.  Heap accesses are ONLY at 2 (write) and 5
   (read); they are ordered write ->po send ->sync recv ->po read. *)
Definition chan_pub_trace : Trace :=
  [ mkEv 0 (KSpawn 1); mkEv 1 (KStart 0); mkEv 0 (KWrite 7);
    mkEv 0 (KSend 0); mkEv 1 (KRecv 0 3); mkEv 1 (KRead 7) ].

Lemma chan_pub_loc_pos : forall i l, acc_loc_at chan_pub_trace i = Some l -> i = 2 \/ i = 5.
Proof.
  intros i l H. pose proof (acc_loc_at_lt _ _ _ H) as Hlt. cbn in Hlt.
  unfold chan_pub_trace, acc_loc_at in H.
  destruct i as [|[|[|[|[|[|i]]]]]]; cbn in H;
    [ discriminate | discriminate | left; reflexivity
    | discriminate | discriminate | right; reflexivity | lia ].
Qed.

Lemma chan_pub_owned : Owned chan_pub_trace.
Proof.
  intros i j Hij [l [Hi Hj]]. left.
  destruct (chan_pub_loc_pos i l Hi) as [-> | ->];
    destruct (chan_pub_loc_pos j l Hj) as [-> | ->]; try lia.
  apply (transfer_orders chan_pub_trace 2 3 4 5).
  - unfold po, tid_at; cbn. repeat split; lia.
  - unfold sync; cbn. exists (mkEv 1 (KRecv 0 3)); cbn. split; reflexivity.
  - unfold po, tid_at; cbn. repeat split; lia.
Qed.

(* [upd] is opaque, so project through the [upd] stack with [upd_same]/[upd_other] before [reflexivity]. *)
Ltac upd_proj := repeat first [ rewrite upd_same | rewrite upd_other by discriminate ].

Theorem chan_pub_exec_trace :
  exists cfg, rsteps (rinit_cfg chan_pub_prog) cfg /\ rc_trace cfg = chan_pub_trace.
Proof.
  unfold rinit_cfg. eexists. split.
  - eapply rsteps_step.
    { eapply rstep_spawn with (tid := 0) (cid := 1); upd_proj; reflexivity. }
    eapply rsteps_step.
    { eapply rstep_write with (tid := 0); upd_proj; reflexivity. }
    eapply rsteps_step.
    { eapply rstep_send with (tid := 0); upd_proj; reflexivity. }
    eapply rsteps_step.
    { eapply rstep_recv with (tid := 1); upd_proj; reflexivity. }
    eapply rsteps_step.
    { eapply rstep_read with (tid := 1); upd_proj; reflexivity. }
    apply rsteps_refl.
  - cbn. reflexivity.
Qed.

(** The executed 2-goroutine message-passing program is race-free AND hb-irreflexive — derived from
    reachability + ownership, with the WRITE PUBLISHED PURELY OVER THE CHANNEL (the fork edge cannot
    carry it).  The operational analogue of "send happens-before the matching receive completes". *)
Theorem chan_pub_exec_race_free :
  exists cfg, rsteps (rinit_cfg chan_pub_prog) cfg /\
              TraceRaceFree (rc_trace cfg) /\ (forall i, ~ hbt (rc_trace cfg) i i).
Proof.
  destruct chan_pub_exec_trace as [cfg [Hsteps Htr]].
  exists cfg. split; [exact Hsteps |].
  apply (reachable_owned_safe_r chan_pub_prog cfg Hsteps).
  rewrite Htr. exact chan_pub_owned.
Qed.

(** ---- The refinement: the rich calculus implements the [run_io] channel laws ----
    [rchan] is the channel VALUE-FIFO.  A send ENQUEUES the value (matching the
    [run_io] law [chan_buf_send]: buffer after send = buffer ++ [v]); a receive
    DEQUEUES the head (matching [chan_buf_recv]: buffer = v :: rest).  And the HEAP
    gives read-after-write.  So the operational calculus soundly models Fido's IO
    channels and memory — the keystone connection at the state level. *)
Definition rchan (cfg : RConfig) (c : nat) : list nat := map fst (rc_bufs cfg c).

Lemma rchan_send_law : forall (b : nat -> list (nat*nat)) c v pos,
  map fst (upd b c (b c ++ [(v, pos)]) c) = map fst (b c) ++ [v].
Proof. intros. rewrite upd_same, map_app. reflexivity. Qed.

Lemma rchan_recv_law : forall (b : nat -> list (nat*nat)) c v s brest,
  b c = (v, s) :: brest -> map fst (b c) = v :: map fst (upd b c brest c).
Proof. intros b c v s brest H. rewrite upd_same, H. reflexivity. Qed.

Lemma rheap_read_after_write : forall (h : nat -> nat) l v, upd h l v l = v.
Proof. intros. apply upd_same. Qed.

(** Concrete value flow: a receive BINDS the channel value into the continuation, so
    control branches on it.  Goroutine 0 runs [CRecv 0 (fun v => CWrite 0 v CRet)];
    the head buffer entry is [(7, 0)] (value 7, sent at position 0).  After the step
    the goroutine's program is [CWrite 0 7 CRet] — the received 7 has flowed in. *)
Example rich_recv_binds : exists cfg',
  rstep (mkRCfg (fun t => if t =? 0 then CRecv 0 (fun v => CWrite 0 v CRet) else CRet)
                (fun ch => if ch =? 0 then [(7, 0)] else [])
                (fun _ => 0) (fun t => t =? 0) [mkEv 5 (KSend 0)]) cfg'
  /\ rc_prog cfg' 0 = CWrite 0 7 CRet.
Proof.
  eexists. split.
  - apply rstep_recv with (tid := 0) (c := 0); reflexivity.
  - cbn [rc_prog]. rewrite upd_same. reflexivity.
Qed.

(** Concrete real memory: a read returns the HEAP value (42 at location 0) and binds
    it into the continuation — goroutine 0's program becomes [CWrite 1 42 CRet]. *)
Example rich_read_binds : exists cfg',
  rstep (mkRCfg (fun t => if t =? 0 then CRead 0 (fun v => CWrite 1 v CRet) else CRet)
                (fun _ => []) (fun l => if l =? 0 then 42 else 0) (fun t => t =? 0) []) cfg'
  /\ rc_prog cfg' 0 = CWrite 1 42 CRet.
Proof.
  eexists. split.
  - apply rstep_read with (tid := 0) (l := 0); reflexivity.
  - cbn [rc_prog]. rewrite upd_same. cbn. reflexivity.
Qed.

(** The rich calculus also has the exact-FIFO invariant (the send-position component
    of each buffer is strictly increasing) — completing its property set. *)
Definition RBufSorted (cfg : RConfig) : Prop := forall c, Incr (map snd (rc_bufs cfg c)).

Lemma rstep_preserves_sorted : forall cfg cfg',
  rstep cfg cfg' -> RInv cfg -> RBufSorted cfg -> RBufSorted cfg'.
Proof.
  intros cfg cfg' Hstep [Hwf Hbuf] Hsort.
  destruct Hstep as
    [ p b h lv tr tid c v k Hlv Hp _
    | p b h lv tr tid c f v s brest Hlv Hp Hbc
    | p b h lv tr tid l v k Hlv Hp
    | p b h lv tr tid l f Hlv Hp
    | p b h lv tr tid child k cid Hlv Hp Hcid
    | p b h lv tr tid cases c f v s brest Hlv Hp Hin Hbc
    | p b h lv tr tid c k Hlv Hp _
    | p b h lv tr tid c f pos e Hlv Hp Hbc Hpos Hek
    | p b h lv tr tid cases c f pos e Hlv Hp Hin Hbc Hpos Hek ];
    intros c0; cbn [rc_bufs rc_trace].
  - destruct (Nat.eq_dec c0 c) as [->|Hne].
    + rewrite upd_same. rewrite map_app. apply Incr_app.
      * exact (Hsort c).
      * intros x Hx. apply in_map_iff in Hx. destruct Hx as [[v' s'] [Heq Hin]].
        cbn in Heq. subst x. destruct (Hbuf c v' s' Hin) as [Hlt _]. exact Hlt.
    + rewrite (upd_other _ _ _ _ Hne). exact (Hsort c0).
  - destruct (Nat.eq_dec c0 c) as [->|Hne].
    + rewrite upd_same. specialize (Hsort c). cbn [rc_bufs] in Hsort.
      rewrite Hbc in Hsort. cbn in Hsort. apply Incr_tail in Hsort. exact Hsort.
    + rewrite (upd_other _ _ _ _ Hne). exact (Hsort c0).
  - exact (Hsort c0).
  - exact (Hsort c0).
  - exact (Hsort c0).
  - (* select: same as recv (the chosen channel loses its head) *)
    destruct (Nat.eq_dec c0 c) as [->|Hne].
    + rewrite upd_same. specialize (Hsort c). cbn [rc_bufs] in Hsort.
      rewrite Hbc in Hsort. cbn in Hsort. apply Incr_tail in Hsort. exact Hsort.
    + rewrite (upd_other _ _ _ _ Hne). exact (Hsort c0).
  - (* close: bufs unchanged *) exact (Hsort c0).
  - (* recv_closed: bufs unchanged *) exact (Hsort c0).
  - (* select_closed: bufs unchanged *) exact (Hsort c0).
Qed.

Lemma rinit_sorted : forall p, RBufSorted (rinit_cfg p).
Proof. intros p c. cbn. exact I. Qed.

Lemma rsteps_preserves_both : forall a b,
  rsteps a b -> RInv a -> RBufSorted a -> RInv b /\ RBufSorted b.
Proof.
  intros a b H. induction H; intros Hinv Hsort; [split; assumption|].
  apply IHrsteps.
  - exact (rstep_preserves_inv _ _ H Hinv).
  - exact (rstep_preserves_sorted _ _ H Hinv Hsort).
Qed.

Theorem reachable_sorted_r : forall p cfg, rsteps (rinit_cfg p) cfg -> RBufSorted cfg.
Proof.
  intros p cfg H. apply (rsteps_preserves_both _ _ H (rinit_inv p) (rinit_sorted p)).
Qed.

(** ── SYNCHRONOUS (unbuffered) RENDEZVOUS, DERIVED — no new rule, no cascade. ──

    The calculus's channels are nominally unbounded-buffered, but an UNBUFFERED handoff (Go: a send
    on a cap-0 channel blocks until a receiver takes the value) is REPRESENTABLE as the existing
    [rstep_send] immediately followed by the matching [rstep_recv]: the value never RESTS in the
    buffer — it is enqueued then dequeued back-to-back, so the buffer returns to empty and the value
    passes straight from sender [t0]'s [v] to receiver [t1]'s continuation [k2 v].  This is the
    operational shadow of the hb-model's [cap = 0] rendezvous edge ([hbe_send_recv] +
    [hbe_recv_send]); it needs no [RConfig] capacity field and leaves every other proof untouched. *)
Theorem rendezvous_via_buffer : forall p b h lv tr c v k1 k2 t0 t1,
  t0 <> t1 -> lv t0 = true -> lv t1 = true ->
  p t0 = CSend c v k1 -> p t1 = CRecv c k2 -> b c = [] -> closedb tr c = false ->
  exists cfg',
    rsteps (mkRCfg p b h lv tr) cfg'
    /\ rc_prog cfg' t0 = k1            (* sender continued *)
    /\ rc_prog cfg' t1 = k2 v          (* receiver got exactly the sent value [v] *)
    /\ rc_bufs cfg' c = [].            (* the value did NOT rest in the buffer — a true handoff *)
Proof.
  intros p b h lv tr c v k1 k2 t0 t1 Hne Hlv0 Hlv1 Hp0 Hp1 Hbc Hcl.
  eexists. split; [| split; [| split]].
  - (* the two-step rendezvous: t0 sends, then t1 immediately receives *)
    eapply rsteps_step; [ eapply rstep_send with (tid := t0); eassumption |].
    eapply rsteps_step; [| apply rsteps_refl].
    eapply rstep_recv with (tid := t1) (c := c) (f := k2) (v := v) (s := length tr) (brest := []).
    + exact Hlv1.
    + cbn. rewrite (upd_other _ _ _ _ (not_eq_sym Hne)). exact Hp1.
    + cbn. rewrite upd_same, Hbc. reflexivity.
  - cbn [rc_prog]. rewrite (upd_other _ _ _ _ Hne), upd_same. reflexivity.
  - cbn [rc_prog]. rewrite upd_same. reflexivity.
  - cbn [rc_bufs]. rewrite upd_same. reflexivity.
Qed.

(** ============================================================================
    STEP 1 KEYSTONE — the TERM-LEVEL bridge: a rich-calculus channel step
    SIMULATES [run_io] of the program's DENOTATION.

    [Cmd] is the DEEP embedding of an IO program.  [Denotes c m] is the deep↔shallow
    correspondence — built as a RELATION because [CRecv]'s continuation is a Coq
    function [nat -> Cmd], so a denotation FUNCTION cannot structurally recurse, but
    the relation pairs each [Cmd] with the [IO] term it stands for.  Then
    [denote_sim_send] / [denote_sim_recv] show that ONE [rstep] channel action
    run-reduces the [IO] denotation EXACTLY as the [run_io] laws specify, while the
    channel buffer stays matched ([WMatch1]).  This is the missing link: it ties the
    abstract [rstep] (where race-freedom is PROVEN) to the actual [run_io]/[World]
    model we EXTRACT from — grounded in the real IO laws [run_bind]/[run_send]/
    [run_recv]/[chan_buf_send]/[chan_buf_recv] (no NEW axioms; [Print Assumptions]
    below shows exactly that base).

    Value carrier = [GoI64] (the FULL-WIDTH Go int64, tag [TI64], [Z]-carried — NOT
    the bounded [Sint63] [int]); [recv] needs a [GoTypeTag] and [GoTypeTag nat] is
    provably EMPTY, so calculus [nat] values are coded into IO [GoI64] by [inj]/[prj].
    [Hret] (the round-trip [prj (inj n) = n]) is the faithful-coding condition.  HONEST SCOPE (break #1):
    the UNBOUNDED form [forall n : nat, prj (inj n) = n] is IMPOSSIBLE — an injection [nat ↪ GoI64] with a
    left inverse cannot exist ([GoI64] is FINITE).  It holds only over the REPRESENTABLE range; the concrete
    coding [keystone_inj]/[keystone_prj] below round-trips exactly when [Z.of_nat n < 2^63]
    ([keystone_roundtrip], machine-checked) — a value outside that range is not a real Go int64 anyway.  The
    section still carries the abstract unbounded [Hret] as a Hypothesis (so it is currently INSTANTIABLE only
    vacuously); re-founding the bridge on the bounded round-trip (threading a representability predicate
    through [OnChan]/[SimInv]/[denote_sim_*]/[denote_adequate] + the heap analogues) is the remaining work —
    see PROGRESS.md.  The realizable coding + its bounded round-trip are PROVED here as that foundation.

    SPAWN is deliberately ABSENT from this bridge: [go_spawn] has NO [run_io] law,
    because [run_io] is SEQUENTIAL and cannot express interleaving.  That is exactly
    why the calculus is the model for concurrency and why the race-freedom guarantee
    lives on [rstep], not on [run_io].
    ============================================================================ *)
(** The CONCRETE realizable coding [keystone_inj]/[keystone_prj] and its bounded round-trip
    [keystone_roundtrip] are defined in [builtins.v] (where [Z]/[i64wrap] live) — the break-#1 foundation. *)

Section Keystone.
  Variable chenv : nat -> GoChan GoI64.    (* calculus channel id -> the IO channel *)
  Variable locenv : nat -> Ref GoI64.      (* calculus location  -> the IO ref cell *)
  Variable inj : nat -> GoI64.             (* calculus value -> IO value (a coding) *)
  Variable prj : GoI64 -> nat.             (* IO value -> calculus value *)
  Variable Vrep : nat -> Prop.             (* "representable": a value the coding handles faithfully (fits int64) *)
  (* Break #1 fix: the round-trip is REALIZABLE — it holds only on REPRESENTABLE values, not all of [nat]
     (an unbounded [forall n, prj (inj n) = n] is impossible, [GoI64] finite).  Instantiate with
     [Vrep n := Z.of_nat n < 2^63], [inj := keystone_inj], [prj := keystone_prj], [Hret := keystone_roundtrip]. *)
  Hypothesis Hret  : forall n, Vrep n -> prj (inj n) = n.
  Hypothesis Vrep0 : Vrep 0.               (* the zero value is representable (the initial heap holds it) *)

  (* Deep<->shallow correspondence.  D_recv's premise is itself a [forall x],
     reflecting the HOAS continuation: the IO term [g] must agree with [denote] of
     the calculus continuation [f] at every received value. *)
  Inductive Denotes : Cmd -> IO unit -> Prop :=
    | D_ret   : Denotes CRet (ret tt)
    | D_send  : forall ch v k m, Denotes k m ->
        Denotes (CSend ch v k) (bind (send TI64 (chenv ch) (inj v)) (fun _ => m))
    | D_recv  : forall ch f g, (forall x, Denotes (f (prj x)) (g x)) ->
        Denotes (CRecv ch f) (bind (recv TI64 (chenv ch)) g)
    | D_write : forall l v k m, Denotes k m ->
        Denotes (CWrite l v k) (bind (ref_set (locenv l) (inj v)) (fun _ => m))
    | D_read  : forall l f g, (forall x, Denotes (f (prj x)) (g x)) ->
        Denotes (CRead l f) (bind (ref_get TI64 (locenv l)) g).

  (* World <-> config on one channel [c]: the IO buffer is the calculus buffer, coded.
     (Single channel keeps it frame-free — a send/recv touches only [c]'s buffer, and
     the IO channel laws relate exactly that buffer; multi-channel would need a
     channel-separation/frame law, tracked.) *)
  Definition WMatch1 (c : nat) (w : World) (cfg : RConfig) : Prop :=
    chan_buf TI64 (chenv c) w = map inj (rchan cfg c).

  (** A SEND step: the deep [CSend] run-reduces to its continuation at the world after
      [chan_send_upd], and the buffer match is preserved — mirroring [rstep_send]. *)
  Lemma denote_sim_send : forall p b h lv tr tid c v k m w,
    Denotes (CSend c v k) m ->
    WMatch1 c w (mkRCfg p b h lv tr) ->
    chan_closed (chenv c) w = false ->
    exists m',
      Denotes k m' /\
      run_io m w = run_io m' (chan_send_upd TI64 (chenv c) (inj v) w) /\
      WMatch1 c (chan_send_upd TI64 (chenv c) (inj v) w)
              (mkRCfg (upd p tid k) (upd b c (b c ++ [(v, length tr)])) h lv
                      (tr ++ [mkEv tid (KSend c)])).
  Proof.
    intros p b h lv tr tid c v k m w HD HM Hclosed.
    inversion HD as [| ch0 v0 k0 m' HDk Hch Hm | | | ]; subst.
    exists m'. split; [exact HDk | split].
    - rewrite run_bind, (run_send TI64 (chenv c) (inj v) w Hclosed). cbn. reflexivity.
    - unfold WMatch1, rchan in *. cbn [rc_bufs] in *. rewrite upd_same.
      rewrite (chan_buf_send TI64 (chenv c) (inj v) w), HM, !map_app. cbn. reflexivity.
  Qed.

  (** A RECV step: the deep [CRecv] run-reduces by BINDING the head value; [Hret]
      recovers the calculus value, so the continuation matches [f v] — mirroring
      [rstep_recv].  This is where the faithful coding is genuinely used. *)
  Lemma denote_sim_recv : forall p b h lv tr tid c f m w v s brest,
    Denotes (CRecv c f) m ->
    WMatch1 c w (mkRCfg p b h lv tr) ->
    b c = (v, s) :: brest ->
    Vrep v ->                                   (* the head value is representable — so it round-trips *)
    exists m',
      Denotes (f v) m' /\
      run_io m w = run_io m' (chan_recv_upd TI64 (chenv c) w) /\
      WMatch1 c (chan_recv_upd TI64 (chenv c) w)
              (mkRCfg (upd p tid (f v)) (upd b c brest) h lv (tr ++ [mkEv tid (KRecv c s)])).
  Proof.
    intros p b h lv tr tid c f m w v s brest HD HM Hbc Hv.
    inversion HD as [| | ch0 f0 g HDg Hch Hm | | ]; subst.
    assert (Hbuf : chan_buf TI64 (chenv c) w = inj v :: map inj (map fst brest)).
    { unfold WMatch1, rchan in HM. cbn [rc_bufs] in HM. rewrite Hbc in HM. cbn in HM. exact HM. }
    exists (g (inj v)). split; [| split].
    - specialize (HDg (inj v)). rewrite (Hret v Hv) in HDg. exact HDg.
    - rewrite run_bind, (run_recv TI64 (chenv c) (inj v) (map inj (map fst brest)) w Hbuf).
      cbn. reflexivity.
    - unfold WMatch1, rchan. cbn [rc_bufs]. rewrite upd_same.
      rewrite (chan_buf_recv TI64 (chenv c) (inj v) (map inj (map fst brest)) w Hbuf). reflexivity.
  Qed.

  (* World <-> config on one location [l]: the IO ref's value is the calculus heap
     value, coded.  Single location, frame-free, same as [WMatch1] for channels. *)
  Definition WHMatch1 (l : nat) (w : World) (cfg : RConfig) : Prop :=
    ref_sel (locenv l) w = inj (rc_heap cfg l).

  (** A WRITE step: the deep [CWrite] run-reduces to its continuation at the world
      after [ref_upd], the heap match holding by [ref_sel_upd_same] — mirroring
      [rstep_write].  (No precondition: a write overwrites unconditionally.) *)
  Lemma denote_sim_write : forall p b h lv tr tid l v k m w,
    Denotes (CWrite l v k) m ->
    exists m',
      Denotes k m' /\
      run_io m w = run_io m' (ref_upd (locenv l) (inj v) w) /\
      WHMatch1 l (ref_upd (locenv l) (inj v) w)
              (mkRCfg (upd p tid k) b (upd h l v) lv (tr ++ [mkEv tid (KWrite l)])).
  Proof.
    intros p b h lv tr tid l v k m w HD.
    inversion HD as [| | | l0 v0 k0 m' HDk Hl Hm | ]; subst.
    exists m'. split; [exact HDk | split].
    - rewrite run_bind, (run_ref_set (locenv l) (inj v) w). cbn. reflexivity.
    - unfold WHMatch1. cbn [rc_heap]. rewrite upd_same, ref_sel_upd_same. reflexivity.
  Qed.

  (** A READ step: the deep [CRead] run-reduces by BINDING the ref value (no world
      change); [Hret] recovers the calculus heap value so the continuation matches
      [f (h l)] — mirroring [rstep_read]. *)
  Lemma denote_sim_read : forall p b h lv tr tid l f m w,
    Denotes (CRead l f) m ->
    WHMatch1 l w (mkRCfg p b h lv tr) ->
    Vrep (h l) ->                               (* the heap value at [l] is representable — so it round-trips *)
    exists m',
      Denotes (f (h l)) m' /\
      run_io m w = run_io m' w /\
      WHMatch1 l w (mkRCfg (upd p tid (f (h l))) b h lv (tr ++ [mkEv tid (KRead l)])).
  Proof.
    intros p b h lv tr tid l f m w HD HM Hv.
    inversion HD as [| | | | l0 f0 g HDg Hl Hm]; subst.
    unfold WHMatch1 in HM. cbn [rc_heap] in HM.
    exists (g (inj (h l))). split; [| split].
    - specialize (HDg (inj (h l))). rewrite (Hret (h l) Hv) in HDg. exact HDg.
    - rewrite run_bind, (run_ref_get TI64 (locenv l) w). cbn. rewrite HM. reflexivity.
    - unfold WHMatch1. cbn [rc_heap]. exact HM.
  Qed.

  (** [CRet] is the terminal: its denotation just returns, no world change. *)
  Lemma denote_sim_ret : forall w, run_io (ret tt) w = ORet tt w.
  Proof. intro w. apply run_ret. Qed.

  (** ---- End-to-end composition: a WHOLE single-goroutine program ----
      The per-step lemmas chain into one adequacy theorem.  The frame-free fragment:
      a SINGLE channel [c], send/recv only (no memory, no spawn — those would need a
      cross-resource separation law / would leave [run_io]).  [OnChan] is the syntactic
      restriction; [SimInv] is the invariant carried along the execution. *)
  Inductive OnChan (c : nat) : Cmd -> Prop :=
    | OC_ret  : OnChan c CRet
    | OC_send : forall v k, Vrep v -> OnChan c k -> OnChan c (CSend c v k)   (* sent values are representable *)
    | OC_recv : forall f, (forall x, Vrep x -> OnChan c (f x)) -> OnChan c (CRecv c f).  (* recv'd value is representable *)

  Definition SimInv (c : nat) (m0 : IO unit) (w0 : World) (cfg : RConfig) : Prop :=
    OnChan c (rc_prog cfg 0)
    /\ (forall t, t <> 0 -> rc_prog cfg t = CRet)
    /\ rc_live cfg = (fun t => Nat.eqb t 0)
    /\ NoCloseTrace (rc_trace cfg)
    /\ Forall Vrep (rchan cfg c)          (* every buffered value is representable — so a recv round-trips *)
    /\ exists m w, Denotes (rc_prog cfg 0) m
                   /\ WMatch1 c w cfg
                   /\ chan_closed (chenv c) w = false
                   /\ run_io m0 w0 = run_io m w.

  (** One [rstep] preserves the simulation invariant.  Only goroutine 0 is live, so
      the step is its; by [OnChan] it is a send/recv on [c], handled by the matching
      per-step lemma; write/read/spawn cannot occur (not [OnChan]). *)
  Lemma siminv_step : forall c m0 w0 cfg cfg',
    rstep cfg cfg' -> SimInv c m0 w0 cfg -> SimInv c m0 w0 cfg'.
  Proof.
    intros c m0 w0 cfg cfg' Hstep
           [HOC [Hidle [Hlive [HNC [HVb [m [w [HD [HM [Hcl Hrun]]]]]]]]]].
    destruct Hstep as
      [ p b h lv tr tid c1 v k Hlv Hp _
      | p b h lv tr tid c1 f v s brest Hlv Hp Hbc
      | p b h lv tr tid l v k Hlv Hp
      | p b h lv tr tid l f Hlv Hp
      | p b h lv tr tid child k cid Hlv Hp Hcid
      | p b h lv tr tid cases c1 f v s brest Hlv Hp Hin Hbc
      | p b h lv tr tid c1 k Hlv Hp _
      | p b h lv tr tid c1 f pos e Hlv Hp Hbc Hpos Hek
      | p b h lv tr tid cases c1 f pos e Hlv Hp Hin Hbc Hpos Hek ];
    cbn [rc_prog rc_live] in HOC, Hidle, Hlive, HD;
    rewrite Hlive in Hlv; cbn in Hlv; apply Nat.eqb_eq in Hlv; subst tid; subst lv.
    - (* send *)
      rewrite Hp in HOC, HD. inversion HOC as [| v' k' HVv HOCk |]; subst c1.
      destruct (denote_sim_send _ _ _ _ _ 0 c v k m w HD HM Hcl)
        as [m' [HDk' [Hrun' HM']]].
      unfold SimInv; cbn [rc_prog rc_live]; rewrite upd_same.
      split; [exact HOCk | split; [| split; [| split; [| split]]]].
      + intros t Ht. rewrite (upd_other _ _ _ _ Ht). exact (Hidle t Ht).
      + reflexivity.
      + cbn [rc_trace] in HNC |- *. apply NoClose_app; [exact HNC | intros c'; discriminate].
      + (* buffer gains [v], which is representable (OC_send) *)
        unfold rchan in HVb |- *; cbn [rc_bufs] in HVb |- *. rewrite upd_same, map_app. cbn.
        apply Forall_app. split; [exact HVb | repeat constructor; exact HVv].
      + exists m', (chan_send_upd TI64 (chenv c) (inj v) w).
        split; [exact HDk' | split; [exact HM' | split]].
        * rewrite (chan_closed_send TI64 (chenv c) (inj v) w). exact Hcl.
        * rewrite Hrun. exact Hrun'.
    - (* recv *)
      rewrite Hp in HOC, HD. inversion HOC as [| | f' HOCf]; subst c1.
      (* the head value is representable, from the buffer-Forall invariant *)
      assert (Hv : Vrep v).
      { unfold rchan in HVb; cbn [rc_bufs] in HVb. rewrite Hbc in HVb. cbn in HVb.
        exact (Forall_inv HVb). }
      destruct (denote_sim_recv _ _ _ _ _ 0 c f m w v s brest HD HM Hbc Hv)
        as [m' [HDk' [Hrun' HM']]].
      unfold SimInv; cbn [rc_prog rc_live]; rewrite upd_same.
      split; [exact (HOCf v Hv) | split; [| split; [| split; [| split]]]].
      + intros t Ht. rewrite (upd_other _ _ _ _ Ht). exact (Hidle t Ht).
      + reflexivity.
      + cbn [rc_trace] in HNC |- *. apply NoClose_app; [exact HNC | intros c'; discriminate].
      + (* buffer loses its head; the tail is still all representable *)
        unfold rchan in HVb |- *; cbn [rc_bufs] in HVb |- *. rewrite upd_same.
        rewrite Hbc in HVb. cbn in HVb. exact (Forall_inv_tail HVb).
      + exists m', (chan_recv_upd TI64 (chenv c) w).
        split; [exact HDk' | split; [exact HM' | split]].
        * rewrite (chan_closed_recv TI64 (chenv c) w). exact Hcl.
        * rewrite Hrun. exact Hrun'.
    - (* write — impossible under OnChan *)
      rewrite Hp in HOC. inversion HOC.
    - (* read — impossible under OnChan *)
      rewrite Hp in HOC. inversion HOC.
    - (* spawn — impossible under OnChan *)
      rewrite Hp in HOC. inversion HOC.
    - (* select — impossible under OnChan (OnChan has no CSelect constructor) *)
      rewrite Hp in HOC. inversion HOC.
    - (* close — impossible under OnChan (OnChan has no CClose constructor) *)
      rewrite Hp in HOC. inversion HOC.
    - (* recv_closed — impossible: an OnChan program never closes, so the trace has no
         KClose for the closed-recv premise to point at (NoCloseTrace). *)
      cbn [rc_trace] in HNC. exfalso. exact (HNC pos e Hpos c1 Hek).
    - (* select_closed — impossible under OnChan (OnChan has no CSelect constructor) *)
      rewrite Hp in HOC. inversion HOC.
  Qed.

  Lemma siminv_steps : forall c m0 w0 cfg cfg',
    rsteps cfg cfg' -> SimInv c m0 w0 cfg -> SimInv c m0 w0 cfg'.
  Proof.
    intros c m0 w0 cfg cfg' H. induction H; intros HS; [exact HS|].
    apply IHrsteps. exact (siminv_step _ _ _ _ _ H HS).
  Qed.

  Lemma siminv_init : forall c prog0 m w0,
    OnChan c prog0 -> Denotes prog0 m ->
    chan_buf TI64 (chenv c) w0 = [] -> chan_closed (chenv c) w0 = false ->
    SimInv c m w0 (rinit_cfg (fun t => if Nat.eqb t 0 then prog0 else CRet)).
  Proof.
    intros c prog0 m w0 HOC HD Hbuf Hcl.
    unfold SimInv, rinit_cfg; cbn [rc_prog rc_live].
    split; [exact HOC | split; [| split; [| split; [| split]]]].
    - intros t Ht. destruct (Nat.eqb t 0) eqn:E;
        [apply Nat.eqb_eq in E; congruence | reflexivity].
    - reflexivity.
    - intros pos e Hpos c'. exfalso. apply nth_error_lt in Hpos. cbn in Hpos. lia.
    - unfold rchan; cbn [rc_bufs]. constructor.   (* initial buffer is empty ⇒ Forall vacuous *)
    - exists m, w0. split; [exact HD | split; [| split]].
      + unfold WMatch1, rchan; cbn [rc_bufs]. rewrite Hbuf. reflexivity.
      + exact Hcl.
      + reflexivity.
  Qed.

  (** THE END-TO-END THEOREM.  If the rich calculus runs a single-channel,
      single-goroutine program to completion ([CRet]), then [run_io] of its
      DENOTATION also completes — [ORet tt] — at a final world whose channel buffer
      MATCHES the calculus's.  So the calculus execution and the extracted program's
      [run_io] meaning AGREE on the whole run, not just per step. *)
  Theorem denote_adequate : forall c prog0 m w0 cfg_final,
    OnChan c prog0 -> Denotes prog0 m ->
    chan_buf TI64 (chenv c) w0 = [] -> chan_closed (chenv c) w0 = false ->
    rsteps (rinit_cfg (fun t => if Nat.eqb t 0 then prog0 else CRet)) cfg_final ->
    rc_prog cfg_final 0 = CRet ->
    exists w_final, run_io m w0 = ORet tt w_final /\ WMatch1 c w_final cfg_final.
  Proof.
    intros c prog0 m w0 cfg_final HOC HD Hbuf Hcl Hrsteps Hdone.
    pose proof (siminv_steps _ _ _ _ _ Hrsteps
                  (siminv_init _ _ _ _ HOC HD Hbuf Hcl)) as HS.
    destruct HS as [_ [_ [_ [_ [_ [m' [w' [HD' [HM' [_ Hrun']]]]]]]]]].
    rewrite Hdone in HD'. inversion HD'; subst.
    exists w'. split; [rewrite Hrun'; apply run_ret | exact HM'].
  Qed.

  (** ── The MEMORY analogue of [denote_adequate]: single-goroutine adequacy for a HEAP program. ──
      [OnChan]/[denote_adequate] above cover send/recv on a channel; this covers WRITE/READ on a
      single location [l], reusing the per-step [denote_sim_write]/[denote_sim_read].  It is the heap
      half of the eventual combined (channel + memory) multi-goroutine adequacy (limit #2 slice 2c);
      stated single-goroutine, single-location here.  [OnLoc] is the syntactic restriction
      (write/read on [l] only); the World heap cell at [l] stays matched to the calculus heap. *)
  Inductive OnLoc (l : nat) : Cmd -> Prop :=
    | OL_ret   : OnLoc l CRet
    | OL_write : forall v k, Vrep v -> OnLoc l k -> OnLoc l (CWrite l v k)   (* written values are representable *)
    | OL_read  : forall f, (forall x, Vrep x -> OnLoc l (f x)) -> OnLoc l (CRead l f).  (* read value is representable *)

  Definition SimInvMem (l : nat) (m0 : IO unit) (w0 : World) (cfg : RConfig) : Prop :=
    OnLoc l (rc_prog cfg 0)
    /\ (forall t, t <> 0 -> rc_prog cfg t = CRet)
    /\ rc_live cfg = (fun t => Nat.eqb t 0)
    /\ Vrep (rc_heap cfg l)               (* the heap value at [l] is representable — so a read round-trips *)
    /\ exists m w, Denotes (rc_prog cfg 0) m
                   /\ WHMatch1 l w cfg
                   /\ run_io m0 w0 = run_io m w.

  Lemma siminvmem_step : forall l m0 w0 cfg cfg',
    rstep cfg cfg' -> SimInvMem l m0 w0 cfg -> SimInvMem l m0 w0 cfg'.
  Proof.
    intros l m0 w0 cfg cfg' Hstep
           [HOL [Hidle [Hlive [HVh [m [w [HD [HM Hrun]]]]]]]].
    destruct Hstep as
      [ p b h lv tr tid c1 v k Hlv Hp _
      | p b h lv tr tid c1 f v s brest Hlv Hp Hbc
      | p b h lv tr tid l1 v k Hlv Hp
      | p b h lv tr tid l1 f Hlv Hp
      | p b h lv tr tid child k cid Hlv Hp Hcid
      | p b h lv tr tid cases c1 f v s brest Hlv Hp Hin Hbc
      | p b h lv tr tid c1 k Hlv Hp _
      | p b h lv tr tid c1 f pos e Hlv Hp Hbc Hpos Hek
      | p b h lv tr tid cases c1 f pos e Hlv Hp Hin Hbc Hpos Hek ];
    cbn [rc_prog rc_live rc_heap] in HOL, Hidle, Hlive, HVh, HD;
    rewrite Hlive in Hlv; cbn in Hlv; apply Nat.eqb_eq in Hlv; subst tid.
    - (* send — impossible under OnLoc *) rewrite Hp in HOL. inversion HOL.
    - (* recv — impossible *) rewrite Hp in HOL. inversion HOL.
    - (* write *)
      rewrite Hp in HOL, HD. inversion HOL as [| v' k' HVv HOLk |]; subst l1.
      destruct (denote_sim_write p b h lv tr 0 l v k m w HD) as [m' [HDk' [Hrun' HM']]].
      unfold SimInvMem; cbn [rc_prog rc_live]; rewrite upd_same.
      split; [exact HOLk | split; [| split; [| split]]].
      + intros t Ht. rewrite (upd_other _ _ _ _ Ht). exact (Hidle t Ht).
      + exact Hlive.
      + cbn [rc_heap]. rewrite upd_same. exact HVv.   (* heap value at [l] is now [v], representable *)
      + exists m', (ref_upd (locenv l) (inj v) w).
        split; [exact HDk' | split; [exact HM' | rewrite Hrun; exact Hrun']].
    - (* read *)
      rewrite Hp in HOL, HD. inversion HOL as [| | f' HOLf]; subst l1.
      destruct (denote_sim_read p b h lv tr 0 l f m w HD HM HVh) as [m' [HDk' [Hrun' HM']]].
      unfold SimInvMem; cbn [rc_prog rc_live]; rewrite upd_same.
      split; [exact (HOLf (h l) HVh) | split; [| split; [| split]]].
      + intros t Ht. rewrite (upd_other _ _ _ _ Ht). exact (Hidle t Ht).
      + exact Hlive.
      + cbn [rc_heap]. exact HVh.                      (* heap unchanged by a read *)
      + exists m', w. split; [exact HDk' | split; [exact HM' | rewrite Hrun; exact Hrun']].
    - (* spawn — impossible *) rewrite Hp in HOL. inversion HOL.
    - (* select — impossible *) rewrite Hp in HOL. inversion HOL.
    - (* close — impossible *) rewrite Hp in HOL. inversion HOL.
    - (* recv_closed — impossible *) rewrite Hp in HOL. inversion HOL.
    - (* select_closed — impossible *) rewrite Hp in HOL. inversion HOL.
  Qed.

  Lemma siminvmem_steps : forall l m0 w0 cfg cfg',
    rsteps cfg cfg' -> SimInvMem l m0 w0 cfg -> SimInvMem l m0 w0 cfg'.
  Proof.
    intros l m0 w0 cfg cfg' H. induction H; intros HS; [exact HS|].
    apply IHrsteps. exact (siminvmem_step _ _ _ _ _ H HS).
  Qed.

  Lemma siminvmem_init : forall l prog0 m w0,
    OnLoc l prog0 -> Denotes prog0 m ->
    WHMatch1 l w0 (rinit_cfg (fun t => if Nat.eqb t 0 then prog0 else CRet)) ->
    SimInvMem l m w0 (rinit_cfg (fun t => if Nat.eqb t 0 then prog0 else CRet)).
  Proof.
    intros l prog0 m w0 HOL HD HM.
    unfold SimInvMem, rinit_cfg; cbn [rc_prog rc_live].
    split; [exact HOL | split; [| split; [| split]]].
    - intros t Ht. destruct (Nat.eqb t 0) eqn:E;
        [apply Nat.eqb_eq in E; congruence | reflexivity].
    - reflexivity.
    - cbn [rc_heap]. exact Vrep0.   (* initial heap holds 0, representable *)
    - exists m, w0. split; [exact HD | split; [exact HM | reflexivity]].
  Qed.

  (** Memory END-TO-END: a single-goroutine WRITE/READ program run to [CRet] — its [run_io]
      denotation completes ([ORet tt]) at a world whose cell [l] MATCHES the calculus heap. *)
  Theorem denote_adequate_mem : forall l prog0 m w0 cfg_final,
    OnLoc l prog0 -> Denotes prog0 m ->
    WHMatch1 l w0 (rinit_cfg (fun t => if Nat.eqb t 0 then prog0 else CRet)) ->
    rsteps (rinit_cfg (fun t => if Nat.eqb t 0 then prog0 else CRet)) cfg_final ->
    rc_prog cfg_final 0 = CRet ->
    exists w_final, run_io m w0 = ORet tt w_final /\ WHMatch1 l w_final cfg_final.
  Proof.
    intros l prog0 m w0 cfg_final HOL HD HM Hrsteps Hdone.
    pose proof (siminvmem_steps _ _ _ _ _ Hrsteps
                  (siminvmem_init _ _ _ _ HOL HD HM)) as HS.
    destruct HS as [_ [_ [_ [_ [m' [w' [HD' [HM' Hrun']]]]]]]].
    rewrite Hdone in HD'. inversion HD'; subst.
    exists w'. split; [rewrite Hrun'; apply run_ret | exact HM'].
  Qed.

End Keystone.

(** ════════════════════════════════════════════════════════════════════════════
    LIMIT #2, slice 1 — TYPED POINTERS ARE THE OPERATIONAL CALCULUS'S LOCATIONS.

    The Keystone refines the operational calculus to the [run_io] World, but its memory
    cells are abstract [Ref]s reached through a [locenv], and the race/deadlock theory
    ([mp_trace], [Owned], [TraceRaceFree]) reasons over UNTYPED [nat] locations.  This
    section closes the typed-location half of limit #2 for POINTERS: the operational
    memory steps [rstep_write]/[rstep_read] are simulated by the EXTRACTABLE Go-pointer
    derefs [ptr_set]/[ptr_get] — exactly what the plugin emits as [*p = v] / [*p].  So a
    calculus location [l] is not an abstract [nat] but a genuine, runnable *T cell: the
    pointer [ptrenv l].

    The deref ops are DEFINITIONALLY the Keystone's ref-accesses at [ptr_as_ref]
    ([ptr_set_is_ref]/[ptr_get_is_ref]), so the bridge inherits read-after-write +
    aliasing with no new heap and no new axiom.  SCOPE (honest): this is the per-cell
    memory bridge — it identifies the calculus location with the extractable *T.  The
    multi-goroutine execution that GENERATES [mp_trace] from a typed pointer-handoff
    program — tying [mp_trace_race_free] to the typed *T end-to-end — is slice 2 (it
    needs a multi-goroutine [Denotes]); deliberately NOT claimed here. *)
Section KeystonePtr.
  Variable ptrenv : nat -> Ptr GoI64.   (* calculus location -> the extractable Go pointer *)
  Variable inj : nat -> GoI64.          (* calculus value    -> coded IO value *)

  (* a calculus location, viewed as the Keystone ref of its pointer's cell *)
  Definition plocenv (l : nat) : Ref GoI64 := ptr_as_ref TI64 (ptrenv l).

  (* The bridge's pointers are LIVE (non-nil): a calculus location maps to an ALLOCATED *T cell, whose
     handle is nonzero (break #5: [valid_fresh_nonzero] — allocators never return location 0).  This is
     the standing modeling assumption that lets the raw [ptr_set]/[ptr_get] (which now PANIC on nil,
     break #6) coincide with the bridge ref-accesses. *)
  Hypothesis ptrenv_live : forall l, PrimInt63.eqb (p_loc (ptrenv l)) 0%uint63 = false.

  (* EXTRACTABLE deref = bridge ref-access: on a live pointer the *T ops the plugin emits ARE the ref
     accesses the Keystone reasons about — so a calculus location is a real (non-nil) Go pointer. *)
  Lemma ptr_set_is_ref : forall l v, ptr_set TI64 (ptrenv l) v = ref_set (plocenv l) v.
  Proof.
    intros l v. apply run_io_inj. intro w.
    rewrite run_ptr_set, run_ref_set, ptrenv_live. reflexivity.
  Qed.
  Lemma ptr_get_is_ref : forall l, ptr_get TI64 (ptrenv l) = ref_get TI64 (plocenv l).
  Proof.
    intros l. apply run_io_inj. intro w.
    rewrite run_ptr_get, run_ref_get, ptrenv_live. reflexivity.
  Qed.

  (* one-cell heap match: the IO world value at [ptrenv l] codes the calculus heap value. *)
  Definition PHMatch (l : nat) (w : World) (h : nat -> nat) : Prop :=
    ref_sel (plocenv l) w = inj (h l).

  (** WRITE through the EXTRACTABLE pointer simulates [rstep_write]: the IO world advances by
      [ref_upd] exactly as the operational heap advances by [upd h l v], and the one-cell match
      is preserved (post value [inj v], mirroring [upd h l v l = v]).  Mirrors [denote_sim_write]
      but over the genuine *T deref [ptr_set]. *)
  Lemma ptr_write_sim : forall l v h w,
    run_io (ptr_set TI64 (ptrenv l) (inj v)) w = ORet tt (ref_upd (plocenv l) (inj v) w)
    /\ PHMatch l (ref_upd (plocenv l) (inj v) w) (upd h l v).
  Proof.
    intros l v h w. split.
    - rewrite ptr_set_is_ref, run_ref_set. reflexivity.
    - unfold PHMatch. rewrite upd_same, ref_sel_upd_same. reflexivity.
  Qed.

  (** READ through the EXTRACTABLE pointer simulates [rstep_read]: no world change, and the value
      read is the coded calculus heap value [inj (h l)] (recovered via the cell match), so the
      continuation sees [h l] — mirroring [denote_sim_read]/[rstep_read]. *)
  Lemma ptr_read_sim : forall l h w,
    PHMatch l w h ->
    run_io (ptr_get TI64 (ptrenv l)) w = ORet (inj (h l)) w.
  Proof.
    intros l h w HM. rewrite ptr_get_is_ref, run_ref_get.
    unfold PHMatch in HM. rewrite HM. reflexivity.
  Qed.

  (** Read-after-write through the EXTRACTABLE pointer — the typed cell is coherent: [*p = v]
      then [*p] yields [v].  Inherited from [ref_sel_upd_same]; the typed-pointer analogue of the
      heap law the bridge stands on, now over the op the plugin actually emits. *)
  Lemma ptr_write_read : forall l v w,
    run_io (ptr_get TI64 (ptrenv l)) (ref_upd (plocenv l) v w)
      = ORet v (ref_upd (plocenv l) v w).
  Proof.
    intros l v w. rewrite ptr_get_is_ref, run_ref_get, ref_sel_upd_same. reflexivity.
  Qed.
End KeystonePtr.

(** PAYOFF (honest, prose — NOT a fabricated theorem).  Combine this section with the operational
    race theory.  [mp_trace] (write loc 0 → send ⤳ recv → read loc 0) is [TraceRaceFree]
    ([mp_trace_race_free]); its conflicting cross-goroutine pair — the write at pos 0 and the read
    at pos 3 of location 0 — is happens-before ordered through the channel handoff ([mp_trace_hb_0_3]),
    hence not a [TraceRace].  By [KeystonePtr], that location 0 is a genuine EXTRACTABLE pointer
    [ptrenv 0] (an *int64), and its write/read ARE [ptr_set]/[ptr_get] on it ([ptr_write_sim] /
    [ptr_read_sim]).  So the operational race guarantee is now known to concern a real *T cell, not an
    abstract [nat].  EXECUTION direction — slice 2a (below, [mp_exec_trace]) now GROUNDS [mp_trace] in
    a real run; what remains (slice 2b) is the TYPED tie: a multi-goroutine [Denotes] proving a typed
    pointer-handoff IO program denotes that very execution — only then is the typed program's
    race-freedom a single closed theorem rather than an identification.  Stated, not overstated. *)

(** ── LIMIT #2, slice 2a — [mp_trace] is GENERATED by a real execution (not hand-built). ──
    Slice 1 identified [mp_trace]'s shared location with the extractable pointer [ptrenv 0], but
    [mp_trace] was a HAND-WRITTEN trace — we asserted its events.  Here the SAME trace is PRODUCED BY
    RUNNING a two-goroutine pointer-handoff program: g0 writes loc 0 then sends ch 0; g1 recvs ch 0
    then reads loc 0.  Executing the canonical interleaving (write, send, recv, read) yields EXACTLY
    [mp_trace] — the send records its own trace position 1 in the buffer, so g1's recv emits [KRecv 0 1]
    — so its race-freedom ([mp_trace_race_free]) is no longer about a literal but about a REACHABLE
    state of an actual program ([mp_exec_race_free]).  This is the operational analogue of
    [fork_exec_trace], now for the message-passing/handoff shape the typed pointer bridge targets.  Both
    goroutines are pre-live (no spawn — [mp_trace] records none; the with-spawn variant is
    [fork_exec_trace]). *)
Definition mp_prog (v0 v1 : nat) : nat -> Cmd :=
  fun t => if Nat.eqb t 0 then CWrite 0 v0 (CSend 0 v1 CRet)
           else if Nat.eqb t 1 then CRecv 0 (fun _ => CRead 0 (fun _ => CRet))
           else CRet.
Definition mp_init (v0 v1 : nat) : RConfig :=
  mkRCfg (mp_prog v0 v1) (fun _ => []) (fun _ => 0)
         (fun t => orb (Nat.eqb t 0) (Nat.eqb t 1)) [].

Theorem mp_exec_trace : forall v0 v1,
  exists cfg, rsteps (mp_init v0 v1) cfg /\ rc_trace cfg = mp_trace.
Proof.
  intros v0 v1. unfold mp_init, mp_prog. eexists. split.
  - eapply rsteps_step.
    { eapply rstep_write with (tid := 0); upd_proj; reflexivity. }
    eapply rsteps_step.
    { eapply rstep_send  with (tid := 0); upd_proj; reflexivity. }
    eapply rsteps_step.
    { eapply rstep_recv  with (tid := 1); upd_proj; reflexivity. }
    eapply rsteps_step.
    { eapply rstep_read  with (tid := 1); upd_proj; reflexivity. }
    apply rsteps_refl.
  - cbn. reflexivity.
Qed.

(** Hence the handoff program's EXECUTION is race-free: the trace it generates is [mp_trace], whose
    only conflicting cross-goroutine pair (the write/read of loc 0 — the extractable [ptrenv 0] by
    slice 1) is ordered by the channel handoff.  Race-freedom is now a property of a RUN, not a
    hand-built literal. *)
Theorem mp_exec_race_free : forall v0 v1,
  exists cfg, rsteps (mp_init v0 v1) cfg /\ TraceRaceFree (rc_trace cfg).
Proof.
  intros v0 v1. destruct (mp_exec_trace v0 v1) as [cfg [Hsteps Htr]].
  exists cfg. split; [exact Hsteps |]. rewrite Htr. exact mp_trace_race_free.
Qed.

(** The handoff's OUTCOME, operationally: after the full run, the cell g0 wrote (loc 0) still holds
    [v0] — the value SURVIVED the channel handoff and was the one g1 read — and the channel has
    DRAINED (buffer empty).  This is the operational mirror of the typed [mp_handoff_delivers] (which
    delivers [inj v0] through the pointer + drains the channel): BOTH models compute the SAME handoff
    outcome [v0]/[inj v0], a concrete cross-model agreement.  (The general N-goroutine ADEQUACY — a
    PROVEN simulation between the interleaved execution and the typed [run_io], generalising the
    single-goroutine [denote_adequate]/[SimInv] — stays the deferred capstone; it is a multi-tick
    refactor, not asserted here.) *)
Theorem mp_exec_state : forall v0 v1,
  exists cfg, rsteps (mp_init v0 v1) cfg
    /\ rc_trace cfg = mp_trace
    /\ rc_heap cfg 0 = v0        (* g0's written value survived the handoff (g1 read it) *)
    /\ rc_bufs cfg 0 = [].       (* the channel drained *)
Proof.
  intros v0 v1. unfold mp_init, mp_prog. eexists. split; [| split; [| split]].
  - eapply rsteps_step. { eapply rstep_write with (tid := 0); upd_proj; reflexivity. }
    eapply rsteps_step. { eapply rstep_send  with (tid := 0); upd_proj; reflexivity. }
    eapply rsteps_step. { eapply rstep_recv  with (tid := 1); upd_proj; reflexivity. }
    eapply rsteps_step. { eapply rstep_read  with (tid := 1); upd_proj; reflexivity. }
    apply rsteps_refl.
  - cbn. reflexivity.
  - cbn [rc_heap]. upd_proj. reflexivity.
  - cbn [rc_bufs]. upd_proj. reflexivity.
Qed.

(** ── LIMIT #2, slice 2-A — EVERY interleaving of the typed pointer handoff is race-free (Keller-style). ──
    [mp_exec_race_free] showed ONE execution race-free; the goal is ALL of them.  Following Keller 1976's
    inductive-invariant method ("Formal Verification of Parallel Programs"): the channel SERIALIZES
    [mp_prog] — g1's recv waits for g0's send, which follows g0's write — so every reachable state falls
    into one of FIVE phases whose traces are prefixes of [mp_trace].  [MpReach] is that STRENGTHENED
    reachability invariant: the buffer/prog facts (Keller's semaphore-W analogue) pin the phase, which
    the bare "trace is a prefix" could not (it would not be inductive).  This brick = the invariant + its
    BASE case ([mpreach_init]) + the SAFETY direction ([mpreach_race_free]: pre-handoff phases A–D have
    ≤1 memory access — only g0 has written — race-free by [le1_mem_access_race_free]; phase E = [mp_trace],
    race-free by [mp_trace_race_free]).  The rstep-PRESERVATION (the keystone closing the all-interleavings
    theorem) is the next brick. *)
Definition MpReach (v0 v1 : nat) (cfg : RConfig) : Prop :=
  rc_live cfg = (fun t => orb (Nat.eqb t 0) (Nat.eqb t 1))
  /\ ( (rc_trace cfg = [] /\ rc_prog cfg 0 = CWrite 0 v0 (CSend 0 v1 CRet)
        /\ rc_prog cfg 1 = CRecv 0 (fun _ => CRead 0 (fun _ => CRet)) /\ rc_bufs cfg 0 = [])
    \/ (rc_trace cfg = [mkEv 0 (KWrite 0)] /\ rc_prog cfg 0 = CSend 0 v1 CRet
        /\ rc_prog cfg 1 = CRecv 0 (fun _ => CRead 0 (fun _ => CRet)) /\ rc_bufs cfg 0 = [])
    \/ (rc_trace cfg = [mkEv 0 (KWrite 0); mkEv 0 (KSend 0)] /\ rc_prog cfg 0 = CRet
        /\ rc_prog cfg 1 = CRecv 0 (fun _ => CRead 0 (fun _ => CRet)) /\ rc_bufs cfg 0 = [(v1, 1)])
    \/ (rc_trace cfg = [mkEv 0 (KWrite 0); mkEv 0 (KSend 0); mkEv 1 (KRecv 0 1)]
        /\ rc_prog cfg 0 = CRet /\ rc_prog cfg 1 = CRead 0 (fun _ => CRet) /\ rc_bufs cfg 0 = [])
    \/ (rc_trace cfg = mp_trace /\ rc_prog cfg 0 = CRet /\ rc_prog cfg 1 = CRet /\ rc_bufs cfg 0 = []) ).

Lemma mpreach_init : forall v0 v1, MpReach v0 v1 (mp_init v0 v1).
Proof.
  intros v0 v1. unfold MpReach, mp_init, mp_prog. cbn.
  split; [reflexivity | left; repeat split; reflexivity].
Qed.

(** Refinement of [le1_mem_access_race_free]: if every memory access sits at position 0, the trace is
    race-free (a race needs two distinct-goroutine accesses; both would be at 0, same goroutine). *)
Lemma mem_access_only0_race_free : forall t,
  (forall i ai, tr_acc t i = Some ai -> i = 0) -> TraceRaceFree t.
Proof.
  intros t H. apply le1_mem_access_race_free. intros i j Hi Hj.
  destruct (tr_acc t i) as [ai|] eqn:Ei; [| exfalso; apply Hi; reflexivity].
  destruct (tr_acc t j) as [aj|] eqn:Ej; [| exfalso; apply Hj; reflexivity].
  apply H in Ei; apply H in Ej; subst; reflexivity.
Qed.

Lemma mpreach_race_free : forall v0 v1 cfg, MpReach v0 v1 cfg -> TraceRaceFree (rc_trace cfg).
Proof.
  intros v0 v1 cfg [_ Hph].
  (* phases A–D: only g0's write (position 0) is a memory access — [tr_acc_lt] bounds the index, so the
     finitely-many in-range positions are checked and the out-of-range ones are killed by [lia]. *)
  destruct Hph as [[Htr _]|[[Htr _]|[[Htr _]|[[Htr _]|[Htr _]]]]]; rewrite Htr;
    try (apply mem_access_only0_race_free; intros i ai Hi;
         pose proof (tr_acc_lt _ _ _ Hi) as L; destruct i as [|[|[|i]]]; cbn in Hi;
         first [reflexivity | discriminate Hi | (cbn in L; lia)]).
  exact mp_trace_race_free.   (* phase E = mp_trace: ordered write/read *)
Qed.

(** The KEYSTONE: [MpReach] is rstep-PRESERVED.  In each phase the channel/prog state forces the UNIQUE
    next step; every other rstep constructor contradicts a phase fact — head mismatch or empty/nonempty
    buffer (both closed by [congruence] against [Hp0]/[Hp1]/[Hb0]), or a closed-recv/select whose
    [KClose] back-pointer can't exist in mp's KClose-free trace ([nth_error]+[e_kind] discharge).  The
    live set = mp_live bounds the stepping goroutine to {0,1}. *)
Lemma mpreach_step : forall v0 v1 cfg cfg',
  rstep cfg cfg' -> MpReach v0 v1 cfg -> MpReach v0 v1 cfg'.
Proof.
  intros v0 v1 cfg cfg' Hstep [Hlive Hph].
  destruct Hph as [HX|[HX|[HX|[HX|HX]]]]; destruct HX as [Htr [Hp0 [Hp1 Hb0]]];
    destruct Hstep as
      [ p b h lv tr tid c v k Hlv Hp _
      | p b h lv tr tid c f v s brest Hlv Hp Hbc
      | p b h lv tr tid l v k Hlv Hp
      | p b h lv tr tid l f Hlv Hp
      | p b h lv tr tid child k cid Hlv Hp Hcid
      | p b h lv tr tid cases c f v s brest Hlv Hp Hin Hbc
      | p b h lv tr tid c k Hlv Hp _
      | p b h lv tr tid c f pos e Hlv Hp Hbc Hpos Hek
      | p b h lv tr tid cases c f pos e Hlv Hp Hin Hbc Hpos Hek ];
    cbn [rc_live rc_trace rc_prog rc_bufs] in Hlive, Htr, Hp0, Hp1, Hb0;
    rewrite Hlive in Hlv; cbn in Hlv; apply Bool.orb_true_iff in Hlv;
    destruct Hlv as [Hlv|Hlv]; apply Nat.eqb_eq in Hlv; subst tid;
    try (rewrite Hp0 in Hp); try (rewrite Hp1 in Hp);
    try (exfalso; congruence);
    try (exfalso; rewrite Htr in Hpos; destruct pos as [|[|[|pos]]]; cbn in Hpos;
         first [ discriminate Hpos | (injection Hpos as <-; cbn in Hek; discriminate Hek) ]).
  (* The four surviving goals are the unique real steps A→B, B→C, C→D, D→E (phase E has none). *)
  - (* A→B : g0 write *)
    injection Hp as Hl _ Hk; subst l; subst k.
    split; [cbn [rc_live]; exact Hlive |].
    right; left. rewrite Htr. cbn [rc_trace rc_prog rc_bufs]. upd_proj.
    repeat split; first [reflexivity | assumption | (symmetry; assumption)].
  - (* B→C : g0 send *)
    injection Hp as Hc Hv Hk; subst c; subst v; subst k.
    split; [cbn [rc_live]; exact Hlive |].
    right; right; left. rewrite Htr, Hb0. cbn [rc_trace rc_prog rc_bufs]. upd_proj.
    repeat split; first [reflexivity | assumption | (symmetry; assumption)].
  - (* C→D : g1 recv *)
    injection Hp as Hc Hf; subst c.
    rewrite Hb0 in Hbc; injection Hbc as Hv Hs Hbrest; subst v; subst s; subst brest; subst f.
    split; [cbn [rc_live]; exact Hlive |].
    right; right; right; left. rewrite Htr. cbn [rc_trace rc_prog rc_bufs]. upd_proj.
    repeat split; first [reflexivity | assumption | (symmetry; assumption)].
  - (* D→E : g1 read *)
    injection Hp as Hl Hf; subst l; subst f.
    split; [cbn [rc_live]; exact Hlive |].
    right; right; right; right. rewrite Htr. cbn [rc_trace rc_prog rc_bufs]. upd_proj.
    repeat split; first [reflexivity | assumption | (symmetry; assumption)].
Qed.

Lemma mpreach_steps : forall v0 v1 cfg cfg',
  rsteps cfg cfg' -> MpReach v0 v1 cfg -> MpReach v0 v1 cfg'.
Proof.
  intros v0 v1 cfg cfg' H. induction H; intros HM; [exact HM|].
  apply IHrsteps. exact (mpreach_step _ _ _ _ H HM).
Qed.

(** THE ALL-INTERLEAVINGS THEOREM (slice 2-A closed): EVERY reachable state of the typed pointer
    handoff has a race-free trace — not just the one canonical execution [mp_exec_race_free] witnessed.
    The channel's serialization makes [MpReach] an inductive invariant ([mpreach_init] ∘
    [mpreach_steps]) implying [TraceRaceFree] ([mpreach_race_free]).  Race-freedom over ALL schedules. *)
Theorem mp_all_interleavings_race_free : forall v0 v1 cfg,
  rsteps (mp_init v0 v1) cfg -> TraceRaceFree (rc_trace cfg).
Proof.
  intros v0 v1 cfg Hsteps.
  apply (mpreach_race_free v0 v1).
  exact (mpreach_steps _ _ _ _ Hsteps (mpreach_init v0 v1)).
Qed.

(** ── Connecting slice 2-A to the GENERAL ownership framework (a step toward slice 2-B). ──
    [mpreach_race_free] took the ad-hoc ≤1-mem-access route; here mp's reachable traces are shown
    [Owned] (Keller/CSL's discipline: same-location accesses form an hb-chain), so race-freedom ALSO
    flows through the general [owned_race_free].  [mp_reachable_owned] is a concrete instance of the
    slice-2B theorem SHAPE — "a disciplined program's reachable traces are Owned" — for the handoff. *)
Lemma acc_loc_mp : forall i l, acc_loc_at mp_trace i = Some l -> i = 0 \/ i = 3.
Proof.
  intros i l H. pose proof (acc_loc_at_lt _ _ _ H) as L.
  destruct i as [|[|[|[|i]]]]; cbn in H;
    first [ discriminate H | (left; reflexivity) | (right; reflexivity) | (cbn in L; lia) ].
Qed.

Lemma owned_mp_trace : Owned mp_trace.
Proof.
  intros i j Hij [l [Hi Hj]].
  apply acc_loc_mp in Hi; apply acc_loc_mp in Hj.
  destruct Hi as [->| ->]; destruct Hj as [->| ->]; try lia.
  left. exact mp_trace_hb_0_3.
Qed.

Lemma acc_only0_owned : forall t,
  (forall i l, acc_loc_at t i = Some l -> i = 0) -> Owned t.
Proof.
  intros t H i j Hij [l [Hi Hj]]. apply H in Hi; apply H in Hj; subst. lia.
Qed.

Lemma mpreach_owned : forall v0 v1 cfg, MpReach v0 v1 cfg -> Owned (rc_trace cfg).
Proof.
  intros v0 v1 cfg [_ Hph].
  destruct Hph as [[Htr _]|[[Htr _]|[[Htr _]|[[Htr _]|[Htr _]]]]]; rewrite Htr;
    try (apply acc_only0_owned; intros i l Hi;
         pose proof (acc_loc_at_lt _ _ _ Hi) as L; destruct i as [|[|[|i]]]; cbn in Hi;
         first [ reflexivity | discriminate Hi | (cbn in L; lia) ]).
  exact owned_mp_trace.
Qed.

(** mp's reachable traces are Owned — the slice-2B theorem SHAPE for the concrete handoff (a disciplined
    program's reachable traces satisfy the ownership discipline); race-freedom now flows the GENERAL way. *)
Theorem mp_reachable_owned : forall v0 v1 cfg,
  rsteps (mp_init v0 v1) cfg -> Owned (rc_trace cfg).
Proof.
  intros v0 v1 cfg Hsteps.
  apply (mpreach_owned v0 v1).
  exact (mpreach_steps _ _ _ _ Hsteps (mpreach_init v0 v1)).
Qed.

(** ── LIMIT #2, slice 2b — mp_prog's goroutines DENOTE a TYPED pointer-handoff IO program. ──
    Slice 2a grounded [mp_trace] in a real OPERATIONAL run ([mp_prog], nat-valued [Cmd]).  Here each
    goroutine of THAT program is shown to be the Keystone-DENOTATION of an EXTRACTABLE typed
    pointer-handoff IO program — g0 = [*p = v0; ch <- v1], g1 = [<-ch; _ := *p] — where the memory ops
    are the genuine *T derefs [ptr_set]/[ptr_get] the plugin emits ([Denotes]'s [ref_set]/[ref_get]
    are DEFINITIONALLY those, via the pointer-backed [locenv := plocenv ptrenv] of slice 1).  So the
    race-free execution of slice 2a is the operational image of real typed pointer-over-channel code.
    REMAINING (slice 2c): a MULTI-goroutine ADEQUACY composing these per-goroutine denotations with the
    INTERLEAVED [rstep] execution + the World refinement (the single-goroutine [denote_adequate]
    generalised to N) — the one closed end-to-end theorem.  Stated per-goroutine here, not overstated. *)
Lemma mp_prog_goroutines : forall v0 v1,
  mp_prog v0 v1 0 = CWrite 0 v0 (CSend 0 v1 CRet)
  /\ mp_prog v0 v1 1 = CRecv 0 (fun _ => CRead 0 (fun _ => CRet)).
Proof. intros v0 v1. split; reflexivity. Qed.

Section MpTyped.
  Variable chenv : nat -> GoChan GoI64.
  Variable ptrenv : nat -> Ptr GoI64.
  Variable inj : nat -> GoI64.
  Variable prj : GoI64 -> nat.
  (* the handoff pointer is LIVE (non-nil) — an allocated *T cell, nonzero by break #5; lets the raw
     [ptr_set]/[ptr_get] (which now PANIC on nil, break #6) coincide with the bridge ref-accesses. *)
  Hypothesis ptrenv_live : forall l, PrimInt63.eqb (p_loc (ptrenv l)) 0%uint63 = false.

  (* g0 = [*p = v0; ch <- v1] ; g1 = [<-ch; _ := *p] — built from the EXTRACTABLE ptr/chan ops. *)
  Definition mp_g0_io (v0 v1 : nat) : IO unit :=
    bind (ptr_set TI64 (ptrenv 0) (inj v0))
         (fun _ => bind (send TI64 (chenv 0) (inj v1)) (fun _ => ret tt)).
  Definition mp_g1_io : IO unit :=
    bind (recv TI64 (chenv 0))
         (fun _ => bind (ptr_get TI64 (ptrenv 0)) (fun _ => ret tt)).

  (* Each goroutine of mp_prog is the Keystone-denotation of its typed program, the memory ops being
     the genuine *T derefs (pointer-backed locenv = [plocenv ptrenv], slice 1). *)
  Lemma mp_g0_denotes : forall v0 v1,
    Denotes chenv (plocenv ptrenv) inj prj (CWrite 0 v0 (CSend 0 v1 CRet)) (mp_g0_io v0 v1).
  Proof.
    intros v0 v1. unfold mp_g0_io.
    rewrite (ptr_set_is_ref ptrenv ptrenv_live 0 (inj v0)).
    apply D_write. apply D_send. apply D_ret.
  Qed.

  Lemma mp_g1_denotes :
    Denotes chenv (plocenv ptrenv) inj prj (CRecv 0 (fun _ => CRead 0 (fun _ => CRet))) mp_g1_io.
  Proof.
    unfold mp_g1_io. rewrite (ptr_get_is_ref ptrenv ptrenv_live 0).
    apply D_recv. intro x. apply D_read. intro y. apply D_ret.
  Qed.

  (** VALUE CORRECTNESS (companion to 2a's race-freedom): the EXTRACTABLE typed pointer-handoff
      program, run in [run_io] from a world where channel 0 is empty + open, DELIVERS exactly what
      g1 should observe — it RECEIVES [inj v1] over the channel AND reads back [inj v0] through the
      pointer.  The pointee written by g0 survives the [send]+[recv] (channel and heap are separate
      World components — the [ref_sel_chan_{send,recv}_upd] frames), so [*p] reads [inj v0]; the
      channel delivers [inj v1].  So the typed program is not only race-free (2a) but COMPUTES the
      right values end-to-end — the [*T]-over-channel handoff is faithful. *)
  Definition mp_handoff_io (v0 v1 : nat) : IO (GoI64 * GoI64) :=
    bind (ptr_set TI64 (ptrenv 0) (inj v0)) (fun _ =>
    bind (send TI64 (chenv 0) (inj v1)) (fun _ =>
    bind (recv TI64 (chenv 0)) (fun rcvd =>
    bind (ptr_get TI64 (ptrenv 0)) (fun pv => ret (rcvd, pv))))).

  Lemma mp_handoff_delivers : forall v0 v1 w0,
    chan_buf TI64 (chenv 0) w0 = [] ->
    chan_closed (chenv 0) w0 = false ->
    exists w', run_io (mp_handoff_io v0 v1) w0 = ORet (inj v1, inj v0) w'.
  Proof.
    intros v0 v1 w0 Hbuf Hcl. unfold mp_handoff_io.
    rewrite run_bind, run_ptr_set, ptrenv_live; cbv beta iota.
    rewrite run_bind, run_send by exact Hcl; cbv beta iota.
    rewrite run_bind, (run_recv TI64 (chenv 0) (inj v1) (@nil GoI64))
      by (rewrite chan_buf_send, chan_buf_ref_upd_frame, Hbuf; reflexivity); cbv beta iota.
    rewrite run_bind, run_ptr_get, ptrenv_live; cbv beta iota.
    rewrite run_ret, ref_sel_chan_recv_upd, ref_sel_chan_send_upd, ref_sel_upd_same.
    eexists. reflexivity.
  Qed.
End MpTyped.

(** Trust-base audit (verified via [Print Assumptions], 2026-06-15): each step lemma
    rests on EXACTLY the [run_io] law for its operation, and nothing degenerate:
      - [denote_sim_send]  : [run_bind], [run_send],     [chan_buf_send]
      - [denote_sim_recv]  : [run_bind], [run_recv],     [chan_buf_recv]
      - [denote_sim_write] : [run_bind], [run_ref_set],  [ref_sel_upd_same]
      - [denote_sim_read]  : [run_bind], [run_ref_get]
    (+ the carrier/IO types).  [Hret] is a DISCHARGED HYPOTHESIS, not an axiom.  So the
    bridge rests precisely on the [run_io] channel AND heap laws it connects to — the
    honest statement that the rich calculus (where race-freedom is proven) refines the
    [run_io]/[World] model we extract from, for the sequential channel + memory
    fragment.  (Spawn stays out: [go_spawn] has no [run_io] law — see the section
    header.)

    The WHOLE-PROGRAM theorem [denote_adequate] composes the per-step lemmas: for a
    single-channel, single-goroutine program, running it in the calculus to [CRet]
    means [run_io] of its denotation ALSO completes ([ORet tt]) at a world whose
    channel buffer matches — so calculus execution and [run_io] meaning AGREE on the
    whole run.  Its trust base ([Print Assumptions]) adds only [run_ret] and the
    [chan_closed_send]/[chan_closed_recv] frame laws (used to keep the channel open
    along the run) to the per-step bases — still nothing degenerate. *)

(** ============================================================================
    MULTI-GOROUTINE STATE REFINEMENT — the frame law at work.

    [run_io] is SEQUENTIAL: it cannot sequence several goroutines, so there is no
    whole-program [run_io] meaning of a CONCURRENT program (that is the calculus's
    job).  The honest multi-goroutine connection is therefore a STATE refinement: the
    calculus's full channel state stays matched to the [run_io] [World] model under
    ARBITRARY interleaving.  [WMatchC] is the MULTI-channel match (no single-channel
    restriction); [wmatchc_step] shows EVERY [rstep] — by ANY goroutine, on ANY
    channel — preserves it, the CHANNEL SEPARATION (frame) law handling the untouched
    channels.  Crucially this needs NO [Denotes]/[prj]/[Hret]: write/read/spawn do not
    touch buffers (so the world is unchanged there), leaving only send/recv, whose
    buffer evolution is the [chan_buf_send]/[chan_buf_recv] laws + the frame law.

    So [reachable_refines]: every reachable state of a MULTI-goroutine, MULTI-channel
    execution is realized by a [run_io] world — the calculus's state refines the model
    Fido extracts from, across all interleavings.  Combined with the already-proven
    race-freedom on the calculus ([reachable_owned_safe_r]), the guarantee now applies
    to genuinely concurrent programs at the state level.
    ============================================================================ *)
Section KeystoneMulti.
  Variable chenv : nat -> GoChan GoI64.
  Variable inj : nat -> GoI64.
  Hypothesis chenv_inj : forall i j, chenv i = chenv j -> i = j.

  Definition WMatchC (w : World) (cfg : RConfig) : Prop :=
    forall c, chan_buf TI64 (chenv c) w = map inj (rchan cfg c).

  Lemma chenv_neq : forall i j, i <> j -> chenv i <> chenv j.
  Proof. intros i j Hij Heq. apply Hij, chenv_inj, Heq. Qed.

  (** Every [rstep] — any goroutine, any channel — preserves the multi-channel match.
      The frame law keeps the untouched channels matched, so this holds for ARBITRARY
      multi-goroutine interleaving (where race-freedom actually bites). *)
  Lemma wmatchc_step : forall cfg cfg' w,
    rstep cfg cfg' -> WMatchC w cfg -> exists w', WMatchC w' cfg'.
  Proof.
    intros cfg cfg' w Hstep HM.
    destruct Hstep as
      [ p b h lv tr tid c0 v k Hlv Hp _
      | p b h lv tr tid c0 f v s brest Hlv Hp Hbc
      | p b h lv tr tid l v k Hlv Hp
      | p b h lv tr tid l f Hlv Hp
      | p b h lv tr tid child k cid Hlv Hp Hcid
      | p b h lv tr tid cases c0 f v s brest Hlv Hp Hin Hbc
      | p b h lv tr tid c0 k Hlv Hp _
      | p b h lv tr tid c0 f pos e Hlv Hp Hbc Hpos Hek
      | p b h lv tr tid cases c0 f pos e Hlv Hp Hin Hbc Hpos Hek ].
    - (* send: world advances by [chan_send_upd] on channel [c0] *)
      exists (chan_send_upd TI64 (chenv c0) (inj v) w).
      intros c. specialize (HM c). unfold WMatchC, rchan in *; cbn [rc_bufs] in *.
      destruct (Nat.eq_dec c c0) as [->|Hne].
      + rewrite upd_same, chan_buf_send, HM, !map_app. cbn. reflexivity.
      + rewrite (upd_other _ _ _ _ Hne),
          (chan_buf_send_frame TI64 (chenv c0) (chenv c) (inj v) w
             (chenv_neq c0 c (not_eq_sym Hne))).
        exact HM.
    - (* recv: world advances by [chan_recv_upd] on channel [c0] *)
      exists (chan_recv_upd TI64 (chenv c0) w).
      assert (Hbuf : chan_buf TI64 (chenv c0) w = inj v :: map inj (map fst brest)).
      { generalize (HM c0). unfold rchan; cbn [rc_bufs]. rewrite Hbc. cbn. tauto. }
      intros c. specialize (HM c). unfold WMatchC, rchan in *; cbn [rc_bufs] in *.
      destruct (Nat.eq_dec c c0) as [->|Hne].
      + rewrite upd_same,
          (chan_buf_recv TI64 (chenv c0) (inj v) (map inj (map fst brest)) w Hbuf).
        reflexivity.
      + rewrite (upd_other _ _ _ _ Hne),
          (chan_buf_recv_frame TI64 (chenv c0) (chenv c) w
             (chenv_neq c0 c (not_eq_sym Hne))).
        exact HM.
    - (* write: buffers unchanged, so the same world still matches *)
      exists w. intros c. specialize (HM c). unfold WMatchC, rchan in *;
        cbn [rc_bufs] in *. exact HM.
    - (* read: buffers unchanged *)
      exists w. intros c. specialize (HM c). unfold WMatchC, rchan in *;
        cbn [rc_bufs] in *. exact HM.
    - (* spawn: buffers unchanged *)
      exists w. intros c. specialize (HM c). unfold WMatchC, rchan in *;
        cbn [rc_bufs] in *. exact HM.
    - (* select: receives on the chosen channel [c0] — identical world-refinement to recv *)
      exists (chan_recv_upd TI64 (chenv c0) w).
      assert (Hbuf : chan_buf TI64 (chenv c0) w = inj v :: map inj (map fst brest)).
      { generalize (HM c0). unfold rchan; cbn [rc_bufs]. rewrite Hbc. cbn. tauto. }
      intros c. specialize (HM c). unfold WMatchC, rchan in *; cbn [rc_bufs] in *.
      destruct (Nat.eq_dec c c0) as [->|Hne].
      + rewrite upd_same,
          (chan_buf_recv TI64 (chenv c0) (inj v) (map inj (map fst brest)) w Hbuf).
        reflexivity.
      + rewrite (upd_other _ _ _ _ Hne),
          (chan_buf_recv_frame TI64 (chenv c0) (chenv c) w
             (chenv_neq c0 c (not_eq_sym Hne))).
        exact HM.
    - (* close: buffers unchanged, so the same world still matches *)
      exists w. intros c. specialize (HM c). unfold WMatchC, rchan in *;
        cbn [rc_bufs] in *. exact HM.
    - (* recv_closed: buffers unchanged (closed recv binds zero, consumes nothing) *)
      exists w. intros c. specialize (HM c). unfold WMatchC, rchan in *;
        cbn [rc_bufs] in *. exact HM.
    - (* select_closed: buffers unchanged *)
      exists w. intros c. specialize (HM c). unfold WMatchC, rchan in *;
        cbn [rc_bufs] in *. exact HM.
  Qed.

  Lemma wmatchc_steps : forall cfg cfg' w,
    rsteps cfg cfg' -> WMatchC w cfg -> exists w', WMatchC w' cfg'.
  Proof.
    intros cfg cfg' w H. revert w. induction H; intros w HM; [exists w; exact HM|].
    destruct (wmatchc_step _ _ _ H HM) as [w' HM']. exact (IHrsteps w' HM').
  Qed.

  Lemma wmatchc_init : forall p w0,
    (forall c, chan_buf TI64 (chenv c) w0 = []) -> WMatchC w0 (rinit_cfg p).
  Proof.
    intros p w0 Hempty c. unfold WMatchC, rchan, rinit_cfg; cbn [rc_bufs].
    rewrite Hempty. reflexivity.
  Qed.

  (** THE MULTI-GOROUTINE REFINEMENT.  Every reachable state of a concurrent,
      multi-channel execution is realized by some [run_io] world matching all its
      channel buffers — across every interleaving. *)
  Theorem reachable_refines : forall p cfg w0,
    (forall c, chan_buf TI64 (chenv c) w0 = []) ->
    rsteps (rinit_cfg p) cfg ->
    exists w, WMatchC w cfg.
  Proof.
    intros p cfg w0 Hempty Hsteps.
    exact (wmatchc_steps _ _ _ Hsteps (wmatchc_init p w0 Hempty)).
  Qed.

  (** Capstone: a reachable concurrent state is BOTH realized by a [run_io] world AND
      (under the ownership discipline) race-free with a strict-partial-order
      happens-before.  The state refinement (this section) and the race-freedom
      (proven on the calculus) hold of the SAME reachable execution. *)
  Theorem reachable_refines_and_safe : forall p cfg w0,
    (forall c, chan_buf TI64 (chenv c) w0 = []) ->
    rsteps (rinit_cfg p) cfg ->
    Owned (rc_trace cfg) ->
    (exists w, WMatchC w cfg) /\
    TraceRaceFree (rc_trace cfg) /\
    (forall i, ~ hbt (rc_trace cfg) i i).
  Proof.
    intros p cfg w0 Hempty Hsteps HO.
    split; [exact (reachable_refines p cfg w0 Hempty Hsteps) |].
    exact (reachable_owned_safe_r p cfg Hsteps HO).
  Qed.

End KeystoneMulti.

(** ============================================================================
    MULTI-GOROUTINE STATE REFINEMENT — the HEAP analogue (ref separation).

    [WMatchC] (above) refined the calculus's CHANNEL state to [run_io].  Races are about
    MEMORY, so here is the parallel for the HEAP: [WHMatchC] matches every location's
    [run_io] ref value to the operational [rc_heap]; [whmatchc_step] shows EVERY [rstep]
    preserves it, the ref SEPARATION (frame) law [ref_sel_upd_diff] handling the untouched
    locations.  Only [rstep_write] advances the heap world (by [ref_upd]); every other step
    leaves [rc_heap] unchanged, so the same world still matches.  [reachable_refines_heap]:
    every reachable state's MEMORY is realized by a [run_io] world, across all interleavings —
    and [reachable_refines_heap_and_safe] bundles that with the proven race-freedom, so the
    guarantee now covers the memory state that races are actually about.
    ============================================================================ *)
Section KeystoneHeap.
  Variable locenv : nat -> Ref GoI64.
  Variable inj : nat -> GoI64.
  (* Distinct calculus locations sit at distinct World ref CELLS — the heap analogue of
     [chenv_inj].  (Loc-level, not Ref-level: [ref_sel_upd_diff]'s frame is keyed on [r_loc].) *)
  Hypothesis locenv_loc_inj : forall i j, r_loc (locenv i) = r_loc (locenv j) -> i = j.

  Definition WHMatchC (w : World) (cfg : RConfig) : Prop :=
    forall l, ref_sel (locenv l) w = inj (rc_heap cfg l).

  Lemma locenv_loc_neq : forall i j, i <> j -> r_loc (locenv i) <> r_loc (locenv j).
  Proof. intros i j Hij Heq. apply Hij, locenv_loc_inj, Heq. Qed.

  (** Every [rstep] — any goroutine, any location — preserves the multi-location heap match. *)
  Lemma whmatchc_step : forall cfg cfg' w,
    rstep cfg cfg' -> WHMatchC w cfg -> exists w', WHMatchC w' cfg'.
  Proof.
    intros cfg cfg' w Hstep HM.
    destruct Hstep as
      [ p b h lv tr tid c0 v k Hlv Hp _
      | p b h lv tr tid c0 f v s brest Hlv Hp Hbc
      | p b h lv tr tid l v k Hlv Hp
      | p b h lv tr tid l f Hlv Hp
      | p b h lv tr tid child k cid Hlv Hp Hcid
      | p b h lv tr tid cases c0 f v s brest Hlv Hp Hin Hbc
      | p b h lv tr tid c0 k Hlv Hp _
      | p b h lv tr tid c0 f pos e Hlv Hp Hbc Hpos Hek
      | p b h lv tr tid cases c0 f pos e Hlv Hp Hin Hbc Hpos Hek ].
    - (* send: heap untouched, so the same world still matches *)
      exists w. intros l0. specialize (HM l0). unfold WHMatchC in *; cbn [rc_heap] in *. exact HM.
    - (* recv: heap untouched *)
      exists w. intros l0. specialize (HM l0). unfold WHMatchC in *; cbn [rc_heap] in *. exact HM.
    - (* write: world advances by [ref_upd] at location [l] *)
      exists (ref_upd (locenv l) (inj v) w).
      intros l0. specialize (HM l0). unfold WHMatchC in *; cbn [rc_heap] in *.
      destruct (Nat.eq_dec l0 l) as [->|Hne].
      + rewrite upd_same, ref_sel_upd_same. reflexivity.
      + rewrite (upd_other _ _ _ _ Hne),
          (ref_sel_upd_diff (locenv l) (locenv l0) (inj v) w (locenv_loc_neq l l0 (not_eq_sym Hne))).
        exact HM.
    - (* read: heap untouched (a read binds a value, does not write) *)
      exists w. intros l0. specialize (HM l0). unfold WHMatchC in *; cbn [rc_heap] in *. exact HM.
    - (* spawn: heap untouched *)
      exists w. intros l0. specialize (HM l0). unfold WHMatchC in *; cbn [rc_heap] in *. exact HM.
    - (* select: receives on a channel, heap untouched *)
      exists w. intros l0. specialize (HM l0). unfold WHMatchC in *; cbn [rc_heap] in *. exact HM.
    - (* close: heap untouched *)
      exists w. intros l0. specialize (HM l0). unfold WHMatchC in *; cbn [rc_heap] in *. exact HM.
    - (* recv_closed: heap untouched *)
      exists w. intros l0. specialize (HM l0). unfold WHMatchC in *; cbn [rc_heap] in *. exact HM.
    - (* select_closed: heap untouched *)
      exists w. intros l0. specialize (HM l0). unfold WHMatchC in *; cbn [rc_heap] in *. exact HM.
  Qed.

  Lemma whmatchc_steps : forall cfg cfg' w,
    rsteps cfg cfg' -> WHMatchC w cfg -> exists w', WHMatchC w' cfg'.
  Proof.
    intros cfg cfg' w H. revert w. induction H; intros w HM; [exists w; exact HM|].
    destruct (whmatchc_step _ _ _ H HM) as [w' HM']. exact (IHrsteps w' HM').
  Qed.

  Lemma whmatchc_init : forall p w0,
    (forall l, ref_sel (locenv l) w0 = inj 0) -> WHMatchC w0 (rinit_cfg p).
  Proof.
    intros p w0 Hzero l. unfold WHMatchC, rinit_cfg; cbn [rc_heap]. exact (Hzero l).
  Qed.

  (** THE MULTI-GOROUTINE HEAP REFINEMENT.  Every reachable state of a concurrent execution
      has its MEMORY realized by some [run_io] world — across every interleaving. *)
  Theorem reachable_refines_heap : forall p cfg w0,
    (forall l, ref_sel (locenv l) w0 = inj 0) ->
    rsteps (rinit_cfg p) cfg ->
    exists w, WHMatchC w cfg.
  Proof.
    intros p cfg w0 Hzero Hsteps.
    exact (whmatchc_steps _ _ _ Hsteps (whmatchc_init p w0 Hzero)).
  Qed.

  (** Capstone (memory): a reachable concurrent state has its HEAP realized by a [run_io]
      world AND (under the ownership discipline) is race-free with a strict-partial-order
      happens-before — the memory-state refinement and the race-freedom on the SAME execution. *)
  Theorem reachable_refines_heap_and_safe : forall p cfg w0,
    (forall l, ref_sel (locenv l) w0 = inj 0) ->
    rsteps (rinit_cfg p) cfg ->
    Owned (rc_trace cfg) ->
    (exists w, WHMatchC w cfg) /\
    TraceRaceFree (rc_trace cfg) /\
    (forall i, ~ hbt (rc_trace cfg) i i).
  Proof.
    intros p cfg w0 Hzero Hsteps HO.
    split; [exact (reachable_refines_heap p cfg w0 Hzero Hsteps) |].
    exact (reachable_owned_safe_r p cfg Hsteps HO).
  Qed.

End KeystoneHeap.

(** ============================================================================
    COMBINED STATE REFINEMENT — channels AND heap in ONE world.

    [reachable_refines] / [reachable_refines_heap] each match a [run_io] world to ONE component.
    The honest "the [World] IS the whole state" statement uses a SINGLE world matching BOTH: every
    [rstep] advances at most one component ([chan_*_upd] for a channel op, [ref_upd] for a write),
    and the [World]'s ref- and channel-heaps are INDEPENDENT ([ref_sel_chan_*_upd] /
    [chan_buf_ref_upd_frame] in builtins.v), so the untouched component stays matched in the SAME
    advanced world.  [reachable_refines_state]: every reachable state of a concurrent program — its
    channels AND its memory — is realized by ONE [run_io] world, across all interleavings.
    ============================================================================ *)
Section KeystoneState.
  Variable chenv : nat -> GoChan GoI64.
  Variable locenv : nat -> Ref GoI64.
  Variable inj : nat -> GoI64.
  Hypothesis chenv_inj : forall i j, chenv i = chenv j -> i = j.
  Hypothesis locenv_loc_inj : forall i j, r_loc (locenv i) = r_loc (locenv j) -> i = j.

  Lemma kst_chenv_neq : forall i j, i <> j -> chenv i <> chenv j.
  Proof. intros i j Hij Heq. apply Hij, chenv_inj, Heq. Qed.
  Lemma kst_locenv_neq : forall i j, i <> j -> r_loc (locenv i) <> r_loc (locenv j).
  Proof. intros i j Hij Heq. apply Hij, locenv_loc_inj, Heq. Qed.

  Definition WState (w : World) (cfg : RConfig) : Prop :=
    WMatchC chenv inj w cfg /\ WHMatchC locenv inj w cfg.

  Lemma wstate_step : forall cfg cfg' w,
    rstep cfg cfg' -> WState w cfg -> exists w', WState w' cfg'.
  Proof.
    intros cfg cfg' w Hstep [HMc HMh].
    unfold WMatchC, rchan in HMc. unfold WHMatchC in HMh.
    destruct Hstep as
      [ p b h lv tr tid c0 v k Hlv Hp _
      | p b h lv tr tid c0 f v s brest Hlv Hp Hbc
      | p b h lv tr tid l v k Hlv Hp
      | p b h lv tr tid l f Hlv Hp
      | p b h lv tr tid child k cid Hlv Hp Hcid
      | p b h lv tr tid cases c0 f v s brest Hlv Hp Hin Hbc
      | p b h lv tr tid c0 k Hlv Hp _
      | p b h lv tr tid c0 f pos e Hlv Hp Hbc Hpos Hek
      | p b h lv tr tid cases c0 f pos e Hlv Hp Hin Hbc Hpos Hek ].
    - (* send: channel world advances; heap untouched and refs framed through chan_send_upd *)
      exists (chan_send_upd TI64 (chenv c0) (inj v) w). split.
      + unfold WMatchC, rchan; cbn [rc_bufs]; intros c. destruct (Nat.eq_dec c c0) as [->|Hne].
        * rewrite upd_same, chan_buf_send, (HMc c0), !map_app. cbn. reflexivity.
        * rewrite (upd_other _ _ _ _ Hne),
            (chan_buf_send_frame TI64 (chenv c0) (chenv c) (inj v) w (kst_chenv_neq c0 c (not_eq_sym Hne))).
          exact (HMc c).
      + unfold WHMatchC; cbn [rc_heap]; intros l. rewrite ref_sel_chan_send_upd. exact (HMh l).
    - (* recv: channel world advances; heap framed through chan_recv_upd *)
      assert (Hbuf : chan_buf TI64 (chenv c0) w = inj v :: map inj (map fst brest))
        by (rewrite (HMc c0); cbn [rc_bufs]; rewrite Hbc; reflexivity).
      exists (chan_recv_upd TI64 (chenv c0) w). split.
      + unfold WMatchC, rchan; cbn [rc_bufs]; intros c. destruct (Nat.eq_dec c c0) as [->|Hne].
        * rewrite upd_same, (chan_buf_recv TI64 (chenv c0) (inj v) (map inj (map fst brest)) w Hbuf).
          reflexivity.
        * rewrite (upd_other _ _ _ _ Hne),
            (chan_buf_recv_frame TI64 (chenv c0) (chenv c) w (kst_chenv_neq c0 c (not_eq_sym Hne))).
          exact (HMc c).
      + unfold WHMatchC; cbn [rc_heap]; intros l. rewrite ref_sel_chan_recv_upd. exact (HMh l).
    - (* write: heap world advances; channels untouched and bufs framed through ref_upd *)
      exists (ref_upd (locenv l) (inj v) w). split.
      + unfold WMatchC, rchan; cbn [rc_bufs]; intros c. rewrite chan_buf_ref_upd_frame. exact (HMc c).
      + unfold WHMatchC; cbn [rc_heap]; intros l0. destruct (Nat.eq_dec l0 l) as [->|Hne].
        * rewrite upd_same, ref_sel_upd_same. reflexivity.
        * rewrite (upd_other _ _ _ _ Hne),
            (ref_sel_upd_diff (locenv l) (locenv l0) (inj v) w (kst_locenv_neq l l0 (not_eq_sym Hne))).
          exact (HMh l0).
    - (* read: world unchanged *)
      exists w. split; [unfold WMatchC, rchan; cbn [rc_bufs]; exact HMc
                       | unfold WHMatchC; cbn [rc_heap]; exact HMh].
    - (* spawn: world unchanged *)
      exists w. split; [unfold WMatchC, rchan; cbn [rc_bufs]; exact HMc
                       | unfold WHMatchC; cbn [rc_heap]; exact HMh].
    - (* select: channel world advances (recv on chosen channel); heap framed *)
      assert (Hbuf : chan_buf TI64 (chenv c0) w = inj v :: map inj (map fst brest))
        by (rewrite (HMc c0); cbn [rc_bufs]; rewrite Hbc; reflexivity).
      exists (chan_recv_upd TI64 (chenv c0) w). split.
      + unfold WMatchC, rchan; cbn [rc_bufs]; intros c. destruct (Nat.eq_dec c c0) as [->|Hne].
        * rewrite upd_same, (chan_buf_recv TI64 (chenv c0) (inj v) (map inj (map fst brest)) w Hbuf).
          reflexivity.
        * rewrite (upd_other _ _ _ _ Hne),
            (chan_buf_recv_frame TI64 (chenv c0) (chenv c) w (kst_chenv_neq c0 c (not_eq_sym Hne))).
          exact (HMc c).
      + unfold WHMatchC; cbn [rc_heap]; intros l. rewrite ref_sel_chan_recv_upd. exact (HMh l).
    - (* close: world unchanged (buffers and heap untouched) *)
      exists w. split; [unfold WMatchC, rchan; cbn [rc_bufs]; exact HMc
                       | unfold WHMatchC; cbn [rc_heap]; exact HMh].
    - (* recv_closed: world unchanged *)
      exists w. split; [unfold WMatchC, rchan; cbn [rc_bufs]; exact HMc
                       | unfold WHMatchC; cbn [rc_heap]; exact HMh].
    - (* select_closed: world unchanged *)
      exists w. split; [unfold WMatchC, rchan; cbn [rc_bufs]; exact HMc
                       | unfold WHMatchC; cbn [rc_heap]; exact HMh].
  Qed.

  Lemma wstate_steps : forall cfg cfg' w,
    rsteps cfg cfg' -> WState w cfg -> exists w', WState w' cfg'.
  Proof.
    intros cfg cfg' w H. revert w. induction H; intros w HM; [exists w; exact HM|].
    destruct (wstate_step _ _ _ H HM) as [w' HM']. exact (IHrsteps w' HM').
  Qed.

  Lemma wstate_init : forall p w0,
    (forall c, chan_buf TI64 (chenv c) w0 = []) ->
    (forall l, ref_sel (locenv l) w0 = inj 0) ->
    WState w0 (rinit_cfg p).
  Proof.
    intros p w0 Hempty Hzero. split.
    - intros c. unfold rchan, rinit_cfg; cbn [rc_bufs]. rewrite Hempty. reflexivity.
    - intros l. unfold rinit_cfg; cbn [rc_heap]. exact (Hzero l).
  Qed.

  (** THE COMBINED REFINEMENT.  Every reachable state of a concurrent program — its channels AND its
      memory — is realized by ONE [run_io] world, across every interleaving. *)
  Theorem reachable_refines_state : forall p cfg w0,
    (forall c, chan_buf TI64 (chenv c) w0 = []) ->
    (forall l, ref_sel (locenv l) w0 = inj 0) ->
    rsteps (rinit_cfg p) cfg ->
    exists w, WMatchC chenv inj w cfg /\ WHMatchC locenv inj w cfg.
  Proof.
    intros p cfg w0 Hempty Hzero Hsteps.
    exact (wstate_steps _ _ _ Hsteps (wstate_init p w0 Hempty Hzero)).
  Qed.

  (** Capstone: that single world realizes the FULL reachable state AND (under ownership) the
      execution is race-free with a strict-partial-order happens-before. *)
  Theorem reachable_refines_state_and_safe : forall p cfg w0,
    (forall c, chan_buf TI64 (chenv c) w0 = []) ->
    (forall l, ref_sel (locenv l) w0 = inj 0) ->
    rsteps (rinit_cfg p) cfg ->
    Owned (rc_trace cfg) ->
    (exists w, WMatchC chenv inj w cfg /\ WHMatchC locenv inj w cfg) /\
    TraceRaceFree (rc_trace cfg) /\
    (forall i, ~ hbt (rc_trace cfg) i i).
  Proof.
    intros p cfg w0 Hempty Hzero Hsteps HO.
    split; [exact (reachable_refines_state p cfg w0 Hempty Hzero Hsteps) |].
    exact (reachable_owned_safe_r p cfg Hsteps HO).
  Qed.

End KeystoneState.

(** ============================================================================
    DEADLOCK FREEDOM (progress) for the RICH calculus.

    The operational semantics REPRESENTS deadlock; here we (a) characterize EXACTLY
    what a deadlock is in this model, and (b) prove a genuine deadlock-FREEDOM theorem
    for a real class of programs.

    Enabledness in this model: [CSend]/[CWrite]/[CRead] are always enabled; [CSpawn]
    is enabled given a fresh goroutine id (true for reachable configs — finitely many
    are live); [CRecv c] is enabled IFF channel [c]'s buffer is non-empty; [CRet] is
    not enabled (that goroutine is finished).  So the ONLY way to block is a receive on
    an empty channel — and a deadlock is: someone is unfinished, yet every live
    goroutine is finished or blocked on such a receive ("all waiting to receive, no one
    sending").  [rstuck_blocked] proves exactly that characterization.
    ============================================================================ *)

Definition rcan_step (cfg : RConfig) : Prop := exists cfg', rstep cfg cfg'.
Definition rdone (cfg : RConfig) : Prop :=
  forall tid, rc_live cfg tid = true -> rc_prog cfg tid = CRet.
Definition RStuck (cfg : RConfig) : Prop := ~ rcan_step cfg /\ ~ rdone cfg.

(* Decidable select-readiness: scan the cases, return the FIRST ready one (channel non-empty)
   as [Some (c, f, v, s)], or [None] if EVERY case's channel is empty (the select blocks). *)
Fixpoint sel_first_ready (b : nat -> list (nat * nat))
                         (cases : list (nat * (nat -> Cmd)))
                         : option (nat * (nat -> Cmd) * nat * nat) :=
  match cases with
  | [] => None
  | (c, f) :: rest =>
      match b c with
      | (v, s) :: _ => Some (c, f, v, s)
      | [] => sel_first_ready b rest
      end
  end.

(* [Some] result is a genuine ready case: [(c,f)] is in [cases] and [c]'s buffer heads with [(v,s)]. *)
Lemma sel_first_ready_sound : forall b cases c f v s,
  sel_first_ready b cases = Some (c, f, v, s) ->
  In (c, f) cases /\ exists rest, b c = (v, s) :: rest.
Proof.
  induction cases as [|[c0 f0] rest IH]; intros c f v s H; cbn in H; [discriminate|].
  destruct (b c0) as [|[v0 s0] brest] eqn:Hb0.
  - destruct (IH _ _ _ _ H) as [Hin Hex]. split; [right; exact Hin | exact Hex].
  - injection H as -> -> -> ->. split; [left; reflexivity | exists brest; exact Hb0].
Qed.

(* CLOSED-AWARE select readiness: a case [(c,f)] is ready if [c]'s buffer is non-empty ([SR_buf],
   fires [rstep_select]) OR [c] is closed and drained ([SR_closed], fires [rstep_select_closed]).
   [None] iff EVERY case is empty-AND-open — the only genuinely blocking select. *)
Inductive SelReady : Type :=
  | SR_buf    (c : nat) (f : nat -> Cmd) (v s : nat)
  | SR_closed (c : nat) (f : nat -> Cmd).

Fixpoint sel_ready_cl (b : nat -> list (nat * nat)) (tr : Trace)
                      (cases : list (nat * (nat -> Cmd))) : option SelReady :=
  match cases with
  | [] => None
  | (c, f) :: rest =>
      match b c with
      | (v, s) :: _ => Some (SR_buf c f v s)
      | [] => if closedb tr c then Some (SR_closed c f) else sel_ready_cl b tr rest
      end
  end.

Lemma sel_ready_cl_buf : forall b tr cases c f v s,
  sel_ready_cl b tr cases = Some (SR_buf c f v s) ->
  In (c, f) cases /\ exists rest, b c = (v, s) :: rest.
Proof.
  induction cases as [|[c0 f0] rest IH]; intros c f v s H; cbn in H; [discriminate|].
  destruct (b c0) as [|[v0 s0] brest] eqn:Hb0.
  - destruct (closedb tr c0) eqn:Hcl0; [discriminate|].
    destruct (IH _ _ _ _ H) as [Hin Hex]. split; [right; exact Hin | exact Hex].
  - injection H as -> -> -> ->. split; [left; reflexivity | exists brest; exact Hb0].
Qed.

Lemma sel_ready_cl_closed : forall b tr cases c f,
  sel_ready_cl b tr cases = Some (SR_closed c f) ->
  In (c, f) cases /\ b c = [] /\ closedb tr c = true.
Proof.
  induction cases as [|[c0 f0] rest IH]; intros c f H; cbn in H; [discriminate|].
  destruct (b c0) as [|[v0 s0] brest] eqn:Hb0.
  - destruct (closedb tr c0) eqn:Hcl0.
    + injection H as -> ->. split; [left; reflexivity | split; [exact Hb0 | exact Hcl0]].
    + destruct (IH _ _ H) as [Hin [Hbc Hclc]]. split; [right; exact Hin | split; [exact Hbc | exact Hclc]].
  - discriminate.
Qed.

(* A live goroutine BLOCKED — now CLOSED-PRECISE: a CRecv is blocked iff its channel is empty AND
   OPEN ([closedb (rc_trace cfg) c = false]); a CSelect is blocked iff NO case is ready, where a case
   is ready when its channel is buffered OR closed-and-drained ([sel_ready_cl] = [None]).  A recv/
   select on a CLOSED, drained channel is READY ([rstep_recv_closed] / [rstep_select_closed], binds
   the zero value), so it is correctly NOT blocked — the precision the open-only notion lacked
   ([rclosed_recv_not_blocked] / [rclosed_select_not_blocked] witness the difference).  [ready_can_step]
   (¬blocked ⇒ can step) and [rstuck_blocked] (stuck ⇒ done ∨ blocked) are now EXACT inverses:
   ¬blocked is now NECESSARY as well as sufficient for progress. *)
Definition blocked (cfg : RConfig) (tid : nat) : Prop :=
  (exists c f, rc_prog cfg tid = CRecv c f
               /\ rc_bufs cfg c = []
               /\ closedb (rc_trace cfg) c = false)
  \/ (exists cases, rc_prog cfg tid = CSelect cases
                    /\ sel_ready_cl (rc_bufs cfg) (rc_trace cfg) cases = None).

(* A fresh goroutine id is available — holds for any reachable config (only finitely
   many goroutines are ever spawned), so [CSpawn] never blocks for lack of an id. *)
Definition FreshAvail (cfg : RConfig) : Prop := exists cid, rc_live cfg cid = false.

(* A live goroutine about to PANIC: its head is a [CClose] of an ALREADY-closed channel (Go's
   double-close panic).  Distinct from [blocked] (a deadlock) and from [rdone] — it is the third way
   a non-stepping goroutine arises.  ([rstep_close]/[rstep_send]'s [closedb = false] guard makes both
   non-steps; it is the operational image of [close_chan]/[send]'s [OPanic] in the IO model —
   [double_close_panics] / [send_closed_panics].)  Decidable: inspect the head, then [closedb]. *)
Definition rpanicking (cfg : RConfig) (tid : nat) : Prop :=
  (exists c k, rc_prog cfg tid = CClose c k /\ closedb (rc_trace cfg) c = true)
  \/ (exists c v k, rc_prog cfg tid = CSend c v k /\ closedb (rc_trace cfg) c = true).

Definition rpanicking_dec : forall cfg tid, {rpanicking cfg tid} + {~ rpanicking cfg tid}.
Proof.
  intros cfg tid.
  destruct (rc_prog cfg tid) as [ | c v k | c f | l v k | l f | child k | cases | c k ] eqn:Hp.
  (* CRet, CRecv, CWrite, CRead, CSpawn, CSelect: neither a CClose nor a CSend head *)
  1,3,4,5,6,7: right; intros [[c0 [k0 [Hpc _]]] | [c0 [v0 [k0 [Hpc _]]]]]; rewrite Hp in Hpc; discriminate.
  - (* CSend: panicking iff the channel is closed *)
    destruct (closedb (rc_trace cfg) c) eqn:Hcl.
    + left. right. exists c, v, k. split; [exact Hp | exact Hcl].
    + right. intros [[c0 [k0 [Hpc _]]] | [c0 [v0 [k0 [Hpc Hcl0]]]]]; rewrite Hp in Hpc;
        [discriminate | injection Hpc as -> _ _; rewrite Hcl in Hcl0; discriminate].
  - (* CClose: panicking iff the channel is closed *)
    destruct (closedb (rc_trace cfg) c) eqn:Hcl.
    + left. left. exists c, k. split; [exact Hp | exact Hcl].
    + right. intros [[c0 [k0 [Hpc Hcl0]]] | [c0 [v0 [k0 [Hpc _]]]]]; rewrite Hp in Hpc;
        [injection Hpc as -> _; rewrite Hcl in Hcl0; discriminate | discriminate].
Defined.

(** PROGRESS: any live goroutine that is neither finished, blocked, NOR panicking can take a step
    (so the whole config can step).  The heart of deadlock-freedom.  [~ rpanicking] is the new
    hypothesis the [rstep_close] guard forces: a double-close goroutine genuinely cannot step. *)
Lemma ready_can_step : forall cfg tid,
  FreshAvail cfg ->
  rc_live cfg tid = true ->
  rc_prog cfg tid <> CRet ->
  ~ blocked cfg tid ->
  ~ rpanicking cfg tid ->
  rcan_step cfg.
Proof.
  intros [p b h lv tr] tid [cid Hcid] Hlive Hnret Hnblk Hnpan.
  unfold rcan_step, blocked, rpanicking in *; cbn [rc_prog rc_live rc_bufs rc_trace] in *.
  destruct (p tid) as [ | c v k | c f | l v k | l f | child k | cases | c k ] eqn:Hp.
  - congruence.
  - (* send: enabled IFF still OPEN; on a closed channel it would PANIC (contradiction) *)
    destruct (closedb tr c) eqn:Hcl.
    + exfalso. apply Hnpan. right. exists c, v, k. split; [reflexivity | exact Hcl].
    + eexists; eapply rstep_send; eassumption.
  - destruct (b c) as [ | [v s] rest] eqn:Hb.
    + (* empty buffer: CLOSED ⇒ rstep_recv_closed (zero); OPEN ⇒ genuinely blocked (contradiction) *)
      destruct (closedb tr c) eqn:Hcl.
      * destruct (closedb_true_witness _ _ Hcl) as [pos [e [Hpos Hek]]].
        eexists; eapply rstep_recv_closed; eassumption.
      * exfalso. apply Hnblk. left. exists c, f.
        split; [reflexivity | split; [exact Hb | exact Hcl]].
    + eexists; eapply rstep_recv; eassumption.
  - eexists; eapply rstep_write; eassumption.
  - eexists; eapply rstep_read; eassumption.
  - eexists; eapply rstep_spawn; eassumption.
  - (* select: a ready case (buffered OR closed-drained) steps; no ready case ⇒ blocked *)
    destruct (sel_ready_cl b tr cases) as [[c f v s | c f]|] eqn:Hsel.
    + destruct (sel_ready_cl_buf _ _ _ _ _ _ _ Hsel) as [Hin [rest Hb]].
      eexists; eapply rstep_select; eassumption.
    + destruct (sel_ready_cl_closed _ _ _ _ _ Hsel) as [Hin [Hb Hcl]].
      destruct (closedb_true_witness _ _ Hcl) as [pos [e [Hpos Hek]]].
      eexists; eapply rstep_select_closed; eassumption.
    + exfalso. apply Hnblk. right. exists cases. split; [reflexivity | exact Hsel].
  - (* close: enabled IFF still OPEN; on an already-closed channel it would PANIC (contradiction) *)
    destruct (closedb tr c) eqn:Hcl.
    + exfalso. apply Hnpan. left. exists c, k. split; [reflexivity | exact Hcl].
    + eexists; eapply rstep_close; eassumption.
Qed.

(** THE DEADLOCK CHARACTERIZATION (now PANIC-AWARE): in a stuck config, EVERY live goroutine is
    finished ([CRet]), blocked (empty-open recv / no-ready-case select), OR about to PANIC (double
    close).  These are the THREE ways a live goroutine fails to step — Go's run-time distinguishes
    deadlock from panic, and so does this.  (Contrapositive of progress: a goroutine that is none of
    the three is ready, so the config could step.) *)
Theorem rstuck_blocked : forall cfg,
  FreshAvail cfg -> RStuck cfg ->
  forall tid, rc_live cfg tid = true ->
    rc_prog cfg tid = CRet \/ blocked cfg tid \/ rpanicking cfg tid.
Proof.
  intros cfg Hfresh [Hnstep _] tid Hlive.
  (* a double-close is decidably panicking; otherwise the non-CRecv/CSelect heads are all enabled
     (a CClose now needs an OPEN channel — [~rpanicking] gives that), a CRecv is blocked iff empty
     AND open, a CSelect iff no case is buffered-or-closed-ready — all decidable, no classical logic. *)
  destruct (rpanicking_dec cfg tid) as [Hpan | Hnpan]; [right; right; exact Hpan |].
  destruct (rc_prog cfg tid) as [ | c v k | c f | l v k | l f | child k | cases | c k ] eqn:Hp.
  - left. reflexivity.
  - exfalso. apply Hnstep. apply (ready_can_step cfg tid Hfresh Hlive).
    + rewrite Hp; discriminate.
    + unfold blocked. intros [[c0 [f0 [Hpc _]]] | [cs0 [Hpc _]]]; rewrite Hp in Hpc; discriminate.
    + exact Hnpan.
  - destruct (rc_bufs cfg c) as [ | hd rest ] eqn:Hb.
    + (* empty buffer: blocked iff OPEN; if closed it can step (contradiction with stuck) *)
      destruct (closedb (rc_trace cfg) c) eqn:Hcl.
      * exfalso. apply Hnstep. apply (ready_can_step cfg tid Hfresh Hlive).
        -- rewrite Hp; discriminate.
        -- unfold blocked. intros [[c0 [f0 [Hpc [Hbc0 Hcl0]]]] | [cs0 [Hpc _]]]; rewrite Hp in Hpc;
             [injection Hpc as Hcc Hff; subst c0; rewrite Hcl in Hcl0; discriminate Hcl0 | discriminate].
        -- exact Hnpan.
      * right; left. unfold blocked. left. exists c, f.
        split; [exact Hp | split; [exact Hb | exact Hcl]].
    + exfalso. apply Hnstep. apply (ready_can_step cfg tid Hfresh Hlive).
      * rewrite Hp; discriminate.
      * unfold blocked. intros [[c0 [f0 [Hpc [Hbc0 _]]]] | [cs0 [Hpc _]]]; rewrite Hp in Hpc;
          [injection Hpc as Hcc Hff; subst c0; rewrite Hb in Hbc0; discriminate Hbc0 | discriminate].
      * exact Hnpan.
  - exfalso. apply Hnstep. apply (ready_can_step cfg tid Hfresh Hlive).
    + rewrite Hp; discriminate.
    + unfold blocked. intros [[c0 [f0 [Hpc _]]] | [cs0 [Hpc _]]]; rewrite Hp in Hpc; discriminate.
    + exact Hnpan.
  - exfalso. apply Hnstep. apply (ready_can_step cfg tid Hfresh Hlive).
    + rewrite Hp; discriminate.
    + unfold blocked. intros [[c0 [f0 [Hpc _]]] | [cs0 [Hpc _]]]; rewrite Hp in Hpc; discriminate.
    + exact Hnpan.
  - exfalso. apply Hnstep. apply (ready_can_step cfg tid Hfresh Hlive).
    + rewrite Hp; discriminate.
    + unfold blocked. intros [[c0 [f0 [Hpc _]]] | [cs0 [Hpc _]]]; rewrite Hp in Hpc; discriminate.
    + exact Hnpan.
  - (* select: ready (buffered OR closed-drained) ⇒ can step (contradiction); else blocked *)
    destruct (sel_ready_cl (rc_bufs cfg) (rc_trace cfg) cases) as [sr|] eqn:Hsel.
    + exfalso. apply Hnstep. apply (ready_can_step cfg tid Hfresh Hlive).
      * rewrite Hp; discriminate.
      * unfold blocked. intros [[c0 [f0 [Hpc _]]] | [cs0 [Hpc Hnone]]]; rewrite Hp in Hpc;
          [discriminate | injection Hpc as ->; rewrite Hsel in Hnone; discriminate].
      * exact Hnpan.
    + right; left. unfold blocked. right. exists cases. split; [exact Hp | exact Hsel].
  - (* close: NOT panicking (handled above), so the channel is OPEN ⇒ enabled ⇒ contradiction *)
    exfalso. apply Hnstep. apply (ready_can_step cfg tid Hfresh Hlive).
    + rewrite Hp; discriminate.
    + unfold blocked. intros [[c0 [f0 [Hpc _]]] | [cs0 [Hpc _]]]; rewrite Hp in Hpc; discriminate.
    + exact Hnpan.
Qed.

(** PANIC ≠ DEADLOCK, witnessed.  [rdouble_close_cfg]: goroutine 0 is poised to [close 5], but 5 is
    already closed (a [KClose 5] sits at trace position 0).  It is [rpanicking] (Go would panic), it
    genuinely CANNOT step (the [rstep_close] guard [closedb tr 5 = false] is false — no silent
    re-close), and [rstuck_blocked] classifies it as PANICKING, NOT blocked — the operational image of
    [double_close_panics] in the IO model. *)
Definition rdouble_close_cfg : RConfig :=
  mkRCfg (fun t => if Nat.eqb t 0 then CClose 5 CRet else CRet)
         (fun _ => []) (fun _ => 0) (fun t => Nat.eqb t 0)
         [mkEv 1 (KClose 5)].

Theorem rdouble_close_panicking : rpanicking rdouble_close_cfg 0.
Proof. left. exists 5, CRet. split; reflexivity. Qed.

Theorem rdouble_close_cant_step : ~ rcan_step rdouble_close_cfg.
Proof.
  intros [cfg' Hstep]. unfold rdouble_close_cfg in Hstep.
  inversion Hstep; subst; cbn in *;
    match goal with H : (_ =? 0) = true |- _ => apply Nat.eqb_eq in H; subst end;
    cbn in *; try discriminate;
    (* the close rule survives the head match; resolve its channel to 5, then the guard
       [closedb [KClose 5] 5 = false] reduces to [true = false] — absurd *)
    try (match goal with H : CClose _ _ = CClose _ _ |- _ => injection H as <- <- end);
    subst; cbn in *; try discriminate.
Qed.

(** SEND on a closed channel is likewise a PANIC, not a step (Go).  [rsend_closed_cfg]: goroutine 0
    is poised to [send 7 on 5], but 5 is already closed — it is [rpanicking] (the CSend disjunct) and
    genuinely cannot step (the [rstep_send] guard bites); the operational image of [send_closed_panics]. *)
Definition rsend_closed_cfg : RConfig :=
  mkRCfg (fun t => if Nat.eqb t 0 then CSend 5 7 CRet else CRet)
         (fun _ => []) (fun _ => 0) (fun t => Nat.eqb t 0)
         [mkEv 1 (KClose 5)].

Theorem rsend_closed_panicking : rpanicking rsend_closed_cfg 0.
Proof. right. exists 5, 7, CRet. split; reflexivity. Qed.

Theorem rsend_closed_cant_step : ~ rcan_step rsend_closed_cfg.
Proof.
  intros [cfg' Hstep]. unfold rsend_closed_cfg in Hstep.
  inversion Hstep; subst; cbn in *;
    match goal with H : (_ =? 0) = true |- _ => apply Nat.eqb_eq in H; subst end;
    cbn in *; try discriminate;
    try (match goal with H : CSend _ _ _ = CSend _ _ _ |- _ => injection H as <- <- <- end);
    subst; cbn in *; try discriminate.
Qed.

(** Deadlock is REPRESENTABLE in the rich calculus too: one goroutine receiving on an
    empty channel with no sender is stuck (cf. [block_stuck] for the simple calculus). *)
Definition rblock_cfg : RConfig :=
  mkRCfg (fun t => if Nat.eqb t 0 then CRecv 0 (fun _ => CRet) else CRet)
         (fun _ => []) (fun _ => 0) (fun t => Nat.eqb t 0) [].

Lemma rblock_stuck : RStuck rblock_cfg.
Proof.
  split.
  - intros [cfg' Hstep]. unfold rblock_cfg in Hstep.
    (* the open empty channel mismatches every step head; the closed-recv/select heads need a
       [KClose] in the (empty) trace, so their [nth_error [] pos = Some e] premise is absurd *)
    inversion Hstep; subst; cbn in *;
      match goal with H : (_ =? 0) = true |- _ => apply Nat.eqb_eq in H; subst end;
      cbn in *; try discriminate;
      match goal with H : nth_error [] _ = Some _ |- _ =>
        apply nth_error_lt in H; cbn in H; lia end.
  - intros Hdone. specialize (Hdone 0 eq_refl). cbn in Hdone. discriminate.
Qed.

(** CLOSED-CHANNEL READINESS in the RICH calculus — the operational closed-recv slice ported from
    the simple calculus ([closed_recv_can_step] etc.).  A [CRecv]/[CSelect] on a CLOSED, drained
    channel STEPS, binding the zero value [0] — whereas on an OPEN empty channel it is [RStuck]
    ([rblock_stuck] / [rsel_block_stuck]).  Channel 5 is closed (a [KClose 5] at trace position 0)
    and its buffer is empty. *)
Definition rclosed_chan_cfg : RConfig :=
  mkRCfg (fun t => if Nat.eqb t 0 then CRecv 5 (fun _ => CRet)
                   else if Nat.eqb t 1 then CSelect [(5, fun _ => CRet)] else CRet)
         (fun _ => []) (fun _ => 0) (fun t => orb (Nat.eqb t 0) (Nat.eqb t 1))
         [mkEv 2 (KClose 5)].

(** The recv from the closed, drained channel CAN step (Go: returns zero) — where buffered
    [rstep_recv] could not.  The emitted [KRecv 5 0]'s producer is the close at position 0. *)
Theorem rclosed_recv_can_step : exists cfg', rstep rclosed_chan_cfg cfg'.
Proof.
  eexists. eapply rstep_recv_closed with (tid := 0) (c := 5) (pos := 0) (e := mkEv 2 (KClose 5));
    [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity ].
Qed.

(** A SELECT whose only case channel is closed+drained is likewise READY (the case fires with zero)
    — the relational fix for the exact bug the sequential [select_recv2] had (it fabricated / fell
    through), now in the value-carrying calculus. *)
Theorem rclosed_select_can_step : exists cfg', rstep rclosed_chan_cfg cfg'.
Proof.
  eexists. eapply rstep_select_closed with (tid := 1) (cases := [(5, fun _ => CRet)]) (c := 5)
                                           (f := fun _ => CRet) (pos := 0) (e := mkEv 2 (KClose 5));
    [ reflexivity | reflexivity | left; reflexivity | reflexivity | reflexivity | reflexivity ].
Qed.

(** And the closed-recv keeps the trace well-formed (a real, sound transition): the resulting
    config still satisfies [RInv], so its happens-before stays a strict partial order. *)
Theorem rclosed_recv_preserves_inv :
  forall cfg', rstep rclosed_chan_cfg cfg' -> RInv rclosed_chan_cfg -> RInv cfg'.
Proof. intros cfg' Hstep Hinv. exact (rstep_preserves_inv _ _ Hstep Hinv). Qed.

(** PRECISION PAYOFF of the closed-aware [blocked]: the closed-drained recv (goroutine 0) and
    closed-drained select (goroutine 1) of [rclosed_chan_cfg] are NOT [blocked] — correctly
    classified as READY (they step, [rclosed_recv_can_step] / [rclosed_select_can_step]).  Under the
    earlier open-only [blocked] both WOULD have been (wrongly) called blocked: this is exactly the
    over-approximation the [closedb] / [sel_ready_cl] refinement removes. *)
Theorem rclosed_recv_not_blocked : ~ blocked rclosed_chan_cfg 0.
Proof.
  intros [[c [f [Hp [Hb Hcl]]]] | [cases [Hp _]]].
  - cbn in Hp. injection Hp as Hc _. subst c. cbn in Hcl. discriminate Hcl.
  - cbn in Hp. discriminate Hp.
Qed.

Theorem rclosed_select_not_blocked : ~ blocked rclosed_chan_cfg 1.
Proof.
  intros [[c [f [Hp _]]] | [cases [Hp Hnone]]].
  - cbn in Hp. discriminate Hp.
  - cbn in Hp. injection Hp as Hcs. subst cases. cbn in Hnone. discriminate Hnone.
Qed.

(** ── CLOSED IS PERMANENT (Go: a channel, once closed, stays closed — never reopens; recvs keep
    returning the zero value for the rest of the run). ──

    [closedb] only GROWS along execution: every [rstep] appends events to the trace (one, or two for
    [rstep_spawn]) and never removes any, and [closedb] (an [existsb] over the trace) is monotone
    under append.  This is the trace-core
    FOUNDATION for making the operational close/send faithful to Go's double-close / send-on-closed
    PANIC — the genuinely-open sub-item.  (The IO/[World] model ALREADY panics on those:
    [close_chan]/[send] [OPanic] when closed, witnessed by [double_close_panics]/[send_closed_panics];
    the remaining gap is the rich calculus's UNGUARDED [rstep_close]/[rstep_send], which silently
    re-close.  A guard [closedb tr c = false] makes them faithful — and permanence is what makes the
    guard meaningful: a closed channel can never be validly re-closed.  That guard + a panic-aware
    deadlock characterization is the next slice.) *)

Lemma closedb_app : forall t1 t2 c, closedb (t1 ++ t2) c = orb (closedb t1 c) (closedb t2 c).
Proof. intros t1 t2 c. unfold closedb. apply existsb_app. Qed.

(* Every [rstep] APPENDS a non-empty suffix — one event for all rules EXCEPT [rstep_spawn], which
   appends TWO (the parent's [KSpawn] and the child's [KStart]).  Buffers/heap/liveness may change;
   the trace only grows.  (The exact-suffix shape is irrelevant downstream — only "grows" matters.) *)
Lemma rstep_grows_trace : forall cfg cfg', rstep cfg cfg' ->
  exists suf, rc_trace cfg' = rc_trace cfg ++ suf.
Proof. intros cfg cfg' Hstep. destruct Hstep; cbn [rc_trace]; eexists; reflexivity. Qed.

Lemma rstep_closedb_mono : forall cfg cfg' c, rstep cfg cfg' ->
  closedb (rc_trace cfg) c = true -> closedb (rc_trace cfg') c = true.
Proof.
  intros cfg cfg' c Hstep H.
  destruct (rstep_grows_trace _ _ Hstep) as [suf He]. rewrite He, closedb_app, H. reflexivity.
Qed.

Lemma rsteps_closedb_mono : forall cfg cfg' c, rsteps cfg cfg' ->
  closedb (rc_trace cfg) c = true -> closedb (rc_trace cfg') c = true.
Proof.
  intros cfg cfg' c Hsteps. induction Hsteps as [|a b d Hab Hbd IH]; intros H; [exact H|].
  apply IH. exact (rstep_closedb_mono _ _ c Hab H).
Qed.

(** PAYOFF 1: channel 5 of [rclosed_chan_cfg] is closed in EVERY reachable successor — closedness
    never lapses, so the channel never "reopens". *)
Theorem rclosed_chan_stays_closed : forall cfg,
  rsteps rclosed_chan_cfg cfg -> closedb (rc_trace cfg) 5 = true.
Proof. intros cfg Hsteps. apply (rsteps_closedb_mono _ _ _ Hsteps). reflexivity. Qed.

(** PAYOFF 2 (the operational form of Go's "receive from a closed channel proceeds immediately"):
    from ANY config where [c] is closed, at ANY reachable later state, a live goroutine parked at
    [CRecv c] on a drained buffer CAN step (closed-recv, yielding zero) — permanence guarantees the
    closedness is still there to fire it.  No deadlock is possible on a closed channel. *)
Theorem reachable_closed_recv_can_step : forall cfg0 cfg tid c f,
  closedb (rc_trace cfg0) c = true -> rsteps cfg0 cfg ->
  rc_live cfg tid = true -> rc_prog cfg tid = CRecv c f -> rc_bufs cfg c = [] ->
  rcan_step cfg.
Proof.
  intros cfg0 cfg tid c f Hcl0 Hsteps Hlive Hp Hb.
  pose proof (rsteps_closedb_mono _ _ c Hsteps Hcl0) as Hcl.
  destruct (closedb_true_witness _ _ Hcl) as [pos [e [Hpos Hek]]].
  destruct cfg as [p b h lv tr]; cbn [rc_live rc_prog rc_bufs rc_trace] in *.
  eexists. eapply rstep_recv_closed; eassumption.
Qed.

(** ── CSELECT, the authoritative select in the RICH (value-carrying) calculus: the two select
    code-review findings #3 proven here end-to-end. ── *)

(** PER-CASE CONTINUATIONS (review #3): [select { case <-ch: A() | case <-ch: B() }] — the SAME
    channel with DISTINCT bodies — is representable (impossible with the shared-continuation
    [PSelect]), and BOTH cases are eligible (Go may choose either), yielding two successors that run
    DIFFERENT continuations.  ([rsel_cfg] is a post-send state: position 0 is the earlier send, so
    it is [RInv]-valid.) *)
Definition rsel_A : Cmd := CWrite 1 1 CRet.
Definition rsel_B : Cmd := CWrite 2 2 CRet.
Definition rsel_cfg : RConfig :=
  mkRCfg (fun t => if Nat.eqb t 0 then CSelect [(0, fun _ => rsel_A); (0, fun _ => rsel_B)] else CRet)
         (fun c => if Nat.eqb c 0 then [(42, 0)] else [])
         (fun _ => 0) (fun t => Nat.eqb t 0)
         [mkEv 0 (KSend 0)].

Theorem rselect_per_case_continuation :
  exists cfg1 cfg2, rstep rsel_cfg cfg1 /\ rstep rsel_cfg cfg2 /\
                    rc_prog cfg1 0 = rsel_A /\ rc_prog cfg2 0 = rsel_B /\ rsel_A <> rsel_B.
Proof.
  eexists. eexists. split; [| split; [| split; [| split]]].
  - eapply rstep_select with (tid:=0) (c:=0) (f:=fun _ => rsel_A) (v:=42) (s:=0);
      [ reflexivity | reflexivity | left; reflexivity | reflexivity ].
  - eapply rstep_select with (tid:=0) (c:=0) (f:=fun _ => rsel_B) (v:=42) (s:=0);
      [ reflexivity | reflexivity | right; left; reflexivity | reflexivity ].
  - cbn. rewrite upd_same. reflexivity.
  - cbn. rewrite upd_same. reflexivity.
  - unfold rsel_A, rsel_B. intro H. inversion H.
Qed.

(** EMPTY SELECT IS DEADLOCK, NOT A VALUE (review #3, rich-calculus version): a select with no
    ready case (and no other goroutine to make one ready) is [RStuck] — a LOCAL non-step, never a
    fabricated zero. *)
Definition rsel_block_cfg : RConfig :=
  mkRCfg (fun t => if Nat.eqb t 0 then CSelect [(0, fun _ => CRet); (1, fun _ => CRet)] else CRet)
         (fun _ => []) (fun _ => 0) (fun t => Nat.eqb t 0) [].

Lemma rsel_block_stuck : RStuck rsel_block_cfg.
Proof.
  split.
  - intros [cfg' Hstep]. unfold rsel_block_cfg in Hstep.
    (* every buffer is empty, so the rstep_select readiness premise [[] = (v,s)::_] is absurd;
       all other rstep heads mismatch [CSelect]; the closed-select head needs a [KClose] in the
       (empty) trace, so its [nth_error [] pos = Some e] premise is absurd too *)
    inversion Hstep; subst; cbn in *;
      match goal with H : (_ =? 0) = true |- _ => apply Nat.eqb_eq in H; subst end;
      cbn in *; try discriminate;
      match goal with H : nth_error [] _ = Some _ |- _ =>
        apply nth_error_lt in H; cbn in H; lia end.
  - intros Hdone. specialize (Hdone 0 eq_refl). cbn in Hdone. discriminate.
Qed.

(** ── BRIDGE: the typed sequential [select_recv2] (builtins.v) is a SOUND but INCOMPLETE scheduler
    of this authoritative relational [CSelect]. ──

    [select_recv2 ta ch1 k1 ta ch2 k2] takes ch1 if ready, else ch2 (ch1-PRIORITY) — exactly the
    deterministic "first ready case" of the cases list [[(ch1,·); (ch2,·)]], which is precisely
    [sel_first_ready].  These two theorems make the select-review verdict ("the deterministic
    interpreter is ONE example scheduler, non-authoritative") a PROOF:
    (1) SOUND — the deterministic first-ready choice is always a PERMITTED [rstep_select];
    (2) INCOMPLETE — when two cases are ready it realises only ch1, yet [rstep_select] ALSO permits
        the ch2 transition the typed model never takes; and
    (3) WORLD-LEVEL — the real [select_recv2] (not just [sel_first_ready]) reduces, on a ready
        channel, to a plain [recv] there ([select_recv2_ch1_buffered] etc. in builtins.v), which is
        already operationally bridged — see [select_fire_is_recv_fire] below. *)

(** (1) SOUNDNESS: whatever case the ch1-priority scheduler ([sel_first_ready]) picks, the
    authoritative nondeterministic select HAS that transition. *)
Theorem det_select_sound :
  forall p b h lv tr tid cases c f v s,
    lv tid = true -> p tid = CSelect cases ->
    sel_first_ready b cases = Some (c, f, v, s) ->
    exists brest,
      b c = (v, s) :: brest /\
      rstep (mkRCfg p b h lv tr)
            (mkRCfg (upd p tid (f v)) (upd b c brest) h lv (tr ++ [mkEv tid (KRecv c s)])).
Proof.
  intros p b h lv tr tid cases c f v s Hlv Hp Hsel.
  destruct (sel_first_ready_sound _ _ _ _ _ _ Hsel) as [Hin [brest Hb]].
  exists brest. split; [exact Hb |]. eapply rstep_select; eassumption.
Qed.

(** (2) INCOMPLETENESS: in [rsel2_cfg] BOTH channel 0 and channel 1 are ready; the ch1-priority
    scheduler picks channel 0 ([sel_first_ready] returns the channel-0 case), yet [rstep_select]
    ALSO has the channel-1 successor — a behaviour the deterministic typed select never realises. *)
Definition rsel2_cfg : RConfig :=
  mkRCfg (fun t => if Nat.eqb t 0 then CSelect [(0, fun _ => CRet); (1, fun _ => CRet)] else CRet)
         (fun c => if Nat.eqb c 0 then [(7, 0)] else if Nat.eqb c 1 then [(9, 1)] else [])
         (fun _ => 0) (fun t => Nat.eqb t 0)
         [mkEv 0 (KSend 0); mkEv 0 (KSend 1)].

Theorem det_select_incomplete :
  (* the ch1-priority scheduler deterministically picks channel 0 *)
  sel_first_ready (rc_bufs rsel2_cfg) [(0, fun _ : nat => CRet); (1, fun _ => CRet)]
    = Some (0, (fun _ => CRet), 7, 0)
  (* yet the authoritative select ALSO permits the channel-1 transition (distinct trace event) *)
  /\ exists cfg1, rstep rsel2_cfg cfg1
                  /\ rc_trace cfg1 = rc_trace rsel2_cfg ++ [mkEv 0 (KRecv 1 1)].
Proof.
  split; [ reflexivity |].
  eexists. split.
  - eapply rstep_select with (tid:=0) (c:=1) (f:=fun _ => CRet) (v:=9) (s:=1);
      [ reflexivity | reflexivity | right; left; reflexivity | reflexivity ].
  - reflexivity.
Qed.

(** (3) WORLD-level connection (closes the gap that [det_select_sound] used [sel_first_ready] as a
    STAND-IN for the real [select_recv2]).  Operationally, firing a BUFFERED select case [(c,f)]
    reaches the IDENTICAL successor config as a plain [rstep_recv] on [c] would — select-taking-a-
    ready-channel IS a recv on that channel.  This mirrors, in the calculus, the [run_io] theorem
    [select_recv2_ch1_buffered] (builtins.v): [select_recv2] on a ready ch1 = [bind (recv ta ch1) k1].
    Composed — [select_recv2] = [recv] (World, builtins) ∘ [recv] ↔ [rstep_recv] ([denote_sim_recv],
    World) ∘ [rstep_recv] = [rstep_select]-successor (here) — the typed [select_recv2] is tied to the
    operational select through [run_io], not merely to [sel_first_ready]. *)
Theorem select_fire_is_recv_fire :
  forall p b h lv tr tid cases c f v s brest,
    lv tid = true -> In (c, f) cases -> b c = (v, s) :: brest ->
    let succ := mkRCfg (upd p tid (f v)) (upd b c brest) h lv (tr ++ [mkEv tid (KRecv c s)]) in
    (p tid = CSelect cases -> rstep (mkRCfg p b h lv tr) succ)   (* select firing case (c,f) … *)
    /\ (p tid = CRecv c f  -> rstep (mkRCfg p b h lv tr) succ).  (* …reaches the SAME config as recv on c *)
Proof.
  intros p b h lv tr tid cases c f v s brest Hlv Hin Hb. cbn. split; intro Hp.
  - eapply rstep_select; eassumption.
  - eapply rstep_recv; eassumption.
Qed.

(** (4) COMPLETENESS UNDER A UNIQUE READY CASE — the exact converse of (2), and the precise boundary
    of the deterministic model's faithfulness.  The incompleteness in (2) is caused ENTIRELY by a
    CHOICE among ≥2 ready cases.  Remove the choice — let the cases have a UNIQUE buffered-ready case
    — and every buffered [rstep_select] firing of that goroutine collapses to ONE successor, exactly
    the one the deterministic ch1-priority interpreter ([sel_first_ready]) takes.  So in that regime
    the cheap typed [select_recv2] is not merely SOUND (1) but COMPLETE: Go's pseudo-random pick
    ranges over a SINGLE candidate, hence the deterministic model forbids NOTHING Go permits.  This is
    the "sound-but-narrow interim" the builtins.v select note only promises — now a THEOREM.

    SCOPE (honest, per the select review's TOCTOU caveat): the uniqueness hypothesis is over BUFFERED
    readiness ([b c' <> []]).  A CLOSED-and-drained case is an ORTHOGONAL readiness source (it fires
    [rstep_select_closed], a different successor), so full Go-completeness additionally needs the
    open-channel side condition — no case closed-drained — which the all-open configs of (1)/(2)
    satisfy.  Within the buffered regime this is the precise ⊆ matching [det_select_sound]'s ⊇. *)
Lemma det_select_complete_unique :
  forall p b h lv tr tid cases c f v s brest,
    p tid = CSelect cases ->
    b c = (v, s) :: brest ->
    (forall c' f', In (c', f') cases -> b c' <> [] -> (c', f') = (c, f)) ->  (* UNIQUE buffered-ready case *)
    forall c2 f2 v2 s2 brest2,
      In (c2, f2) cases -> b c2 = (v2, s2) :: brest2 ->                       (* any buffered firing... *)
      mkRCfg (upd p tid (f2 v2)) (upd b c2 brest2) h lv (tr ++ [mkEv tid (KRecv c2 s2)])
      = mkRCfg (upd p tid (f v)) (upd b c brest) h lv (tr ++ [mkEv tid (KRecv c s)]).  (* ...IS the det one *)
Proof.
  intros p b h lv tr tid cases c f v s brest Hp Hbc Huniq c2 f2 v2 s2 brest2 Hin2 Hb2.
  assert (Hcf : (c2, f2) = (c, f)) by (apply Huniq; [exact Hin2 | rewrite Hb2; discriminate]).
  injection Hcf as Hc2 Hf2; subst c2 f2.
  rewrite Hbc in Hb2. inversion Hb2; subst. reflexivity.
Qed.

(** Headline: in the unique-ready regime the deterministic interpreter is EXACT — its pick is the ONE
    permitted buffered select transition.  [det_select_sound] gives ⊇ (the pick is permitted);
    [det_select_complete_unique] gives ⊆ (every permitted buffered firing IS the pick).  Together:
    sound ∧ complete, so the typed [select_recv2] is fully faithful to Go's select on that goroutine's
    buffered cases — the regime where Go's nondeterminism degenerates to a function.
    [Print Assumptions det_select_exact_unique] = Closed under the global context: fully axiom-free,
    not even the Int63/Float substrate (pure [nat]/[list]/inductive reasoning over [rstep]). *)
Corollary det_select_exact_unique :
  forall p b h lv tr tid cases c f v s brest,
    lv tid = true -> p tid = CSelect cases ->
    sel_first_ready b cases = Some (c, f, v, s) -> b c = (v, s) :: brest ->
    (forall c' f', In (c', f') cases -> b c' <> [] -> (c', f') = (c, f)) ->
    rstep (mkRCfg p b h lv tr)                                                (* ⊇ SOUND: permitted *)
          (mkRCfg (upd p tid (f v)) (upd b c brest) h lv (tr ++ [mkEv tid (KRecv c s)]))
    /\ (forall c2 f2 v2 s2 brest2, In (c2, f2) cases -> b c2 = (v2, s2) :: brest2 ->  (* ⊆ COMPLETE *)
          mkRCfg (upd p tid (f2 v2)) (upd b c2 brest2) h lv (tr ++ [mkEv tid (KRecv c2 s2)])
          = mkRCfg (upd p tid (f v)) (upd b c brest) h lv (tr ++ [mkEv tid (KRecv c s)])).
Proof.
  intros p b h lv tr tid cases c f v s brest Hlv Hp Hsel Hbc Huniq. split.
  - destruct (sel_first_ready_sound _ _ _ _ _ _ Hsel) as [Hin _].
    eapply rstep_select; [exact Hlv | exact Hp | exact Hin | exact Hbc].
  - intros c2 f2 v2 s2 brest2 Hin2 Hb2.
    exact (det_select_complete_unique p b h lv tr tid cases c f v s brest Hp Hbc Huniq
             c2 f2 v2 s2 brest2 Hin2 Hb2).
Qed.

(** ----------------------------------------------------------------------------
    DEADLOCK FREEDOM for a real class: RECEIVE-FREE programs.

    Only a receive can block, so a program that never receives can never deadlock —
    yet sends, writes, reads, AND spawns (genuine concurrency) are all allowed.  This
    is a real, GENERAL deadlock-freedom theorem (over the whole receive-free class),
    not a per-program argument.
    ---------------------------------------------------------------------------- *)
Inductive RecvFree : Cmd -> Prop :=
  | RF_ret   : RecvFree CRet
  | RF_send  : forall c v k, RecvFree k -> RecvFree (CSend c v k)
  | RF_write : forall l v k, RecvFree k -> RecvFree (CWrite l v k)
  | RF_read  : forall l f, (forall x, RecvFree (f x)) -> RecvFree (CRead l f)
  | RF_spawn : forall child k, RecvFree child -> RecvFree k -> RecvFree (CSpawn child k)
  | RF_close : forall c k, RecvFree k -> RecvFree (CClose c k).

Definition RecvFreeCfg (cfg : RConfig) : Prop :=
  forall tid, rc_live cfg tid = true -> RecvFree (rc_prog cfg tid).

(* A receive-free goroutine is never blocked (blocking needs a [CRecv] head). *)
Lemma recvfree_not_blocked : forall cfg tid,
  RecvFree (rc_prog cfg tid) -> ~ blocked cfg tid.
Proof.
  intros cfg tid HRF [[c [f [Hp _]]] | [cases [Hp _]]];
    rewrite Hp in HRF; inversion HRF.
Qed.

(** PROGRESS for receive-free configs (witness form): while ANY live goroutine has work left, the
    config can step OR that goroutine is about to PANIC (double-close) — i.e. it never DEADLOCKS.
    (Receive-free rules out the only blocking head; the sole remaining non-step is a double-close,
    a panic not a deadlock — so this is honest progress-or-panic, never silent stuck.) *)
Lemma recvfree_progress : forall cfg tid,
  FreshAvail cfg -> RecvFreeCfg cfg ->
  rc_live cfg tid = true -> rc_prog cfg tid <> CRet ->
  rcan_step cfg \/ rpanicking cfg tid.
Proof.
  intros cfg tid Hfresh HRF Hlive Hnret.
  destruct (rpanicking_dec cfg tid) as [Hpan | Hnpan]; [right; exact Hpan | left].
  apply (ready_can_step cfg tid Hfresh Hlive Hnret).
  - apply recvfree_not_blocked. exact (HRF tid Hlive).
  - exact Hnpan.
Qed.

(* Receive-freeness of all live goroutines is preserved by every step (the [recv]
   case is vacuous — a receive-free config has no [CRecv] head to step). *)
Lemma rstep_recvfree : forall cfg cfg',
  rstep cfg cfg' -> RecvFreeCfg cfg -> RecvFreeCfg cfg'.
Proof.
  intros cfg cfg' Hstep HRF tid'.
  unfold RecvFreeCfg in HRF.
  destruct Hstep as
    [ p b h lv tr tid c v k Hlv Hp _
    | p b h lv tr tid c f v s brest Hlv Hp Hbc
    | p b h lv tr tid l v k Hlv Hp
    | p b h lv tr tid l f Hlv Hp
    | p b h lv tr tid child k cid Hlv Hp Hcid
    | p b h lv tr tid cases c f v s brest Hlv Hp Hin Hbc
    | p b h lv tr tid c k Hlv Hp _
    | p b h lv tr tid c f pos e Hlv Hp Hbc Hpos Hek
    | p b h lv tr tid cases c f pos e Hlv Hp Hin Hbc Hpos Hek ];
    cbn [rc_prog rc_live] in *; intros Hlive';
    pose proof (HRF tid Hlv) as Ht; rewrite Hp in Ht.
  - (* send *)
    destruct (Nat.eq_dec tid' tid) as [->|Hne].
    + rewrite upd_same. inversion Ht; assumption.
    + rewrite (upd_other _ _ _ _ Hne). exact (HRF tid' Hlive').
  - (* recv — vacuous: a receive-free config has no CRecv head to step *)
    inversion Ht.
  - (* write *)
    destruct (Nat.eq_dec tid' tid) as [->|Hne].
    + rewrite upd_same. inversion Ht; assumption.
    + rewrite (upd_other _ _ _ _ Hne). exact (HRF tid' Hlive').
  - (* read *)
    destruct (Nat.eq_dec tid' tid) as [->|Hne].
    + rewrite upd_same. inversion Ht; subst.
      match goal with H : forall x, RecvFree _ |- _ => exact (H (h l)) end.
    + rewrite (upd_other _ _ _ _ Hne). exact (HRF tid' Hlive').
  - (* spawn *)
    inversion Ht; subst.
    destruct (Nat.eq_dec tid' cid) as [->|Hne1].
    + rewrite upd_same. assumption.
    + rewrite (upd_other _ _ _ _ Hne1) in Hlive'.
      rewrite (upd_other _ _ _ _ Hne1).
      destruct (Nat.eq_dec tid' tid) as [->|Hne2].
      * rewrite upd_same. assumption.
      * rewrite (upd_other _ _ _ _ Hne2). exact (HRF tid' Hlive').
  - (* select — vacuous: a receive-free config has no CSelect head to step *)
    inversion Ht.
  - (* close: continuation is receive-free (RF_close) *)
    destruct (Nat.eq_dec tid' tid) as [->|Hne].
    + rewrite upd_same. inversion Ht; assumption.
    + rewrite (upd_other _ _ _ _ Hne). exact (HRF tid' Hlive').
  - (* recv_closed — vacuous: a receive-free config has no CRecv head to step *)
    inversion Ht.
  - (* select_closed — vacuous: a receive-free config has no CSelect head to step *)
    inversion Ht.
Qed.

(** A fresh goroutine id always exists — the live set is finite (bounded by some [n]),
    an invariant preserved by every step (a spawn adds one id).  So [CSpawn] never
    blocks for lack of an id, and [FreshAvail] holds of every reachable config. *)
Definition LiveFin (cfg : RConfig) : Prop :=
  exists n, forall t, n <= t -> rc_live cfg t = false.

Lemma livefin_fresh : forall cfg, LiveFin cfg -> FreshAvail cfg.
Proof. intros cfg [n Hn]. exists n. apply Hn. apply le_n. Qed.

Lemma livefin_init : forall p, LiveFin (rinit_cfg p).
Proof.
  intros p. exists 1. intros t Ht. cbn.
  destruct t; [inversion Ht | reflexivity].
Qed.

Lemma rstep_livefin : forall cfg cfg', rstep cfg cfg' -> LiveFin cfg -> LiveFin cfg'.
Proof.
  intros cfg cfg' Hstep [n Hn].
  destruct Hstep as
    [ p b h lv tr tid c v k Hlv Hp _
    | p b h lv tr tid c f v s brest Hlv Hp Hbc
    | p b h lv tr tid l v k Hlv Hp
    | p b h lv tr tid l f Hlv Hp
    | p b h lv tr tid child k cid Hlv Hp Hcid
    | p b h lv tr tid cases c f v s brest Hlv Hp Hin Hbc
    | p b h lv tr tid c k Hlv Hp _
    | p b h lv tr tid c f pos e Hlv Hp Hbc Hpos Hek
    | p b h lv tr tid cases c f pos e Hlv Hp Hin Hbc Hpos Hek ];
    cbn [rc_live] in *.
  - exists n; exact Hn.
  - exists n; exact Hn.
  - exists n; exact Hn.
  - exists n; exact Hn.
  - (* spawn: new id [cid] becomes live; bound grows to [max n (S cid)] *)
    exists (Nat.max n (S cid)). intros t Ht. cbn [rc_live].
    destruct (Nat.eq_dec t cid) as [->|Hne].
    + exfalso. apply (Nat.lt_irrefl cid).
      apply (Nat.lt_le_trans cid (Nat.max n (S cid)) cid);
        [apply (Nat.lt_le_trans cid (S cid) (Nat.max n (S cid)));
           [apply Nat.lt_succ_diag_r | apply Nat.le_max_r] | exact Ht].
    + rewrite (upd_other _ _ _ _ Hne). apply Hn.
      apply (Nat.le_trans n (Nat.max n (S cid)) t); [apply Nat.le_max_l | exact Ht].
  - (* select: live set unchanged *) exists n; exact Hn.
  - (* close: live set unchanged *) exists n; exact Hn.
  - (* recv_closed: live set unchanged *) exists n; exact Hn.
  - (* select_closed: live set unchanged *) exists n; exact Hn.
Qed.

Lemma rsteps_recvfree_livefin : forall cfg cfg',
  rsteps cfg cfg' -> RecvFreeCfg cfg -> LiveFin cfg ->
  RecvFreeCfg cfg' /\ LiveFin cfg'.
Proof.
  intros cfg cfg' H. induction H; intros HRF HLF; [split; assumption|].
  apply IHrsteps;
    [exact (rstep_recvfree _ _ H HRF) | exact (rstep_livefin _ _ H HLF)].
Qed.

(** THE DEADLOCK-FREEDOM THEOREM (panic-aware).  In ANY reachable state of a receive-free program,
    every live UNFINISHED goroutine can step OR is about to PANIC (double-close) — so the program
    never DEADLOCKS; the only way it fails to progress is a run-time panic, exactly as in Go. *)
Theorem reachable_recvfree_progress : forall p cfg,
  (forall t, RecvFree (p t)) ->
  rsteps (rinit_cfg p) cfg ->
  forall tid, rc_live cfg tid = true -> rc_prog cfg tid <> CRet ->
    rcan_step cfg \/ rpanicking cfg tid.
Proof.
  intros p cfg HpRF Hsteps tid Hlive Hnret.
  assert (HRF0 : RecvFreeCfg (rinit_cfg p)).
  { intros t _. cbn. apply HpRF. }
  destruct (rsteps_recvfree_livefin _ _ Hsteps HRF0 (livefin_init p)) as [HRF HLF].
  exact (recvfree_progress cfg tid (livefin_fresh _ HLF) HRF Hlive Hnret).
Qed.

(** ----------------------------------------------------------------------------
    A RECEIVING program that is deadlock-free.  Receive-free is the clean general
    class; here is the complement — a program that DOES receive yet never deadlocks,
    because the UNBOUNDED BUFFER lets the send happen before the matching receive.
    [sr_prog] sends 42 on channel 0, then receives it back.  We exhibit the exact
    reachable shapes ([SRShape]) and show every reachable config is done-or-can-step.
    ---------------------------------------------------------------------------- *)
Definition sr_prog : Cmd := CSend 0 42 (CRecv 0 (fun _ => CRet)).
Definition sr_init : RConfig := rinit_cfg (fun t => if Nat.eqb t 0 then sr_prog else CRet).

Definition SRShape (cfg : RConfig) : Prop :=
  rc_live cfg = (fun t => Nat.eqb t 0)
  /\ (forall t, t <> 0 -> rc_prog cfg t = CRet)
  /\ ( (rc_prog cfg 0 = CSend 0 42 (CRecv 0 (fun _ => CRet)) /\ rc_bufs cfg 0 = [])
       \/ (rc_prog cfg 0 = CRecv 0 (fun _ => CRet) /\ exists s, rc_bufs cfg 0 = [(42, s)])
       \/ rc_prog cfg 0 = CRet )
  /\ closedb (rc_trace cfg) 0 = false.   (* sr never closes channel 0 — so its SEND never panics *)

Lemma sr_init_shape : SRShape sr_init.
Proof.
  unfold SRShape, sr_init, rinit_cfg; cbn [rc_live rc_prog rc_bufs].
  split; [reflexivity | split; [ | split]].
  - intros t Ht. destruct (Nat.eqb t 0) eqn:E;
      [apply Nat.eqb_eq in E; congruence | reflexivity].
  - left. split; reflexivity.
  - reflexivity.
Qed.

Lemma sr_step_shape : forall cfg cfg', rstep cfg cfg' -> SRShape cfg -> SRShape cfg'.
Proof.
  intros cfg cfg' Hstep [Hlive [Hidle [Hphase Hcl0]]].
  destruct Hstep as
    [ p b h lv tr tid c v k Hlv Hp _
    | p b h lv tr tid c f v s brest Hlv Hp Hbc
    | p b h lv tr tid l v k Hlv Hp
    | p b h lv tr tid l f Hlv Hp
    | p b h lv tr tid child k cid Hlv Hp Hcid
    | p b h lv tr tid cases c f v s brest Hlv Hp Hin Hbc
    | p b h lv tr tid c k Hlv Hp _
    | p b h lv tr tid c f pos e Hlv Hp Hbc Hpos Hek
    | p b h lv tr tid cases c f pos e Hlv Hp Hin Hbc Hpos Hek ];
    cbn [rc_live rc_prog rc_bufs] in *;
    rewrite Hlive in Hlv; cbn in Hlv; apply Nat.eqb_eq in Hlv; subst tid;
    destruct Hphase as [[Hp0 Hb0] | [[Hp0 [s0 Hb0]] | Hp0]];
    rewrite Hp0 in Hp; try discriminate Hp.
  - (* send rule + send shape -> receive shape *)
    inversion Hp; subst.
    unfold SRShape; cbn [rc_live rc_prog rc_bufs].
    split; [reflexivity | split; [ | split]].
    + intros t Ht. rewrite (upd_other _ _ _ _ Ht). exact (Hidle t Ht).
    + right; left. split.
      * rewrite upd_same. reflexivity.
      * exists (length tr). rewrite upd_same, Hb0. reflexivity.
    + (* closedness preserved: the appended KSend 0 is not a KClose 0 *)
      cbn [rc_trace] in Hcl0 |- *. rewrite closedb_app, Hcl0. reflexivity.
  - (* recv rule + receive shape -> finished *)
    inversion Hp; subst. rewrite Hb0 in Hbc. inversion Hbc; subst.
    unfold SRShape; cbn [rc_live rc_prog rc_bufs].
    split; [reflexivity | split; [ | split]].
    + intros t Ht. rewrite (upd_other _ _ _ _ Ht). exact (Hidle t Ht).
    + right; right. rewrite upd_same. reflexivity.
    + (* closedness preserved: the appended KRecv 0 is not a KClose 0 *)
      cbn [rc_trace] in Hcl0 |- *. rewrite closedb_app, Hcl0. reflexivity.
  - (* recv_closed rule + receive shape: impossible — buffer is non-empty ([(42,s0)] <> []) *)
    inversion Hp; subst. rewrite Hb0 in Hbc. discriminate Hbc.
Qed.

Lemma sr_steps_shape : forall a b, rsteps a b -> SRShape a -> SRShape b.
Proof.
  intros a b H. induction H; intros HS; [exact HS|].
  apply IHrsteps. exact (sr_step_shape _ _ H HS).
Qed.

Lemma sr_shape_progress : forall cfg, SRShape cfg -> rdone cfg \/ rcan_step cfg.
Proof.
  intros cfg [Hlive [_ [Hphase Hcl0]]].
  assert (Hfresh : FreshAvail cfg) by (exists 1; rewrite Hlive; reflexivity).
  destruct Hphase as [[Hp0 Hb0] | [[Hp0 [s0 Hb0]] | Hp0]].
  - right. apply (ready_can_step cfg 0 Hfresh).
    + rewrite Hlive; reflexivity.
    + rewrite Hp0; discriminate.
    + unfold blocked. intros [[c0 [f0 [Hpc _]]] | [cs0 [Hpc _]]]; rewrite Hp0 in Hpc; discriminate.
    + (* send shape: the CSend-panic disjunct needs channel 0 closed, but [Hcl0] says it is open *)
      unfold rpanicking. intros [[c0 [k0 [Hpc _]]] | [c0 [v0 [k0 [Hpc Hclp]]]]]; rewrite Hp0 in Hpc;
        [discriminate | injection Hpc as Hc0 _ _; subst c0; rewrite Hcl0 in Hclp; discriminate].
  - right. apply (ready_can_step cfg 0 Hfresh).
    + rewrite Hlive; reflexivity.
    + rewrite Hp0; discriminate.
    + unfold blocked. intros [[c0 [f0 [Hpc [Hbc _]]]] | [cs0 [Hpc _]]]; rewrite Hp0 in Hpc;
        [congruence | discriminate].
    + (* recv shape: neither CClose nor CSend head, so not panicking *)
      unfold rpanicking. intros [[c0 [k0 [Hpc _]]] | [c0 [v0 [k0 [Hpc _]]]]]; rewrite Hp0 in Hpc;
        discriminate.
  - left. intros tid Hl. rewrite Hlive in Hl. cbn in Hl.
    apply Nat.eqb_eq in Hl. subst tid. exact Hp0.
Qed.

(** Deadlock-free: NO reachable state of [sr_prog] is stuck — it always finishes or
    makes progress, even though it performs a receive (the buffered channel lets the
    send precede the receive).  Axiom-free, like the whole deadlock theory. *)
Theorem sr_never_stuck : forall cfg, rsteps sr_init cfg -> ~ RStuck cfg.
Proof.
  intros cfg Hsteps [Hnstep Hndone].
  pose proof (sr_steps_shape _ _ Hsteps sr_init_shape) as HS.
  destruct (sr_shape_progress cfg HS) as [Hd | Hc]; [exact (Hndone Hd) | exact (Hnstep Hc)].
Qed.

(** ════════════════════════════════════════════════════════════════════════════════════════════════
    BIDIRECTIONAL exchange — deadlock-free under GENUINE interleaving.
    ════════════════════════════════════════════════════════════════════════════════════════════════
    [sr_never_stuck] was ONE goroutine self-communicating — a LINEAR run.  Here TWO distinct goroutines
    each BOTH send and receive across two channels, and BOTH opening sends are concurrently enabled, so
    the reachable-state space BRANCHES (a 7-shape lattice, not a line — the diamond is shapes 4→{5,6}).
    It is the canonical "concurrent message passing", deadlock-free precisely because each goroutine
    SENDS before it blocks on a receive (the classic deadlock is the OTHER order — both receive first;
    that one genuinely gets stuck, [ex_recvfirst_stuck] below).  The test: does the manual
    reachable-shape method survive real interleaving? *)
Definition ex0  : Cmd := CSend 0 42 (CRecv 1 (fun _ => CRet)).   (* g0: send c0(42), then recv c1 *)
Definition ex0b : Cmd := CRecv 1 (fun _ => CRet).                (* g0 after its send *)
Definition ex1  : Cmd := CSend 1 43 (CRecv 0 (fun _ => CRet)).   (* g1: send c1(43), then recv c0 *)
Definition ex1b : Cmd := CRecv 0 (fun _ => CRet).                (* g1 after its send *)
Definition ex_prog : nat -> Cmd :=
  fun t => if Nat.eqb t 0 then ex0 else if Nat.eqb t 1 then ex1 else CRet.
Definition ex_init : RConfig :=
  mkRCfg ex_prog (fun _ => []) (fun _ => 0) (fun t => orb (Nat.eqb t 0) (Nat.eqb t 1)) [].

(** The 7 reachable shapes (g0-phase, g1-phase) with their forced buffers. *)
Definition EXShape (cfg : RConfig) : Prop :=
  rc_live cfg = (fun t => orb (Nat.eqb t 0) (Nat.eqb t 1))
  /\ (forall t, t <> 0 -> t <> 1 -> rc_prog cfg t = CRet)
  /\ closedb (rc_trace cfg) 0 = false
  /\ closedb (rc_trace cfg) 1 = false
  /\ ( (rc_prog cfg 0 = ex0  /\ rc_prog cfg 1 = ex1  /\ rc_bufs cfg 0 = [] /\ rc_bufs cfg 1 = [])
    \/ (rc_prog cfg 0 = ex0b /\ rc_prog cfg 1 = ex1  /\ (exists s, rc_bufs cfg 0 = [(42,s)]) /\ rc_bufs cfg 1 = [])
    \/ (rc_prog cfg 0 = ex0  /\ rc_prog cfg 1 = ex1b /\ rc_bufs cfg 0 = [] /\ (exists s, rc_bufs cfg 1 = [(43,s)]))
    \/ (rc_prog cfg 0 = ex0b /\ rc_prog cfg 1 = ex1b /\ (exists s, rc_bufs cfg 0 = [(42,s)]) /\ (exists s, rc_bufs cfg 1 = [(43,s)]))
    \/ (rc_prog cfg 0 = CRet  /\ rc_prog cfg 1 = ex1b /\ (exists s, rc_bufs cfg 0 = [(42,s)]) /\ rc_bufs cfg 1 = [])
    \/ (rc_prog cfg 0 = ex0b /\ rc_prog cfg 1 = CRet  /\ rc_bufs cfg 0 = [] /\ (exists s, rc_bufs cfg 1 = [(43,s)]))
    \/ (rc_prog cfg 0 = CRet  /\ rc_prog cfg 1 = CRet  /\ rc_bufs cfg 0 = [] /\ rc_bufs cfg 1 = []) ).

(** Every goroutine's head is a send / recv / ret — kills the write/read/spawn/select/close rules. *)
Definition ex_head (c : Cmd) : Prop :=
  match c with CSend _ _ _ => True | CRecv _ _ => True | CRet => True | _ => False end.

Lemma ex_heads : forall cfg, EXShape cfg -> forall t, ex_head (rc_prog cfg t).
Proof.
  intros cfg [_ [Hidle [_ [_ Hph]]]] t.
  destruct (Nat.eq_dec t 0) as [->|H0].
  - destruct Hph as [[H _]|[[H _]|[[H _]|[[H _]|[[H _]|[[H _]|[H _]]]]]]]; rewrite H; exact I.
  - destruct (Nat.eq_dec t 1) as [->|H1].
    + destruct Hph as [[_ [H _]]|[[_ [H _]]|[[_ [H _]]|[[_ [H _]]|[[_ [H _]]|[[_ [H _]]|[_ [H _]]]]]]]];
        rewrite H; exact I.
    + rewrite (Hidle t H0 H1); exact I.
Qed.

Lemma ex_init_shape : EXShape ex_init.
Proof.
  unfold EXShape, ex_init; cbn [rc_live rc_prog rc_bufs rc_trace].
  split; [reflexivity | split; [|split; [reflexivity | split; [reflexivity |]]]].
  - intros t H0 H1. unfold ex_prog.
    destruct (Nat.eqb t 0) eqn:E0; [apply Nat.eqb_eq in E0; congruence|].
    destruct (Nat.eqb t 1) eqn:E1; [apply Nat.eqb_eq in E1; congruence|]. reflexivity.
  - left. unfold ex_prog; cbn. repeat split; reflexivity.
Qed.

(** Every shape is DONE or CAN-STEP.  In a send shape the sender steps (send always enabled, channel
    open); in a recv shape the matching buffer is non-empty so the receiver steps; shape 7 is done. *)
Lemma ex_shape_progress : forall cfg, EXShape cfg -> rdone cfg \/ rcan_step cfg.
Proof.
  intros cfg [Hlive [Hidle [Hcl0 [Hcl1 Hph]]]].
  assert (Hfresh : FreshAvail cfg) by (exists 2; rewrite Hlive; reflexivity).
  destruct Hph as [[A0 [A1 [_ _]]] | [[A0 [A1 [_ _]]] | [[A0 [A1 [_ _]]]
                | [[A0 [A1 [[s0 B0] [s1 B1]]]] | [[A0 [A1 [[s0 B0] _]]]
                | [[A0 [A1 [_ [s1 B1]]]] | [A0 [A1 [_ _]]]]]]]]].
  - (* S1 (a,a): g0 sends c0 *)
    right. apply (ready_can_step cfg 0 Hfresh).
    + rewrite Hlive; reflexivity.
    + rewrite A0; unfold ex0; discriminate.
    + unfold blocked; intros [[c0 [f0 [Hpc _]]]|[cs0 [Hpc _]]]; rewrite A0 in Hpc; unfold ex0 in Hpc; discriminate.
    + unfold rpanicking; intros [[c0 [k0 [Hpc _]]]|[c0 [v0 [k0 [Hpc Hclp]]]]]; rewrite A0 in Hpc; unfold ex0 in Hpc;
        [discriminate | injection Hpc as Hc0 _ _; subst c0; rewrite Hcl0 in Hclp; discriminate].
  - (* S2 (b,a): g1 sends c1 *)
    right. apply (ready_can_step cfg 1 Hfresh).
    + rewrite Hlive; reflexivity.
    + rewrite A1; unfold ex1; discriminate.
    + unfold blocked; intros [[c0 [f0 [Hpc _]]]|[cs0 [Hpc _]]]; rewrite A1 in Hpc; unfold ex1 in Hpc; discriminate.
    + unfold rpanicking; intros [[c0 [k0 [Hpc _]]]|[c0 [v0 [k0 [Hpc Hclp]]]]]; rewrite A1 in Hpc; unfold ex1 in Hpc;
        [discriminate | injection Hpc as Hc0 _ _; subst c0; rewrite Hcl1 in Hclp; discriminate].
  - (* S3 (a,b): g0 sends c0 *)
    right. apply (ready_can_step cfg 0 Hfresh).
    + rewrite Hlive; reflexivity.
    + rewrite A0; unfold ex0; discriminate.
    + unfold blocked; intros [[c0 [f0 [Hpc _]]]|[cs0 [Hpc _]]]; rewrite A0 in Hpc; unfold ex0 in Hpc; discriminate.
    + unfold rpanicking; intros [[c0 [k0 [Hpc _]]]|[c0 [v0 [k0 [Hpc Hclp]]]]]; rewrite A0 in Hpc; unfold ex0 in Hpc;
        [discriminate | injection Hpc as Hc0 _ _; subst c0; rewrite Hcl0 in Hclp; discriminate].
  - (* S4 (b,b): g0 receives c1 (buffer [(43,s1)] non-empty) *)
    right. apply (ready_can_step cfg 0 Hfresh).
    + rewrite Hlive; reflexivity.
    + rewrite A0; unfold ex0b; discriminate.
    + unfold blocked; intros [[c0 [f0 [Hpc [Hbc _]]]]|[cs0 [Hpc _]]]; rewrite A0 in Hpc; unfold ex0b in Hpc;
        [injection Hpc as Hc0 _; subst c0; rewrite B1 in Hbc; discriminate | discriminate].
    + unfold rpanicking; intros [[c0 [k0 [Hpc _]]]|[c0 [v0 [k0 [Hpc _]]]]]; rewrite A0 in Hpc; unfold ex0b in Hpc; discriminate.
  - (* S5 (c,b): g1 receives c0 (buffer [(42,s0)] non-empty) *)
    right. apply (ready_can_step cfg 1 Hfresh).
    + rewrite Hlive; reflexivity.
    + rewrite A1; unfold ex1b; discriminate.
    + unfold blocked; intros [[c0 [f0 [Hpc [Hbc _]]]]|[cs0 [Hpc _]]]; rewrite A1 in Hpc; unfold ex1b in Hpc;
        [injection Hpc as Hc0 _; subst c0; rewrite B0 in Hbc; discriminate | discriminate].
    + unfold rpanicking; intros [[c0 [k0 [Hpc _]]]|[c0 [v0 [k0 [Hpc _]]]]]; rewrite A1 in Hpc; unfold ex1b in Hpc; discriminate.
  - (* S6 (b,c): g0 receives c1 (buffer [(43,s1)] non-empty) *)
    right. apply (ready_can_step cfg 0 Hfresh).
    + rewrite Hlive; reflexivity.
    + rewrite A0; unfold ex0b; discriminate.
    + unfold blocked; intros [[c0 [f0 [Hpc [Hbc _]]]]|[cs0 [Hpc _]]]; rewrite A0 in Hpc; unfold ex0b in Hpc;
        [injection Hpc as Hc0 _; subst c0; rewrite B1 in Hbc; discriminate | discriminate].
    + unfold rpanicking; intros [[c0 [k0 [Hpc _]]]|[c0 [v0 [k0 [Hpc _]]]]]; rewrite A0 in Hpc; unfold ex0b in Hpc; discriminate.
  - (* S7 (c,c): DONE *)
    left. intros tid Hl. rewrite Hlive in Hl. cbn in Hl.
    apply Bool.orb_true_iff in Hl. destruct Hl as [E|E]; apply Nat.eqb_eq in E; subst tid; assumption.
Qed.

(* tiny helpers for the upd bookkeeping in the step lemma *)
Ltac upds := rewrite upd_same.
Ltac updo := first [ rewrite upd_other by discriminate | rewrite upd_other by assumption ].

(** THE STEP LEMMA — [rstep] keeps you inside the 7 shapes.  The write/read/spawn/select/close/
    select_closed rules are impossible (heads are send/recv/ret, [ex_heads]); [recv_closed] is
    impossible (channels 0,1 are never closed).  SEND and RECV walk the lattice:
    send: 1→2, 1→3, 3→4, 2→4;  recv: 4→5, 4→6, 5→7, 6→7. *)
Lemma ex_step_shape : forall cfg cfg', rstep cfg cfg' -> EXShape cfg -> EXShape cfg'.
Proof.
  intros cfg cfg' Hstep HS.
  pose proof (ex_heads cfg HS) as Hheads.
  destruct HS as [Hlive [Hidle [Hcl0 [Hcl1 Hph]]]].
  destruct Hstep as
    [ p b h lv tr tid c v k Hlv Hp Hopen
    | p b h lv tr tid c f v s brest Hlv Hp Hbc
    | p b h lv tr tid l v k Hlv Hp
    | p b h lv tr tid l f Hlv Hp
    | p b h lv tr tid child k cid Hlv Hp Hcid
    | p b h lv tr tid cases c f v s brest Hlv Hp Hin Hbc
    | p b h lv tr tid c k Hlv Hp Hopen
    | p b h lv tr tid c f pos e Hlv Hp Hbc Hpos Hek
    | p b h lv tr tid cases c f pos e Hlv Hp Hin Hbc Hpos Hek ];
    cbn [rc_live rc_prog rc_bufs rc_trace] in *;
    (* kill write/read/spawn/select/close/select_closed: their head is not a send/recv/ret *)
    try (exfalso; specialize (Hheads tid); rewrite Hp in Hheads; exact Hheads).
  - (* ── SEND ── *)
    rewrite Hlive in Hlv; cbn in Hlv; apply Bool.orb_true_iff in Hlv;
      destruct Hlv as [E|E]; apply Nat.eqb_eq in E; subst tid.
    + (* tid = 0: fires only when p0 = ex0 (shapes 1,3) *)
      destruct Hph as [H|[H|[H|[H|[H|[H|H]]]]]]; destruct H as [A0 [A1 [B0 B1]]];
        rewrite A0 in Hp; try (unfold ex0b in Hp; discriminate); try discriminate;
        unfold ex0 in Hp; injection Hp as Hc Hv Hk; subst c v k.
      * (* shape 1 → shape 2 *)  (* B0:b0=[], B1:b1=[] *)
        split; [exact Hlive | split; [ intros t Ht0 Ht1; cbn [rc_prog]; updo; exact (Hidle t Ht0 Ht1)
        | split; [ cbn [rc_trace]; rewrite closedb_app, Hcl0; reflexivity
        | split; [ cbn [rc_trace]; rewrite closedb_app, Hcl1; reflexivity
        | right; left; cbn [rc_prog rc_bufs];
          split; [ upds; reflexivity
          | split; [ updo; exact A1
          | split; [ exists (length tr); upds; rewrite B0; reflexivity
          | updo; exact B1 ]]]]]]].
      * (* shape 3 → shape 4 *)  (* B0:b0=[], B1:∃s1 *)
        destruct B1 as [s1 B1].
        split; [exact Hlive | split; [ intros t Ht0 Ht1; cbn [rc_prog]; updo; exact (Hidle t Ht0 Ht1)
        | split; [ cbn [rc_trace]; rewrite closedb_app, Hcl0; reflexivity
        | split; [ cbn [rc_trace]; rewrite closedb_app, Hcl1; reflexivity
        | right; right; right; left; cbn [rc_prog rc_bufs];
          split; [ upds; reflexivity
          | split; [ updo; exact A1
          | split; [ exists (length tr); upds; rewrite B0; reflexivity
          | exists s1; updo; exact B1 ]]]]]]].
    + (* tid = 1: fires only when p1 = ex1 (shapes 1,2) *)
      destruct Hph as [H|[H|[H|[H|[H|[H|H]]]]]]; destruct H as [A0 [A1 [B0 B1]]];
        rewrite A1 in Hp; try (unfold ex1b in Hp; discriminate); try discriminate;
        unfold ex1 in Hp; injection Hp as Hc Hv Hk; subst c v k.
      * (* shape 1 → shape 3 *)  (* B0:b0=[], B1:b1=[] *)
        split; [exact Hlive | split; [ intros t Ht0 Ht1; cbn [rc_prog]; updo; exact (Hidle t Ht0 Ht1)
        | split; [ cbn [rc_trace]; rewrite closedb_app, Hcl0; reflexivity
        | split; [ cbn [rc_trace]; rewrite closedb_app, Hcl1; reflexivity
        | right; right; left; cbn [rc_prog rc_bufs];
          split; [ updo; exact A0
          | split; [ upds; reflexivity
          | split; [ updo; exact B0
          | exists (length tr); upds; rewrite B1; reflexivity ]]]]]]].
      * (* shape 2 → shape 4 *)  (* B0:∃s0, B1:b1=[] *)
        destruct B0 as [s0 B0].
        split; [exact Hlive | split; [ intros t Ht0 Ht1; cbn [rc_prog]; updo; exact (Hidle t Ht0 Ht1)
        | split; [ cbn [rc_trace]; rewrite closedb_app, Hcl0; reflexivity
        | split; [ cbn [rc_trace]; rewrite closedb_app, Hcl1; reflexivity
        | right; right; right; left; cbn [rc_prog rc_bufs];
          split; [ updo; exact A0
          | split; [ upds; reflexivity
          | split; [ exists s0; updo; exact B0
          | exists (length tr); upds; rewrite B1; reflexivity ]]]]]]].
  - (* ── RECV ── *)
    rewrite Hlive in Hlv; cbn in Hlv; apply Bool.orb_true_iff in Hlv;
      destruct Hlv as [E|E]; apply Nat.eqb_eq in E; subst tid.
    + (* tid = 0: head ex0b = CRecv 1; fires in shapes 4,6; shape 2 has b1=[] *)
      destruct Hph as [H|[H|[H|[H|[H|[H|H]]]]]]; destruct H as [A0 [A1 [B0 B1]]];
        rewrite A0 in Hp; try (unfold ex0 in Hp; discriminate); try discriminate;
        unfold ex0b in Hp; injection Hp as Hc Hf; subst c f.
      * (* shape 2: b1 = [] contradicts Hbc *) rewrite B1 in Hbc; discriminate.
      * (* shape 4 → shape 5 *)  (* B0:∃s0, B1:∃s1 *)
        destruct B0 as [s0 B0]; destruct B1 as [s1 B1].
        rewrite B1 in Hbc; injection Hbc as Hv Hs Hrest; subst v s brest.
        split; [exact Hlive | split; [ intros t Ht0 Ht1; cbn [rc_prog]; updo; exact (Hidle t Ht0 Ht1)
        | split; [ cbn [rc_trace]; rewrite closedb_app, Hcl0; reflexivity
        | split; [ cbn [rc_trace]; rewrite closedb_app, Hcl1; reflexivity
        | right; right; right; right; left; cbn [rc_prog rc_bufs];
          split; [ upds; reflexivity
          | split; [ updo; exact A1
          | split; [ exists s0; updo; exact B0
          | upds; reflexivity ]]]]]]].
      * (* shape 6 → shape 7 *)  (* B0:b0=[], B1:∃s1 *)
        destruct B1 as [s1 B1].
        rewrite B1 in Hbc; injection Hbc as Hv Hs Hrest; subst v s brest.
        split; [exact Hlive | split; [ intros t Ht0 Ht1; cbn [rc_prog]; updo; exact (Hidle t Ht0 Ht1)
        | split; [ cbn [rc_trace]; rewrite closedb_app, Hcl0; reflexivity
        | split; [ cbn [rc_trace]; rewrite closedb_app, Hcl1; reflexivity
        | right; right; right; right; right; right; cbn [rc_prog rc_bufs];
          split; [ upds; reflexivity
          | split; [ updo; exact A1
          | split; [ updo; exact B0
          | upds; reflexivity ]]]]]]].
    + (* tid = 1: head ex1b = CRecv 0; fires in shapes 4,5; shape 3 has b0=[] *)
      destruct Hph as [H|[H|[H|[H|[H|[H|H]]]]]]; destruct H as [A0 [A1 [B0 B1]]];
        rewrite A1 in Hp; try (unfold ex1 in Hp; discriminate); try discriminate;
        unfold ex1b in Hp; injection Hp as Hc Hf; subst c f.
      * (* shape 3: b0 = [] contradicts Hbc *) rewrite B0 in Hbc; discriminate.
      * (* shape 4 → shape 6 *)  (* B0:∃s0, B1:∃s1 *)
        destruct B0 as [s0 B0]; destruct B1 as [s1 B1].
        rewrite B0 in Hbc; injection Hbc as Hv Hs Hrest; subst v s brest.
        split; [exact Hlive | split; [ intros t Ht0 Ht1; cbn [rc_prog]; updo; exact (Hidle t Ht0 Ht1)
        | split; [ cbn [rc_trace]; rewrite closedb_app, Hcl0; reflexivity
        | split; [ cbn [rc_trace]; rewrite closedb_app, Hcl1; reflexivity
        | right; right; right; right; right; left; cbn [rc_prog rc_bufs];
          split; [ updo; exact A0
          | split; [ upds; reflexivity
          | split; [ upds; reflexivity
          | exists s1; updo; exact B1 ]]]]]]].
      * (* shape 5 → shape 7 *)  (* B0:∃s0, B1:b1=[] *)
        destruct B0 as [s0 B0].
        rewrite B0 in Hbc; injection Hbc as Hv Hs Hrest; subst v s brest.
        split; [exact Hlive | split; [ intros t Ht0 Ht1; cbn [rc_prog]; updo; exact (Hidle t Ht0 Ht1)
        | split; [ cbn [rc_trace]; rewrite closedb_app, Hcl0; reflexivity
        | split; [ cbn [rc_trace]; rewrite closedb_app, Hcl1; reflexivity
        | right; right; right; right; right; right; cbn [rc_prog rc_bufs];
          split; [ updo; exact A0
          | split; [ upds; reflexivity
          | split; [ upds; reflexivity
          | updo; exact B1 ]]]]]]].
  - (* ── RECV_CLOSED ── impossible: the recv channel (0 or 1) is never closed ── *)
    rewrite Hlive in Hlv; cbn in Hlv; apply Bool.orb_true_iff in Hlv;
      destruct Hlv as [E|E]; apply Nat.eqb_eq in E; subst tid.
    + destruct Hph as [H|[H|[H|[H|[H|[H|H]]]]]]; destruct H as [A0 [A1 [B0 B1]]];
        rewrite A0 in Hp; try (unfold ex0 in Hp; discriminate); try discriminate;
        unfold ex0b in Hp; injection Hp as Hc Hf; subst c;
        exfalso; apply (closedb_false_not tr 1 Hcl1); exists pos, e; split; assumption.
    + destruct Hph as [H|[H|[H|[H|[H|[H|H]]]]]]; destruct H as [A0 [A1 [B0 B1]]];
        rewrite A1 in Hp; try (unfold ex1 in Hp; discriminate); try discriminate;
        unfold ex1b in Hp; injection Hp as Hc Hf; subst c;
        exfalso; apply (closedb_false_not tr 0 Hcl0); exists pos, e; split; assumption.
Qed.

Lemma ex_steps_shape : forall a b, rsteps a b -> EXShape a -> EXShape b.
Proof.
  intros a b H. induction H; intros HS; [exact HS|].
  apply IHrsteps. exact (ex_step_shape _ _ H HS).
Qed.

(** PAYOFF: the bidirectional, genuinely-interleaving exchange NEVER deadlocks. *)
Theorem ex_never_stuck : forall cfg, rsteps ex_init cfg -> ~ RStuck cfg.
Proof.
  intros cfg Hsteps [Hnstep Hndone].
  pose proof (ex_steps_shape _ _ Hsteps ex_init_shape) as HS.
  destruct (ex_shape_progress cfg HS) as [Hd | Hc]; [exact (Hndone Hd) | exact (Hnstep Hc)].
Qed.

(** CONTRAST: the SAME two goroutines but RECEIVE-FIRST deadlock immediately — the model faithfully
    represents the classic circular wait (each blocked on the other's not-yet-sent value). *)
Definition rf_prog : nat -> Cmd :=
  fun t => if Nat.eqb t 0 then CRecv 1 (fun _ => CSend 0 42 CRet)
           else if Nat.eqb t 1 then CRecv 0 (fun _ => CSend 1 43 CRet) else CRet.
Definition rf_init : RConfig :=
  mkRCfg rf_prog (fun _ => []) (fun _ => 0) (fun t => orb (Nat.eqb t 0) (Nat.eqb t 1)) [].

Theorem ex_recvfirst_stuck : RStuck rf_init.
Proof.
  split.
  - (* no step: both goroutines block on empty receives — use inversion so the concrete config's
       live/prog functions are substituted in (destruct on a concrete config index would not). *)
    intros [cfg' Hstep]. unfold rf_init in Hstep.
    inversion Hstep; subst; cbn in *;
      match goal with
      | [ H : (Nat.eqb ?t 0 || Nat.eqb ?t 1)%bool = true |- _ ] =>
          apply Bool.orb_true_iff in H; destruct H as [E|E]; apply Nat.eqb_eq in E; subst t
      end;
      cbn in *;
      repeat match goal with
      | [ H : CRecv _ _ = CSend _ _ _ |- _ ] => discriminate H
      | [ H : CRecv _ _ = CWrite _ _ _ |- _ ] => discriminate H
      | [ H : CRecv _ _ = CRead _ _ |- _ ] => discriminate H
      | [ H : CRecv _ _ = CSpawn _ _ |- _ ] => discriminate H
      | [ H : CRecv _ _ = CSelect _ |- _ ] => discriminate H
      | [ H : CRecv _ _ = CClose _ _ |- _ ] => discriminate H
      | [ H : CSend _ _ _ = CRecv _ _ |- _ ] => discriminate H
      | [ H : [] = (_ :: _) |- _ ] => discriminate H
      | [ H : CRecv ?c1 _ = CRecv ?c2 _ |- _ ] => injection H as -> _
      | [ H : nth_error [] ?pos = Some _ |- _ ] => destruct pos; discriminate H
      end.
  - (* not done: goroutine 0 is parked at a CRecv, not CRet *)
    intros Hd. specialize (Hd 0). unfold rf_init in Hd; cbn [rc_live rc_prog] in Hd.
    unfold rf_prog in Hd; cbn in Hd. discriminate (Hd eq_refl).
Qed.

(** ════════════════════════════════════════════════════════════════════════════════════════════════
    UNBUFFERED-CHANNEL FORCING — capacity, and the cap-0 synchronous-rendezvous semantics.
    ════════════════════════════════════════════════════════════════════════════════════════════════
    The rich [rstep] above models channels with UNBOUNDED buffers (every send always enqueues).  Go's
    real channels carry a CAPACITY: a [make(chan T, n)] holds at most [n] queued values, and an
    UNBUFFERED channel ([make(chan T)], capacity 0) holds NONE — a send on it cannot buffer, so it must
    RENDEZVOUS with a receiver (it BLOCKS until one is ready), per go.dev/ref/spec#Channel_types and the
    memory model ("The k-th receive ... happens before the k-th send completes" for unbuffered).  The
    [rendezvous_via_buffer] lemma earlier DERIVES the value-handoff, but does NOT force it (a send could
    still buffer).  This self-contained channel-fragment calculus adds the missing FORCING: a capacity
    GUARD on the async send, plus a synchronous RENDEZVOUS rule, and proves that on a capacity-0 channel
    BUFFERING IS IMPOSSIBLE (the buffer is empty in every reachable state) so every transfer is a direct
    handshake — and an unbuffered send with no waiting receiver is STUCK (the blocking behaviour).

    Scope is honest and bounded: this models the channel fragment ([CSend]/[CRecv]) only — enough to
    state and prove the forcing.  Integrating [cap] into the full [rstep] (heap/spawn/select) is a
    separate cascade (it adds an [rc_cap] field to [RConfig], touched at ~42 [mkRCfg] sites) and is
    deferred; the SEMANTICS that was missing — unbuffered = synchronous-only + blocking — is HERE. *)
Section BoundedChannels.

(** [cap c] = capacity of channel [c]; [cap c = 0] is an UNBUFFERED channel. *)
Variable cap : nat -> nat.

(** Channel-fragment config: per-goroutine program, per-channel value buffer, liveness. *)
Record CConfig := mkCC { cc_prog : nat -> Cmd; cc_bufs : nat -> list nat; cc_live : nat -> bool }.

Inductive cstep : CConfig -> CConfig -> Prop :=
  (* ASYNC send — enqueue, but ONLY when the buffer has ROOM ([length < cap]).  For [cap c = 0] the
     guard [length (b c) < 0] is UNSATISFIABLE, so an unbuffered channel can never buffer. *)
  | cstep_send : forall p b lv tid c v k,
      lv tid = true -> p tid = CSend c v k -> length (b c) < cap c ->
      cstep (mkCC p b lv) (mkCC (upd p tid k) (upd b c (b c ++ [v])) lv)
  (* RECV — dequeue the FIFO head (buffer non-empty). *)
  | cstep_recv : forall p b lv tid c f v rest,
      lv tid = true -> p tid = CRecv c f -> b c = v :: rest ->
      cstep (mkCC p b lv) (mkCC (upd p tid (f v)) (upd b c rest) lv)
  (* SYNCHRONOUS rendezvous — a sender and a DISTINCT receiver on the same channel step TOGETHER, the
     value passing DIRECTLY (buffer unchanged).  Guarded by [b c = []] so it never bypasses a buffered
     value (FIFO stays honest); for an unbuffered channel that guard always holds, and this is the ONLY
     enabled transfer. *)
  | cstep_sync : forall p b lv ts tr c v k f,
      lv ts = true -> lv tr = true -> ts <> tr ->
      p ts = CSend c v k -> p tr = CRecv c f -> b c = [] ->
      cstep (mkCC p b lv) (mkCC (upd (upd p ts k) tr (f v)) b lv).

Inductive csteps : CConfig -> CConfig -> Prop :=
  | csteps_refl : forall s, csteps s s
  | csteps_step : forall a b c, cstep a b -> csteps b c -> csteps a c.

(** FORCING (one step): a capacity-0 channel's buffer that is empty STAYS empty — async send can't
    fire (guard unsatisfiable), recv needs a non-empty buffer (vacuous), sync leaves the buffer alone. *)
Lemma cstep_cap0_buf : forall ch s s',
  cap ch = 0 -> cstep s s' -> cc_bufs s ch = [] -> cc_bufs s' ch = [].
Proof.
  intros ch s s' Hcap Hstep Hempty.
  destruct Hstep as [p b lv tid c v k Hlv Hp Hroom
                    | p b lv tid c f v rest Hlv Hp Hbc
                    | p b lv ts tr c v k f Hlvs Hlvr Hne Hps Hpr Hbc];
    cbn in Hempty |- *.
  - (* send *) destruct (Nat.eq_dec ch c) as [->|Hne].
    + exfalso. rewrite Hcap in Hroom. lia.
    + rewrite upd_other by exact Hne. exact Hempty.
  - (* recv *) destruct (Nat.eq_dec ch c) as [->|Hne].
    + rewrite Hempty in Hbc. discriminate.
    + rewrite upd_other by exact Hne. exact Hempty.
  - (* sync: buffer unchanged *) exact Hempty.
Qed.

(** FORCING (whole execution): an unbuffered channel NEVER buffers along ANY run from an empty buffer. *)
Lemma csteps_cap0_buf : forall ch s s',
  cap ch = 0 -> csteps s s' -> cc_bufs s ch = [] -> cc_bufs s' ch = [].
Proof.
  intros ch s s' Hcap Hsteps. induction Hsteps as [|a b d Hab Hbd IH]; intros Hempty.
  - exact Hempty.
  - apply IH. exact (cstep_cap0_buf ch a b Hcap Hab Hempty).
Qed.

(** BLOCKING — the unbuffered send blocks until a receiver.  GENERAL form: in an unbuffered world,
    a config where EVERY live goroutine is parked at a SEND (and all buffers empty) is STUCK — async
    send is forbidden (cap-0 guard), recv/rendezvous need a receiver and there is none.  The
    operational content of "an unbuffered send with no ready receiver deadlocks". *)
Lemma all_senders_stuck : forall s,
  (forall ch, cap ch = 0) ->
  (forall ch, cc_bufs s ch = []) ->
  (forall tid, cc_live s tid = true -> exists c v k, cc_prog s tid = CSend c v k) ->
  ~ exists s', cstep s s'.
Proof.
  intros s Hcap Hbuf Hsend [s' Hstep].
  destruct Hstep as [p b lv tid c v k Hlv Hp Hroom
                    | p b lv tid c f v rest Hlv Hp Hbc
                    | p b lv ts tr c v k f Hlvs Hlvr Hne Hps Hpr Hbc].
  - (* send: guard [length (b c) < cap c], but [cap c = 0] *) rewrite Hcap in Hroom. lia.
  - (* recv: this goroutine is a SEND, not a CRecv *)
    destruct (Hsend tid Hlv) as [c0 [v0 [k0 Hps]]]. cbn in Hps. congruence.
  - (* sync: the would-be RECEIVER is a SEND *)
    destruct (Hsend tr Hlvr) as [c0 [v0 [k0 Hps0]]]. cbn in Hps0. congruence.
Qed.

(** Concrete witness: two goroutines both SEND on unbuffered channel 0, nobody receives → STUCK. *)
Corollary ublock_stuck : (forall ch, cap ch = 0) ->
  ~ exists s', cstep (mkCC (fun t => CSend 0 (if Nat.eqb t 0 then 7 else 8) CRet)
                           (fun _ => []) (fun t => orb (Nat.eqb t 0) (Nat.eqb t 1))) s'.
Proof.
  intros Hcap. apply all_senders_stuck; cbn.
  - exact Hcap.
  - intros ch. reflexivity.
  - intros tid _. exists 0, (if Nat.eqb tid 0 then 7 else 8), CRet. reflexivity.
Qed.

(** RENDEZVOUS fires — on the SAME unbuffered channel, a sender (g0) and a receiver (g1) step together
    even though buffering is impossible: the synchronous handshake is the cap-0 transfer mechanism. *)
Definition urv_cfg : CConfig :=
  mkCC (fun t => if Nat.eqb t 0 then CSend 0 42 CRet else CRecv 0 (fun _ => CRet))
       (fun _ => [])
       (fun t => orb (Nat.eqb t 0) (Nat.eqb t 1)).

Lemma urv_can_sync : exists s', cstep urv_cfg s'.
Proof.
  eexists. unfold urv_cfg.
  eapply cstep_sync with (ts := 0) (tr := 1);
    [ reflexivity | reflexivity | discriminate | reflexivity | reflexivity | reflexivity ].
Qed.

(** SAFETY — the buffer NEVER exceeds its capacity (no overflow): [cstep_send] fires only with ROOM
    ([length < cap], so the post-length [S length ≤ cap]), [cstep_recv] shrinks, [cstep_sync] leaves
    the buffer.  This is the bounded-buffer invariant Go's runtime enforces. *)
Lemma cstep_cap_respected : forall ch s s',
  cstep s s' -> length (cc_bufs s ch) <= cap ch -> length (cc_bufs s' ch) <= cap ch.
Proof.
  intros ch s s' Hstep Hle.
  destruct Hstep as [p b lv tid c v k Hlv Hp Hroom
                    | p b lv tid c f v rest Hlv Hp Hbc
                    | p b lv ts tr c v k f Hlvs Hlvr Hne Hps Hpr Hbc];
    cbn in Hle |- *.
  - (* send: post-length = S (length (b c)) ≤ cap c since [length (b c) < cap c] *)
    destruct (Nat.eq_dec ch c) as [->|Hne].
    + rewrite upd_same, length_app. cbn. lia.
    + rewrite upd_other by exact Hne. exact Hle.
  - (* recv: the buffer only shrinks *)
    destruct (Nat.eq_dec ch c) as [->|Hne].
    + rewrite upd_same. rewrite Hbc in Hle. cbn in Hle. lia.
    + rewrite upd_other by exact Hne. exact Hle.
  - (* sync: buffer unchanged *) exact Hle.
Qed.

Lemma csteps_cap_respected : forall ch s s',
  csteps s s' -> length (cc_bufs s ch) <= cap ch -> length (cc_bufs s' ch) <= cap ch.
Proof.
  intros ch s s' Hsteps. induction Hsteps as [|a b d Hab Hbd IH]; intros Hle.
  - exact Hle.
  - apply IH. exact (cstep_cap_respected ch a b Hab Hle).
Qed.

(** Starting from empty buffers, EVERY reachable buffer respects its capacity — overflow is impossible
    along any run. *)
Corollary csteps_from_empty_cap_respected : forall ch s s',
  (forall c, cc_bufs s c = []) -> csteps s s' -> length (cc_bufs s' ch) <= cap ch.
Proof.
  intros ch s s' Hempty Hsteps.
  apply (csteps_cap_respected ch s s' Hsteps). rewrite Hempty. cbn. lia.
Qed.

(** LIVENESS dual of [all_senders_stuck] — a BUFFERED send with ROOM never blocks: a goroutine parked
    at [CSend c] on a channel with [length (buf c) < cap c] can ALWAYS step (async enqueue).  So
    capacity > current length ⇒ progress, while capacity 0 ⇒ block — the two halves of Go's channel
    blocking semantics. *)
Lemma buffered_send_progresses : forall s tid c v k,
  cc_live s tid = true -> cc_prog s tid = CSend c v k -> length (cc_bufs s c) < cap c ->
  exists s', cstep s s'.
Proof.
  intros [p b lv] tid c v k Hlv Hp Hroom. cbn in *.
  eexists. eapply cstep_send; eassumption.
Qed.

End BoundedChannels.
