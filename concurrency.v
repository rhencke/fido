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

(** ── DYNAMIC-SPAWN OWNERSHIP TRANSFER (trace core) ───────────────────────────
    [mp_trace]'s handoff has BOTH goroutines pre-live.  Here the reader is SPAWNED by the writer and
    the location is handed to that freshly-created child — the genuinely harder shape that
    [mp_all_interleavings_race_free]'s preamble flags as the dynamic-tid frontier.  Thread 0 writes x
    (loc 0), SPAWNS child [cid], then sends on chan 0; the child STARTS (its [KStart] back-points at
    the spawn — the child-identity edge [WfTrace] demands), receives c0 (matched send at pos 3), then
    reads x.  The only conflicting cross-goroutine pair (g0's write / the child's read of x) is ordered
    by the channel handoff carried ACROSS the spawn boundary: write →po→ send →sync→ recv →po→ read.
    These three witnesses certify the dynamic-spawn handoff trace is well-formed (back-pointers valid,
    incl. KStart→KSpawn) and race-free regardless of which fresh tid the runtime hands the child.  The
    all-interleavings invariant over the spawning PROGRAM (a [MpReach]-style inductive reachability with
    the child tid existentially quantified) is the follow-on slice. ── *)
Definition dst_trace (cid : nat) : Trace :=
  [ mkEv 0 (KWrite 0)       (* pos 0: thread 0 writes x         *)
  ; mkEv 0 (KSpawn cid)     (* pos 1: thread 0 spawns child cid *)
  ; mkEv cid (KStart 1)     (* pos 2: child starts (spawn = pos 1) *)
  ; mkEv 0 (KSend 0)        (* pos 3: thread 0 sends on c0      *)
  ; mkEv cid (KRecv 0 3)    (* pos 4: child recvs c0 (from = pos 3) *)
  ; mkEv cid (KRead 0) ].   (* pos 5: child reads x             *)

Lemma dst_trace_wf : forall cid, WfTrace (dst_trace cid).
Proof.
  intros cid i e H.
  destruct i as [|[|[|[|[|[|i]]]]]].
  - cbn in H; inversion H; subst; cbn; exact I.
  - cbn in H; inversion H; subst; cbn; exact I.
  - cbn in H; inversion H; subst; cbn.
    split; [lia | exists (mkEv 0 (KSpawn cid)); split; reflexivity].
  - cbn in H; inversion H; subst; cbn; exact I.
  - cbn in H; inversion H; subst; cbn.
    split; [lia | exists (mkEv 0 (KSend 0)); split; [reflexivity | left; reflexivity]].
  - cbn in H; inversion H; subst; cbn; exact I.
  - apply nth_error_lt in H; cbn in H; lia.
Qed.

(** The write happens-before the read, through the channel handoff carried across the spawn. *)
Lemma dst_trace_hb_0_5 : forall cid, hbt (dst_trace cid) 0 5.
Proof.
  intro cid.
  apply hbt_trans with (j := 3).
  - apply hbt_po. unfold po, tid_at; cbn. repeat split; lia.
  - apply hbt_trans with (j := 4).
    + apply hbt_sync. unfold sync. exists (mkEv cid (KRecv 0 3)). cbn. split; reflexivity.
    + apply hbt_po. unfold po, tid_at; cbn. repeat split; lia.
Qed.

(** The dynamic-spawn handoff PROGRAM is whole-trace race-free: its only conflicting cross-goroutine
    pair (the write/read of x) is ordered by the channel handoff — for ANY fresh child tid. *)
Theorem dst_trace_race_free : forall cid, TraceRaceFree (dst_trace cid).
Proof.
  intros cid i j [Htid [[ai [aj [Hai [Haj _]]]] [Hnij Hnji]]].
  pose proof (tr_acc_lt _ _ _ Hai) as Hi. pose proof (tr_acc_lt _ _ _ Haj) as Hj.
  cbn in Hi, Hj.
  destruct i as [|[|[|[|[|[|i]]]]]]; try lia;
  destruct j as [|[|[|[|[|[|j]]]]]]; try lia;
    cbn in Hai, Haj, Htid;
    try discriminate Hai; try discriminate Haj;
    try (apply Htid; reflexivity).
  - apply Hnij. exact (dst_trace_hb_0_5 cid).   (* i=0 (write), j=5 (read) *)
  - apply Hnji. exact (dst_trace_hb_0_5 cid).   (* i=5 (read),  j=0 (write) *)
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

(** ============================================================================
    LIMIT #2 — PART 2, brick 1: PRIVATE-MEMORY DISCIPLINE ⇒ reachable race-freedom
    (the ABSTRACT-OWNERSHIP base case — arbitrary N, an INDUCTIVE INVARIANT, no
    per-program state-enumeration).

    The trace disciplines (LocPrivate / HandoffDisciplined / SyncDisciplined) say a
    GIVEN trace is [Owned]; [reachable_owned_safe_r] still needs [Owned] as a HYPOTHESIS.
    This brick EARNS race-freedom from a STRUCTURAL PROGRAM property, for an arbitrary
    number of goroutines, the way the general N-goroutine theorem must — a Keller-style
    invariant preserved by EVERY [rstep], NOT a per-program phase enumeration (which
    explodes).  It is the CSL ownership base case: OWNERSHIP WITHOUT TRANSFER.

    Discipline: a static owner map [own : loc -> tid] gives each location ONE owner, and
    every goroutine's program only ever reads/writes locations IT owns ([OnlyAcc]).  Then
    no two goroutines ever touch one location, so every reachable trace is [LocPrivate] —
    hence [Owned], hence race-free — for ANY number of goroutines.  Spawn is admitted for a
    MEMORY-FREE child ([OA_spawn] + [MemFree] below): a channel-only goroutine touches no heap,
    so it owns nothing and cannot race — DYNAMIC [CSpawn] of such a child preserves the discipline
    (the bounded first step past the spawn-free base).  Ownership-SPLIT (a child that inherits SOME
    of the parent's locations) and ownership-TRANSFER on send→recv remain the next bricks.
    Proof-only (concurrency.v emits no Go). *)

(* A [MemFree] command touches NO shared memory — only channels (send/recv/select/close), spawn of
   further memory-free children, and return.  A memory-free goroutine is vacuously [OnlyAcc P] for ANY
   owner [P] ([memfree_onlyacc]), so the private-memory discipline can admit its DYNAMIC spawn without a
   dynamic owner map (the channel-relay goroutines of the cursed demo are exactly this shape). *)
Inductive MemFree : Cmd -> Prop :=
  | MF_ret    : MemFree CRet
  | MF_send   : forall c v k, MemFree k -> MemFree (CSend c v k)
  | MF_recv   : forall c f, (forall v, MemFree (f v)) -> MemFree (CRecv c f)
  | MF_select : forall cases, (forall c f, In (c, f) cases -> forall v, MemFree (f v)) ->
                  MemFree (CSelect cases)
  | MF_close  : forall c k, MemFree k -> MemFree (CClose c k)
  | MF_spawn  : forall child k, MemFree child -> MemFree k -> MemFree (CSpawn child k).
  (* NO MF_write / MF_read — a memory-free command never accesses the heap. *)

Inductive OnlyAcc (P : nat -> Prop) : Cmd -> Prop :=
  | OA_ret    : OnlyAcc P CRet
  | OA_send   : forall c v k, OnlyAcc P k -> OnlyAcc P (CSend c v k)
  | OA_recv   : forall c f, (forall v, OnlyAcc P (f v)) -> OnlyAcc P (CRecv c f)
  | OA_write  : forall l v k, P l -> OnlyAcc P k -> OnlyAcc P (CWrite l v k)
  | OA_read   : forall l f, P l -> (forall v, OnlyAcc P (f v)) -> OnlyAcc P (CRead l f)
  | OA_select : forall cases, (forall c f, In (c, f) cases -> forall v, OnlyAcc P (f v)) ->
                  OnlyAcc P (CSelect cases)
  | OA_close  : forall c k, OnlyAcc P k -> OnlyAcc P (CClose c k)
  | OA_spawn  : forall child k, MemFree child -> OnlyAcc P k -> OnlyAcc P (CSpawn child k).
  (* OA_spawn: a disciplined goroutine may SPAWN a MEMORY-FREE child (it owns no heap, cannot race),
     then continue under its own ownership — admitting dynamic [CSpawn] for channel-only children. *)

(* Per-constructor inversions (used in the preservation proof). *)
Lemma oa_send_inv : forall P c v k, OnlyAcc P (CSend c v k) -> OnlyAcc P k.
Proof. intros P c v k H. inversion H; subst. assumption. Qed.
Lemma oa_recv_inv : forall P c f, OnlyAcc P (CRecv c f) -> forall v, OnlyAcc P (f v).
Proof. intros P c f H. inversion H; subst. assumption. Qed.
Lemma oa_write_inv : forall P l v k, OnlyAcc P (CWrite l v k) -> P l /\ OnlyAcc P k.
Proof. intros P l v k H. inversion H; subst. split; assumption. Qed.
Lemma oa_read_inv : forall P l f, OnlyAcc P (CRead l f) -> P l /\ (forall v, OnlyAcc P (f v)).
Proof. intros P l f H. inversion H; subst. split; assumption. Qed.
Lemma oa_close_inv : forall P c k, OnlyAcc P (CClose c k) -> OnlyAcc P k.
Proof. intros P c k H. inversion H; subst. assumption. Qed.
Lemma oa_select_inv : forall P cases, OnlyAcc P (CSelect cases) ->
  forall c f, In (c, f) cases -> forall v, OnlyAcc P (f v).
Proof. intros P cases H. inversion H; subst. assumption. Qed.
Lemma oa_spawn_inv : forall P child k, OnlyAcc P (CSpawn child k) -> MemFree child /\ OnlyAcc P k.
Proof. intros P child k H. inversion H; subst. split; assumption. Qed.

(* A memory-free command is [OnlyAcc] for EVERY owner predicate — it constrains no location. *)
Lemma memfree_onlyacc : forall c, MemFree c -> forall P, OnlyAcc P c.
Proof.
  intros c H. induction H as
    [ | c v k _ IHk | c f _ IHf | cases _ IHcs | c k _ IHk | child k Hchild _ _ IHk ];
    intros P.
  - apply OA_ret.
  - apply OA_send. apply IHk.
  - apply OA_recv. intros v. apply IHf.
  - apply OA_select. intros c0 f Hin v. apply (IHcs c0 f Hin v).
  - apply OA_close. apply IHk.
  - apply OA_spawn; [ exact Hchild | apply IHk ].
Qed.

(* Each location's owning goroutine; goroutine [g] may access [l] iff [own l = g]. *)
Definition PrivateDisc (own : nat -> nat) (cfg : RConfig) : Prop :=
  (forall i l, acc_loc_at (rc_trace cfg) i = Some l -> tid_at (rc_trace cfg) i = own l)
  /\ (forall g, rc_live cfg g = true -> OnlyAcc (fun l => own l = g) (rc_prog cfg g)).

(* Trace-append helpers for [tid_at] / [acc_loc_at] (old positions unchanged; the new one reads the event). *)
Lemma tid_at_app1 : forall (t : Trace) e i, i < length t -> tid_at (t ++ [e]) i = tid_at t i.
Proof. intros t e i Hi. unfold tid_at. rewrite nth_error_app1 by exact Hi. reflexivity. Qed.
Lemma acc_loc_at_app1 : forall (t : Trace) e i, i < length t -> acc_loc_at (t ++ [e]) i = acc_loc_at t i.
Proof. intros t e i Hi. unfold acc_loc_at. rewrite nth_error_app1 by exact Hi. reflexivity. Qed.
Lemma tid_at_app_new : forall (t : Trace) e, tid_at (t ++ [e]) (length t) = e_tid e.
Proof. intros t e. unfold tid_at. rewrite nth_error_app_new. reflexivity. Qed.
Lemma acc_loc_at_app_new : forall (t : Trace) e,
  acc_loc_at (t ++ [e]) (length t) =
  match e_kind e with KWrite l => Some l | KRead l => Some l | _ => None end.
Proof. intros t e. unfold acc_loc_at. rewrite nth_error_app_new. reflexivity. Qed.

(** ============================================================================
    INCREMENTAL [Owned] — the reusable core for the GENERAL dynamic-ownership invariant.

    The per-program transfer witnesses ([mp]/[fork]/[xfer]/[dst]) all establish [Owned] by
    WHOLE-TRACE phase enumeration (a [...Reach] disjunction over the finitely-many reachable
    states), which does NOT generalise to arbitrary programs (phase explosion).  The abstract
    invariant instead needs [Owned] preserved ONE APPENDED ACCESS AT A TIME, so that an
    [rstep]-indexed induction can carry it.  [owned_snoc] is that step: appending a memory
    access to location [L] preserves [Owned] PROVIDED the new access is happens-before-after
    EVERY prior access to [L] (its only new conflicting partners).  [owned_step_snoc] then
    reduces that to a SINGLE per-step obligation — happens-before from the location's PREVIOUS
    access ([lp L], the last-position map) to the new one — by carrying the auxiliary
    [AccBeforeLast] invariant (every past access hb-before its location's latest).  This is
    exactly the obligation a dynamic OWNER argument discharges (same owner ⇒ program order;
    transferred owner ⇒ the send/recv or spawn/start synchronisation edge), so it is the clean
    interface between the trace-level race theory and the forthcoming ownership-transfer
    reachability proof.  All [hbt]-based and append-monotone — no [WfTrace] needed.
    ============================================================================ *)

(* The newly-appended event's accessed location, when it IS a memory access. *)
Lemma acc_new_L : forall (t : Trace) e L,
  (e_kind e = KWrite L \/ e_kind e = KRead L) ->
  acc_loc_at (t ++ [e]) (length t) = Some L.
Proof. intros t e L He. rewrite acc_loc_at_app_new. destruct He as [H|H]; rewrite H; reflexivity. Qed.

(* Append-monotonicity of the happens-before relation and its components: an edge among
   OLD positions survives appending a new event (the new event only adds forward edges). *)
Lemma po_app1 : forall (t : Trace) e i j, po t i j -> po (t ++ [e]) i j.
Proof.
  intros t e i j H. destruct H as [Hij [Hj Htid]].
  assert (Hi : i < length t) by lia.
  split; [exact Hij | split].
  - rewrite length_app. cbn. lia.
  - rewrite (tid_at_app1 t e i Hi), (tid_at_app1 t e j Hj). exact Htid.
Qed.

Lemma sync_app1 : forall (t : Trace) e i j, sync t i j -> sync (t ++ [e]) i j.
Proof.
  intros t e i j [ev [Hnth Hk]]. exists ev. split; [| exact Hk].
  pose proof (nth_error_lt _ _ _ Hnth) as Hj.
  rewrite nth_error_app1 by exact Hj. exact Hnth.
Qed.

Lemma hbt_app1 : forall (t : Trace) e i j, hbt t i j -> hbt (t ++ [e]) i j.
Proof.
  intros t e i j H. induction H as [i j Hpo | i j Hsy | i j k Hij IHij Hjk IHjk].
  - apply hbt_po. apply po_app1. exact Hpo.
  - apply hbt_sync. apply sync_app1. exact Hsy.
  - apply hbt_trans with (j := j); [exact IHij | exact IHjk].
Qed.

Lemma same_loc_app1 : forall (t : Trace) e i j,
  i < length t -> j < length t -> same_loc t i j -> same_loc (t ++ [e]) i j.
Proof.
  intros t e i j Hi Hj [l [Hil Hjl]]. exists l.
  rewrite (acc_loc_at_app1 t e i Hi), (acc_loc_at_app1 t e j Hj). split; [exact Hil | exact Hjl].
Qed.

Lemma same_loc_app1_inv : forall (t : Trace) e i j,
  i < length t -> j < length t -> same_loc (t ++ [e]) i j -> same_loc t i j.
Proof.
  intros t e i j Hi Hj [l [Hil Hjl]]. exists l.
  rewrite (acc_loc_at_app1 t e i Hi) in Hil. rewrite (acc_loc_at_app1 t e j Hj) in Hjl.
  split; [exact Hil | exact Hjl].
Qed.

(* THE INCREMENTAL STEP (all-past form): appending an access to [L] preserves [Owned], given the
   new access is hb-after every prior access to [L].  Old conflicting pairs are unchanged; the
   only new pairs put the appended access last, and a non-latest old partner is separated by the
   latest one ([Owned]'s "exists [k] strictly between" disjunct). *)
Lemma owned_snoc : forall (t : Trace) e L,
  Owned t ->
  (e_kind e = KWrite L \/ e_kind e = KRead L) ->
  (forall i, i < length t -> acc_loc_at t i = Some L -> hbt (t ++ [e]) i (length t)) ->
  Owned (t ++ [e]).
Proof.
  intros t e L HO He Hnew i j Hij Hsl.
  assert (Hjlen : j < length (t ++ [e])).
  { destruct Hsl as [l [_ Hjl]]. exact (acc_loc_at_lt _ _ _ Hjl). }
  rewrite length_app in Hjlen; cbn in Hjlen.
  destruct (Nat.eq_dec j (length t)) as [Hjeq | Hjne].
  - (* the new access is the later partner *)
    subst j. left.
    destruct Hsl as [l [Hil Hjl]].
    rewrite (acc_new_L t e L He) in Hjl. injection Hjl as Hll. subst l.
    assert (Hi : i < length t) by lia.
    rewrite (acc_loc_at_app1 t e i Hi) in Hil.
    exact (Hnew i Hi Hil).
  - (* both partners are old positions — defer to [Owned t] and lift across the append *)
    assert (Hjlt : j < length t) by lia.
    assert (Hilt : i < length t) by lia.
    pose proof (same_loc_app1_inv t e i j Hilt Hjlt Hsl) as Hslt.
    destruct (HO i j Hij Hslt) as [Hhb | [k [[Hik Hkj] [Hsik Hskj]]]].
    + left. apply hbt_app1. exact Hhb.
    + right. exists k. assert (Hklt : k < length t) by lia.
      split; [split; [exact Hik | exact Hkj] | split].
      * apply same_loc_app1; [exact Hilt | exact Hklt | exact Hsik].
      * apply same_loc_app1; [exact Hklt | exact Hjlt | exact Hskj].
Qed.

(* The last-position map [lp]: [lp L] is a trace position accessing [L] (the LATEST one, as the
   invariants below force).  [upd_lastpos] bumps it to the new event's position on each access. *)
Definition upd_lastpos (lp : nat -> nat) (L p : nat) : nat -> nat :=
  fun L'' => if Nat.eqb L'' L then p else lp L''.
Lemma upd_lastpos_same : forall lp L p, upd_lastpos lp L p L = p.
Proof. intros. unfold upd_lastpos. rewrite Nat.eqb_refl. reflexivity. Qed.
Lemma upd_lastpos_other : forall lp L p L'', L'' <> L -> upd_lastpos lp L p L'' = lp L''.
Proof. intros lp L p L'' Hne. unfold upd_lastpos. apply Nat.eqb_neq in Hne. rewrite Hne. reflexivity. Qed.

(* [lp L] is a genuine access position for every accessed [L]. *)
Definition LastPosValid (t : Trace) (lp : nat -> nat) : Prop :=
  forall L, (exists i, acc_loc_at t i = Some L) -> acc_loc_at t (lp L) = Some L.

(* Every access is at, or happens-before, its location's recorded latest access. *)
Definition AccBeforeLast (t : Trace) (lp : nat -> nat) : Prop :=
  forall L i, acc_loc_at t i = Some L -> i = lp L \/ hbt t i (lp L).

(* THE PACKAGED INCREMENTAL STEP: with [AccBeforeLast] carried, preserving [Owned] across one new
   access to [L] reduces to the SINGLE obligation [hbt (t ++ [e]) (lp L) (length t)] — the new
   access is hb-after [L]'s PREVIOUS access.  Returns the updated invariants for the next step. *)
Lemma owned_step_snoc : forall (t : Trace) e L lp,
  Owned t -> LastPosValid t lp -> AccBeforeLast t lp ->
  (e_kind e = KWrite L \/ e_kind e = KRead L) ->
  ((exists i, acc_loc_at t i = Some L) -> hbt (t ++ [e]) (lp L) (length t)) ->
  Owned (t ++ [e])
  /\ LastPosValid (t ++ [e]) (upd_lastpos lp L (length t))
  /\ AccBeforeLast (t ++ [e]) (upd_lastpos lp L (length t)).
Proof.
  intros t e L lp HO HV HB He Hobl.
  (* discharge [owned_snoc]'s all-past hypothesis from [AccBeforeLast] + the single obligation *)
  assert (Hall : forall i, i < length t -> acc_loc_at t i = Some L -> hbt (t ++ [e]) i (length t)).
  { intros i Hi Hacc.
    assert (Hex : exists i0, acc_loc_at t i0 = Some L) by (exists i; exact Hacc).
    specialize (Hobl Hex).
    destruct (HB L i Hacc) as [Heq | Hhb].
    - rewrite Heq. exact Hobl.
    - exact (hbt_trans (t ++ [e]) i (lp L) (length t) (hbt_app1 t e i (lp L) Hhb) Hobl). }
  pose proof (owned_snoc t e L HO He Hall) as HOt'.
  split; [exact HOt' | split].
  - (* LastPosValid carries: bumped location reads the new event; others unchanged and still valid *)
    intros L'' [j Hj].
    destruct (Nat.eq_dec L'' L) as [-> | Hne].
    + rewrite upd_lastpos_same. exact (acc_new_L t e L He).
    + rewrite (upd_lastpos_other lp L (length t) L'' Hne).
      assert (HaccT : exists i, acc_loc_at t i = Some L'').
      { destruct (Nat.lt_ge_cases j (length t)) as [Hjl | Hjg].
        - exists j. rewrite (acc_loc_at_app1 t e j Hjl) in Hj. exact Hj.
        - exfalso. pose proof (acc_loc_at_lt _ _ _ Hj) as Hb.
          rewrite length_app in Hb; cbn in Hb.
          assert (Hjeq : j = length t) by lia. subst j.
          rewrite (acc_new_L t e L He) in Hj. injection Hj as Hll. apply Hne. symmetry; exact Hll. }
      pose proof (HV L'' HaccT) as HvL''.
      pose proof (acc_loc_at_lt _ _ _ HvL'') as Hlt.
      rewrite (acc_loc_at_app1 t e (lp L'') Hlt). exact HvL''.
  - (* AccBeforeLast carries: new access is its own latest; old accesses keep their witness *)
    intros L'' i Hi.
    destruct (Nat.lt_ge_cases i (length t)) as [Hil | Hig].
    + rewrite (acc_loc_at_app1 t e i Hil) in Hi.
      destruct (Nat.eq_dec L'' L) as [-> | Hne].
      * rewrite upd_lastpos_same. right. exact (Hall i Hil Hi).
      * rewrite (upd_lastpos_other lp L (length t) L'' Hne).
        destruct (HB L'' i Hi) as [Heq | Hhb].
        -- left. exact Heq.
        -- right. exact (hbt_app1 t e i (lp L'') Hhb).
    + pose proof (acc_loc_at_lt _ _ _ Hi) as Hb. rewrite length_app in Hb; cbn in Hb.
      assert (Hieq : i = length t) by lia. subst i.
      rewrite (acc_new_L t e L He) in Hi. injection Hi as Hll. subst L''.
      left. rewrite upd_lastpos_same. reflexivity.
Qed.

(* Sanity that [owned_snoc] APPLIES: one goroutine writes loc 9 then reads it — the read at pos 1
   is hb-after the write at pos 0 by program order, so [Owned] holds, built incrementally. *)
Definition seq_acc_trace : Trace := [mkEv 0 (KWrite 9); mkEv 0 (KRead 9)].
Lemma seq_acc_owned : Owned seq_acc_trace.
Proof.
  change seq_acc_trace with ([mkEv 0 (KWrite 9)] ++ [mkEv 0 (KRead 9)]).
  apply (owned_snoc [mkEv 0 (KWrite 9)] (mkEv 0 (KRead 9)) 9).
  - intros i j Hij Hsl. exfalso.
    destruct Hsl as [l [_ Hjl]]. pose proof (acc_loc_at_lt _ _ _ Hjl) as Hj. cbn in Hj. lia.
  - right. reflexivity.
  - intros i Hi Hacc. cbn in Hi. assert (i = 0) by lia. subst i.
    apply hbt_po. unfold po, tid_at. cbn. repeat split; lia.
Qed.

(** ============================================================================
    OWNERSHIP-TRANSFER DISCHARGE — turning [owned_step_snoc]'s per-step obligation into the
    OWNER argument.  [owned_step_snoc] reduced preserving [Owned] across a new access to a single
    obligation: [hbt (t ++ [e]) (lp L) (length t)] (the new access is hb-after L's PREVIOUS access).
    [AcqConn] is the per-location witness a dynamic OWNER carries to discharge it: location [L] is
    held by goroutine [g], and L's last access [lp L] is hb-connected to a position [acq L] that is
    [g]'s own — program-ordered before whatever [g] does next.  Three transitions, proved standalone
    (no [WfTrace], axiom-free), are the trace-level moves the forthcoming config invariant
    [region_inv_step] threads over [rstep]:
      - [acqconn_hbt_new]   : any new [g]-event after [acq L] is hb-after [lp L] — discharges an
                              ACCESS's obligation AND supplies a SEND's buffer hb-support (one lemma);
      - [owned_step_by_owner]: composing it INTO [owned_step_snoc] — an OWNER's access preserves
                              [Owned] (the core safety step of the transfer reachability proof);
      - [acqconn_after_access]: after [g] accesses [L], the connection re-establishes at the new pos;
      - [recv_establishes_acqconn]: a RECV acquires [L] — the buffer carried the sender's support
                              [hbt t (lp L) s], the recv's back-pointer is [s], so the new owner is
                              connected through the send→recv [sync] edge.
    [WT] (below) is the matching PROGRAM discipline: a LINEAR region-threading typing — send RELEASES
    the sent location, recv ACQUIRES it ([OnlyAcc] is non-linear, so cannot express transfer).
    ============================================================================ *)

Definition AcqConn (t : Trace) (lp acq : nat -> nat) (L g : nat) : Prop :=
  tid_at t (acq L) = g /\ acq L < length t /\ (lp L = acq L \/ hbt t (lp L) (acq L)).

(* The discharge: any event appended by [g] (the owner) is hb-after L's previous access [lp L] —
   via [po] from [acq L] (an earlier [g]-position) to the new event, prefixed by the [lp L]→[acq L]
   connection.  Serves BOTH an access ([owned_step_snoc] obligation) and a send (buffer hb-support). *)
Lemma acqconn_hbt_new : forall t e lp acq L g,
  AcqConn t lp acq L g -> e_tid e = g -> hbt (t ++ [e]) (lp L) (length t).
Proof.
  intros t e lp acq L g [Htid [Hlt Hconn]] Hg.
  assert (Hpo : po (t ++ [e]) (acq L) (length t)).
  { unfold po. split; [exact Hlt | split].
    - rewrite length_app; cbn; lia.
    - rewrite (tid_at_app1 t e (acq L) Hlt), tid_at_app_new, Hg. exact Htid. }
  destruct Hconn as [Heq | Hhb].
  - rewrite Heq. apply hbt_po. exact Hpo.
  - apply hbt_trans with (j := acq L); [apply hbt_app1; exact Hhb | apply hbt_po; exact Hpo].
Qed.

(* THE CORE SAFETY STEP: an OWNER accessing a location it holds preserves [Owned] (and carries the
   aux invariants forward) — [acqconn_hbt_new] discharges the single obligation [owned_step_snoc] left. *)
Lemma owned_step_by_owner : forall t e L lp acq g,
  Owned t -> LastPosValid t lp -> AccBeforeLast t lp ->
  (e_kind e = KWrite L \/ e_kind e = KRead L) -> e_tid e = g ->
  AcqConn t lp acq L g ->
  Owned (t ++ [e])
  /\ LastPosValid (t ++ [e]) (upd_lastpos lp L (length t))
  /\ AccBeforeLast (t ++ [e]) (upd_lastpos lp L (length t)).
Proof.
  intros t e L lp acq g HO HV HB He Hg HAC.
  apply (owned_step_snoc t e L lp HO HV HB He).
  intros _. exact (acqconn_hbt_new t e lp acq L g HAC Hg).
Qed.

(* After [g] accesses [L] at the new position, the connection re-establishes there (the access is
   its own latest: [lp] and [acq] both bumped to the new position). *)
Lemma acqconn_after_access : forall t e lp acq L g,
  e_tid e = g ->
  AcqConn (t ++ [e]) (upd_lastpos lp L (length t)) (upd_lastpos acq L (length t)) L g.
Proof.
  intros t e lp acq L g Hg. unfold AcqConn. rewrite !upd_lastpos_same. split; [| split].
  - rewrite tid_at_app_new. exact Hg.
  - rewrite length_app; cbn; lia.
  - left. reflexivity.
Qed.

(* A RECV acquires [L]: the buffer entry carried the sender's support [hbt t (lp L) s], and the recv
   event's back-pointer is [s] (so [sync] s→recv), connecting the new owner [g] through the send→recv
   edge.  [acq L] is set to the recv position. *)
Lemma recv_establishes_acqconn : forall t c s lp acq L g,
  hbt t (lp L) s ->
  AcqConn (t ++ [mkEv g (KRecv c s)]) lp (upd_lastpos acq L (length t)) L g.
Proof.
  intros t c s lp acq L g Hsupp. unfold AcqConn. rewrite upd_lastpos_same. split; [| split].
  - rewrite tid_at_app_new. reflexivity.
  - rewrite length_app; cbn; lia.
  - right. apply hbt_trans with (j := s).
    + apply hbt_app1. exact Hsupp.
    + apply hbt_sync. unfold sync. exists (mkEv g (KRecv c s)). split.
      * rewrite nth_error_app_new. reflexivity.
      * cbn. reflexivity.
Qed.

(** ── [WT]: the LINEAR region-threading typing — the PROGRAM-level transfer discipline.
    A region [R : nat -> bool] is the set of locations a goroutine currently OWNS; the judgment
    threads it: write/read keep the region (must own the cell); SEND of location [l] RELEASES it
    ([rdel R l] for the continuation); RECV ACQUIRES the received location ([radd R v]).  This is
    SUBSTRUCTURAL — a sent location leaves the sender's region — which [OnlyAcc] (a fixed, freely
    duplicable predicate) cannot express.  (Channels here carry POINTERS — the sent value IS the
    transferred location, Go's idiomatic "hand the pointer over a channel".) ── *)
Definition radd (R : nat -> bool) (l : nat) : nat -> bool := fun x => orb (R x) (Nat.eqb x l).
Definition rdel (R : nat -> bool) (l : nat) : nat -> bool := fun x => andb (R x) (negb (Nat.eqb x l)).
Lemma radd_same : forall R l, radd R l l = true.
Proof. intros R l. unfold radd. rewrite Nat.eqb_refl. destruct (R l); reflexivity. Qed.
Lemma rdel_same : forall R l, rdel R l l = false.
Proof. intros R l. unfold rdel. rewrite Nat.eqb_refl. destruct (R l); reflexivity. Qed.

Inductive WT : (nat -> bool) -> Cmd -> Prop :=
  | WT_ret  : forall R, WT R CRet
  | WT_write: forall R l v k, R l = true -> WT R k -> WT R (CWrite l v k)
  | WT_read : forall R l f, R l = true -> (forall v, WT R (f v)) -> WT R (CRead l f)
  | WT_send : forall R c l k, R l = true -> WT (rdel R l) k -> WT R (CSend c l k)
  | WT_recv : forall R c f, (forall v, WT (radd R v) (f v)) -> WT R (CRecv c f)
  (* SPAWN SPLITS the region: the child gets a sub-region [Rc ⊆ R] and runs [WT Rc child]; the parent
     keeps the rest [R \ Rc] for its continuation.  Linear: the two are disjoint by construction
     ([andb (R l) (negb (Rc l))] removes exactly [Rc]). *)
  | WT_spawn : forall R Rc child k,
      (forall l, Rc l = true -> R l = true) ->
      WT Rc child ->
      WT (fun l => andb (R l) (negb (Rc l))) k ->
      WT R (CSpawn child k).

Lemma wt_write_inv : forall R l v k, WT R (CWrite l v k) -> R l = true /\ WT R k.
Proof. intros R l v k H. inversion H; subst. split; assumption. Qed.
Lemma wt_read_inv : forall R l f, WT R (CRead l f) -> R l = true /\ (forall v, WT R (f v)).
Proof. intros R l f H. inversion H; subst. split; assumption. Qed.
Lemma wt_send_inv : forall R c l k, WT R (CSend c l k) -> R l = true /\ WT (rdel R l) k.
Proof. intros R c l k H. inversion H; subst. split; assumption. Qed.
Lemma wt_recv_inv : forall R c f, WT R (CRecv c f) -> forall v, WT (radd R v) (f v).
Proof. intros R c f H. inversion H; subst. assumption. Qed.
Lemma wt_spawn_inv : forall R child k, WT R (CSpawn child k) ->
  exists Rc, (forall l, Rc l = true -> R l = true) /\ WT Rc child
             /\ WT (fun l => andb (R l) (negb (Rc l))) k.
Proof. intros R child k H. inversion H; subst. eexists. split; [eassumption | split; eassumption]. Qed.

(* Witnesses that the linear discipline is inhabited: a SENDER owns loc 7, writes it, then sends it
   away (releasing — the continuation no longer owns 7); a RECEIVER owns nothing, receives a pointer,
   then writes through it (acquired). *)
Lemma wt_sender : WT (fun l => Nat.eqb l 7) (CWrite 7 0 (CSend 0 7 CRet)).
Proof. apply WT_write; [reflexivity | apply WT_send; [reflexivity | apply WT_ret]]. Qed.
Lemma wt_receiver : WT (fun _ => false) (CRecv 0 (fun x => CWrite x 0 CRet)).
Proof. apply WT_recv. intro v. apply WT_write; [apply radd_same | apply WT_ret]. Qed.

(** ============================================================================
    THE CONFIG INVARIANT [RegionInv] — assembling bricks 1+2 into a GENERAL transfer race-freedom
    result for arbitrary pointer-handoff programs (no per-program phase enumeration).  A single-valued
    ghost [own : nat -> Owner] (Held g | Transit) gives DISJOINTNESS for free (a location has one
    owner); each live goroutine's program is [WT]-typed under its held region [heldby own g]; the
    channel buffer holds the in-transit locations with the sender's hb-support; and per held+accessed
    location an [AcqConn] witness pins the owner to the trace, carrying [Owned] forward by
    [owned_step_snoc].  [region_inv_step] proves EVERY [rstep] preserves it (write/read = owner access,
    send = release, recv = acquire; spawn/select/close vacuous by [WT]-inversion, closed-recv by
    [NoClose]); hence every reachable trace is [Owned] — race-free, ALL interleavings.
    ============================================================================ *)

Inductive Owner := Held (g : nat) | Transit.

(* [g]'s held region, decoded from the single-valued owner map. *)
Definition heldby (own : nat -> Owner) (g : nat) : nat -> bool :=
  fun l => match own l with Held g' => Nat.eqb g' g | Transit => false end.
Definition upd_own (own : nat -> Owner) (l : nat) (o : Owner) : nat -> Owner :=
  fun x => if Nat.eqb x l then o else own x.
Lemma upd_own_same : forall own l o, upd_own own l o l = o.
Proof. intros. unfold upd_own. rewrite Nat.eqb_refl. reflexivity. Qed.
Lemma upd_own_other : forall own l o x, x <> l -> upd_own own l o x = own x.
Proof. intros own l o x Hne. unfold upd_own. apply Nat.eqb_neq in Hne. rewrite Hne. reflexivity. Qed.
Lemma heldby_held : forall own g L, own L = Held g -> heldby own g L = true.
Proof. intros own g L H. unfold heldby. rewrite H. apply Nat.eqb_refl. Qed.
Lemma heldby_true : forall own g L, heldby own g L = true -> own L = Held g.
Proof.
  intros own g L H. unfold heldby in H. destruct (own L) as [g'|] eqn:E.
  - apply Nat.eqb_eq in H. subst g'. reflexivity.
  - discriminate.
Qed.

(* WT's region appears as a HYPOTHESIS position, so a pointwise-equal region must be CONVERTIBLE
   WITHOUT funext.  [wt_region_ext] does that by induction on the derivation — [radd]/[rdel] preserve
   pointwise equality — so the owner-map updates (which change the region only pointwise) re-type the
   continuation with no axiom.  This is why [own] can stay single-valued yet WT stay funext-free. *)
Lemma wt_region_ext : forall R c, WT R c -> forall R', (forall l, R l = R' l) -> WT R' c.
Proof.
  intros R c HWT. induction HWT as
    [ R | R l v k Hl _ IHk | R l f Hl _ IHf | R c l k Hl _ IHk | R c f _ IHf
    | R Rc child k Hsub Hchild _ _ IHk ];
    intros R' Hext.
  - apply WT_ret.
  - apply WT_write; [rewrite <- Hext; exact Hl | apply IHk; exact Hext].
  - apply WT_read; [rewrite <- Hext; exact Hl | intro v; apply IHf; exact Hext].
  - apply WT_send; [rewrite <- Hext; exact Hl |
      apply IHk; intro x; unfold rdel; rewrite Hext; reflexivity].
  - apply WT_recv. intro v. apply IHf. intro x; unfold radd; rewrite Hext; reflexivity.
  - apply (WT_spawn R' Rc child k).
    + intros l Hl. rewrite <- Hext. exact (Hsub l Hl).
    + exact Hchild.
    + apply IHk. intro x. rewrite Hext. reflexivity.
Qed.

(* AcqConn lifts across an appended event (the connection lives among old positions). *)
Lemma acqconn_app1 : forall t e lp acq L g, AcqConn t lp acq L g -> AcqConn (t ++ [e]) lp acq L g.
Proof.
  intros t e lp acq L g [Htid [Hlt Hconn]]. unfold AcqConn. split; [| split].
  - rewrite (tid_at_app1 t e (acq L) Hlt). exact Htid.
  - rewrite length_app; cbn; lia.
  - destruct Hconn as [Heq | Hhb]; [left; exact Heq | right; apply hbt_app1; exact Hhb].
Qed.

(* AcqConn depends on [lp]/[acq] only at [L], so maps agreeing there are interchangeable. *)
Lemma acqconn_ext : forall t lp acq lp' acq' L g,
  AcqConn t lp acq L g -> lp L = lp' L -> acq L = acq' L -> AcqConn t lp' acq' L g.
Proof.
  intros t lp acq lp' acq' L g [Htid [Hlt Hconn]] Hlpe Hacqe.
  unfold AcqConn. rewrite <- Hacqe, <- Hlpe. split; [exact Htid | split; [exact Hlt | exact Hconn]].
Qed.

(* A WT program never closes a channel (no [CClose] constructor), so no [KClose] is ever emitted —
   which kills the closed-recv [rstep] case in preservation. *)
Definition NoClose (t : Trace) : Prop :=
  forall i e, nth_error t i = Some e -> match e_kind e with KClose _ => False | _ => True end.
Lemma noclose_app : forall t e, NoClose t ->
  match e_kind e with KClose _ => False | _ => True end -> NoClose (t ++ [e]).
Proof.
  intros t e HNC He i e0 Hnth.
  destruct (Nat.lt_ge_cases i (length t)) as [Hlt | Hge].
  - rewrite nth_error_app1 in Hnth by exact Hlt. exact (HNC i e0 Hnth).
  - pose proof (nth_error_lt _ _ _ Hnth) as Hb. rewrite length_app in Hb; cbn in Hb.
    assert (i = length t) by lia. subst i. rewrite nth_error_app_new in Hnth.
    injection Hnth as Heq. subst e0. exact He.
Qed.

(* The invariant: WT regions (disjoint by single-valued [own]), buffer carries in-transit locations
   with sender hb-support, per held+accessed location an AcqConn witness, and the trace stays Owned. *)
Definition RegionInv (own : nat -> Owner) (lp acq : nat -> nat) (cfg : RConfig) : Prop :=
  (forall g, rc_live cfg g = true -> WT (heldby own g) (rc_prog cfg g))
  /\ (forall L g, own L = Held g -> (exists i, acc_loc_at (rc_trace cfg) i = Some L) ->
        AcqConn (rc_trace cfg) lp acq L g)
  /\ (forall c L s, In (L, s) (rc_bufs cfg c) ->
        own L = Transit /\ ((exists i, acc_loc_at (rc_trace cfg) i = Some L) ->
                            hbt (rc_trace cfg) (lp L) s))
  /\ Owned (rc_trace cfg) /\ LastPosValid (rc_trace cfg) lp /\ AccBeforeLast (rc_trace cfg) lp
  /\ NoClose (rc_trace cfg).

(* An access to L≠l in [t ++ [e]] (e a memory access of l) already exists in [t] (the new event
   accesses l, not L). *)
Lemma acc_app_other : forall t e L l,
  (e_kind e = KWrite l \/ e_kind e = KRead l) -> L <> l ->
  (exists i, acc_loc_at (t ++ [e]) i = Some L) -> (exists i, acc_loc_at t i = Some L).
Proof.
  intros t e L l He Hne [i Hi].
  destruct (Nat.lt_ge_cases i (length t)) as [Hlt | Hge].
  - exists i. rewrite (acc_loc_at_app1 t e i Hlt) in Hi. exact Hi.
  - exfalso. pose proof (acc_loc_at_lt _ _ _ Hi) as Hb. rewrite length_app in Hb; cbn in Hb.
    assert (i = length t) by lia. subst i. rewrite (acc_new_L t e l He) in Hi.
    injection Hi as Hll. apply Hne. symmetry; exact Hll.
Qed.

(* THE CORE SAFETY STEP (owner ACCESS): an [rstep_write] by the location's owner preserves [RegionInv]
   — the heart of the transfer reachability proof.  [own] is unchanged (a write transfers nothing);
   the trace grows by one owner-access, discharged via [owned_step_snoc] + [AcqConn]. *)
Lemma region_inv_write : forall own lp acq p b h lv tr tid l v k,
  RegionInv own lp acq (mkRCfg p b h lv tr) ->
  lv tid = true -> p tid = CWrite l v k ->
  RegionInv own (upd_lastpos lp l (length tr)) (upd_lastpos acq l (length tr))
            (mkRCfg (upd p tid k) b (upd h l v) lv (tr ++ [mkEv tid (KWrite l)])).
Proof.
  intros own lp acq p b h lv tr tid l v k HRI Hlv Hp.
  destruct HRI as [Hprog [Hacq [Hbuf [HO [HV [HB HNC]]]]]].
  cbn [rc_prog rc_live rc_bufs rc_trace] in *.
  pose proof (Hprog tid Hlv) as HW. rewrite Hp in HW.
  apply wt_write_inv in HW. destruct HW as [Hheld HWk].
  pose proof (heldby_true _ _ _ Hheld) as Hown.
  destruct (owned_step_snoc tr (mkEv tid (KWrite l)) l lp HO HV HB (or_introl eq_refl)
              (fun Hex => acqconn_hbt_new tr (mkEv tid (KWrite l)) lp acq l tid (Hacq l tid Hown Hex) eq_refl))
    as [HO' [HV' HB']].
  unfold RegionInv. cbn [rc_prog rc_live rc_bufs rc_trace].
  split; [| split; [| split; [| split; [exact HO' | split; [exact HV' | split; [exact HB' |]]]]]].
  - intros g Hg. destruct (Nat.eq_dec g tid) as [->|Hne].
    + rewrite upd_same. exact HWk.
    + rewrite (upd_other p tid k g Hne). exact (Hprog g Hg).
  - intros L g HownL Hex.
    destruct (Nat.eq_dec L l) as [->|Hne].
    + rewrite Hown in HownL. injection HownL as Hgt. subst g.
      exact (acqconn_after_access tr (mkEv tid (KWrite l)) lp acq l tid eq_refl).
    + pose proof (acc_app_other tr (mkEv tid (KWrite l)) L l (or_introl eq_refl) Hne Hex) as HaccTr.
      apply (acqconn_ext (tr ++ [mkEv tid (KWrite l)]) lp acq
               (upd_lastpos lp l (length tr)) (upd_lastpos acq l (length tr)) L g).
      * exact (acqconn_app1 tr (mkEv tid (KWrite l)) lp acq L g (Hacq L g HownL HaccTr)).
      * symmetry. exact (upd_lastpos_other lp l (length tr) L Hne).
      * symmetry. exact (upd_lastpos_other acq l (length tr) L Hne).
  - intros c0 L s Hin. destruct (Hbuf c0 L s Hin) as [HT Hsupp].
    split; [exact HT |].
    assert (Hne : L <> l). { intro Heq; subst L. rewrite Hown in HT. discriminate. }
    rewrite (upd_lastpos_other lp l (length tr) L Hne). intros Hex.
    pose proof (acc_app_other tr (mkEv tid (KWrite l)) L l (or_introl eq_refl) Hne Hex) as HaccTr.
    exact (hbt_app1 tr (mkEv tid (KWrite l)) (lp L) s (Hsupp HaccTr)).
  - apply noclose_app; [exact HNC | exact I].
Qed.

(* The READ analogue (owner ACCESS): [rstep_read] by the owner preserves [RegionInv].  Identical to
   write modulo the event ([KRead l]) and continuation ([f (h l)]). *)
Lemma region_inv_read : forall own lp acq p b h lv tr tid l f,
  RegionInv own lp acq (mkRCfg p b h lv tr) ->
  lv tid = true -> p tid = CRead l f ->
  RegionInv own (upd_lastpos lp l (length tr)) (upd_lastpos acq l (length tr))
            (mkRCfg (upd p tid (f (h l))) b h lv (tr ++ [mkEv tid (KRead l)])).
Proof.
  intros own lp acq p b h lv tr tid l f HRI Hlv Hp.
  destruct HRI as [Hprog [Hacq [Hbuf [HO [HV [HB HNC]]]]]].
  cbn [rc_prog rc_live rc_bufs rc_trace] in *.
  pose proof (Hprog tid Hlv) as HW. rewrite Hp in HW.
  apply wt_read_inv in HW. destruct HW as [Hheld HWf].
  pose proof (heldby_true _ _ _ Hheld) as Hown.
  destruct (owned_step_snoc tr (mkEv tid (KRead l)) l lp HO HV HB (or_intror eq_refl)
              (fun Hex => acqconn_hbt_new tr (mkEv tid (KRead l)) lp acq l tid (Hacq l tid Hown Hex) eq_refl))
    as [HO' [HV' HB']].
  unfold RegionInv. cbn [rc_prog rc_live rc_bufs rc_trace].
  split; [| split; [| split; [| split; [exact HO' | split; [exact HV' | split; [exact HB' |]]]]]].
  - intros g Hg. destruct (Nat.eq_dec g tid) as [->|Hne].
    + rewrite upd_same. exact (HWf (h l)).
    + rewrite (upd_other p tid (f (h l)) g Hne). exact (Hprog g Hg).
  - intros L g HownL Hex.
    destruct (Nat.eq_dec L l) as [->|Hne].
    + rewrite Hown in HownL. injection HownL as Hgt. subst g.
      exact (acqconn_after_access tr (mkEv tid (KRead l)) lp acq l tid eq_refl).
    + pose proof (acc_app_other tr (mkEv tid (KRead l)) L l (or_intror eq_refl) Hne Hex) as HaccTr.
      apply (acqconn_ext (tr ++ [mkEv tid (KRead l)]) lp acq
               (upd_lastpos lp l (length tr)) (upd_lastpos acq l (length tr)) L g).
      * exact (acqconn_app1 tr (mkEv tid (KRead l)) lp acq L g (Hacq L g HownL HaccTr)).
      * symmetry. exact (upd_lastpos_other lp l (length tr) L Hne).
      * symmetry. exact (upd_lastpos_other acq l (length tr) L Hne).
  - intros c0 L s Hin. destruct (Hbuf c0 L s Hin) as [HT Hsupp].
    split; [exact HT |].
    assert (Hne : L <> l). { intro Heq; subst L. rewrite Hown in HT. discriminate. }
    rewrite (upd_lastpos_other lp l (length tr) L Hne). intros Hex.
    pose proof (acc_app_other tr (mkEv tid (KRead l)) L l (or_intror eq_refl) Hne Hex) as HaccTr.
    exact (hbt_app1 tr (mkEv tid (KRead l)) (lp L) s (Hsupp HaccTr)).
  - apply noclose_app; [exact HNC | exact I].
Qed.

(* ── Non-memory events (send/recv) leave the [Owned]/last-position trace facts untouched: they add
   no memory access, so no new same-location pair and no new latest. ── *)
Lemma acc_app_nonmem : forall t e L,
  match e_kind e with KWrite _ => False | KRead _ => False | _ => True end ->
  (exists i, acc_loc_at (t ++ [e]) i = Some L) -> (exists i, acc_loc_at t i = Some L).
Proof.
  intros t e L He [i Hi].
  destruct (Nat.lt_ge_cases i (length t)) as [Hlt | Hge].
  - exists i. rewrite (acc_loc_at_app1 t e i Hlt) in Hi. exact Hi.
  - exfalso. pose proof (acc_loc_at_lt _ _ _ Hi) as Hb. rewrite length_app in Hb; cbn in Hb.
    assert (i = length t) by lia. subst i. rewrite acc_loc_at_app_new in Hi.
    destruct (e_kind e); cbn in He, Hi; try discriminate; contradiction.
Qed.

Lemma owned_app_nonmem : forall t e,
  Owned t -> match e_kind e with KWrite _ => False | KRead _ => False | _ => True end ->
  Owned (t ++ [e]).
Proof.
  intros t e HO He i j Hij Hsl.
  assert (Hjlt : j < length t).
  { destruct (Nat.eq_dec j (length t)) as [Heq|Hjne].
    - exfalso. subst j. destruct Hsl as [l [_ Hjl]]. rewrite acc_loc_at_app_new in Hjl.
      destruct (e_kind e); cbn in He, Hjl; try discriminate; contradiction.
    - destruct Hsl as [l [_ Hjl]]. pose proof (acc_loc_at_lt _ _ _ Hjl) as Hb.
      rewrite length_app in Hb; cbn in Hb. lia. }
  assert (Hilt : i < length t) by lia.
  pose proof (same_loc_app1_inv t e i j Hilt Hjlt Hsl) as Hslt.
  destruct (HO i j Hij Hslt) as [Hhb | [k [[Hik Hkj] [Hsik Hskj]]]].
  - left. apply hbt_app1. exact Hhb.
  - right. exists k. assert (Hklt : k < length t) by lia.
    split; [split; [exact Hik | exact Hkj] | split;
      [apply same_loc_app1; [exact Hilt | exact Hklt | exact Hsik]
      |apply same_loc_app1; [exact Hklt | exact Hjlt | exact Hskj]]].
Qed.

Lemma lastposvalid_app_nonmem : forall t e lp,
  LastPosValid t lp -> match e_kind e with KWrite _ => False | KRead _ => False | _ => True end ->
  LastPosValid (t ++ [e]) lp.
Proof.
  intros t e lp HV He L Hex.
  pose proof (acc_app_nonmem t e L He Hex) as HexT.
  pose proof (HV L HexT) as Hvalid.
  pose proof (acc_loc_at_lt _ _ _ Hvalid) as Hlt.
  rewrite (acc_loc_at_app1 t e (lp L) Hlt). exact Hvalid.
Qed.

Lemma accbeforelast_app_nonmem : forall t e lp,
  AccBeforeLast t lp -> match e_kind e with KWrite _ => False | KRead _ => False | _ => True end ->
  AccBeforeLast (t ++ [e]) lp.
Proof.
  intros t e lp HB He L i Hi.
  destruct (Nat.lt_ge_cases i (length t)) as [Hlt | Hge].
  - rewrite (acc_loc_at_app1 t e i Hlt) in Hi.
    destruct (HB L i Hi) as [Heq | Hhb]; [left; exact Heq | right; apply hbt_app1; exact Hhb].
  - exfalso. pose proof (acc_loc_at_lt _ _ _ Hi) as Hb. rewrite length_app in Hb; cbn in Hb.
    assert (i = length t) by lia. subst i. rewrite acc_loc_at_app_new in Hi.
    destruct (e_kind e); cbn in He, Hi; try discriminate; contradiction.
Qed.

(* ── Region-map effect of a RELEASE (own v := Transit): pointwise it is exactly [rdel] of the held
   region, and it leaves OTHER goroutines' regions unchanged (they did not own v). ── *)
Lemma heldby_release : forall own v g x,
  heldby (upd_own own v Transit) g x = rdel (heldby own g) v x.
Proof.
  intros own v g x. unfold heldby, upd_own, rdel.
  destruct (Nat.eqb x v) eqn:E; cbn; destruct (own x) as [g'|]; cbn;
    try reflexivity; destruct (Nat.eqb g' g); reflexivity.
Qed.

Lemma heldby_release_other : forall own v tid g x,
  g <> tid -> own v = Held tid ->
  heldby (upd_own own v Transit) g x = heldby own g x.
Proof.
  intros own v tid g x Hne Hv. unfold heldby, upd_own.
  destruct (Nat.eqb x v) eqn:E.
  - apply Nat.eqb_eq in E; subst x. rewrite Hv. cbn.
    symmetry. apply Nat.eqb_neq. intro Heq; subst tid; apply Hne; reflexivity.
  - reflexivity.
Qed.

(* THE RELEASE STEP: an [rstep_send] of a held pointer [v] preserves [RegionInv].  [v] LEAVES the
   sender's region ([rdel]) and becomes Transit, entering the channel buffer with the sender's
   happens-before support [hbt (lp v) (length tr)] (from the sender's own [AcqConn], via
   [acqconn_hbt_new]) — exactly what the eventual receiver needs to acquire it race-free. *)
Lemma region_inv_send : forall own lp acq p b h lv tr tid c v k,
  RegionInv own lp acq (mkRCfg p b h lv tr) ->
  lv tid = true -> p tid = CSend c v k ->
  RegionInv (upd_own own v Transit) lp acq
            (mkRCfg (upd p tid k) (upd b c (b c ++ [(v, length tr)])) h lv (tr ++ [mkEv tid (KSend c)])).
Proof.
  intros own lp acq p b h lv tr tid c v k HRI Hlv Hp.
  destruct HRI as [Hprog [Hacq [Hbuf [HO [HV [HB HNC]]]]]].
  cbn [rc_prog rc_live rc_bufs rc_trace] in *.
  pose proof (Hprog tid Hlv) as HW. rewrite Hp in HW.
  apply wt_send_inv in HW. destruct HW as [Hheld HWk].
  pose proof (heldby_true _ _ _ Hheld) as Hown.
  assert (Hnm : match e_kind (mkEv tid (KSend c)) with KWrite _ => False | KRead _ => False | _ => True end) by exact I.
  unfold RegionInv. cbn [rc_prog rc_live rc_bufs rc_trace].
  split; [| split; [| split; [| split;
    [ exact (owned_app_nonmem tr (mkEv tid (KSend c)) HO Hnm)
    | split; [ exact (lastposvalid_app_nonmem tr (mkEv tid (KSend c)) lp HV Hnm)
    | split; [ exact (accbeforelast_app_nonmem tr (mkEv tid (KSend c)) lp HB Hnm)
    | apply noclose_app; [exact HNC | exact I] ]]]]]].
  - (* prog: tid loses v (rdel); other goroutines unchanged *)
    intros g Hg. destruct (Nat.eq_dec g tid) as [->|Hne].
    + rewrite upd_same. apply (wt_region_ext (rdel (heldby own tid) v) k HWk).
      intro x. symmetry. apply heldby_release.
    + rewrite (upd_other p tid k g Hne). apply (wt_region_ext (heldby own g) (p g) (Hprog g Hg)).
      intro x. symmetry. exact (heldby_release_other own v tid g x Hne Hown).
  - (* acq: any still-Held location is <> v, so its AcqConn carries over *)
    intros L g HownL Hex.
    assert (HLne : L <> v). { intro Heq; subst L. rewrite upd_own_same in HownL. discriminate. }
    rewrite (upd_own_other own v Transit L HLne) in HownL.
    pose proof (acc_app_nonmem tr (mkEv tid (KSend c)) L Hnm Hex) as HaccTr.
    exact (acqconn_app1 tr (mkEv tid (KSend c)) lp acq L g (Hacq L g HownL HaccTr)).
  - (* buf: old entries carry over (own unchanged at L<>v); the NEW entry (v, length tr) is Transit
       with the sender's hb-support *)
    intros c0 L s Hin.
    destruct (Nat.eq_dec c0 c) as [->|Hcne].
    + rewrite upd_same in Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      * destruct (Hbuf c L s Hin) as [HT Hsupp].
        assert (HLne : L <> v). { intro Heq; subst L. rewrite Hown in HT. discriminate. }
        split; [rewrite (upd_own_other own v Transit L HLne); exact HT |].
        intros Hex. pose proof (acc_app_nonmem tr (mkEv tid (KSend c)) L Hnm Hex) as HaccTr.
        exact (hbt_app1 tr (mkEv tid (KSend c)) (lp L) s (Hsupp HaccTr)).
      * cbn in Hin. destruct Hin as [Heq | []]. injection Heq as HLv Hsv. subst L s.
        split; [rewrite upd_own_same; reflexivity |].
        intros Hex. pose proof (acc_app_nonmem tr (mkEv tid (KSend c)) v Hnm Hex) as HaccTr.
        exact (acqconn_hbt_new tr (mkEv tid (KSend c)) lp acq v tid (Hacq v tid Hown HaccTr) eq_refl).
    + rewrite (upd_other b c (b c ++ [(v, length tr)]) c0 Hcne) in Hin.
      destruct (Hbuf c0 L s Hin) as [HT Hsupp].
      assert (HLne : L <> v). { intro Heq; subst L. rewrite Hown in HT. discriminate. }
      split; [rewrite (upd_own_other own v Transit L HLne); exact HT |].
      intros Hex. pose proof (acc_app_nonmem tr (mkEv tid (KSend c)) L Hnm Hex) as HaccTr.
      exact (hbt_app1 tr (mkEv tid (KSend c)) (lp L) s (Hsupp HaccTr)).
Qed.

(* ── Region-map effect of an ACQUIRE (own v := Held g): pointwise [radd] of g's region; leaves
   OTHER goroutines' regions unchanged (v was in transit, owned by no goroutine). ── *)
Lemma heldby_acquire : forall own v g x,
  heldby (upd_own own v (Held g)) g x = radd (heldby own g) v x.
Proof.
  intros own v g x. unfold heldby, upd_own, radd.
  destruct (Nat.eqb x v) eqn:E; cbn.
  - rewrite Nat.eqb_refl. destruct (own x) as [g'|]; cbn;
      [destruct (Nat.eqb g' g); reflexivity | reflexivity].
  - destruct (own x) as [g'|]; cbn;
      [destruct (Nat.eqb g' g); reflexivity | reflexivity].
Qed.

Lemma heldby_acquire_other : forall own v g g' x,
  g' <> g -> own v = Transit ->
  heldby (upd_own own v (Held g)) g' x = heldby own g' x.
Proof.
  intros own v g g' x Hne Hv. unfold heldby, upd_own.
  destruct (Nat.eqb x v) eqn:E.
  - apply Nat.eqb_eq in E; subst x. rewrite Hv. cbn.
    apply Nat.eqb_neq. intro Heq; subst g; apply Hne; reflexivity.
  - reflexivity.
Qed.

(* ── Buffer LINEARITY: a transferred location occupies at most one buffer slot total — no duplicate
   within a channel ([NoDup] of values), and never in two channels at once.  This is what makes a RECV
   (popping the head) leave the location absent from the REMAINING buffers, so re-owning it to the
   receiver preserves "buffered ⟹ Transit".  Maintained by the discipline: a send only buffers a HELD
   (hence un-buffered) location; a recv shrinks the buffer. ── *)
Definition BufLin (cfg : RConfig) : Prop :=
  (forall c, NoDup (map fst (rc_bufs cfg c)))
  /\ (forall c1 c2 L, In L (map fst (rc_bufs cfg c1)) -> In L (map fst (rc_bufs cfg c2)) -> c1 = c2).

(* THE ACQUIRE STEP: an [rstep_recv] popping a pointer [v] preserves [RegionInv].  [v] ENTERS the
   receiver's region ([radd]) and becomes [Held tid]; its [AcqConn] is forged through the send→recv
   [sync] edge ([recv_establishes_acqconn], using the buffer's stored hb-support).  [BufLin] guarantees
   the popped [v] is gone from the remaining buffers, so they stay "Transit". *)
Lemma region_inv_recv : forall own lp acq p b h lv tr tid c f v s brest,
  RegionInv own lp acq (mkRCfg p b h lv tr) -> BufLin (mkRCfg p b h lv tr) ->
  lv tid = true -> p tid = CRecv c f -> b c = (v, s) :: brest ->
  RegionInv (upd_own own v (Held tid)) lp (upd_lastpos acq v (length tr))
            (mkRCfg (upd p tid (f v)) (upd b c brest) h lv (tr ++ [mkEv tid (KRecv c s)])).
Proof.
  intros own lp acq p b h lv tr tid c f v s brest HRI HBL Hlv Hp Hbc.
  destruct HRI as [Hprog [Hacq [Hbuf [HO [HV [HB HNC]]]]]].
  destruct HBL as [HND HCC].
  cbn [rc_prog rc_live rc_bufs rc_trace] in *.
  pose proof (Hprog tid Hlv) as HW. rewrite Hp in HW.
  pose proof (wt_recv_inv _ _ _ HW) as HWf.
  assert (Hhead : In (v, s) (b c)) by (rewrite Hbc; left; reflexivity).
  destruct (Hbuf c v s Hhead) as [HvT Hvsupp].
  assert (Hnm : match e_kind (mkEv tid (KRecv c s)) with KWrite _ => False | KRead _ => False | _ => True end) by exact I.
  assert (HvND : ~ In v (map fst brest)).
  { pose proof (HND c) as HNDc. rewrite Hbc in HNDc. cbn in HNDc.
    inversion HNDc as [|x l Hnotin Hrest]; subst. exact Hnotin. }
  (* helper: a remaining-buffer entry's location is ≠ v *)
  assert (Hrem : forall c0 L s0, In (L, s0) (upd b c brest c0) -> L <> v).
  { intros c0 L s0 Hin Heq. subst L. destruct (Nat.eq_dec c0 c) as [->|Hcne].
    - rewrite upd_same in Hin. apply (in_map fst) in Hin. cbn in Hin. exact (HvND Hin).
    - rewrite (upd_other b c brest c0 Hcne) in Hin. apply (in_map fst) in Hin. cbn in Hin.
      assert (Hvc : In v (map fst (b c))) by (rewrite Hbc; left; reflexivity).
      exact (Hcne (HCC c0 c v Hin Hvc)). }
  unfold RegionInv. cbn [rc_prog rc_live rc_bufs rc_trace].
  split; [| split; [| split; [| split;
    [ exact (owned_app_nonmem tr (mkEv tid (KRecv c s)) HO Hnm)
    | split; [ exact (lastposvalid_app_nonmem tr (mkEv tid (KRecv c s)) lp HV Hnm)
    | split; [ exact (accbeforelast_app_nonmem tr (mkEv tid (KRecv c s)) lp HB Hnm)
    | apply noclose_app; [exact HNC | exact I] ]]]]]].
  - (* prog: receiver gains v (radd); others unchanged (v was Transit) *)
    intros g Hg. destruct (Nat.eq_dec g tid) as [->|Hne].
    + rewrite upd_same. apply (wt_region_ext (radd (heldby own tid) v) (f v) (HWf v)).
      intro x. symmetry. apply heldby_acquire.
    + rewrite (upd_other p tid (f v) g Hne).
      apply (wt_region_ext (heldby own g) (p g) (Hprog g Hg)).
      intro x. symmetry. exact (heldby_acquire_other own v tid g x Hne HvT).
  - (* acq: v's connection forged through the send→recv edge; others carry over *)
    intros L g HownL Hex.
    destruct (Nat.eq_dec L v) as [->|Hne].
    + rewrite upd_own_same in HownL. injection HownL as Hgt. subst g.
      pose proof (acc_app_nonmem tr (mkEv tid (KRecv c s)) v Hnm Hex) as HaccTr.
      exact (recv_establishes_acqconn tr c s lp acq v tid (Hvsupp HaccTr)).
    + rewrite (upd_own_other own v (Held tid) L Hne) in HownL.
      pose proof (acc_app_nonmem tr (mkEv tid (KRecv c s)) L Hnm Hex) as HaccTr.
      apply (acqconn_ext (tr ++ [mkEv tid (KRecv c s)]) lp acq lp (upd_lastpos acq v (length tr)) L g).
      * exact (acqconn_app1 tr (mkEv tid (KRecv c s)) lp acq L g (Hacq L g HownL HaccTr)).
      * reflexivity.
      * symmetry. exact (upd_lastpos_other acq v (length tr) L Hne).
  - (* buf: remaining entries keep value ≠ v, so own unchanged (Transit) and support lifts *)
    intros c0 L s0 Hin.
    pose proof (Hrem c0 L s0 Hin) as HLne.
    assert (Horig : own L = Transit /\ ((exists i, acc_loc_at tr i = Some L) -> hbt tr (lp L) s0)).
    { destruct (Nat.eq_dec c0 c) as [->|Hcne].
      - rewrite upd_same in Hin. apply (Hbuf c L s0). rewrite Hbc. right. exact Hin.
      - rewrite (upd_other b c brest c0 Hcne) in Hin. exact (Hbuf c0 L s0 Hin). }
    destruct Horig as [HT Hsupp].
    split.
    + rewrite (upd_own_other own v (Held tid) L HLne). exact HT.
    + intros Hex. pose proof (acc_app_nonmem tr (mkEv tid (KRecv c s)) L Hnm Hex) as HaccTr.
      exact (hbt_app1 tr (mkEv tid (KRecv c s)) (lp L) s0 (Hsupp HaccTr)).
Qed.

(* ── BufLin preservation: a SEND appends a fresh (un-buffered) value; a RECV shrinks a buffer. ── *)
Lemma nodup_snoc : forall (l : list nat) a, NoDup l -> ~ In a l -> NoDup (l ++ [a]).
Proof.
  induction l as [|x l IHl]; intros a HND Hni; cbn.
  - constructor; [intros [] | constructor].
  - inversion HND as [|x' l' Hxni HNDl]; subst.
    constructor.
    + rewrite in_app_iff. intros [Hin | Hin].
      * exact (Hxni Hin).
      * cbn in Hin. destruct Hin as [Heq | []]. subst x. apply Hni. left. reflexivity.
    + apply IHl; [exact HNDl | intro Hin; apply Hni; right; exact Hin].
Qed.

Lemma buflin_send : forall (bf : nat -> list (nat * nat)) c v s0,
  (forall ch, NoDup (map fst (bf ch))) ->
  (forall c1 c2 L, In L (map fst (bf c1)) -> In L (map fst (bf c2)) -> c1 = c2) ->
  (forall ch, ~ In v (map fst (bf ch))) ->
  (forall ch, NoDup (map fst (upd bf c (bf c ++ [(v, s0)]) ch)))
  /\ (forall c1 c2 L, In L (map fst (upd bf c (bf c ++ [(v, s0)]) c1)) ->
                      In L (map fst (upd bf c (bf c ++ [(v, s0)]) c2)) -> c1 = c2).
Proof.
  intros bf c v s0 HND HCC Hvnb. split.
  - intro ch. destruct (Nat.eq_dec ch c) as [->|Hne].
    + rewrite upd_same, map_app. cbn. apply nodup_snoc; [apply HND | apply Hvnb].
    + rewrite (upd_other bf c (bf c ++ [(v, s0)]) ch Hne). apply HND.
  - intros c1 c2 L H1 H2.
    destruct (Nat.eq_dec c1 c) as [->|Hc1]; destruct (Nat.eq_dec c2 c) as [->|Hc2].
    + reflexivity.
    + rewrite upd_same, map_app in H1. rewrite (upd_other bf c _ c2 Hc2) in H2.
      apply in_app_iff in H1. destruct H1 as [H1 | H1].
      * exfalso. apply Hc2. symmetry. exact (HCC c c2 L H1 H2).
      * cbn in H1. destruct H1 as [Heq | []]. subst L. exfalso. exact (Hvnb c2 H2).
    + rewrite (upd_other bf c _ c1 Hc1) in H1. rewrite upd_same, map_app in H2.
      apply in_app_iff in H2. destruct H2 as [H2 | H2].
      * exfalso. apply Hc1. exact (HCC c1 c L H1 H2).
      * cbn in H2. destruct H2 as [Heq | []]. subst L. exfalso. exact (Hvnb c1 H1).
    + rewrite (upd_other bf c _ c1 Hc1) in H1. rewrite (upd_other bf c _ c2 Hc2) in H2.
      exact (HCC c1 c2 L H1 H2).
Qed.

Lemma buflin_recv : forall (bf : nat -> list (nat * nat)) c v s brest,
  (forall ch, NoDup (map fst (bf ch))) ->
  (forall c1 c2 L, In L (map fst (bf c1)) -> In L (map fst (bf c2)) -> c1 = c2) ->
  bf c = (v, s) :: brest ->
  (forall ch, NoDup (map fst (upd bf c brest ch)))
  /\ (forall c1 c2 L, In L (map fst (upd bf c brest c1)) -> In L (map fst (upd bf c brest c2)) -> c1 = c2).
Proof.
  intros bf c v s brest HND HCC Hbc. split.
  - intro ch. destruct (Nat.eq_dec ch c) as [->|Hne].
    + rewrite upd_same. pose proof (HND c) as H. rewrite Hbc in H. cbn in H.
      inversion H; subst; assumption.
    + rewrite (upd_other bf c brest ch Hne). apply HND.
  - intros c1 c2 L H1 H2.
    assert (Hsub : forall cx, In L (map fst (upd bf c brest cx)) -> In L (map fst (bf cx))).
    { intros cx Hx. destruct (Nat.eq_dec cx c) as [->|Hcx].
      - rewrite upd_same in Hx. rewrite Hbc. cbn. right. exact Hx.
      - rewrite (upd_other bf c brest cx Hcx) in Hx. exact Hx. }
    exact (HCC c1 c2 L (Hsub c1 H1) (Hsub c2 H2)).
Qed.

(* Owner-LIVENESS coherence: every owned location's owner is a LIVE goroutine.  Needed by the SPAWN
   case — a freshly-spawned [cid] (not yet live) therefore owns nothing, so the split-off region is
   exactly the child's region.  Trivially preserved by all steps (owners are assigned only to the
   live stepping goroutine, and a spawn makes its [cid] live). *)
Definition OwnerLive (own : nat -> Owner) (cfg : RConfig) : Prop :=
  forall l g, own l = Held g -> rc_live cfg g = true.

(** ── SPAWN transfer: ownership SPLIT.  On [CSpawn child k], the parent's region splits — the child
    [cid] takes the sub-region [Rc] (becoming its owner), the parent keeps the rest.  [own_spawn]
    reassigns [Rc] to [cid]; [acq_spawn] sets those locations' [AcqConn] anchor to the [KStart]
    position, so the child's first access to a transferred cell is hb-after the parent's last via the
    [KSpawn]→[KStart] fork edge.  Fresh-[cid] (it owns nothing before, by [OwnerLive] + [lv cid=false])
    makes the child's decoded region exactly [Rc]. ── *)
Definition own_spawn (own : nat -> Owner) (Rc : nat -> bool) (cid : nat) : nat -> Owner :=
  fun l => if Rc l then Held cid else own l.
Definition acq_spawn (acq : nat -> nat) (Rc : nat -> bool) (p : nat) : nat -> nat :=
  fun l => if Rc l then p else acq l.

Lemma heldby_spawn_child : forall own Rc cid l,
  (forall l0, own l0 <> Held cid) -> heldby (own_spawn own Rc cid) cid l = Rc l.
Proof.
  intros own Rc cid l Hfresh. unfold heldby, own_spawn. destruct (Rc l) eqn:E; cbn.
  - rewrite Nat.eqb_refl. reflexivity.
  - destruct (own l) as [g'|] eqn:Eo; cbn.
    + apply Nat.eqb_neq. intro Heq. subst g'. exact (Hfresh l Eo).
    + reflexivity.
Qed.

Lemma heldby_spawn_parent : forall own Rc cid tid l,
  cid <> tid -> heldby (own_spawn own Rc cid) tid l = andb (heldby own tid l) (negb (Rc l)).
Proof.
  intros own Rc cid tid l Hne. apply Nat.eqb_neq in Hne.
  unfold heldby, own_spawn. destruct (Rc l) eqn:E; cbn.
  - rewrite Hne. destruct (own l) as [g'|]; cbn;
      [destruct (Nat.eqb g' tid); reflexivity | reflexivity].
  - destruct (own l) as [g'|]; cbn;
      [destruct (Nat.eqb g' tid); reflexivity | reflexivity].
Qed.

Lemma heldby_spawn_other : forall own Rc cid tid g l,
  g <> cid -> g <> tid -> (forall l0, Rc l0 = true -> own l0 = Held tid) ->
  heldby (own_spawn own Rc cid) g l = heldby own g l.
Proof.
  intros own Rc cid tid g l Hgc Hgt HRc.
  assert (Hcg : Nat.eqb cid g = false) by (apply Nat.eqb_neq; intro Hx; apply Hgc; symmetry; exact Hx).
  assert (Htg : Nat.eqb tid g = false) by (apply Nat.eqb_neq; intro Hx; apply Hgt; symmetry; exact Hx).
  unfold heldby, own_spawn. destruct (Rc l) eqn:E; cbn.
  - rewrite (HRc l E); cbn. rewrite Hcg, Htg. reflexivity.
  - reflexivity.
Qed.

(* The fork edge forges the transferred cell's [AcqConn]: parent's connection → po to the [KSpawn]
   (a tid-event, [acqconn_hbt_new]) → sync to the [KStart] (its back-pointer is the [KSpawn] position)
   → the child owns it, anchored at the [KStart] position. *)
Lemma spawn_establishes_acqconn : forall tr lp acq L tid cid,
  AcqConn tr lp acq L tid ->
  AcqConn (tr ++ [mkEv tid (KSpawn cid); mkEv cid (KStart (length tr))])
          lp (upd_lastpos acq L (S (length tr))) L cid.
Proof.
  intros tr lp acq L tid cid HAC.
  pose proof (acqconn_hbt_new tr (mkEv tid (KSpawn cid)) lp acq L tid HAC eq_refl) as Hhb1.
  assert (Htr' : tr ++ [mkEv tid (KSpawn cid); mkEv cid (KStart (length tr))]
               = (tr ++ [mkEv tid (KSpawn cid)]) ++ [mkEv cid (KStart (length tr))])
    by (rewrite <- app_assoc; reflexivity).
  rewrite Htr'.
  assert (Hlen1 : length (tr ++ [mkEv tid (KSpawn cid)]) = S (length tr))
    by (rewrite length_app; cbn; lia).
  unfold AcqConn. rewrite upd_lastpos_same. split; [| split].
  - unfold tid_at. rewrite <- Hlen1, nth_error_app_new. reflexivity.
  - rewrite length_app, length_app; cbn; lia.
  - right. apply hbt_trans with (j := length tr).
    + apply hbt_app1. exact Hhb1.
    + apply hbt_sync. unfold sync. exists (mkEv cid (KStart (length tr))). split.
      * rewrite <- Hlen1, nth_error_app_new. reflexivity.
      * cbn. reflexivity.
Qed.

(* THE SPAWN STEP: an [rstep_spawn] (ownership SPLIT) preserves [RegionInv] AND [OwnerLive].  [Rc]
   (the split region) comes from inverting the parent's [WT]; the child becomes owner of [Rc] via the
   fork edge, the parent keeps the rest, everyone else is untouched. *)
Lemma region_inv_spawn : forall own lp acq p b h lv tr tid child k cid,
  RegionInv own lp acq (mkRCfg p b h lv tr) -> OwnerLive own (mkRCfg p b h lv tr) ->
  lv tid = true -> p tid = CSpawn child k -> lv cid = false ->
  exists own' acq',
    RegionInv own' lp acq'
      (mkRCfg (upd (upd p tid k) cid child) b h (upd lv cid true)
              (tr ++ [mkEv tid (KSpawn cid); mkEv cid (KStart (length tr))]))
    /\ OwnerLive own'
      (mkRCfg (upd (upd p tid k) cid child) b h (upd lv cid true)
              (tr ++ [mkEv tid (KSpawn cid); mkEv cid (KStart (length tr))])).
Proof.
  intros own lp acq p b h lv tr tid child k cid HRI HOL Hlv Hp Hcid.
  destruct HRI as [Hprog [Hacq [Hbuf [HO [HV [HB HNC]]]]]].
  cbn [rc_prog rc_live rc_bufs rc_trace] in *.
  pose proof (Hprog tid Hlv) as HW. rewrite Hp in HW.
  apply wt_spawn_inv in HW. destruct HW as [Rc [HRcsubR [HWchild HWk]]].
  assert (Htidcid : tid <> cid) by (intro Heq; subst cid; rewrite Hlv in Hcid; discriminate).
  assert (Hcidtid : cid <> tid) by (intro Heq; apply Htidcid; symmetry; exact Heq).
  assert (Hfresh : forall l, own l <> Held cid).
  { intros l Hcon. pose proof (HOL l cid Hcon) as Hx. cbn [rc_live] in Hx. rewrite Hcid in Hx. discriminate. }
  assert (HRcsub : forall l, Rc l = true -> own l = Held tid)
    by (intros l Hl; exact (heldby_true _ _ _ (HRcsubR l Hl))).
  set (e1 := mkEv tid (KSpawn cid)). set (e2 := mkEv cid (KStart (length tr))).
  assert (Hnm1 : match e_kind e1 with KWrite _ => False | KRead _ => False | _ => True end) by exact I.
  assert (Hnm2 : match e_kind e2 with KWrite _ => False | KRead _ => False | _ => True end) by exact I.
  assert (Htr' : tr ++ [e1; e2] = (tr ++ [e1]) ++ [e2]) by (rewrite <- app_assoc; reflexivity).
  exists (own_spawn own Rc cid), (acq_spawn acq Rc (S (length tr))).
  split.
  - unfold RegionInv. cbn [rc_prog rc_live rc_bufs rc_trace].
    split; [| split; [| split; [| split; [| split; [| split]]]]].
    + (* prog *)
      intros g Hg. destruct (Nat.eq_dec g cid) as [->|Hgc].
      * rewrite upd_same. apply (wt_region_ext Rc child HWchild).
        intro l. symmetry. exact (heldby_spawn_child own Rc cid l Hfresh).
      * rewrite (upd_other lv cid true g Hgc) in Hg.
        rewrite (upd_other (upd p tid k) cid child g Hgc).
        destruct (Nat.eq_dec g tid) as [->|Hgt].
        -- rewrite upd_same.
           apply (wt_region_ext (fun l => andb (heldby own tid l) (negb (Rc l))) k HWk).
           intro l. symmetry. exact (heldby_spawn_parent own Rc cid tid l Hcidtid).
        -- rewrite (upd_other p tid k g Hgt).
           apply (wt_region_ext (heldby own g) (p g) (Hprog g Hg)).
           intro l. symmetry. exact (heldby_spawn_other own Rc cid tid g l Hgc Hgt HRcsub).
    + (* acq *)
      intros L g HownL Hex.
      assert (HaccTr : exists i, acc_loc_at tr i = Some L).
      { apply (acc_app_nonmem tr e1 L Hnm1). apply (acc_app_nonmem (tr ++ [e1]) e2 L Hnm2).
        rewrite <- Htr'. exact Hex. }
      rewrite Htr'. unfold own_spawn in HownL. destruct (Rc L) eqn:ERc.
      * injection HownL as Hgcid. subst g.
        pose proof (spawn_establishes_acqconn tr lp acq L tid cid (Hacq L tid (HRcsub L ERc) HaccTr)) as HACs.
        fold e1 e2 in HACs. rewrite Htr' in HACs.
        apply (acqconn_ext ((tr ++ [e1]) ++ [e2]) lp (upd_lastpos acq L (S (length tr)))
                 lp (acq_spawn acq Rc (S (length tr))) L cid HACs).
        -- reflexivity.
        -- unfold acq_spawn. rewrite ERc. rewrite upd_lastpos_same. reflexivity.
      * apply (acqconn_ext ((tr ++ [e1]) ++ [e2]) lp acq
                 lp (acq_spawn acq Rc (S (length tr))) L g).
        -- apply acqconn_app1. apply acqconn_app1. exact (Hacq L g HownL HaccTr).
        -- reflexivity.
        -- unfold acq_spawn. rewrite ERc. reflexivity.
    + (* buf *)
      intros c0 L s0 Hin. destruct (Hbuf c0 L s0 Hin) as [HT Hsupp].
      assert (HLnRc : Rc L = false).
      { destruct (Rc L) eqn:E; [rewrite (HRcsub L E) in HT; discriminate | reflexivity]. }
      split.
      * unfold own_spawn. rewrite HLnRc. exact HT.
      * intros Hex.
        assert (HaccTr : exists i, acc_loc_at tr i = Some L).
        { apply (acc_app_nonmem tr e1 L Hnm1). apply (acc_app_nonmem (tr ++ [e1]) e2 L Hnm2).
          rewrite <- Htr'. exact Hex. }
        rewrite Htr'. apply hbt_app1. apply hbt_app1. exact (Hsupp HaccTr).
    + (* Owned *) rewrite Htr'.
      apply owned_app_nonmem; [apply owned_app_nonmem; [exact HO | exact Hnm1] | exact Hnm2].
    + (* LastPosValid *) rewrite Htr'.
      apply lastposvalid_app_nonmem; [apply lastposvalid_app_nonmem; [exact HV | exact Hnm1] | exact Hnm2].
    + (* AccBeforeLast *) rewrite Htr'.
      apply accbeforelast_app_nonmem; [apply accbeforelast_app_nonmem; [exact HB | exact Hnm1] | exact Hnm2].
    + (* NoClose *) rewrite Htr'.
      apply noclose_app; [apply noclose_app; [exact HNC | exact I] | exact I].
  - (* OwnerLive *)
    intros l g Hg. cbn [rc_live]. unfold own_spawn in Hg. destruct (Rc l) eqn:ERc.
    + injection Hg as Hgcid. subst g. rewrite upd_same. reflexivity.
    + pose proof (HOL l g Hg) as Hlvg. cbn [rc_live] in Hlvg.
      assert (Hgc : g <> cid) by (intro Heq; subst g; exact (Hfresh l Hg)).
      rewrite (upd_other lv cid true g Hgc). exact Hlvg.
Qed.

(* THE PRESERVATION THEOREM: every [rstep] preserves [RegionInv], [BufLin] AND [OwnerLive].  The four
   owner/transfer steps dispatch to the per-case lemmas; spawn/select/close are impossible under [WT]
   (no constructor), and closed-recv is impossible under [NoClose]. *)
Lemma region_inv_step : forall own lp acq cfg cfg',
  RegionInv own lp acq cfg -> BufLin cfg -> OwnerLive own cfg -> rstep cfg cfg' ->
  exists own' lp' acq', RegionInv own' lp' acq' cfg' /\ BufLin cfg' /\ OwnerLive own' cfg'.
Proof.
  intros own lp acq cfg cfg' HRI HBL HOL Hstep.
  destruct Hstep as
    [ p b h lv tr tid c v k Hlv Hp Hcb
    | p b h lv tr tid c f v s brest Hlv Hp Hbc
    | p b h lv tr tid l v k Hlv Hp
    | p b h lv tr tid l f Hlv Hp
    | p b h lv tr tid child k cid Hlv Hp Hcid
    | p b h lv tr tid cases c f v s brest Hlv Hp Hin Hbc
    | p b h lv tr tid c k Hlv Hp Hcb
    | p b h lv tr tid c f pos e Hlv Hp Hbc Hpos Hek
    | p b h lv tr tid cases c f pos e Hlv Hp Hin Hbc Hpos Hek ].
  - (* send *)
    exists (upd_own own v Transit), lp, acq.
    split; [ exact (region_inv_send own lp acq p b h lv tr tid c v k HRI Hlv Hp) | ].
    split.
    + pose proof HRI as HRI2. destruct HRI2 as [Hprog [_ [Hbuf _]]]. destruct HBL as [HND HCC].
      cbn [rc_prog rc_live rc_bufs] in *.
      pose proof (Hprog tid Hlv) as HW. rewrite Hp in HW.
      apply wt_send_inv in HW. destruct HW as [Hheld _]. pose proof (heldby_true _ _ _ Hheld) as Hown.
      assert (Hvnb : forall ch, ~ In v (map fst (b ch))).
      { intros ch Hcon. apply in_map_iff in Hcon. destruct Hcon as [[v' s'] [Hfst Hin']].
        cbn in Hfst. subst v'. destruct (Hbuf ch v s' Hin') as [HT _]. rewrite Hown in HT. discriminate. }
      exact (buflin_send b c v (length tr) HND HCC Hvnb).
    + intros l0 g Hg. destruct (Nat.eq_dec l0 v) as [->|Hne].
      * rewrite upd_own_same in Hg. discriminate.
      * rewrite (upd_own_other own v Transit l0 Hne) in Hg. exact (HOL l0 g Hg).
  - (* recv *)
    exists (upd_own own v (Held tid)), lp, (upd_lastpos acq v (length tr)).
    split; [ exact (region_inv_recv own lp acq p b h lv tr tid c f v s brest HRI HBL Hlv Hp Hbc) | ].
    split.
    + destruct HBL as [HND HCC]. cbn [rc_bufs] in *.
      exact (buflin_recv b c v s brest HND HCC Hbc).
    + intros l0 g Hg. destruct (Nat.eq_dec l0 v) as [->|Hne].
      * rewrite upd_own_same in Hg. injection Hg as Hgt. subst g. exact Hlv.
      * rewrite (upd_own_other own v (Held tid) l0 Hne) in Hg. exact (HOL l0 g Hg).
  - (* write *)
    exists own, (upd_lastpos lp l (length tr)), (upd_lastpos acq l (length tr)).
    split; [ exact (region_inv_write own lp acq p b h lv tr tid l v k HRI Hlv Hp) |
             split; [ exact HBL | exact HOL ] ].
  - (* read *)
    exists own, (upd_lastpos lp l (length tr)), (upd_lastpos acq l (length tr)).
    split; [ exact (region_inv_read own lp acq p b h lv tr tid l f HRI Hlv Hp) |
             split; [ exact HBL | exact HOL ] ].
  - (* spawn: ownership SPLIT — dispatch to region_inv_spawn (bufs unchanged ⇒ BufLin preserved) *)
    destruct (region_inv_spawn own lp acq p b h lv tr tid child k cid HRI HOL Hlv Hp Hcid)
      as [own' [acq' [HRI' HOL']]].
    exists own', lp, acq'. split; [exact HRI' | split; [exact HBL | exact HOL']].
  - (* select: WT has no CSelect *)
    exfalso. destruct HRI as [Hprog _]. pose proof (Hprog tid Hlv) as HW.
    cbn [rc_prog rc_live] in HW. rewrite Hp in HW. inversion HW.
  - (* close: WT has no CClose *)
    exfalso. destruct HRI as [Hprog _]. pose proof (Hprog tid Hlv) as HW.
    cbn [rc_prog rc_live] in HW. rewrite Hp in HW. inversion HW.
  - (* recv_closed: NoClose kills the KClose premise *)
    exfalso. destruct HRI as [_ [_ [_ [_ [_ [_ HNC]]]]]]. cbn [rc_trace] in HNC.
    pose proof (HNC pos e Hpos) as HC. rewrite Hek in HC. cbn in HC. exact HC.
  - (* select_closed: WT has no CSelect *)
    exfalso. destruct HRI as [Hprog _]. pose proof (Hprog tid Hlv) as HW.
    cbn [rc_prog rc_live] in HW. rewrite Hp in HW. inversion HW.
Qed.

Lemma region_inv_steps : forall own lp acq cfg cfg',
  RegionInv own lp acq cfg -> BufLin cfg -> OwnerLive own cfg -> rsteps cfg cfg' ->
  exists own' lp' acq', RegionInv own' lp' acq' cfg' /\ BufLin cfg' /\ OwnerLive own' cfg'.
Proof.
  intros own lp acq cfg cfg' HRI HBL HOL Hsteps. revert own lp acq HRI HBL HOL.
  induction Hsteps as [cfg0 | a b0 c0 Hab Hbc IH]; intros own lp acq HRI HBL HOL.
  - exists own, lp, acq. split; [exact HRI | split; [exact HBL | exact HOL]].
  - destruct (region_inv_step own lp acq a b0 HRI HBL HOL Hab)
      as [own' [lp' [acq' [HRI' [HBL' HOL']]]]].
    exact (IH own' lp' acq' HRI' HBL' HOL').
Qed.

(* THE THEOREM: every reachable trace of a [RegionInv]+[BufLin]+[OwnerLive] program is race-free — for
   ARBITRARY (no-spawn) pointer-handoff programs and ALL interleavings, via the ABSTRACT ownership
   invariant (not a per-program phase enumeration). *)
Theorem region_inv_race_free : forall own lp acq cfg0 cfg,
  RegionInv own lp acq cfg0 -> BufLin cfg0 -> OwnerLive own cfg0 -> rsteps cfg0 cfg ->
  TraceRaceFree (rc_trace cfg).
Proof.
  intros own lp acq cfg0 cfg HRI HBL HOL Hsteps.
  destruct (region_inv_steps own lp acq cfg0 cfg HRI HBL HOL Hsteps) as [own' [lp' [acq' [HRI' _]]]].
  destruct HRI' as [_ [_ [_ [HO _]]]].
  exact (owned_race_free _ HO).
Qed.

(* WITNESS (non-vacuity): g0 owns loc 7, writes it, HANDS IT OFF over channel 0; g1 owns nothing,
   receives the pointer and writes through it.  A genuine cross-goroutine write/write on loc 7 —
   yet EVERY interleaving is race-free, derived from the program structure alone (own := all-g0). *)
Definition witness_prog : nat -> Cmd :=
  fun t => if Nat.eqb t 0 then CWrite 7 1 (CSend 0 7 CRet)
           else if Nat.eqb t 1 then CRecv 0 (fun x => CWrite x 2 CRet) else CRet.
Definition witness_init : RConfig :=
  mkRCfg witness_prog (fun _ => []) (fun _ => 0) (fun t => orb (Nat.eqb t 0) (Nat.eqb t 1)) [].

Lemma witness_regioninv : RegionInv (fun _ => Held 0) (fun _ => 0) (fun _ => 0) witness_init.
Proof.
  unfold RegionInv, witness_init. cbn [rc_prog rc_live rc_bufs rc_trace].
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - intros g Hg. unfold witness_prog. destruct (Nat.eqb g 0) eqn:E0.
    + apply Nat.eqb_eq in E0; subst g.
      apply WT_write; [reflexivity | apply WT_send; [reflexivity | apply WT_ret]].
    + destruct (Nat.eqb g 1) eqn:E1.
      * apply WT_recv. intro v. apply WT_write; [apply radd_same | apply WT_ret].
      * cbn in Hg. discriminate.
  - intros L g _ [i Hi]. unfold acc_loc_at in Hi. destruct i; cbn in Hi; discriminate.
  - intros c L s [].
  - intros i j Hij [l [Hi _]]. unfold acc_loc_at in Hi. destruct i; cbn in Hi; discriminate.
  - intros L [i Hi]. unfold acc_loc_at in Hi. destruct i; cbn in Hi; discriminate.
  - intros L i Hi. unfold acc_loc_at in Hi. destruct i; cbn in Hi; discriminate.
  - intros i e Hi. destruct i; cbn in Hi; discriminate.
Qed.

Lemma witness_buflin : BufLin witness_init.
Proof.
  unfold BufLin, witness_init. cbn [rc_bufs]. split.
  - intro c. cbn. constructor.
  - intros c1 c2 L H1 H2. cbn in H1. destruct H1.
Qed.

Lemma witness_ownerlive : OwnerLive (fun _ => Held 0) witness_init.
Proof. intros l g Hg. injection Hg as Hg0. subst g. reflexivity. Qed.

Theorem witness_all_interleavings_race_free : forall cfg,
  rsteps witness_init cfg -> TraceRaceFree (rc_trace cfg).
Proof.
  intros cfg Hsteps.
  exact (region_inv_race_free (fun _ => Held 0) (fun _ => 0) (fun _ => 0) witness_init cfg
           witness_regioninv witness_buflin witness_ownerlive Hsteps).
Qed.

(* MULTI-HOP / MULTI-CHANNEL witness: a pointer RELAY.  g0 owns loc 7, writes it, sends it on ch0;
   g1 receives the pointer and forwards it on ch1 (acquiring then releasing — it never dereferences);
   g2 receives it and writes through it.  The conflicting cross-goroutine write/WRITE on cell 7 is
   ordered through TWO channel hops (g0→g1→g2) — yet EVERY interleaving is race-free, straight from
   [region_inv_race_free].  This exercises the cross-channel arm of [BufLin] and multi-hop transfer,
   confirming the abstract theorem is not limited to a single handoff. *)
Definition relay_prog : nat -> Cmd :=
  fun t => if Nat.eqb t 0 then CWrite 7 1 (CSend 0 7 CRet)
           else if Nat.eqb t 1 then CRecv 0 (fun x => CSend 1 x CRet)
           else if Nat.eqb t 2 then CRecv 1 (fun y => CWrite y 2 CRet)
           else CRet.
Definition relay_init : RConfig :=
  mkRCfg relay_prog (fun _ => []) (fun _ => 0)
         (fun t => orb (Nat.eqb t 0) (orb (Nat.eqb t 1) (Nat.eqb t 2))) [].

Lemma relay_regioninv : RegionInv (fun _ => Held 0) (fun _ => 0) (fun _ => 0) relay_init.
Proof.
  unfold RegionInv, relay_init. cbn [rc_prog rc_live rc_bufs rc_trace].
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - intros g Hg. unfold relay_prog. destruct (Nat.eqb g 0) eqn:E0.
    + apply Nat.eqb_eq in E0; subst g.
      apply WT_write; [reflexivity | apply WT_send; [reflexivity | apply WT_ret]].
    + destruct (Nat.eqb g 1) eqn:E1.
      * apply WT_recv. intro x. apply WT_send; [apply radd_same | apply WT_ret].
      * destruct (Nat.eqb g 2) eqn:E2.
        -- apply WT_recv. intro y. apply WT_write; [apply radd_same | apply WT_ret].
        -- cbn in Hg. discriminate.
  - intros L g _ [i Hi]. unfold acc_loc_at in Hi. destruct i; cbn in Hi; discriminate.
  - intros c L s [].
  - intros i j Hij [l [Hi _]]. unfold acc_loc_at in Hi. destruct i; cbn in Hi; discriminate.
  - intros L [i Hi]. unfold acc_loc_at in Hi. destruct i; cbn in Hi; discriminate.
  - intros L i Hi. unfold acc_loc_at in Hi. destruct i; cbn in Hi; discriminate.
  - intros i e Hi. destruct i; cbn in Hi; discriminate.
Qed.

Lemma relay_buflin : BufLin relay_init.
Proof.
  unfold BufLin, relay_init. cbn [rc_bufs]. split.
  - intro c. cbn. constructor.
  - intros c1 c2 L H1 H2. cbn in H1. destruct H1.
Qed.

Lemma relay_ownerlive : OwnerLive (fun _ => Held 0) relay_init.
Proof. intros l g Hg. injection Hg as Hg0. subst g. reflexivity. Qed.

Theorem relay_all_interleavings_race_free : forall cfg,
  rsteps relay_init cfg -> TraceRaceFree (rc_trace cfg).
Proof.
  intros cfg Hsteps.
  exact (region_inv_race_free (fun _ => Held 0) (fun _ => 0) (fun _ => 0) relay_init cfg
           relay_regioninv relay_buflin relay_ownerlive Hsteps).
Qed.

(* SPAWN-transfer witness (ownership SPLIT): g0 owns loc 7, writes it, then SPAWNS a child to whom it
   hands off loc 7 (the child's region [Rc = {7}]); the child writes 7.  A genuine cross-goroutine
   write/WRITE on cell 7 — g0's write before the [go], the child's after it — ordered by the
   KSpawn→KStart fork edge, so EVERY interleaving (including the dynamically-spawned child) is
   race-free, derived from the program structure alone. *)
Definition splitw_prog : nat -> Cmd :=
  fun t => if Nat.eqb t 0
           then CWrite 7 1 (CSpawn (CWrite 7 2 CRet) CRet)
           else CRet.
Definition splitw_init : RConfig :=
  mkRCfg splitw_prog (fun _ => []) (fun _ => 0) (fun t => Nat.eqb t 0) [].

Lemma splitw_regioninv : RegionInv (fun _ => Held 0) (fun _ => 0) (fun _ => 0) splitw_init.
Proof.
  unfold RegionInv, splitw_init. cbn [rc_prog rc_live rc_bufs rc_trace].
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - intros g Hg. unfold splitw_prog. destruct (Nat.eqb g 0) eqn:E0.
    + apply Nat.eqb_eq in E0; subst g.
      apply WT_write; [reflexivity |].
      apply (WT_spawn _ (fun l => Nat.eqb l 7) (CWrite 7 2 CRet) CRet).
      * intros l Hl. apply Nat.eqb_eq in Hl; subst l. reflexivity.
      * apply WT_write; [reflexivity | apply WT_ret].
      * apply WT_ret.
    + cbn in Hg. discriminate.
  - intros L g _ [i Hi]. unfold acc_loc_at in Hi. destruct i; cbn in Hi; discriminate.
  - intros c L s [].
  - intros i j Hij [l [Hi _]]. unfold acc_loc_at in Hi. destruct i; cbn in Hi; discriminate.
  - intros L [i Hi]. unfold acc_loc_at in Hi. destruct i; cbn in Hi; discriminate.
  - intros L i Hi. unfold acc_loc_at in Hi. destruct i; cbn in Hi; discriminate.
  - intros i e Hi. destruct i; cbn in Hi; discriminate.
Qed.

Lemma splitw_buflin : BufLin splitw_init.
Proof.
  unfold BufLin, splitw_init. cbn [rc_bufs]. split.
  - intro c. cbn. constructor.
  - intros c1 c2 L H1 H2. cbn in H1. destruct H1.
Qed.

Lemma splitw_ownerlive : OwnerLive (fun _ => Held 0) splitw_init.
Proof. intros l g Hg. injection Hg as Hg0. subst g. reflexivity. Qed.

Theorem splitw_all_interleavings_race_free : forall cfg,
  rsteps splitw_init cfg -> TraceRaceFree (rc_trace cfg).
Proof.
  intros cfg Hsteps.
  exact (region_inv_race_free (fun _ => Held 0) (fun _ => 0) (fun _ => 0) splitw_init cfg
           splitw_regioninv splitw_buflin splitw_ownerlive Hsteps).
Qed.

(* COMBINED spawn+channel witness (BOTH transfer mechanisms in one program — the "spawn a worker, hand
   it work over a channel" idiom).  g0 owns loc 7, writes it, SPAWNS a child to whom it hands off loc 7
   (split); the child SENDS the pointer on channel 0 (channel handoff); g1 receives the pointer and
   writes through it.  Loc 7 thus travels g0 →(fork)→ child →(channel)→ g1 — two DIFFERENT transfer
   mechanisms in sequence — yet the cross-goroutine write/WRITE on cell 7 (g0's vs g1's) is race-free
   for EVERY interleaving, straight from [region_inv_race_free].  This is the general theorem subsuming
   the bespoke spawn+channel ([dst]) phase-enumeration witness. *)
Definition combo_prog : nat -> Cmd :=
  fun t => if Nat.eqb t 0 then CWrite 7 1 (CSpawn (CSend 0 7 CRet) CRet)
           else if Nat.eqb t 1 then CRecv 0 (fun x => CWrite x 2 CRet)
           else CRet.
Definition combo_init : RConfig :=
  mkRCfg combo_prog (fun _ => []) (fun _ => 0)
         (fun t => orb (Nat.eqb t 0) (Nat.eqb t 1)) [].

Lemma combo_regioninv : RegionInv (fun _ => Held 0) (fun _ => 0) (fun _ => 0) combo_init.
Proof.
  unfold RegionInv, combo_init. cbn [rc_prog rc_live rc_bufs rc_trace].
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - intros g Hg. unfold combo_prog. destruct (Nat.eqb g 0) eqn:E0.
    + apply Nat.eqb_eq in E0; subst g.
      apply WT_write; [reflexivity |].
      apply (WT_spawn _ (fun l => Nat.eqb l 7) (CSend 0 7 CRet) CRet).
      * intros l Hl. apply Nat.eqb_eq in Hl; subst l. reflexivity.
      * apply WT_send; [reflexivity | apply WT_ret].
      * apply WT_ret.
    + destruct (Nat.eqb g 1) eqn:E1.
      * apply WT_recv. intro x. apply WT_write; [apply radd_same | apply WT_ret].
      * cbn in Hg. discriminate.
  - intros L g _ [i Hi]. unfold acc_loc_at in Hi. destruct i; cbn in Hi; discriminate.
  - intros c L s [].
  - intros i j Hij [l [Hi _]]. unfold acc_loc_at in Hi. destruct i; cbn in Hi; discriminate.
  - intros L [i Hi]. unfold acc_loc_at in Hi. destruct i; cbn in Hi; discriminate.
  - intros L i Hi. unfold acc_loc_at in Hi. destruct i; cbn in Hi; discriminate.
  - intros i e Hi. destruct i; cbn in Hi; discriminate.
Qed.

Lemma combo_buflin : BufLin combo_init.
Proof.
  unfold BufLin, combo_init. cbn [rc_bufs]. split.
  - intro c. cbn. constructor.
  - intros c1 c2 L H1 H2. cbn in H1. destruct H1.
Qed.

Lemma combo_ownerlive : OwnerLive (fun _ => Held 0) combo_init.
Proof. intros l g Hg. injection Hg as Hg0. subst g. reflexivity. Qed.

Theorem combo_all_interleavings_race_free : forall cfg,
  rsteps combo_init cfg -> TraceRaceFree (rc_trace cfg).
Proof.
  intros cfg Hsteps.
  exact (region_inv_race_free (fun _ => Held 0) (fun _ => 0) (fun _ => 0) combo_init cfg
           combo_regioninv combo_buflin combo_ownerlive Hsteps).
Qed.

(* The owner-of-each-access fact extends across a single appended event, given the new event
   is by its location's owner (when it IS a memory access). *)
Lemma TraceOwned_app : forall own tr ev,
  (forall i l, acc_loc_at tr i = Some l -> tid_at tr i = own l) ->
  (forall l, (e_kind ev = KWrite l \/ e_kind ev = KRead l) -> e_tid ev = own l) ->
  (forall i l, acc_loc_at (tr ++ [ev]) i = Some l -> tid_at (tr ++ [ev]) i = own l).
Proof.
  intros own tr ev Hold Hnew i l Hacc.
  destruct (Nat.lt_ge_cases i (length tr)) as [Hlt | Hge].
  - rewrite (acc_loc_at_app1 tr ev i Hlt) in Hacc.
    rewrite (tid_at_app1 tr ev i Hlt). exact (Hold i l Hacc).
  - pose proof (acc_loc_at_lt _ _ _ Hacc) as Hb. rewrite length_app in Hb; cbn in Hb.
    assert (Hi : i = length tr) by lia. subst i.
    rewrite tid_at_app_new. rewrite acc_loc_at_app_new in Hacc.
    destruct (e_kind ev) as [c0|c0 fr|ch0|par0|loc|loc|c0] eqn:Ek; cbn in Hacc; try discriminate Hacc.
    + injection Hacc as Hll; subst loc. exact (Hnew l (or_introl eq_refl)).
    + injection Hacc as Hll; subst loc. exact (Hnew l (or_intror eq_refl)).
Qed.

(* The program-ownership fact extends across a single [upd] of the stepping goroutine's continuation. *)
Lemma onlyacc_upd : forall own (p : nat -> Cmd) tid (cont : Cmd) (lv : nat -> bool) g,
  (forall g', lv g' = true -> OnlyAcc (fun l => own l = g') (p g')) ->
  OnlyAcc (fun l => own l = tid) cont ->
  lv g = true ->
  OnlyAcc (fun l => own l = g) (upd p tid cont g).
Proof.
  intros own p tid cont lv g Hprog Hcont Hg.
  destruct (Nat.eq_dec g tid) as [->|Hne].
  - rewrite upd_same. exact Hcont.
  - rewrite (upd_other p tid cont g Hne). exact (Hprog g Hg).
Qed.

(* PRESERVATION: every [rstep] keeps the private-memory discipline.  The spawn case is now LIVE:
   the (memory-free) child is [OnlyAcc] for its own owner via [memfree_onlyacc], the parent's
   continuation via [oa_spawn_inv], and the appended [KSpawn]/[KStart] events touch no memory. *)
Lemma private_disc_step : forall own cfg cfg',
  rstep cfg cfg' -> PrivateDisc own cfg -> PrivateDisc own cfg'.
Proof.
  intros own cfg cfg' Hstep HPD. unfold PrivateDisc in HPD |- *. destruct HPD as [Htr Hprog].
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
    cbn [rc_trace rc_prog rc_live] in Htr, Hprog |- *.
  - (* send: cont = k; event KSend (not a memory access) *)
    pose proof (Hprog tid Hlv) as HO. rewrite Hp in HO. apply oa_send_inv in HO. split.
    + apply (TraceOwned_app own tr (mkEv tid (KSend c)) Htr). intros l' [Hw|Hr]; cbn in *; discriminate.
    + intros g Hg. exact (onlyacc_upd own p tid k lv g Hprog HO Hg).
  - (* recv: cont = f v; event KRecv *)
    pose proof (Hprog tid Hlv) as HO. rewrite Hp in HO. split.
    + apply (TraceOwned_app own tr (mkEv tid (KRecv c s)) Htr). intros l' [Hw|Hr]; cbn in *; discriminate.
    + intros g Hg. exact (onlyacc_upd own p tid (f v) lv g Hprog (oa_recv_inv _ _ _ HO v) Hg).
  - (* write: cont = k; event KWrite l, BY ITS OWNER (own l = tid from OnlyAcc) *)
    pose proof (Hprog tid Hlv) as HO. rewrite Hp in HO. apply oa_write_inv in HO. destruct HO as [Hown HOk]. split.
    + apply (TraceOwned_app own tr (mkEv tid (KWrite l)) Htr). intros l' [Hw|Hr]; cbn in *.
      * injection Hw as Heq; subst l'. symmetry. exact Hown.
      * discriminate.
    + intros g Hg. exact (onlyacc_upd own p tid k lv g Hprog HOk Hg).
  - (* read: cont = f (h l); event KRead l, by its owner *)
    pose proof (Hprog tid Hlv) as HO. rewrite Hp in HO. apply oa_read_inv in HO. destruct HO as [Hown HOf]. split.
    + apply (TraceOwned_app own tr (mkEv tid (KRead l)) Htr). intros l' [Hw|Hr]; cbn in *.
      * discriminate.
      * injection Hr as Heq; subst l'. symmetry. exact Hown.
    + intros g Hg. exact (onlyacc_upd own p tid (f (h l)) lv g Hprog (HOf (h l)) Hg).
  - (* spawn: parent cont = k; child cid gets the MEMORY-FREE [child] (OnlyAcc for ANY owner);
       the appended [KSpawn]/[KStart] events are not memory accesses *)
    pose proof (Hprog tid Hlv) as HO. rewrite Hp in HO.
    apply oa_spawn_inv in HO. destruct HO as [HMFchild HOk]. split.
    + replace (tr ++ [mkEv tid (KSpawn cid); mkEv cid (KStart (length tr))])
        with ((tr ++ [mkEv tid (KSpawn cid)]) ++ [mkEv cid (KStart (length tr))])
        by (rewrite <- app_assoc; reflexivity).
      apply (TraceOwned_app own (tr ++ [mkEv tid (KSpawn cid)]) (mkEv cid (KStart (length tr)))).
      * apply (TraceOwned_app own tr (mkEv tid (KSpawn cid)) Htr).
        intros l' [Hw|Hr]; cbn in *; discriminate.
      * intros l' [Hw|Hr]; cbn in *; discriminate.
    + intros g Hg. destruct (Nat.eq_dec g cid) as [->|Hgc].
      * rewrite upd_same. exact (memfree_onlyacc child HMFchild (fun l => own l = cid)).
      * rewrite (upd_other (upd p tid k) cid child g Hgc).
        rewrite (upd_other lv cid true g Hgc) in Hg.
        destruct (Nat.eq_dec g tid) as [->|Hgt].
        -- rewrite upd_same. exact HOk.
        -- rewrite (upd_other p tid k g Hgt). exact (Hprog g Hg).
  - (* select: cont = f v (chosen case); event KRecv *)
    pose proof (Hprog tid Hlv) as HO. rewrite Hp in HO. split.
    + apply (TraceOwned_app own tr (mkEv tid (KRecv c s)) Htr). intros l' [Hw|Hr]; cbn in *; discriminate.
    + intros g Hg. exact (onlyacc_upd own p tid (f v) lv g Hprog (oa_select_inv _ _ HO c f Hin v) Hg).
  - (* close: cont = k; event KClose *)
    pose proof (Hprog tid Hlv) as HO. rewrite Hp in HO. apply oa_close_inv in HO. split.
    + apply (TraceOwned_app own tr (mkEv tid (KClose c)) Htr). intros l' [Hw|Hr]; cbn in *; discriminate.
    + intros g Hg. exact (onlyacc_upd own p tid k lv g Hprog HO Hg).
  - (* recv_closed: cont = f 0; event KRecv *)
    pose proof (Hprog tid Hlv) as HO. rewrite Hp in HO. split.
    + apply (TraceOwned_app own tr (mkEv tid (KRecv c pos)) Htr). intros l' [Hw|Hr]; cbn in *; discriminate.
    + intros g Hg. exact (onlyacc_upd own p tid (f 0) lv g Hprog (oa_recv_inv _ _ _ HO 0) Hg).
  - (* select_closed: cont = f 0; event KRecv *)
    pose proof (Hprog tid Hlv) as HO. rewrite Hp in HO. split.
    + apply (TraceOwned_app own tr (mkEv tid (KRecv c pos)) Htr). intros l' [Hw|Hr]; cbn in *; discriminate.
    + intros g Hg. exact (onlyacc_upd own p tid (f 0) lv g Hprog (oa_select_inv _ _ HO c f Hin 0) Hg).
Qed.

Lemma private_disc_steps : forall own a b, rsteps a b -> PrivateDisc own a -> PrivateDisc own b.
Proof.
  intros own a b H. induction H as [cfg | a b c Hab Hbc IH]; intros HPD; [exact HPD|].
  apply IH. exact (private_disc_step own _ _ Hab HPD).
Qed.

(* SOUNDNESS: the discipline implies the trace is location-private — every same-location pair is
   the SAME goroutine (both equal to the location's unique owner). *)
Lemma private_disc_locprivate : forall own cfg,
  PrivateDisc own cfg -> LocPrivate (rc_trace cfg).
Proof.
  intros own cfg [Htr _] i j [l [Hi Hj]].
  rewrite (Htr i l Hi), (Htr j l Hj). reflexivity.
Qed.

(** THE BRICK: a program whose goroutines only touch their OWN locations runs race-free, for ANY
    number of goroutines and EVERY interleaving — race-freedom EARNED from a checkable structural
    discipline (no [Owned] hypothesis), the abstract-ownership base case (no transfer/spawn yet). *)
Theorem private_disc_reachable_race_free : forall own cfg0 cfg,
  PrivateDisc own cfg0 -> rsteps cfg0 cfg ->
  LocPrivate (rc_trace cfg) /\ TraceRaceFree (rc_trace cfg).
Proof.
  intros own cfg0 cfg HPD Hsteps.
  pose proof (private_disc_locprivate own cfg (private_disc_steps own cfg0 cfg Hsteps HPD)) as HLP.
  split; [exact HLP | exact (locprivate_race_free _ HLP)].
Qed.

(** Witness (positive, N=2): goroutine 0 writes location 0, goroutine 1 writes location 1, both
    pre-live (no spawn).  With [own := id] the discipline holds at init, so EVERY interleaving of
    this genuinely-concurrent program is race-free — derived from the program structure alone. *)
Definition priv_prog : nat -> Cmd :=
  fun t => if Nat.eqb t 0 then CWrite 0 0 CRet
           else if Nat.eqb t 1 then CWrite 1 0 CRet else CRet.
Definition priv_init : RConfig :=
  mkRCfg priv_prog (fun _ => []) (fun _ => 0) (fun t => orb (Nat.eqb t 0) (Nat.eqb t 1)) [].

Lemma priv_init_disc : PrivateDisc (fun l => l) priv_init.
Proof.
  split.
  - intros i l Hacc. cbn in Hacc. unfold acc_loc_at in Hacc.
    destruct i; cbn in Hacc; discriminate.
  - intros g Hg. cbn in Hg |- *.
    destruct g as [|[|g']]; cbn in Hg |- *.
    + apply OA_write; [reflexivity | apply OA_ret].
    + apply OA_write; [reflexivity | apply OA_ret].
    + discriminate Hg.
Qed.

Theorem priv_prog_reachable_race_free : forall cfg,
  rsteps priv_init cfg -> TraceRaceFree (rc_trace cfg).
Proof.
  intros cfg Hsteps.
  exact (proj2 (private_disc_reachable_race_free (fun l => l) priv_init cfg priv_init_disc Hsteps)).
Qed.

(* WITNESS for the memory-free DYNAMIC spawn ([OA_spawn]): goroutine 0 SPAWNS a channel-only child
   ([CSend 0 0 CRet] — touches no heap) then writes its OWN location 0.  With [own := fun _ => 0]
   (goroutine 0 owns everything; the child owns nothing and touches nothing) the discipline holds at
   init, so EVERY interleaving — INCLUDING after the runtime spawn of the second goroutine — is
   race-free, for a program that is NOT spawn-free.  The old [OnlyAcc]-has-no-spawn base could not even
   state this. *)
Definition spawn_prog : nat -> Cmd :=
  fun t => if Nat.eqb t 0
           then CSpawn (CSend 0 0 CRet) (CWrite 0 0 CRet)
           else CRet.
Definition spawn_init : RConfig :=
  mkRCfg spawn_prog (fun _ => []) (fun _ => 0) (fun t => Nat.eqb t 0) [].

Lemma spawn_init_disc : PrivateDisc (fun _ => 0) spawn_init.
Proof.
  split.
  - intros i l Hacc. cbn in Hacc. unfold acc_loc_at in Hacc.
    destruct i; cbn in Hacc; discriminate.
  - intros g Hg. cbn in Hg |- *. destruct g as [|g']; cbn in Hg |- *.
    + apply OA_spawn.
      * apply MF_send. apply MF_ret.
      * apply OA_write; [ reflexivity | apply OA_ret ].
    + discriminate Hg.
Qed.

Theorem spawn_prog_reachable_race_free : forall cfg,
  rsteps spawn_init cfg -> TraceRaceFree (rc_trace cfg).
Proof.
  intros cfg Hsteps.
  exact (proj2 (private_disc_reachable_race_free (fun _ => 0) spawn_init cfg spawn_init_disc Hsteps)).
Qed.

(* NORTH-STAR (FRONTIER 2 at the calculus level): the CURSED DEMO's concurrency SHAPE proven race-free.
   The cursed demo is [type Cursed struct { Cu_chans []chan ChanBox ; Cu_list *ListNode }] — the MAIN
   goroutine owns the HEAP (the [*ListNode], here location 0) and SPAWNS channel-relay goroutines (the
   self-sending-channel goroutines — they only touch channels, [MemFree]); main then recvs the relayed
   values and reads/writes its own list.  This is EXACTLY [OA_spawn]'s shape: memory owned by one
   goroutine, dynamic spawns of memory-free children — so it is race-free, for EVERY interleaving, by
   the discipline alone.  (Modulo the typed↔operational bridge from the extracted Go to this calculus.) *)
Definition cursed_spawn_prog : nat -> Cmd :=
  fun t => if Nat.eqb t 0
           then CSpawn (CSend 1 99 CRet)                  (* relay goroutine A (self-sending channel 1) *)
                  (CSpawn (CSend 2 99 CRet)               (* relay goroutine B (self-sending channel 2) *)
                     (CRecv 1 (fun _ => CRecv 2 (fun _ =>  (* main recvs both relayed values … *)
                        CWrite 0 7 (CRead 0 (fun _ => CRet))))))  (* … then writes+reads its list (loc 0) *)
           else CRet.
Definition cursed_spawn_init : RConfig :=
  mkRCfg cursed_spawn_prog (fun _ => []) (fun _ => 0) (fun t => Nat.eqb t 0) [].

Lemma cursed_spawn_disc : PrivateDisc (fun _ => 0) cursed_spawn_init.
Proof.
  split.
  - intros i l Hacc. cbn in Hacc. unfold acc_loc_at in Hacc.
    destruct i; cbn in Hacc; discriminate.
  - intros g Hg. cbn in Hg |- *. destruct g as [|g']; cbn in Hg |- *.
    + apply OA_spawn; [ apply MF_send; apply MF_ret |].
      apply OA_spawn; [ apply MF_send; apply MF_ret |].
      apply OA_recv; intros _.
      apply OA_recv; intros _.
      apply OA_write; [ reflexivity |].
      apply OA_read; [ reflexivity | intros _; apply OA_ret ].
    + discriminate Hg.
Qed.

Theorem cursed_spawn_reachable_race_free : forall cfg,
  rsteps cursed_spawn_init cfg -> TraceRaceFree (rc_trace cfg).
Proof.
  intros cfg Hsteps.
  exact (proj2 (private_disc_reachable_race_free (fun _ => 0) cursed_spawn_init cfg cursed_spawn_disc Hsteps)).
Qed.

(* GENERAL CAPSTONE of the memory-free line: a program in which EVERY goroutine is [MemFree] — a pure
   channel/spawn program with NO shared memory at all — is race-free for EVERY reachable interleaving,
   for ANY number of goroutines and ANY (dynamic) spawning, regardless of channel topology (self-sending
   channels, channels-in-structs, …  none of which is memory).  A memory-free program is [OnlyAcc] for
   EVERY owner ([memfree_onlyacc]), so [PrivateDisc] holds trivially (any [own] works); race-freedom then
   follows from the discipline.  This is the general statement the specific witnesses above instantiate. *)
Theorem memfree_prog_race_free : forall cfg0 cfg,
  rc_trace cfg0 = [] ->
  (forall g, MemFree (rc_prog cfg0 g)) ->
  rsteps cfg0 cfg -> TraceRaceFree (rc_trace cfg).
Proof.
  intros cfg0 cfg Htr0 Hmf Hsteps.
  assert (HPD : PrivateDisc (fun _ => 0) cfg0).
  { split.
    - intros i l Hacc. rewrite Htr0 in Hacc. unfold acc_loc_at in Hacc.
      destruct i; cbn in Hacc; discriminate.
    - intros g _. apply (memfree_onlyacc _ (Hmf g)). }
  exact (proj2 (private_disc_reachable_race_free (fun _ => 0) cfg0 cfg HPD Hsteps)).
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

(** ---- FORK handoff, PARAMETRIC over the spawned child's tid (the dynamic-CSpawn subtlety). ----
    [fork_handoff_trace] hardcoded the child tid [1], but [rinit_cfg fork_prog] starts only goroutine 0
    live, so [rstep_spawn] picks ANY fresh [cid <> 0].  Here the fork handoff is [Owned] — hence
    race-free — for EVERY such [cid]: the write/read conflict (positions 0/3) is ordered by the SAME
    spawn synchronisation ([transfer_orders] over the [KSpawn cid]→[KStart] edge) regardless of which
    fresh tid the scheduler chose.  This is the foundation the all-interleavings result needs (phase E's
    [Owned] for an arbitrary spawned child); the [ForkReach] reachability invariant pinning every
    reachable state to a prefix of [fork_trace_cid cid] is the next brick. *)
Definition fork_trace_cid (cid : nat) : Trace :=
  [ mkEv 0 (KWrite 7); mkEv 0 (KSpawn cid); mkEv cid (KStart 1); mkEv cid (KRead 7) ].
Lemma fork_loc_pos_cid : forall cid i l, acc_loc_at (fork_trace_cid cid) i = Some l -> i = 0 \/ i = 3.
Proof.
  intros cid i l H. pose proof (acc_loc_at_lt _ _ _ H) as Hlt. cbn in Hlt.
  unfold fork_trace_cid, acc_loc_at in H.
  destruct i as [|[|[|[|i]]]]; cbn in H;
    [ left; reflexivity | discriminate | discriminate | right; reflexivity | lia ].
Qed.
Lemma fork_owned_cid : forall cid, Owned (fork_trace_cid cid).
Proof.
  intros cid i j Hij [l [Hi Hj]]. left.
  destruct (fork_loc_pos_cid cid i l Hi) as [-> | ->];
    destruct (fork_loc_pos_cid cid j l Hj) as [-> | ->]; try lia.
  apply (transfer_orders (fork_trace_cid cid) 0 1 2 3).
  - unfold po, tid_at; cbn. repeat split; lia.
  - unfold sync; cbn. exists (mkEv cid (KStart 1)); cbn. split; reflexivity.
  - unfold po, tid_at; cbn. repeat split; lia.
Qed.
Theorem fork_race_free_cid : forall cid, TraceRaceFree (fork_trace_cid cid).
Proof. intro cid. exact (owned_race_free _ (fork_owned_cid cid)). Qed.

(** EVERY interleaving of the fork-handoff program is race-free — the spawn analogue of
    [mp_all_interleavings_race_free], and HARDER (the goroutine set is DYNAMIC: the child tid is freshly
    spawned).  [ForkReach] is the 4-phase reachability invariant over [rinit_cfg fork_prog]; the child tid
    [cid] is EXISTENTIAL in the post-spawn phases, and the live set there is the [upd]-form the operational
    [rstep_spawn] produces (so no funext).  [fork_live_cases] bounds the stepping goroutine to {0, cid}. *)
Lemma fork_live_cases : forall cid tid,
  upd (fun t => Nat.eqb t 0) cid true tid = true -> tid = 0 \/ tid = cid.
Proof.
  intros cid tid H. destruct (Nat.eq_dec tid cid) as [->|Hne]; [right; reflexivity|].
  rewrite (upd_other _ _ _ _ Hne) in H. apply Nat.eqb_eq in H. left; exact H.
Qed.

(* every memory access at position 0 ⇒ race-free (a race needs two distinct-goroutine accesses, both
   would be position 0 = same goroutine).  Local copy of the later [mem_access_only0_race_free]. *)
Lemma fork_only0_rf : forall t,
  (forall i ai, tr_acc t i = Some ai -> i = 0) -> TraceRaceFree t.
Proof.
  intros t H. apply le1_mem_access_race_free. intros i j Hi Hj.
  destruct (tr_acc t i) as [ai|] eqn:Ei; [|exfalso; apply Hi; reflexivity].
  destruct (tr_acc t j) as [aj|] eqn:Ej; [|exfalso; apply Hj; reflexivity].
  apply H in Ei; apply H in Ej; subst; reflexivity.
Qed.

Definition ForkReach (cfg : RConfig) : Prop :=
     (rc_trace cfg = [] /\ rc_prog cfg 0 = CWrite 7 99 (CSpawn fork_child CRet)
      /\ rc_live cfg = (fun t => Nat.eqb t 0))
  \/ (rc_trace cfg = [mkEv 0 (KWrite 7)] /\ rc_prog cfg 0 = CSpawn fork_child CRet
      /\ rc_live cfg = (fun t => Nat.eqb t 0))
  \/ (exists cid, Nat.eqb cid 0 = false
      /\ rc_trace cfg = [mkEv 0 (KWrite 7); mkEv 0 (KSpawn cid); mkEv cid (KStart 1)]
      /\ rc_prog cfg 0 = CRet /\ rc_prog cfg cid = CRead 7 (fun _ => CRet)
      /\ rc_live cfg = upd (fun t => Nat.eqb t 0) cid true)
  \/ (exists cid, Nat.eqb cid 0 = false
      /\ rc_trace cfg = fork_trace_cid cid
      /\ rc_prog cfg 0 = CRet /\ rc_prog cfg cid = CRet
      /\ rc_live cfg = upd (fun t => Nat.eqb t 0) cid true).

Lemma forkreach_init : ForkReach (rinit_cfg fork_prog).
Proof. left. unfold rinit_cfg, fork_prog; cbn. repeat split; reflexivity. Qed.

Lemma forkreach_race_free : forall cfg, ForkReach cfg -> TraceRaceFree (rc_trace cfg).
Proof.
  intros cfg HFR.
  destruct HFR as [[Htr _]|[[Htr _]|[[cid [_ [Htr _]]]|[cid [_ [Htr _]]]]]]; rewrite Htr.
  - apply fork_only0_rf. intros i ai Hi. destruct i; cbn in Hi; discriminate.
  - apply fork_only0_rf. intros i ai Hi. pose proof (tr_acc_lt _ _ _ Hi) as L.
    destruct i as [|[|[|i]]]; cbn in Hi; first [reflexivity | discriminate Hi | (cbn in L; lia)].
  - apply fork_only0_rf. intros i ai Hi. pose proof (tr_acc_lt _ _ _ Hi) as L.
    destruct i as [|[|[|i]]]; cbn in Hi; first [reflexivity | discriminate Hi | (cbn in L; lia)].
  - exact (fork_race_free_cid cid).
Qed.

Lemma forkreach_step : forall cfg cfg', rstep cfg cfg' -> ForkReach cfg -> ForkReach cfg'.
Proof.
  intros cfg cfg' Hstep HFR.
  destruct HFR as [[Htr [Hp0 Hlive]]
                 |[[Htr [Hp0 Hlive]]
                  |[[cid [Hcid0 [Htr [Hp0 [Hpc Hlive]]]]]
                   |[cid [Hcid0 [Htr [Hp0 [Hpc Hlive]]]]]]]].
  - (* Phase A: g0 at CWrite, only g0 live → write → Phase B *)
    destruct Hstep as
      [ p b h lv tr tid c v k Hlv Hp _ | p b h lv tr tid c f v s brest Hlv Hp Hbc
      | p b h lv tr tid l v k Hlv Hp | p b h lv tr tid l f Hlv Hp
      | p b h lv tr tid child k cid' Hlv Hp Hcid' | p b h lv tr tid cases c f v s brest Hlv Hp Hin Hbc
      | p b h lv tr tid c k Hlv Hp _ | p b h lv tr tid c f pos e Hlv Hp Hbc Hpos Hek
      | p b h lv tr tid cases c f pos e Hlv Hp Hin Hbc Hpos Hek ];
      cbn [rc_live rc_trace rc_prog] in Hlive, Htr, Hp0 |- *;
      rewrite Hlive in Hlv; cbn in Hlv; apply Nat.eqb_eq in Hlv; subst tid;
      rewrite Hp0 in Hp; try (exfalso; congruence).
    injection Hp as Hl Hv Hk; subst l v k.
    right; left. rewrite Htr. cbn [rc_trace rc_prog rc_live]. rewrite upd_same.
    repeat split; first [reflexivity | assumption].
  - (* Phase B: g0 at CSpawn, only g0 live → spawn → Phase C (fresh cid') *)
    destruct Hstep as
      [ p b h lv tr tid c v k Hlv Hp _ | p b h lv tr tid c f v s brest Hlv Hp Hbc
      | p b h lv tr tid l v k Hlv Hp | p b h lv tr tid l f Hlv Hp
      | p b h lv tr tid child k cid' Hlv Hp Hcid' | p b h lv tr tid cases c f v s brest Hlv Hp Hin Hbc
      | p b h lv tr tid c k Hlv Hp _ | p b h lv tr tid c f pos e Hlv Hp Hbc Hpos Hek
      | p b h lv tr tid cases c f pos e Hlv Hp Hin Hbc Hpos Hek ];
      cbn [rc_live rc_trace rc_prog] in Hlive, Htr, Hp0 |- *;
      rewrite Hlive in Hlv; cbn in Hlv; apply Nat.eqb_eq in Hlv; subst tid;
      rewrite Hp0 in Hp; try (exfalso; congruence).
    injection Hp as Hchild Hk; subst child k.
    rewrite Hlive in Hcid'; cbn in Hcid'.
    assert (Hne0 : 0 <> cid') by (apply not_eq_sym, Nat.eqb_neq; exact Hcid').
    right; right; left. exists cid'. rewrite Htr, Hlive. cbn [rc_trace rc_prog rc_live].
    unfold fork_child.
    rewrite (upd_other (upd p 0 CRet) cid' (CRead 7 (fun _ => CRet)) 0 Hne0), !upd_same.
    repeat split; first [exact Hcid' | reflexivity].
  - (* Phase C: g0 done (CRet), gcid at CRead → only gcid steps (read) → Phase D *)
    assert (Hne0 : 0 <> cid) by (apply not_eq_sym, Nat.eqb_neq; exact Hcid0).
    destruct Hstep as
      [ p b h lv tr tid c v k Hlv Hp _ | p b h lv tr tid c f v s brest Hlv Hp Hbc
      | p b h lv tr tid l v k Hlv Hp | p b h lv tr tid l f Hlv Hp
      | p b h lv tr tid child k cid' Hlv Hp Hcid' | p b h lv tr tid cases c f v s brest Hlv Hp Hin Hbc
      | p b h lv tr tid c k Hlv Hp _ | p b h lv tr tid c f pos e Hlv Hp Hbc Hpos Hek
      | p b h lv tr tid cases c f pos e Hlv Hp Hin Hbc Hpos Hek ];
      cbn [rc_live rc_trace rc_prog] in Hlive, Htr, Hp0, Hpc |- *;
      rewrite Hlive in Hlv; apply fork_live_cases in Hlv; destruct Hlv as [->| ->];
      first [ rewrite Hp0 in Hp | rewrite Hpc in Hp ];
      try (exfalso; congruence).
    injection Hp as Hl Hf; subst l f.
    right; right; right. exists cid. rewrite Htr, Hlive. cbn [rc_trace rc_prog rc_live].
    unfold fork_trace_cid.
    rewrite (upd_other p cid CRet 0 Hne0), upd_same.
    repeat split; first [exact Hcid0 | reflexivity | assumption].
  - (* Phase D: both done (CRet) → no step *)
    exfalso.
    destruct Hstep as
      [ p b h lv tr tid c v k Hlv Hp _ | p b h lv tr tid c f v s brest Hlv Hp Hbc
      | p b h lv tr tid l v k Hlv Hp | p b h lv tr tid l f Hlv Hp
      | p b h lv tr tid child k cid' Hlv Hp Hcid' | p b h lv tr tid cases c f v s brest Hlv Hp Hin Hbc
      | p b h lv tr tid c k Hlv Hp _ | p b h lv tr tid c f pos e Hlv Hp Hbc Hpos Hek
      | p b h lv tr tid cases c f pos e Hlv Hp Hin Hbc Hpos Hek ];
      cbn [rc_live rc_prog] in Hlive, Hp0, Hpc;
      rewrite Hlive in Hlv; apply fork_live_cases in Hlv; destruct Hlv as [->| ->];
      first [ rewrite Hp0 in Hp | rewrite Hpc in Hp ]; congruence.
Qed.

Lemma forkreach_steps : forall cfg cfg', rsteps cfg cfg' -> ForkReach cfg -> ForkReach cfg'.
Proof.
  intros cfg cfg' H. induction H as [c | a b c Hab Hbc IH]; intros HFR; [exact HFR|].
  apply IH. exact (forkreach_step _ _ Hab HFR).
Qed.

(** THE FORK ALL-INTERLEAVINGS THEOREM: every reachable state of the fork-handoff program — under any
    schedule and for whatever fresh tid the child was spawned with — is race-free. *)
Theorem fork_all_interleavings_race_free : forall cfg,
  rsteps (rinit_cfg fork_prog) cfg -> TraceRaceFree (rc_trace cfg).
Proof.
  intros cfg Hsteps.
  exact (forkreach_race_free _ (forkreach_steps _ _ Hsteps forkreach_init)).
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

(** NON-VACUITY of the refounded bridge (break #1, slice 2c): instantiate the abstract value-coding with
    the CONCRETE [keystone_inj]/[keystone_prj] and representability [Vrep64 n := Z.of_nat n < 2^63].  The
    section hypotheses are then DISCHARGED — [keystone_roundtrip] is exactly [Hret], [Vrep64_0] is [Vrep0].
    So [denote_adequate] / [denote_adequate_mem] hold for a REAL coding: the typed↔operational bridge
    genuinely connects the calculus to the emitted Go (for representable = real int64 values), no longer a
    vacuous implication parameterised by an impossible round-trip. *)
Definition denote_adequate_keystone (chenv : nat -> GoChan GoI64) (locenv : nat -> Ref GoI64) :=
  denote_adequate chenv locenv keystone_inj keystone_prj Vrep64 keystone_roundtrip.
Definition denote_adequate_mem_keystone (chenv : nat -> GoChan GoI64) (locenv : nat -> Ref GoI64) :=
  denote_adequate_mem chenv locenv keystone_inj keystone_prj Vrep64 keystone_roundtrip Vrep64_0.

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

(** ── OWNERSHIP-TRANSFER handoff is GENERATED by a real execution (write/WRITE). ──
    [handoff_trace] (the write-WRITE ownership transfer — g0 writes loc 7, hands it off over channel
    0, then g1 WRITES the same loc 7) was HAND-WRITTEN; [handoff_race_free] proved it race-free at the
    trace level (the two conflicting writes are ordered by the send→recv, [transfer_orders]).  Here the
    SAME trace is PRODUCED BY RUNNING a transfer program: g0 = [CWrite 7; CSend 0], g1 = [CRecv 0;
    CWrite 7].  Executing the canonical interleaving yields EXACTLY [handoff_trace], so its
    race-freedom is now a property of an actual RUN — the operational analogue of [mp_exec_trace], but
    for a WRITE/WRITE conflict (mp's is write/READ).  This is the program-level grounding the
    ownership-TRANSFER principle needed (the prior exec witnesses — mp/fork/dst — are all write/READ
    handoffs; none had the receiver WRITE the handed-off cell).  Both goroutines pre-live (no spawn). *)
Definition xfer_prog (v0 v1 v2 : nat) : nat -> Cmd :=
  fun t => if Nat.eqb t 0 then CWrite 7 v0 (CSend 0 v1 CRet)
           else if Nat.eqb t 1 then CRecv 0 (fun _ => CWrite 7 v2 CRet)
           else CRet.
Definition xfer_init (v0 v1 v2 : nat) : RConfig :=
  mkRCfg (xfer_prog v0 v1 v2) (fun _ => []) (fun _ => 0)
         (fun t => orb (Nat.eqb t 0) (Nat.eqb t 1)) [].

Theorem xfer_exec_trace : forall v0 v1 v2,
  exists cfg, rsteps (xfer_init v0 v1 v2) cfg /\ rc_trace cfg = handoff_trace.
Proof.
  intros v0 v1 v2. unfold xfer_init, xfer_prog. eexists. split.
  - eapply rsteps_step. { eapply rstep_write with (tid := 0); upd_proj; reflexivity. }
    eapply rsteps_step. { eapply rstep_send  with (tid := 0); upd_proj; reflexivity. }
    eapply rsteps_step. { eapply rstep_recv  with (tid := 1); upd_proj; reflexivity. }
    eapply rsteps_step. { eapply rstep_write with (tid := 1); upd_proj; reflexivity. }
    apply rsteps_refl.
  - cbn. reflexivity.
Qed.

(** Hence the transfer program's EXECUTION is race-free — the conflicting WRITE/WRITE pair on the
    handed-off cell (loc 7) is ordered by the channel handoff, not concurrent. *)
Theorem xfer_exec_race_free : forall v0 v1 v2,
  exists cfg, rsteps (xfer_init v0 v1 v2) cfg /\ TraceRaceFree (rc_trace cfg).
Proof.
  intros v0 v1 v2. destruct (xfer_exec_trace v0 v1 v2) as [cfg [Hsteps Htr]].
  exists cfg. split; [exact Hsteps |]. rewrite Htr. exact handoff_race_free.
Qed.

(** The transfer's OUTCOME, operationally: after the full run the handed-off cell holds [v2] — the
    RECEIVER's write WON, deterministically, BECAUSE the two writes are sync-ordered (g0's first, g1's
    last) — and the channel has DRAINED.  An ordered ownership transfer yields a single well-defined
    final value (no race, no nondeterministic last-writer). *)
Theorem xfer_exec_state : forall v0 v1 v2,
  exists cfg, rsteps (xfer_init v0 v1 v2) cfg
    /\ rc_trace cfg = handoff_trace
    /\ rc_heap cfg 7 = v2         (* g1's write is the LAST write to loc 7 *)
    /\ rc_bufs cfg 0 = [].        (* the channel drained *)
Proof.
  intros v0 v1 v2. unfold xfer_init, xfer_prog. eexists. split; [| split; [| split]].
  - eapply rsteps_step. { eapply rstep_write with (tid := 0); upd_proj; reflexivity. }
    eapply rsteps_step. { eapply rstep_send  with (tid := 0); upd_proj; reflexivity. }
    eapply rsteps_step. { eapply rstep_recv  with (tid := 1); upd_proj; reflexivity. }
    eapply rsteps_step. { eapply rstep_write with (tid := 1); upd_proj; reflexivity. }
    apply rsteps_refl.
  - cbn. reflexivity.
  - cbn [rc_heap]. upd_proj. reflexivity.
  - cbn [rc_bufs]. upd_proj. reflexivity.
Qed.

(** ── DYNAMIC-SPAWN+CHANNEL HANDOFF is GENERATED by a real execution. ──
    [dst_trace] (the trace-core brick above [mp_trace_race_free]) was HAND-WRITTEN.  Here the SAME trace
    is PRODUCED BY RUNNING a program that COMBINES dynamic spawn with channel handoff — the third handoff
    composition, distinct from both [mp_exec_trace] (channel, both pre-live) and [fork_exec_trace] (spawn,
    fork edge only).  g0 writes loc 0, SPAWNS the child (initially only g0 is live, so [rstep_spawn]
    allocates a fresh tid — here cid 1), then SENDS on chan 0; the child RECVS chan 0 (matched send at
    trace position 3 — recorded in the buffer entry) then READS loc 0.  Executing this canonical
    interleaving yields EXACTLY [dst_trace 1], so its race-freedom ([dst_trace_race_free]) is now about a
    REACHABLE state of an actual spawn+channel program, not a literal.  The all-interleavings invariant
    ([DSTReach], a [MpReach]/[ForkReach]-style reachability with the child tid existential) is the
    follow-on slice (this mirrors how [mp]/[fork] each went trace-core → exec → all-interleavings). *)
Definition dst_child : Cmd := CRecv 0 (fun _ => CRead 0 (fun _ => CRet)).
Definition dst_prog (v0 v1 : nat) : nat -> Cmd :=
  fun t => if Nat.eqb t 0
           then CWrite 0 v0 (CSpawn dst_child (CSend 0 v1 CRet))
           else CRet.

Theorem dst_exec_trace : forall v0 v1,
  exists cfg, rsteps (rinit_cfg (dst_prog v0 v1)) cfg /\ rc_trace cfg = dst_trace 1.
Proof.
  intros v0 v1. unfold rinit_cfg, dst_prog, dst_child. eexists. split.
  - eapply rsteps_step. { eapply rstep_write with (tid := 0); upd_proj; reflexivity. }
    eapply rsteps_step. { eapply rstep_spawn with (tid := 0) (cid := 1); upd_proj; reflexivity. }
    eapply rsteps_step. { eapply rstep_send  with (tid := 0); upd_proj; reflexivity. }
    eapply rsteps_step. { eapply rstep_recv  with (tid := 1); upd_proj; reflexivity. }
    eapply rsteps_step. { eapply rstep_read  with (tid := 1); upd_proj; reflexivity. }
    apply rsteps_refl.
  - cbn. reflexivity.
Qed.

(** Hence the spawn+channel handoff's EXECUTION is race-free: the trace it generates is [dst_trace 1],
    whose only conflicting cross-goroutine pair (g0's write / the child's read of loc 0) is ordered by
    the channel handoff carried across the spawn. *)
Theorem dst_exec_race_free : forall v0 v1,
  exists cfg, rsteps (rinit_cfg (dst_prog v0 v1)) cfg /\ TraceRaceFree (rc_trace cfg).
Proof.
  intros v0 v1. destruct (dst_exec_trace v0 v1) as [cfg [Hsteps Htr]].
  exists cfg. split; [exact Hsteps |]. rewrite Htr. exact (dst_trace_race_free 1).
Qed.

(** The handoff's OUTCOME, operationally: after the full run, the cell g0 wrote (loc 0) still holds [v0]
    — it survived the spawn AND the channel handoff and was the value the child read — and the channel has
    DRAINED.  The spawn+channel mirror of [mp_exec_state]. *)
Theorem dst_exec_state : forall v0 v1,
  exists cfg, rsteps (rinit_cfg (dst_prog v0 v1)) cfg
    /\ rc_trace cfg = dst_trace 1
    /\ rc_heap cfg 0 = v0
    /\ rc_bufs cfg 0 = [].
Proof.
  intros v0 v1. unfold rinit_cfg, dst_prog, dst_child. eexists. split; [| split; [| split]].
  - eapply rsteps_step. { eapply rstep_write with (tid := 0); upd_proj; reflexivity. }
    eapply rsteps_step. { eapply rstep_spawn with (tid := 0) (cid := 1); upd_proj; reflexivity. }
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

(** ── ALL-INTERLEAVINGS for the ownership-TRANSFER program (write/WRITE). ──
    [xfer_exec_race_free] above witnessed ONE execution of the transfer program race-free.  Here, as
    [mp_all_interleavings_race_free] does for the write/READ handoff, EVERY interleaving is race-free:
    [XferReach] is the 5-phase reachability invariant (init → g0 write 7 → g0 send → g1 recv → g1 WRITE
    7), rstep-PRESERVED, implying [TraceRaceFree].  Phases A–D have ≤1 memory access (only g0's write 7,
    at position 0); phase E is [handoff_trace], whose conflicting write/write pair is sync-ordered
    ([handoff_race_free]).  So the receiver's write to the handed-off cell is race-free under ANY
    schedule — the all-interleavings strengthening of the transfer witness. *)
Definition XferReach (v0 v1 v2 : nat) (cfg : RConfig) : Prop :=
  rc_live cfg = (fun t => orb (Nat.eqb t 0) (Nat.eqb t 1))
  /\ ( (rc_trace cfg = [] /\ rc_prog cfg 0 = CWrite 7 v0 (CSend 0 v1 CRet)
        /\ rc_prog cfg 1 = CRecv 0 (fun _ => CWrite 7 v2 CRet) /\ rc_bufs cfg 0 = [])
    \/ (rc_trace cfg = [mkEv 0 (KWrite 7)] /\ rc_prog cfg 0 = CSend 0 v1 CRet
        /\ rc_prog cfg 1 = CRecv 0 (fun _ => CWrite 7 v2 CRet) /\ rc_bufs cfg 0 = [])
    \/ (rc_trace cfg = [mkEv 0 (KWrite 7); mkEv 0 (KSend 0)] /\ rc_prog cfg 0 = CRet
        /\ rc_prog cfg 1 = CRecv 0 (fun _ => CWrite 7 v2 CRet) /\ rc_bufs cfg 0 = [(v1, 1)])
    \/ (rc_trace cfg = [mkEv 0 (KWrite 7); mkEv 0 (KSend 0); mkEv 1 (KRecv 0 1)]
        /\ rc_prog cfg 0 = CRet /\ rc_prog cfg 1 = CWrite 7 v2 CRet /\ rc_bufs cfg 0 = [])
    \/ (rc_trace cfg = handoff_trace /\ rc_prog cfg 0 = CRet /\ rc_prog cfg 1 = CRet /\ rc_bufs cfg 0 = []) ).

Lemma xferreach_init : forall v0 v1 v2, XferReach v0 v1 v2 (xfer_init v0 v1 v2).
Proof.
  intros v0 v1 v2. unfold XferReach, xfer_init, xfer_prog. cbn.
  split; [reflexivity | left; repeat split; reflexivity].
Qed.

Lemma xferreach_race_free : forall v0 v1 v2 cfg, XferReach v0 v1 v2 cfg -> TraceRaceFree (rc_trace cfg).
Proof.
  intros v0 v1 v2 cfg [_ Hph].
  destruct Hph as [[Htr _]|[[Htr _]|[[Htr _]|[[Htr _]|[Htr _]]]]]; rewrite Htr;
    try (apply mem_access_only0_race_free; intros i ai Hi;
         pose proof (tr_acc_lt _ _ _ Hi) as L; destruct i as [|[|[|i]]]; cbn in Hi;
         first [reflexivity | discriminate Hi | (cbn in L; lia)]).
  exact handoff_race_free.   (* phase E = handoff_trace: ordered write/write transfer *)
Qed.

Lemma xferreach_step : forall v0 v1 v2 cfg cfg',
  rstep cfg cfg' -> XferReach v0 v1 v2 cfg -> XferReach v0 v1 v2 cfg'.
Proof.
  intros v0 v1 v2 cfg cfg' Hstep [Hlive Hph].
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
  (* The four surviving goals: A→B (g0 write), B→C (g0 send), C→D (g1 recv), D→E (g1 WRITE). *)
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
  - (* D→E : g1 WRITE (the receiver writes the handed-off cell — vs mp's READ) *)
    injection Hp as Hl _ Hk; subst l; subst k.
    split; [cbn [rc_live]; exact Hlive |].
    right; right; right; right. rewrite Htr. cbn [rc_trace rc_prog rc_bufs]. upd_proj.
    repeat split; first [reflexivity | assumption | (symmetry; assumption)].
Qed.

Lemma xferreach_steps : forall v0 v1 v2 cfg cfg',
  rsteps cfg cfg' -> XferReach v0 v1 v2 cfg -> XferReach v0 v1 v2 cfg'.
Proof.
  intros v0 v1 v2 cfg cfg' H. induction H; intros HM; [exact HM|].
  apply IHrsteps. exact (xferreach_step _ _ _ _ _ H HM).
Qed.

(** EVERY interleaving of the transfer program is race-free — the all-interleavings strengthening of
    [xfer_exec_race_free], the write/WRITE analogue of [mp_all_interleavings_race_free]. *)
Theorem xfer_all_interleavings_race_free : forall v0 v1 v2 cfg,
  rsteps (xfer_init v0 v1 v2) cfg -> TraceRaceFree (rc_trace cfg).
Proof.
  intros v0 v1 v2 cfg Hsteps.
  apply (xferreach_race_free v0 v1 v2).
  exact (xferreach_steps _ _ _ _ _ Hsteps (xferreach_init v0 v1 v2)).
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
    LIMIT #2 — slice 2c: THE ONE CLOSED END-TO-END THEOREM (concrete handoff).

    The pieces existed SEPARATELY — 2a ([mp_exec_trace]: operational execution → [mp_trace],
    race-free over ALL interleavings via [mp_all_interleavings_race_free]); 2b ([mp_g0_denotes]/
    [mp_g1_denotes]: each goroutine DENOTES extractable typed *T-over-channel IO); the World
    refinement ([wstate_steps]: channels AND heap matched in ONE [run_io] world); and value
    correctness ([mp_handoff_delivers]).  [mp_end_to_end] COMPOSES them for the concrete typed
    pointer-handoff [mp_prog] under ONE coherent environment ([chenv]/[ptrenv]/[inj]/[prj]):
    a single theorem witnessing that the extractable typed concurrent program (a) executes to
    [mp_trace], (b) race-free on THIS run AND on every interleaving, (c) with each goroutine the
    Keystone-denotation of real typed IO, (d) its full state (channels + memory) realized by a
    [run_io] world, and (e) the equivalent single-threaded handoff IO delivering exactly
    [(inj v1, inj v0)].  This is the closed end-to-end tie the [MpTyped] header deferred — "stated
    per-goroutine here, not overstated" — now stated WHOLE, for one real program.  (N-goroutine
    GENERALITY stays a frontier: [go_spawn] has no [run_io] law by design, so the cross-goroutine
    glue is the STATE refinement (d), not a whole-program [run_io] denotation.)  Proof-only
    (concurrency.v emits no Go) — composes the established lemmas, adds no axiom.
    ============================================================================ *)
Theorem mp_end_to_end :
  forall (chenv : nat -> GoChan GoI64) (ptrenv : nat -> Ptr GoI64)
         (inj : nat -> GoI64) (prj : GoI64 -> nat) (v0 v1 : nat) (w0 : World),
    (forall i j, chenv i = chenv j -> i = j) ->
    (forall i j, r_loc (plocenv ptrenv i) = r_loc (plocenv ptrenv j) -> i = j) ->
    (forall l, PrimInt63.eqb (p_loc (ptrenv l)) 0%uint63 = false) ->
    (forall c, chan_buf TI64 (chenv c) w0 = []) ->
    chan_closed (chenv 0) w0 = false ->
    (forall l, ref_sel (plocenv ptrenv l) w0 = inj 0) ->
    exists cfg,
      (* (a) the typed program EXECUTES, generating the canonical handoff trace *)
      rsteps (mp_init v0 v1) cfg
      /\ rc_trace cfg = mp_trace
      (* (b) race-free — this run, and EVERY interleaving *)
      /\ TraceRaceFree (rc_trace cfg)
      /\ (forall cfg', rsteps (mp_init v0 v1) cfg' -> TraceRaceFree (rc_trace cfg'))
      (* (c) each goroutine of mp_prog is the Keystone-denotation of EXTRACTABLE typed IO *)
      /\ Denotes chenv (plocenv ptrenv) inj prj (mp_prog v0 v1 0) (mp_g0_io chenv ptrenv inj v0 v1)
      /\ Denotes chenv (plocenv ptrenv) inj prj (mp_prog v0 v1 1) (mp_g1_io chenv ptrenv)
      (* (d) the FULL reachable state — channels AND memory — is realized by one run_io world *)
      /\ (exists w, WMatchC chenv inj w cfg /\ WHMatchC (plocenv ptrenv) inj w cfg)
      (* (e) the equivalent single-threaded handoff IO delivers exactly the right values *)
      /\ (exists w', run_io (mp_handoff_io chenv ptrenv inj v0 v1) w0 = ORet (inj v1, inj v0) w').
Proof.
  intros chenv ptrenv inj prj v0 v1 w0 Hchen Hloc Hlive Hbuf Hcl Hheap.
  destruct (mp_exec_trace v0 v1) as [cfg [Hsteps Htr]].
  exists cfg.
  split; [exact Hsteps |].
  split; [exact Htr |].
  split; [rewrite Htr; exact mp_trace_race_free |].
  split; [exact (mp_all_interleavings_race_free v0 v1) |].
  split.
  { rewrite (proj1 (mp_prog_goroutines v0 v1)).
    exact (mp_g0_denotes chenv ptrenv inj prj Hlive v0 v1). }
  split.
  { rewrite (proj2 (mp_prog_goroutines v0 v1)).
    exact (mp_g1_denotes chenv ptrenv inj prj Hlive). }
  split.
  { assert (Hinit : WState chenv (plocenv ptrenv) inj w0 (mp_init v0 v1)).
    { split.
      - intro c. unfold rchan, mp_init; cbn [rc_bufs]. rewrite Hbuf. reflexivity.
      - intro l. unfold mp_init; cbn [rc_heap]. exact (Hheap l). }
    destruct (wstate_steps chenv (plocenv ptrenv) inj Hchen Hloc
                (mp_init v0 v1) cfg w0 Hsteps Hinit) as [w HW].
    exists w. exact HW. }
  exact (mp_handoff_delivers chenv ptrenv inj Hlive v0 v1 w0 (Hbuf 0) Hcl).
Qed.

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

(** ============================================================================
    PRIVATE-MEMORY brick, SCALED: an ARBITRARY-N private parallel program is BOTH
    race-free AND deadlock-free — full safety + liveness, for EVERY N.

    The brick-1 theorem [private_disc_reachable_race_free] holds for arbitrary N; here
    is a PARAMETRIC witness ([priv_prog_N]: for any N, goroutines 0..N-1 each write their
    OWN location, pre-live, no channels/spawn) that instantiates it for UNBOUNDED N, and
    ADDS liveness via the [PureLocal] fragment — programs of only [CWrite]/[CRead]/[CRet]
    (pure shared-memory computation): never blocked (no [CRecv]/[CSelect] head) and never
    panicking (no [CSend]/[CClose] head), so a live unfinished goroutine ALWAYS lets the
    config step.  So unbounded-N private parallel programs run race-free to completion.
    Proof-only.  ============================================================================ *)
Inductive PureLocal : Cmd -> Prop :=
  | PL_ret   : PureLocal CRet
  | PL_write : forall l v k, PureLocal k -> PureLocal (CWrite l v k)
  | PL_read  : forall l f, (forall v, PureLocal (f v)) -> PureLocal (CRead l f).
Definition PureLocalCfg (cfg : RConfig) : Prop :=
  forall tid, rc_live cfg tid = true -> PureLocal (rc_prog cfg tid).

Lemma pl_write_inv : forall l v k, PureLocal (CWrite l v k) -> PureLocal k.
Proof. intros l v k H. inversion H; subst. assumption. Qed.
Lemma pl_read_inv : forall l f, PureLocal (CRead l f) -> forall v, PureLocal (f v).
Proof. intros l f H. inversion H; subst. assumption. Qed.
Lemma pl_not_send   : forall c v k, PureLocal (CSend c v k) -> False.
Proof. intros c v k H. inversion H. Qed.
Lemma pl_not_recv   : forall c f, PureLocal (CRecv c f) -> False.
Proof. intros c f H. inversion H. Qed.
Lemma pl_not_spawn  : forall child k, PureLocal (CSpawn child k) -> False.
Proof. intros child k H. inversion H. Qed.
Lemma pl_not_select : forall cases, PureLocal (CSelect cases) -> False.
Proof. intros cases H. inversion H. Qed.
Lemma pl_not_close  : forall c k, PureLocal (CClose c k) -> False.
Proof. intros c k H. inversion H. Qed.

Lemma pl_not_blocked : forall cfg tid, PureLocal (rc_prog cfg tid) -> ~ blocked cfg tid.
Proof. intros cfg tid HPL [[c [f [Hp _]]] | [cases [Hp _]]]; rewrite Hp in HPL; inversion HPL. Qed.
Lemma pl_not_panicking : forall cfg tid, PureLocal (rc_prog cfg tid) -> ~ rpanicking cfg tid.
Proof. intros cfg tid HPL [[c [k [Hp _]]] | [c [v [k [Hp _]]]]]; rewrite Hp in HPL; inversion HPL. Qed.

Lemma purelocal_upd : forall (p : nat -> Cmd) tid cont (lv : nat -> bool) g,
  (forall g', lv g' = true -> PureLocal (p g')) -> PureLocal cont -> lv g = true ->
  PureLocal (upd p tid cont g).
Proof.
  intros p tid cont lv g Hp Hcont Hg.
  destruct (Nat.eq_dec g tid) as [->|Hne].
  - rewrite upd_same. exact Hcont.
  - rewrite (upd_other p tid cont g Hne). exact (Hp g Hg).
Qed.

Lemma pure_local_step : forall cfg cfg', rstep cfg cfg' -> PureLocalCfg cfg -> PureLocalCfg cfg'.
Proof.
  intros cfg cfg' Hstep HPL. unfold PureLocalCfg in HPL |- *.
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
    cbn [rc_prog rc_live] in HPL |- *; intros g Hg;
    pose proof (HPL tid Hlv) as H; rewrite Hp in H.
  - exfalso. exact (pl_not_send _ _ _ H).
  - exfalso. exact (pl_not_recv _ _ H).
  - exact (purelocal_upd p tid k lv g HPL (pl_write_inv _ _ _ H) Hg).
  - exact (purelocal_upd p tid (f (h l)) lv g HPL (pl_read_inv _ _ H (h l)) Hg).
  - exfalso. exact (pl_not_spawn _ _ H).
  - exfalso. exact (pl_not_select _ H).
  - exfalso. exact (pl_not_close _ _ H).
  - exfalso. exact (pl_not_recv _ _ H).
  - exfalso. exact (pl_not_select _ H).
Qed.

Lemma pure_local_steps : forall a b, rsteps a b -> PureLocalCfg a -> PureLocalCfg b.
Proof.
  intros a b H. induction H as [cfg | a b c Hab Hbc IH]; intros HPL; [exact HPL|].
  apply IH. exact (pure_local_step _ _ Hab HPL).
Qed.

(* A live, unfinished, PURE-LOCAL goroutine always lets the config step — no deadlock, no panic. *)
Lemma pure_local_progress : forall cfg tid,
  FreshAvail cfg -> PureLocalCfg cfg ->
  rc_live cfg tid = true -> rc_prog cfg tid <> CRet -> rcan_step cfg.
Proof.
  intros cfg tid Hfresh HPL Hlive Hnret.
  apply (ready_can_step cfg tid Hfresh Hlive Hnret).
  - apply pl_not_blocked. exact (HPL tid Hlive).
  - apply pl_not_panicking. exact (HPL tid Hlive).
Qed.

Lemma rsteps_livefin : forall a b, rsteps a b -> LiveFin a -> LiveFin b.
Proof.
  intros a b H. induction H as [cfg | a b c Hab Hbc IH]; intros HLF; [exact HLF|].
  apply IH. exact (rstep_livefin _ _ Hab HLF).
Qed.

(* The arbitrary-N private parallel program: goroutine t (for t < N) writes location t. *)
Definition priv_prog_N (N : nat) : nat -> Cmd :=
  fun t => if Nat.ltb t N then CWrite t 0 CRet else CRet.
Definition priv_init_N (N : nat) : RConfig :=
  mkRCfg (priv_prog_N N) (fun _ => []) (fun _ => 0) (fun t => Nat.ltb t N) [].

Lemma priv_init_N_disc : forall N, PrivateDisc (fun l => l) (priv_init_N N).
Proof.
  intros N. split.
  - intros i l Hacc. cbn in Hacc. unfold acc_loc_at in Hacc. destruct i; cbn in Hacc; discriminate.
  - intros g Hg. unfold priv_init_N, priv_prog_N in *. cbn [rc_live rc_prog] in Hg |- *.
    destruct (Nat.ltb g N) eqn:E.
    + apply OA_write; [reflexivity | apply OA_ret].
    + congruence.
Qed.
Lemma priv_init_N_purelocal : forall N, PureLocalCfg (priv_init_N N).
Proof.
  intros N g Hg. unfold priv_init_N, priv_prog_N in *. cbn [rc_live rc_prog] in Hg |- *.
  destruct (Nat.ltb g N) eqn:E.
  - apply PL_write. apply PL_ret.
  - congruence.
Qed.
Lemma priv_init_N_livefin : forall N, LiveFin (priv_init_N N).
Proof. intros N. exists N. intros t Ht. cbn. apply Nat.ltb_ge. exact Ht. Qed.

(** SAFETY: for EVERY N, every interleaving of the N-way private parallel program is race-free. *)
Theorem priv_prog_N_race_free : forall N cfg,
  rsteps (priv_init_N N) cfg -> TraceRaceFree (rc_trace cfg).
Proof.
  intros N cfg Hsteps.
  exact (proj2 (private_disc_reachable_race_free (fun l => l) (priv_init_N N) cfg
                 (priv_init_N_disc N) Hsteps)).
Qed.

(** LIVENESS: for EVERY N, at any reachable state, any live goroutine with work left lets the config
    step — the program NEVER deadlocks and NEVER panics; it runs to completion. *)
Theorem priv_prog_N_deadlock_free : forall N cfg tid,
  rsteps (priv_init_N N) cfg -> rc_live cfg tid = true -> rc_prog cfg tid <> CRet ->
  rcan_step cfg.
Proof.
  intros N cfg tid Hsteps Hlive Hnret.
  pose proof (pure_local_steps _ _ Hsteps (priv_init_N_purelocal N)) as HPL.
  pose proof (rsteps_livefin _ _ Hsteps (priv_init_N_livefin N)) as HLF.
  exact (pure_local_progress cfg tid (livefin_fresh _ HLF) HPL Hlive Hnret).
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

(* ====================================================================== *)
(** * Forge-proof session typing — the protocol indices are OPERATIONAL.

    [builtins.v]'s extracted session type WAS a one-field RECORD [Sess i j A :=
    MkSess { run_sess : IO A }], so the public [MkSess] wrapped an ARBITRARY [IO A]
    regardless of the protocol indices: [MkSess (ret tt) : Sess (PSend A P) P unit]
    type-checked yet COMMUNICATED NOTHING — the indices were phantom (review #3 R9).
    Rocq 9.2 cannot make a record constructor private without opaque module
    ascription (which needs a Module-Type [Parameter]); the chosen fix is the
    DEEPER one — tie the run to the protocol so the index simply CANNOT lie.  [Sess]
    in builtins.v has since been MIGRATED onto this inductive shape (so the extracted
    type is forge-proof too) AND UNIFIED with this theory: [PSess]/[PS…] below are now
    plain aliases for the extracted [builtins.Sess]/[S…], so every theorem here is
    LITERALLY about the forge-proof type Fido emits.

    A session becomes an INDUCTIVE [PSess] indexed by the protocol, whose only
    builders are the disciplined combinators (send / recv / ret / lift / bind).
    There is no "wrap arbitrary [IO] at the wrong protocol" constructor, so the
    index is structurally honest.  We read off the COMMUNICATION TRACE a [PSess]
    performs ([PEmits]) and prove it is EXACTLY the sequence the protocol
    prescribes ([proto_steps]) — making the indices a genuine behavioural
    specification.  This is brick 1 of the R9 deeper fix; later bricks denote
    [PSess] into the [builtins.v] channel IO and migrate the extracted [Sess]. *)

(** A protocol step's observable shape: send or receive of a value of a type.
    ([PK…] avoids [EvKind]'s [KSend]/[KRecv], which instead carry a channel id.) *)
Inductive StepKind : Type :=
  | PKSend : Type -> StepKind
  | PKRecv : Type -> StepKind.

(** The communication sequence a protocol prescribes, head-first ([PEnd ↦ []]). *)
Fixpoint proto_steps (p : Proto) : list StepKind :=
  match p with
  | builtins.PSend A p' => PKSend A :: proto_steps p'
  | builtins.PRecv A p' => PKRecv A :: proto_steps p'
  | PEnd                 => []
  end.

(** The forge-proof session type is the EXTRACTED [builtins.Sess] (post-migration
    UNIFICATION, 2026-06-22) — an inductive whose constructors are the disciplined
    ops [SRet]/[SSend]/[SRecv]/[SLift]/[SBind].  Each step that advances the protocol
    performs the matching communication; [SLift] (local IO, no message) keeps the
    state FIXED ([P ↦ P]) so it cannot forge a send/recv step; there is no
    [MkSess]-style "arbitrary [IO] at any index" builder.  [PSess]/[PS…] below are
    readable ALIASES for [Sess]/[S…], so this whole theory is LITERALLY about the
    forge-proof type Fido emits. *)
Notation PSess := Sess.
Notation PSRet := SRet.
Notation PSSend := SSend.
Notation PSRecv := SRecv.
Notation PSLift := SLift.
Notation PSBind := SBind.

(** The communication trace a session performs.  A RELATION, not a [Fixpoint]:
    [PSBind]'s continuation [k a] is not a structural subterm (so a recursive
    function would fail the guard), and the bound value [a] is immaterial anyway —
    [k a]'s indices [Q ↦ R] fix its trace for EVERY [a] (proved in the [PSBind]
    case below).  Soundness is then an induction on this derivation. *)
Inductive PEmits : forall {i j : Proto} {A : Type}, PSess i j A -> list StepKind -> Prop :=
  | EmitRet  : forall (P : Proto) (A : Type) (x : A),
                 PEmits (@PSRet P A x) []
  | EmitSend : forall (A : Type) (P : Proto) (v : A),
                 PEmits (@PSSend A P v) [PKSend A]
  | EmitRecv : forall (A : Type) (P : Proto) (tag : GoTypeTag A),
                 PEmits (@PSRecv A P tag) [PKRecv A]
  | EmitLift : forall (P : Proto) (A : Type) (m : IO A),
                 PEmits (@PSLift P A m) []
  | EmitBind : forall (P Q R : Proto) (A B : Type)
                      (m : PSess P Q A) (k : A -> PSess Q R B) (a : A)
                      (sm sk : list StepKind),
                 PEmits m sm -> PEmits (k a) sk ->
                 PEmits (@PSBind P Q R A B m k) (sm ++ sk).

(** SOUNDNESS — the operational tie.  Whatever trace [steps] a session emits,
    appending the steps still OWED from its end state [j] reconstructs the FULL
    protocol [i].  So the session performs EXACTLY the [i ↦ j] fragment — no
    silent skips, no spurious extra messages.  The index is the behaviour. *)
Theorem psess_emits_proto :
  forall (i j : Proto) (A : Type) (s : PSess i j A) (steps : list StepKind),
    PEmits s steps -> steps ++ proto_steps j = proto_steps i.
Proof.
  intros i j A s steps H.
  induction H as [ | | | | P Q R A0 B m k a sm sk Hm IHm Hk IHk ]; simpl.
  - reflexivity.                       (* Ret  : [] ++ proto_steps P = proto_steps P *)
  - reflexivity.                       (* Send : [PKSend A] ++ steps P = steps (PSend A P) *)
  - reflexivity.                       (* Recv : symmetric *)
  - reflexivity.                       (* Lift : [] ++ proto_steps P = proto_steps P *)
  - rewrite <- app_assoc, IHk. exact IHm.   (* Bind : (sm++sk)++R = sm++(sk++R) = sm++Q = P *)
Qed.

(** Headline corollary: a COMPLETE session ([j = PEnd]) performs PRECISELY the
    protocol's whole communication sequence.  The forged [MkSess (ret tt) : Sess
    (PSend A P) P unit] — which would emit [[]] ≠ [[PKSend A; …]] — has NO [PSess]
    counterpart, so the leak that motivated R9 is closed by construction here. *)
Corollary psess_full_emits_proto :
  forall (i : Proto) (A : Type) (s : PSess i PEnd A) (steps : list StepKind),
    PEmits s steps -> steps = proto_steps i.
Proof.
  intros i A s steps H.
  apply psess_emits_proto in H. simpl in H.
  rewrite app_nil_r in H. exact H.
Qed.

(** The PRECISE contrast with the forgeable record.  NO session that opens with a
    send can emit the empty trace: [steps = []] would force [proto_steps P] to be
    its own proper tail (a strictly longer list), which a length argument refutes.
    [MkSess (ret tt) : Sess (PSend A P) P unit] is exactly that impossible-here
    forgery — emitting nothing while typed as a send. *)
Corollary psess_send_nonempty :
  forall (A : Type) (P : Proto) (s : PSess (builtins.PSend A P) P unit) (steps : list StepKind),
    PEmits s steps -> steps <> [].
Proof.
  intros A P s steps H. apply psess_emits_proto in H. simpl in H.
  intro Hnil. rewrite Hnil in H. simpl in H.
  apply (f_equal (@length StepKind)) in H. simpl in H. lia.
Qed.

(** Concrete witness that the model is inhabited and the trace is exactly the
    protocol's: a client for [PSend unit PEnd] that sends [tt] then ends. *)
Definition ex_proto : Proto := builtins.PSend unit PEnd.

Definition ex_client : PSess ex_proto PEnd unit :=
  PSBind (PSSend tt) (fun _ => PSRet tt).

Example ex_client_emits : PEmits ex_client (proto_steps ex_proto).
Proof.
  unfold ex_client, ex_proto. cbn [proto_steps].
  rewrite <- (app_nil_r [PKSend unit]).
  eapply EmitBind with (a := tt).
  - apply EmitSend.
  - apply EmitRet.
Qed.

(** Trust base — verified via [Print Assumptions psess_full_emits_proto] /
    [psess_send_nonempty] (2026-06-22): EXACTLY Rocq's primitive substrate,
    [PrimInt63.*] / [PrimFloat.*] with their spec axioms ([Uint63Axioms.*]),
    pulled in only because [PSess] mentions [IO]/[GoTypeTag].  No funext, no
    Eqdep / UIP / JMeq — the dependent [induction] on [PEmits] stays clean (it is
    plain [induction], NEVER the Eqdep-introducing dependent variant that would
    breach rule 3) — and no project-declared assumption and no unfinished proof of
    any kind.  So the soundness of the protocol-indexed session rests on the same
    trust base as the rest of Fido, and the seal-vs-deeper-fix tension of R9 is
    sidestepped entirely. *)

(** ** Session DUALITY — the client and server agree (communication safety).

    The whole point of a session TYPE is that the two endpoints follow
    COMPLEMENTARY protocols: where one sends, the other receives the SAME type, in
    the SAME order.  [dual] (builtins.v) flips every send↔recv at the protocol
    level; here we lift it to the TRACE level and prove a client realising [P] and a
    server realising [dual P] perform traces that are exact mirror images — every
    message the client sends is exactly the one the server receives, with no type
    mismatch and no orphaned message.  This is the deadlock/agreement core of
    session typing, now proved for the forge-proof [PSess].  Brick 2 of the R9
    deeper fix (still pure-protocol; the channel-IO denotation is brick 3). *)

(** A single step's complement: a send of [A] is matched by a receive of [A]. *)
Definition flip_step (s : StepKind) : StepKind :=
  match s with
  | PKSend A => PKRecv A
  | PKRecv A => PKSend A
  end.

Lemma flip_step_involutive : forall s, flip_step (flip_step s) = s.
Proof. intros [A | A]; reflexivity. Qed.

(** The dual protocol prescribes EXACTLY the flipped communication sequence. *)
Theorem proto_steps_dual : forall p : Proto,
  proto_steps (dual p) = map flip_step (proto_steps p).
Proof.
  induction p as [A p' IH | A p' IH | ]; simpl.
  - rewrite IH. reflexivity.            (* PSend A p' ↦ dual gives PRecv, flip gives PKRecv *)
  - rewrite IH. reflexivity.            (* PRecv A p' ↦ symmetric *)
  - reflexivity.                        (* PEnd ↦ [] = map _ [] *)
Qed.

(** COMMUNICATION SAFETY for a session pair: a complete client realising [P] and a
    complete server realising [dual P] emit traces that are exact mirror images —
    the server receives precisely what the client sends (same types, same order),
    and vice versa.  No type mismatch, no orphaned or missing message.  Proved for
    the forge-proof [PSess], so a well-typed session pair CANNOT desynchronise — the
    classical session-types safety property, here a corollary of [PSess] soundness
    plus protocol duality. *)
Corollary psess_pair_complementary :
  forall (P : Proto) (client : PSess P PEnd unit) (server : PSess (dual P) PEnd unit)
         (cs ss : list StepKind),
    PEmits client cs -> PEmits server ss -> ss = map flip_step cs.
Proof.
  intros P client server cs ss Hc Hs.
  apply psess_full_emits_proto in Hc.
  apply psess_full_emits_proto in Hs.
  subst cs ss. apply proto_steps_dual.
Qed.

(** Trust base — verified by [Print Assumptions] (2026-06-22): [proto_steps_dual]
    is "Closed under the global context" (FULLY axiom-free — pure protocol algebra
    over [Proto]/[list], touches no primitive); [psess_pair_complementary] inherits
    brick 1's substrate (PrimInt63.*/PrimFloat.* only, via [psess_full_emits_proto]).
    No funext, no Eqdep/UIP/JMeq anywhere, no project-declared assumption. *)

(** ** Session PROGRESS / deadlock-freedom — a dual pair never gets stuck.

    Brick 2 showed the FULL traces of a client/server pair mirror each other.  This
    brick shows the STEP-BY-STEP execution never deadlocks.  Model a synchronized
    communication as a [pair_step] on the two endpoints' REMAINING protocols (the
    matched head [PSend A] / [PRecv A] cancel, both advancing); then prove that a
    dual pair [(P, dual P)] is stuck ONLY at [(PEnd, PEnd)] — at every other state
    exactly one endpoint is ready to send while the other is ready to receive the
    SAME type, so a step is always available.  Together with the trace mirroring of
    brick 2 this is the classical session-types safety pair (PRESERVATION + PROGRESS).
    Protocol-level (a complete [PSess] realises its protocol by brick 1, so its
    available steps ARE these); brick 3 of the R9 deeper fix, still pure-protocol. *)

(** One synchronized step: the sender's head [PSend A] and the receiver's matching
    head [PRecv A] cancel, both endpoints advancing to their continuations. *)
Inductive pair_step : Proto * Proto -> Proto * Proto -> Prop :=
  | ps_send : forall (A : Type) (P' Q : Proto),
      pair_step (builtins.PSend A P', builtins.PRecv A Q) (P', Q)
  | ps_recv : forall (A : Type) (P' Q : Proto),
      pair_step (builtins.PRecv A P', builtins.PSend A Q) (P', Q).

(** PROGRESS + PRESERVATION in one: a dual pair is either both-finished, or it can
    take a matched step — AND the stepped pair is again dual (so the invariant that
    the two ends stay complementary is maintained for the whole run). *)
Theorem dual_pair_progress : forall P : Proto,
  (P = PEnd /\ dual P = PEnd) \/
  (exists P' Q' : Proto, pair_step (P, dual P) (P', Q') /\ Q' = dual P').
Proof.
  destruct P as [A P' | A P' | ]; simpl.
  - right. exists P', (dual P'). split; [ apply ps_send | reflexivity ].
  - right. exists P', (dual P'). split; [ apply ps_recv | reflexivity ].
  - left. split; reflexivity.
Qed.

(** DEADLOCK-FREEDOM: the ONLY dual pair that cannot step is the finished one
    [(PEnd, PEnd)].  So a well-typed session pair never wedges with one endpoint
    blocked on the other — it always either runs to completion or makes progress. *)
Corollary dual_pair_stuck_iff_done : forall P : Proto,
  (~ exists P' Q' : Proto, pair_step (P, dual P) (P', Q')) <-> P = PEnd.
Proof.
  intros P. split.
  - intros Hns. destruct (dual_pair_progress P) as [[HP _] | [P' [Q' [Hstep _]]]].
    + exact HP.
    + exfalso. apply Hns. exists P', Q'. exact Hstep.
  - intros ->. intros [P' [Q' H]]. simpl in H. inversion H.
Qed.

(** Trust base — pure protocol algebra over [Proto] (destruct + [inversion] on the
    first-order [pair_step], no dependent elimination): [dual_pair_progress] /
    [dual_pair_stuck_iff_done] are Closed under the global context (FULLY axiom-free
    — no PrimInt63/PrimFloat, no funext, no Eqdep/UIP).  Verified by [Print Assumptions]. *)

(** ** Session LIVENESS — a dual pair runs deterministically to completion.

    Brick 3 gave single-step progress (a dual pair can always step until done).
    This brick gives the WHOLE-RUN story: the synchronized reduction is
    DETERMINISTIC (no divergent choice) and TERMINATES at [(PEnd, PEnd)] — every
    well-typed session pair runs to completion in finitely many matched steps and
    halts at the unique stuck state (brick 3).  Together bricks 1–4 are the full
    session-types safety+liveness theory for the forge-proof [PSess]: SOUNDNESS (1),
    COMMUNICATION SAFETY (2), PROGRESS / deadlock-freedom (3), TERMINATION +
    DETERMINISM (4).  A real foundation note: a FAITHFUL real-channel denotation
    ([PSess] → [builtins] [IO] over a [GoChan]) is blocked — a heterogeneous session
    channel needs [GoChan GoAny] but [GoTypeTag GoAny] is universe-inconsistent
    (builtins.v), the same idealisation that forces [run_sess = ret tt]; the
    remaining extraction-soundness step is therefore the plugin MIGRATION, not a
    Rocq denotation.  Brick 4 of the R9 deeper fix, still pure-protocol. *)

(** Reflexive-transitive closure of [pair_step]: a whole synchronized run. *)
Inductive pair_steps : Proto * Proto -> Proto * Proto -> Prop :=
  | pss_refl : forall st, pair_steps st st
  | pss_step : forall st1 st2 st3,
      pair_step st1 st2 -> pair_steps st2 st3 -> pair_steps st1 st3.

(** TERMINATION: every dual pair reduces to the finished state [(PEnd, PEnd)] — the
    session always runs to completion (no infinite communication, no premature
    stop).  [proto_steps]'s length is the exact number of matched steps. *)
Theorem dual_pair_terminates : forall P : Proto,
  pair_steps (P, dual P) (PEnd, PEnd).
Proof.
  induction P as [A P' IH | A P' IH | ]; simpl.
  - eapply pss_step; [ apply ps_send | exact IH ].
  - eapply pss_step; [ apply ps_recv | exact IH ].
  - apply pss_refl.
Qed.

(** DETERMINISM: from a dual pair the next step is UNIQUE — [P]'s head fixes which
    endpoint sends and which receives, so the run cannot branch or diverge. *)
Lemma dual_pair_step_deterministic : forall P st1 st2,
  pair_step (P, dual P) st1 -> pair_step (P, dual P) st2 -> st1 = st2.
Proof.
  intros P st1 st2 H1 H2. destruct P as [A P' | A P' | ]; simpl in H1, H2.
  - inversion H1; subst; inversion H2; subst; reflexivity.
  - inversion H1; subst; inversion H2; subst; reflexivity.
  - inversion H1.
Qed.

(** Concrete bidirectional witness (exercises [PSRecv], unlike brick 1's send-only
    example): a ping-pong protocol — send an [int64], receive one back. *)
Definition pingpong : Proto := builtins.PSend GoI64 (builtins.PRecv GoI64 PEnd).

Definition pingpong_client : PSess pingpong PEnd unit :=
  PSBind (PSSend (zero_val TI64))
         (fun _ => PSBind (PSRecv TI64) (fun _ => PSRet tt)).

(** The client's trace is EXACTLY the protocol [send int64; recv int64] … *)
Example pingpong_client_emits : PEmits pingpong_client (proto_steps pingpong).
Proof.
  unfold pingpong_client, pingpong. cbn [proto_steps].
  change (PKSend GoI64 :: PKRecv GoI64 :: nil)
    with ((PKSend GoI64 :: nil) ++ ((PKRecv GoI64 :: nil) ++ @nil StepKind)).
  eapply EmitBind with (a := tt).
  - apply EmitSend.
  - eapply EmitBind with (a := zero_val TI64).
    + apply EmitRecv.
    + apply EmitRet.
Qed.

(** … and the full dual pair runs to completion. *)
Example pingpong_terminates : pair_steps (pingpong, dual pingpong) (PEnd, PEnd).
Proof. apply dual_pair_terminates. Qed.

(** Trust base — [dual_pair_terminates] / [dual_pair_step_deterministic] are pure
    [Proto] algebra (induction / destruct + [inversion] on the first-order
    [pair_step]): Closed under the global context, FULLY axiom-free.  The pingpong
    witnesses pull only the PrimInt63/PrimFloat substrate (via [GoI64]/[TI64]).
    No funext, no Eqdep/UIP.  Verified by [Print Assumptions]. *)

(** ** Run–trace coherence — the synchronized run communicates EXACTLY the protocol.

    Brick 4 proved the dual-pair reduction terminates and is deterministic, but the
    bare [pair_step] carried no message.  This brick records each step's
    communicated [StepKind] and proves the whole run from [(P, dual P)] to
    [(PEnd, PEnd)] emits EXACTLY [proto_steps P] — so the terminating, deterministic
    run is not merely live, it carries precisely the protocol's message sequence.
    This UNIFIES the three trace notions: the protocol SPEC ([proto_steps]), the
    session TERM's trace ([PEmits], brick 1), and now the synchronized RUN's trace
    all coincide.  Brick 5 of the R9 deeper fix, still pure-protocol. *)

(** A step that records the communicated kind (from the sender's view). *)
Inductive pair_step_tr : Proto * Proto -> StepKind -> Proto * Proto -> Prop :=
  | pst_send : forall (A : Type) (P' Q : Proto),
      pair_step_tr (builtins.PSend A P', builtins.PRecv A Q) (PKSend A) (P', Q)
  | pst_recv : forall (A : Type) (P' Q : Proto),
      pair_step_tr (builtins.PRecv A P', builtins.PSend A Q) (PKRecv A) (P', Q).

(** A traced run accumulates the communicated kinds in order. *)
Inductive pair_steps_tr : Proto * Proto -> list StepKind -> Proto * Proto -> Prop :=
  | pstr_refl : forall st, pair_steps_tr st [] st
  | pstr_step : forall st1 k st2 tr st3,
      pair_step_tr st1 k st2 -> pair_steps_tr st2 tr st3 ->
      pair_steps_tr st1 (k :: tr) st3.

(** A traced step IS a [pair_step] (the kind is just extra information). *)
Lemma pair_step_tr_untr : forall st1 k st2, pair_step_tr st1 k st2 -> pair_step st1 st2.
Proof. intros st1 k st2 H. inversion H; subst; [ apply ps_send | apply ps_recv ]. Qed.

(** … so a traced run IS a [pair_step] run (brick 4 — termination applies). *)
Lemma pair_steps_tr_forget : forall st tr st', pair_steps_tr st tr st' -> pair_steps st st'.
Proof.
  intros st tr st' H. induction H as [ | st1 k st2 tr st3 Hstep _ IH ].
  - apply pss_refl.
  - eapply pss_step; [ apply (pair_step_tr_untr _ _ _ Hstep) | exact IH ].
Qed.

(** COHERENCE: the dual-pair run emits EXACTLY the protocol's message sequence. *)
Theorem dual_pair_run_trace : forall P : Proto,
  pair_steps_tr (P, dual P) (proto_steps P) (PEnd, PEnd).
Proof.
  induction P as [A P' IH | A P' IH | ]; simpl.
  - eapply pstr_step; [ apply pst_send | exact IH ].
  - eapply pstr_step; [ apply pst_recv | exact IH ].
  - apply pstr_refl.
Qed.

(** Trust base — pure [Proto] algebra (induction + [inversion] on the first-order
    [pair_step_tr]): [dual_pair_run_trace] / the forget lemmas are Closed under the
    global context, FULLY axiom-free.  No funext, no Eqdep/UIP.  Verified by
    [Print Assumptions].  Together bricks 1–5 are the model-layer session theory;
    the remaining R9 step is the plugin MIGRATION (extracted [Sess] RECORD → an
    INDUCTIVE, so the EXTRACTED type is forge-proof too).  RESEARCHED this tick: the
    plugin lowers session ops by COMBINATOR name ([ssend]…) via [emit_sess_action],
    so migration must keep those names (NoInline wrappers) OR retarget the plugin to
    the inductive's constructors; [Sess] erases by name ([is_erased_record_typename])
    so the inductive erases too.  Intricate + golden-affecting ⇒ a focused fresh
    tick, NOT skipped. *)












