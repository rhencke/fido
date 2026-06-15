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
Require Import Coq.Numbers.Cyclic.Int63.PrimInt63.   (* [int] (Go int64) — the keystone value carrier *)
Import ListNotations.

Inductive EvKind :=
  | KSend  (chan : nat)
  | KRecv  (chan : nat) (from : nat)   (* matched send is at trace position [from] *)
  | KSpawn (child : nat)
  | KStart (parent : nat)              (* this goroutine was spawned at position [parent] *)
  | KWrite (loc : nat)
  | KRead  (loc : nat).

Record Ev := mkEv { e_tid : nat; e_kind : EvKind }.
Definition Trace := list Ev.

Definition tid_at (t : Trace) (i : nat) : nat :=
  match nth_error t i with Some e => e_tid e | None => 0 end.

(** A trace is WELL-FORMED when every back-pointer points to an EARLIER event of the
    right kind: a receive's [from] is an earlier send on the same channel; a start's
    [parent] is an earlier spawn.  A real execution always satisfies this — you
    receive a value already sent, and a goroutine runs after its [go]. *)
Definition WfTrace (t : Trace) : Prop :=
  forall i e, nth_error t i = Some e ->
    match e_kind e with
    | KRecv c from =>
        from < i /\ exists e', nth_error t from = Some e' /\ e_kind e' = KSend c
    | KStart parent =>
        parent < i /\ exists e' ch, nth_error t parent = Some e' /\ e_kind e' = KSpawn ch
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
  destruct (e_kind e) as [c|c from0|ch|parent0|l|l]; cbn in Hwf, Hk; try contradiction.
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
    split; [lia | exists (mkEv 0 (KSend 0)); split; reflexivity].
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
  | PSpawn (child:nat).   (* spawn goroutine [child] (its body pre-registered in cfg_prog) *)

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
                  (tr ++ [mkEv tid (KSpawn child)])).

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
  | KRecv c from => from < length t /\ exists e', nth_error t from = Some e' /\ e_kind e' = KSend c
  | KStart parent => parent < length t /\ exists e' ch, nth_error t parent = Some e' /\ e_kind e' = KSpawn ch
  | _ => True
  end ->
  WfTrace (t ++ [e]).
Proof.
  intros t e Hwf Hnew i e0 Hi.
  destruct (Nat.lt_ge_cases i (length t)) as [Hlt | Hge].
  - rewrite nth_error_app_old in Hi by exact Hlt.
    specialize (Hwf i e0 Hi).
    destruct (e_kind e0) as [c0|c0 from0|ch0|parent0|l0|l0] eqn:Ek; cbn in Hwf |- *; auto.
    + destruct Hwf as [Hf [e' [He' Hk']]]. split; [exact Hf|].
      exists e'. rewrite nth_error_app_old by lia. split; [exact He'|exact Hk'].
    + destruct Hwf as [Hf [e' [ch [He' Hk']]]]. split; [exact Hf|].
      exists e', ch. rewrite nth_error_app_old by lia. split; [exact He'|exact Hk'].
  - rewrite nth_error_app2 in Hi by lia.
    pose proof (nth_error_lt _ _ _ Hi) as Hb. cbn in Hb.
    assert (Hzero : i - length t = 0) by lia.
    assert (Hieq : i = length t) by lia.
    rewrite Hzero in Hi. cbn in Hi. injection Hi as Hi; subst e0.
    destruct (e_kind e) as [c0|c0 from0|ch0|parent0|l0|l0] eqn:Ek; cbn in Hnew |- *; auto.
    + destruct Hnew as [Hf [e' [He' Hk']]]. split; [rewrite Hieq; exact Hf|].
      exists e'. rewrite nth_error_app_old by exact Hf. split; [exact He'|exact Hk'].
    + destruct Hnew as [Hf [e' [ch [He' Hk']]]]. split; [rewrite Hieq; exact Hf|].
      exists e', ch. rewrite nth_error_app_old by exact Hf. split; [exact He'|exact Hk'].
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

Lemma step_preserves_inv : forall cfg cfg', step cfg cfg' -> Inv cfg -> Inv cfg'.
Proof.
  intros cfg cfg' Hstep [Hwf Hbuf].
  destruct Hstep as
    [ p b lv tr tid c rest Hlv Hp
    | p b lv tr tid c rest s brest Hlv Hp Hbc
    | p b lv tr tid l rest Hlv Hp
    | p b lv tr tid l rest Hlv Hp
    | p b lv tr tid child rest Hlv Hp ];
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
    split; [exact Hlt | exists e'; split; [exact He'|exact Hk']].
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
    | p b lv tr tid child rest Hlv Hp ];
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
      cbn in *; discriminate.
  - intros Hdone. specialize (Hdone 0 eq_refl). discriminate Hdone.
Qed.

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
    axioms specify, so it is a sound model of Fido's IO channels.
    ============================================================================ *)

Inductive Cmd : Type :=
  | CRet   : Cmd
  | CSend  : nat -> nat -> Cmd -> Cmd          (* send value on channel, continue *)
  | CRecv  : nat -> (nat -> Cmd) -> Cmd        (* recv from channel, BIND value, continue *)
  | CWrite : nat -> nat -> Cmd -> Cmd          (* write value to location, continue *)
  | CRead  : nat -> (nat -> Cmd) -> Cmd        (* read location, BIND value, continue *)
  | CSpawn : Cmd -> Cmd -> Cmd.                (* spawn child, continue parent *)

Record RConfig := mkRCfg {
  rc_prog  : nat -> Cmd;
  rc_bufs  : nat -> list (nat * nat);   (* channel -> FIFO of (value, send-position) *)
  rc_heap  : nat -> nat;                 (* location -> value *)
  rc_live  : nat -> bool;
  rc_trace : Trace
}.

Inductive rstep : RConfig -> RConfig -> Prop :=
  | rstep_send : forall p b h lv tr tid c v k,
      lv tid = true -> p tid = CSend c v k ->
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
  | rstep_spawn : forall p b h lv tr tid child k cid,
      lv tid = true -> p tid = CSpawn child k -> lv cid = false ->
      rstep (mkRCfg p b h lv tr)
            (mkRCfg (upd (upd p tid k) cid child) b h (upd lv cid true)
                    (tr ++ [mkEv tid (KSpawn cid)])).

Definition RBufOk (cfg : RConfig) : Prop :=
  forall c v s, In (v, s) (rc_bufs cfg c) ->
    s < length (rc_trace cfg) /\
    exists e', nth_error (rc_trace cfg) s = Some e' /\ e_kind e' = KSend c.

Definition RInv (cfg : RConfig) : Prop := WfTrace (rc_trace cfg) /\ RBufOk cfg.

Lemma rstep_preserves_inv : forall cfg cfg', rstep cfg cfg' -> RInv cfg -> RInv cfg'.
Proof.
  intros cfg cfg' Hstep [Hwf Hbuf].
  destruct Hstep as
    [ p b h lv tr tid c v k Hlv Hp
    | p b h lv tr tid c f v s brest Hlv Hp Hbc
    | p b h lv tr tid l v k Hlv Hp
    | p b h lv tr tid l f Hlv Hp
    | p b h lv tr tid child k cid Hlv Hp Hcid ];
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
    split; [exact Hlt | exists e'; split; [exact He'|exact Hk']].
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
  (* spawn WfTrace / RBufOk *)
  - apply WfTrace_app; [exact Hwf | cbn; exact I].
  - intros c0 v0 s0 Hin. cbn [rc_bufs rc_trace] in Hin |- *.
    destruct (Hbuf c0 v0 s0 Hin) as [Hlt Hex]. apply BufOk_pos_app; assumption.
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

(** ---- The refinement: the rich calculus implements the [run_io] channel laws ----
    [rchan] is the channel VALUE-FIFO.  A send ENQUEUES the value (matching the
    [run_io] axiom [chan_buf_send]: buffer after send = buffer ++ [v]); a receive
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
    [ p b h lv tr tid c v k Hlv Hp
    | p b h lv tr tid c f v s brest Hlv Hp Hbc
    | p b h lv tr tid l v k Hlv Hp
    | p b h lv tr tid l f Hlv Hp
    | p b h lv tr tid child k cid Hlv Hp Hcid ];
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

(** ============================================================================
    STEP 1 KEYSTONE — the TERM-LEVEL bridge: a rich-calculus channel step
    SIMULATES [run_io] of the program's DENOTATION.

    [Cmd] is the DEEP embedding of an IO program.  [Denotes c m] is the deep↔shallow
    correspondence — built as a RELATION because [CRecv]'s continuation is a Coq
    function [nat -> Cmd], so a denotation FUNCTION cannot structurally recurse, but
    the relation pairs each [Cmd] with the [IO] term it stands for.  Then
    [denote_sim_send] / [denote_sim_recv] show that ONE [rstep] channel action
    run-reduces the [IO] denotation EXACTLY as the [run_io] axioms specify, while the
    channel buffer stays matched ([WMatch1]).  This is the missing link: it ties the
    abstract [rstep] (where race-freedom is PROVEN) to the actual [run_io]/[World]
    model we EXTRACT from — grounded in the real IO axioms [run_bind]/[run_send]/
    [run_recv]/[chan_buf_send]/[chan_buf_recv] (no NEW axioms; [Print Assumptions]
    below shows exactly that base).

    Value carrier = [int] (Go int64, tag [TInt64]); [recv] needs a [GoTypeTag] and
    [GoTypeTag nat] is provably EMPTY, so calculus [nat] values are coded into IO
    [int] by [inj]/[prj].  [Hret] (the round-trip [prj (inj n) = n]) is the standard
    faithful-coding condition — realizable on the bounded (< 2^62) value regime the
    int model already lives in; it is the section's only hypothesis, NOT an axiom.

    SPAWN is deliberately ABSENT from this bridge: [go_spawn] has NO [run_io] law,
    because [run_io] is SEQUENTIAL and cannot express interleaving.  That is exactly
    why the calculus is the model for concurrency and why the race-freedom guarantee
    lives on [rstep], not on [run_io].
    ============================================================================ *)
Section Keystone.
  Variable chenv : nat -> GoChan int.    (* calculus channel id -> the IO channel *)
  Variable locenv : nat -> Ref int.      (* calculus location  -> the IO ref cell *)
  Variable inj : nat -> int.             (* calculus value -> IO value (a coding) *)
  Variable prj : int -> nat.             (* IO value -> calculus value *)
  Hypothesis Hret : forall n, prj (inj n) = n.   (* the coding round-trips *)

  (* Deep<->shallow correspondence.  D_recv's premise is itself a [forall x],
     reflecting the HOAS continuation: the IO term [g] must agree with [denote] of
     the calculus continuation [f] at every received value. *)
  Inductive Denotes : Cmd -> IO unit -> Prop :=
    | D_ret   : Denotes CRet (ret tt)
    | D_send  : forall ch v k m, Denotes k m ->
        Denotes (CSend ch v k) (bind (send (chenv ch) (inj v)) (fun _ => m))
    | D_recv  : forall ch f g, (forall x, Denotes (f (prj x)) (g x)) ->
        Denotes (CRecv ch f) (bind (recv TInt64 (chenv ch)) g)
    | D_write : forall l v k m, Denotes k m ->
        Denotes (CWrite l v k) (bind (ref_set (locenv l) (inj v)) (fun _ => m))
    | D_read  : forall l f g, (forall x, Denotes (f (prj x)) (g x)) ->
        Denotes (CRead l f) (bind (ref_get TInt64 (locenv l)) g).

  (* World <-> config on one channel [c]: the IO buffer is the calculus buffer, coded.
     (Single channel keeps it frame-free — a send/recv touches only [c]'s buffer, and
     the IO channel axioms relate exactly that buffer; multi-channel would need a
     channel-separation/frame law, tracked.) *)
  Definition WMatch1 (c : nat) (w : World) (cfg : RConfig) : Prop :=
    chan_buf (chenv c) w = map inj (rchan cfg c).

  (** A SEND step: the deep [CSend] run-reduces to its continuation at the world after
      [chan_send_upd], and the buffer match is preserved — mirroring [rstep_send]. *)
  Lemma denote_sim_send : forall p b h lv tr tid c v k m w,
    Denotes (CSend c v k) m ->
    WMatch1 c w (mkRCfg p b h lv tr) ->
    chan_closed (chenv c) w = false ->
    exists m',
      Denotes k m' /\
      run_io m w = run_io m' (chan_send_upd (chenv c) (inj v) w) /\
      WMatch1 c (chan_send_upd (chenv c) (inj v) w)
              (mkRCfg (upd p tid k) (upd b c (b c ++ [(v, length tr)])) h lv
                      (tr ++ [mkEv tid (KSend c)])).
  Proof.
    intros p b h lv tr tid c v k m w HD HM Hclosed.
    inversion HD as [| ch0 v0 k0 m' HDk Hch Hm | | | ]; subst.
    exists m'. split; [exact HDk | split].
    - rewrite run_bind, (run_send (chenv c) (inj v) w Hclosed). cbn. reflexivity.
    - unfold WMatch1, rchan in *. cbn [rc_bufs] in *. rewrite upd_same.
      rewrite (chan_buf_send (chenv c) (inj v) w), HM, !map_app. cbn. reflexivity.
  Qed.

  (** A RECV step: the deep [CRecv] run-reduces by BINDING the head value; [Hret]
      recovers the calculus value, so the continuation matches [f v] — mirroring
      [rstep_recv].  This is where the faithful coding is genuinely used. *)
  Lemma denote_sim_recv : forall p b h lv tr tid c f m w v s brest,
    Denotes (CRecv c f) m ->
    WMatch1 c w (mkRCfg p b h lv tr) ->
    b c = (v, s) :: brest ->
    exists m',
      Denotes (f v) m' /\
      run_io m w = run_io m' (chan_recv_upd (chenv c) w) /\
      WMatch1 c (chan_recv_upd (chenv c) w)
              (mkRCfg (upd p tid (f v)) (upd b c brest) h lv (tr ++ [mkEv tid (KRecv c s)])).
  Proof.
    intros p b h lv tr tid c f m w v s brest HD HM Hbc.
    inversion HD as [| | ch0 f0 g HDg Hch Hm | | ]; subst.
    assert (Hbuf : chan_buf (chenv c) w = inj v :: map inj (map fst brest)).
    { unfold WMatch1, rchan in HM. cbn [rc_bufs] in HM. rewrite Hbc in HM. cbn in HM. exact HM. }
    exists (g (inj v)). split; [| split].
    - specialize (HDg (inj v)). rewrite Hret in HDg. exact HDg.
    - rewrite run_bind, (run_recv TInt64 (chenv c) (inj v) (map inj (map fst brest)) w Hbuf).
      cbn. reflexivity.
    - unfold WMatch1, rchan. cbn [rc_bufs]. rewrite upd_same.
      rewrite (chan_buf_recv (chenv c) (inj v) (map inj (map fst brest)) w Hbuf). reflexivity.
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
    exists m',
      Denotes (f (h l)) m' /\
      run_io m w = run_io m' w /\
      WHMatch1 l w (mkRCfg (upd p tid (f (h l))) b h lv (tr ++ [mkEv tid (KRead l)])).
  Proof.
    intros p b h lv tr tid l f m w HD HM.
    inversion HD as [| | | | l0 f0 g HDg Hl Hm]; subst.
    unfold WHMatch1 in HM. cbn [rc_heap] in HM.
    exists (g (inj (h l))). split; [| split].
    - specialize (HDg (inj (h l))). rewrite Hret in HDg. exact HDg.
    - rewrite run_bind, (run_ref_get TInt64 (locenv l) w). cbn. rewrite HM. reflexivity.
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
    | OC_send : forall v k, OnChan c k -> OnChan c (CSend c v k)
    | OC_recv : forall f, (forall x, OnChan c (f x)) -> OnChan c (CRecv c f).

  Definition SimInv (c : nat) (m0 : IO unit) (w0 : World) (cfg : RConfig) : Prop :=
    OnChan c (rc_prog cfg 0)
    /\ (forall t, t <> 0 -> rc_prog cfg t = CRet)
    /\ rc_live cfg = (fun t => Nat.eqb t 0)
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
           [HOC [Hidle [Hlive [m [w [HD [HM [Hcl Hrun]]]]]]]].
    destruct Hstep as
      [ p b h lv tr tid c1 v k Hlv Hp
      | p b h lv tr tid c1 f v s brest Hlv Hp Hbc
      | p b h lv tr tid l v k Hlv Hp
      | p b h lv tr tid l f Hlv Hp
      | p b h lv tr tid child k cid Hlv Hp Hcid ];
    cbn [rc_prog rc_live] in HOC, Hidle, Hlive, HD;
    rewrite Hlive in Hlv; cbn in Hlv; apply Nat.eqb_eq in Hlv; subst tid; subst lv.
    - (* send *)
      rewrite Hp in HOC, HD. inversion HOC as [| v' k' HOCk |]; subst c1.
      destruct (denote_sim_send _ _ _ _ _ 0 c v k m w HD HM Hcl)
        as [m' [HDk' [Hrun' HM']]].
      unfold SimInv; cbn [rc_prog rc_live]; rewrite upd_same.
      split; [exact HOCk | split; [| split]].
      + intros t Ht. rewrite (upd_other _ _ _ _ Ht). exact (Hidle t Ht).
      + reflexivity.
      + exists m', (chan_send_upd (chenv c) (inj v) w).
        split; [exact HDk' | split; [exact HM' | split]].
        * rewrite (chan_closed_send (chenv c) (inj v) w). exact Hcl.
        * rewrite Hrun. exact Hrun'.
    - (* recv *)
      rewrite Hp in HOC, HD. inversion HOC as [| | f' HOCf]; subst c1.
      destruct (denote_sim_recv _ _ _ _ _ 0 c f m w v s brest HD HM Hbc)
        as [m' [HDk' [Hrun' HM']]].
      unfold SimInv; cbn [rc_prog rc_live]; rewrite upd_same.
      split; [exact (HOCf v) | split; [| split]].
      + intros t Ht. rewrite (upd_other _ _ _ _ Ht). exact (Hidle t Ht).
      + reflexivity.
      + exists m', (chan_recv_upd (chenv c) w).
        split; [exact HDk' | split; [exact HM' | split]].
        * rewrite (chan_closed_recv (chenv c) w). exact Hcl.
        * rewrite Hrun. exact Hrun'.
    - (* write — impossible under OnChan *)
      rewrite Hp in HOC. inversion HOC.
    - (* read — impossible under OnChan *)
      rewrite Hp in HOC. inversion HOC.
    - (* spawn — impossible under OnChan *)
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
    chan_buf (chenv c) w0 = [] -> chan_closed (chenv c) w0 = false ->
    SimInv c m w0 (rinit_cfg (fun t => if Nat.eqb t 0 then prog0 else CRet)).
  Proof.
    intros c prog0 m w0 HOC HD Hbuf Hcl.
    unfold SimInv, rinit_cfg; cbn [rc_prog rc_live].
    split; [exact HOC | split; [| split]].
    - intros t Ht. destruct (Nat.eqb t 0) eqn:E;
        [apply Nat.eqb_eq in E; congruence | reflexivity].
    - reflexivity.
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
    chan_buf (chenv c) w0 = [] -> chan_closed (chenv c) w0 = false ->
    rsteps (rinit_cfg (fun t => if Nat.eqb t 0 then prog0 else CRet)) cfg_final ->
    rc_prog cfg_final 0 = CRet ->
    exists w_final, run_io m w0 = ORet tt w_final /\ WMatch1 c w_final cfg_final.
  Proof.
    intros c prog0 m w0 cfg_final HOC HD Hbuf Hcl Hrsteps Hdone.
    pose proof (siminv_steps _ _ _ _ _ Hrsteps
                  (siminv_init _ _ _ _ HOC HD Hbuf Hcl)) as HS.
    destruct HS as [_ [_ [_ [m' [w' [HD' [HM' [_ Hrun']]]]]]]].
    rewrite Hdone in HD'. inversion HD'; subst.
    exists w'. split; [rewrite Hrun'; apply run_ret | exact HM'].
  Qed.

End Keystone.

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
  Variable chenv : nat -> GoChan int.
  Variable inj : nat -> int.
  Hypothesis chenv_inj : forall i j, chenv i = chenv j -> i = j.

  Definition WMatchC (w : World) (cfg : RConfig) : Prop :=
    forall c, chan_buf (chenv c) w = map inj (rchan cfg c).

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
      [ p b h lv tr tid c0 v k Hlv Hp
      | p b h lv tr tid c0 f v s brest Hlv Hp Hbc
      | p b h lv tr tid l v k Hlv Hp
      | p b h lv tr tid l f Hlv Hp
      | p b h lv tr tid child k cid Hlv Hp Hcid ].
    - (* send: world advances by [chan_send_upd] on channel [c0] *)
      exists (chan_send_upd (chenv c0) (inj v) w).
      intros c. specialize (HM c). unfold WMatchC, rchan in *; cbn [rc_bufs] in *.
      destruct (Nat.eq_dec c c0) as [->|Hne].
      + rewrite upd_same, chan_buf_send, HM, !map_app. cbn. reflexivity.
      + rewrite (upd_other _ _ _ _ Hne),
          (chan_buf_send_frame (chenv c0) (chenv c) (inj v) w
             (chenv_neq c0 c (not_eq_sym Hne))).
        exact HM.
    - (* recv: world advances by [chan_recv_upd] on channel [c0] *)
      exists (chan_recv_upd (chenv c0) w).
      assert (Hbuf : chan_buf (chenv c0) w = inj v :: map inj (map fst brest)).
      { generalize (HM c0). unfold rchan; cbn [rc_bufs]. rewrite Hbc. cbn. tauto. }
      intros c. specialize (HM c). unfold WMatchC, rchan in *; cbn [rc_bufs] in *.
      destruct (Nat.eq_dec c c0) as [->|Hne].
      + rewrite upd_same,
          (chan_buf_recv (chenv c0) (inj v) (map inj (map fst brest)) w Hbuf).
        reflexivity.
      + rewrite (upd_other _ _ _ _ Hne),
          (chan_buf_recv_frame (chenv c0) (chenv c) w
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
  Qed.

  Lemma wmatchc_steps : forall cfg cfg' w,
    rsteps cfg cfg' -> WMatchC w cfg -> exists w', WMatchC w' cfg'.
  Proof.
    intros cfg cfg' w H. revert w. induction H; intros w HM; [exists w; exact HM|].
    destruct (wmatchc_step _ _ _ H HM) as [w' HM']. exact (IHrsteps w' HM').
  Qed.

  Lemma wmatchc_init : forall p w0,
    (forall c, chan_buf (chenv c) w0 = []) -> WMatchC w0 (rinit_cfg p).
  Proof.
    intros p w0 Hempty c. unfold WMatchC, rchan, rinit_cfg; cbn [rc_bufs].
    rewrite Hempty. reflexivity.
  Qed.

  (** THE MULTI-GOROUTINE REFINEMENT.  Every reachable state of a concurrent,
      multi-channel execution is realized by some [run_io] world matching all its
      channel buffers — across every interleaving. *)
  Theorem reachable_refines : forall p cfg w0,
    (forall c, chan_buf (chenv c) w0 = []) ->
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
    (forall c, chan_buf (chenv c) w0 = []) ->
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

(* A live goroutine BLOCKED: waiting to receive on an empty channel. *)
Definition blocked (cfg : RConfig) (tid : nat) : Prop :=
  exists c f, rc_prog cfg tid = CRecv c f /\ rc_bufs cfg c = [].

(* A fresh goroutine id is available — holds for any reachable config (only finitely
   many goroutines are ever spawned), so [CSpawn] never blocks for lack of an id. *)
Definition FreshAvail (cfg : RConfig) : Prop := exists cid, rc_live cfg cid = false.

(** PROGRESS: any live goroutine that is neither finished nor blocked can take a step
    (so the whole config can step).  The heart of deadlock-freedom. *)
Lemma ready_can_step : forall cfg tid,
  FreshAvail cfg ->
  rc_live cfg tid = true ->
  rc_prog cfg tid <> CRet ->
  ~ blocked cfg tid ->
  rcan_step cfg.
Proof.
  intros [p b h lv tr] tid [cid Hcid] Hlive Hnret Hnblk.
  unfold rcan_step, blocked in *; cbn [rc_prog rc_live rc_bufs] in *.
  destruct (p tid) as [ | c v k | c f | l v k | l f | child k ] eqn:Hp.
  - congruence.
  - eexists; eapply rstep_send; eassumption.
  - destruct (b c) as [ | [v s] rest] eqn:Hb.
    + exfalso. apply Hnblk. exists c, f. split; [reflexivity | exact Hb].
    + eexists; eapply rstep_recv; eassumption.
  - eexists; eapply rstep_write; eassumption.
  - eexists; eapply rstep_read; eassumption.
  - eexists; eapply rstep_spawn; eassumption.
Qed.

(** THE DEADLOCK CHARACTERIZATION: in a stuck config, EVERY live goroutine is either
    finished ([CRet]) or blocked on an empty-channel receive.  (Contrapositive of
    progress: if any live goroutine were ready, the config could step.) *)
Theorem rstuck_blocked : forall cfg,
  FreshAvail cfg -> RStuck cfg ->
  forall tid, rc_live cfg tid = true -> rc_prog cfg tid = CRet \/ blocked cfg tid.
Proof.
  intros cfg Hfresh [Hnstep _] tid Hlive.
  (* the non-CRecv heads are all enabled, so they can't occur in a stuck config;
     a CRecv is blocked iff its buffer is empty — both decidable, no classical logic. *)
  destruct (rc_prog cfg tid) as [ | c v k | c f | l v k | l f | child k ] eqn:Hp.
  - left. reflexivity.
  - exfalso. apply Hnstep. apply (ready_can_step cfg tid Hfresh Hlive).
    + rewrite Hp; discriminate.
    + unfold blocked. intros [c0 [f0 [Hpc _]]]. rewrite Hp in Hpc. discriminate Hpc.
  - destruct (rc_bufs cfg c) as [ | hd rest ] eqn:Hb.
    + right. unfold blocked. exists c, f. split; [exact Hp | exact Hb].
    + exfalso. apply Hnstep. apply (ready_can_step cfg tid Hfresh Hlive).
      * rewrite Hp; discriminate.
      * unfold blocked. intros [c0 [f0 [Hpc Hbc]]]. rewrite Hp in Hpc.
        injection Hpc as Hcc Hff. subst c0. rewrite Hb in Hbc. discriminate Hbc.
  - exfalso. apply Hnstep. apply (ready_can_step cfg tid Hfresh Hlive).
    + rewrite Hp; discriminate.
    + unfold blocked. intros [c0 [f0 [Hpc _]]]. rewrite Hp in Hpc. discriminate Hpc.
  - exfalso. apply Hnstep. apply (ready_can_step cfg tid Hfresh Hlive).
    + rewrite Hp; discriminate.
    + unfold blocked. intros [c0 [f0 [Hpc _]]]. rewrite Hp in Hpc. discriminate Hpc.
  - exfalso. apply Hnstep. apply (ready_can_step cfg tid Hfresh Hlive).
    + rewrite Hp; discriminate.
    + unfold blocked. intros [c0 [f0 [Hpc _]]]. rewrite Hp in Hpc. discriminate Hpc.
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
    inversion Hstep; subst; cbn in *;
      match goal with H : (_ =? 0) = true |- _ => apply Nat.eqb_eq in H; subst end;
      cbn in *; discriminate.
  - intros Hdone. specialize (Hdone 0 eq_refl). cbn in Hdone. discriminate.
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
  | RF_spawn : forall child k, RecvFree child -> RecvFree k -> RecvFree (CSpawn child k).

Definition RecvFreeCfg (cfg : RConfig) : Prop :=
  forall tid, rc_live cfg tid = true -> RecvFree (rc_prog cfg tid).

(* A receive-free goroutine is never blocked (blocking needs a [CRecv] head). *)
Lemma recvfree_not_blocked : forall cfg tid,
  RecvFree (rc_prog cfg tid) -> ~ blocked cfg tid.
Proof. intros cfg tid HRF [c [f [Hp _]]]. rewrite Hp in HRF. inversion HRF. Qed.

(** PROGRESS for receive-free configs (witness form): while ANY live goroutine has
    work left, the config can step — i.e. it never deadlocks.  (No need to extract a
    witness from [~ rdone]: the caller supplies the unfinished goroutine, which exists
    exactly when the config is not done.) *)
Lemma recvfree_progress : forall cfg tid,
  FreshAvail cfg -> RecvFreeCfg cfg ->
  rc_live cfg tid = true -> rc_prog cfg tid <> CRet ->
  rcan_step cfg.
Proof.
  intros cfg tid Hfresh HRF Hlive Hnret.
  apply (ready_can_step cfg tid Hfresh Hlive Hnret).
  apply recvfree_not_blocked. exact (HRF tid Hlive).
Qed.

(* Receive-freeness of all live goroutines is preserved by every step (the [recv]
   case is vacuous — a receive-free config has no [CRecv] head to step). *)
Lemma rstep_recvfree : forall cfg cfg',
  rstep cfg cfg' -> RecvFreeCfg cfg -> RecvFreeCfg cfg'.
Proof.
  intros cfg cfg' Hstep HRF tid'.
  unfold RecvFreeCfg in HRF.
  destruct Hstep as
    [ p b h lv tr tid c v k Hlv Hp
    | p b h lv tr tid c f v s brest Hlv Hp Hbc
    | p b h lv tr tid l v k Hlv Hp
    | p b h lv tr tid l f Hlv Hp
    | p b h lv tr tid child k cid Hlv Hp Hcid ];
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
    [ p b h lv tr tid c v k Hlv Hp
    | p b h lv tr tid c f v s brest Hlv Hp Hbc
    | p b h lv tr tid l v k Hlv Hp
    | p b h lv tr tid l f Hlv Hp
    | p b h lv tr tid child k cid Hlv Hp Hcid ];
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
Qed.

Lemma rsteps_recvfree_livefin : forall cfg cfg',
  rsteps cfg cfg' -> RecvFreeCfg cfg -> LiveFin cfg ->
  RecvFreeCfg cfg' /\ LiveFin cfg'.
Proof.
  intros cfg cfg' H. induction H; intros HRF HLF; [split; assumption|].
  apply IHrsteps;
    [exact (rstep_recvfree _ _ H HRF) | exact (rstep_livefin _ _ H HLF)].
Qed.

(** THE DEADLOCK-FREEDOM THEOREM.  In ANY reachable state of a receive-free program,
    every live UNFINISHED goroutine can step — so the program never deadlocks; it
    always makes progress while work remains. *)
Theorem reachable_recvfree_progress : forall p cfg,
  (forall t, RecvFree (p t)) ->
  rsteps (rinit_cfg p) cfg ->
  forall tid, rc_live cfg tid = true -> rc_prog cfg tid <> CRet -> rcan_step cfg.
Proof.
  intros p cfg HpRF Hsteps tid Hlive Hnret.
  assert (HRF0 : RecvFreeCfg (rinit_cfg p)).
  { intros t _. cbn. apply HpRF. }
  destruct (rsteps_recvfree_livefin _ _ Hsteps HRF0 (livefin_init p)) as [HRF HLF].
  exact (recvfree_progress cfg tid (livefin_fresh _ HLF) HRF Hlive Hnret).
Qed.
