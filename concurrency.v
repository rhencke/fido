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
