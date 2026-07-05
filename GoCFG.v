(** ==================================================================================================
    GoCFG — control flow as a CFG (the goto model): the SEMANTIC AUTHORITY for block-structured
    control flow.  (Go spec "If statements" / "For statements" / "Goto statements" /
    "Return statements")

    A function body is a set of labelled basic blocks; each block runs its IO effects then
    transfers control — [Jump n] (goto block n) or [Done] (return).  [goto] is the native edge;
    structured Go forms are recovered downstream by the TRUSTED plugin lowering (SPEC_CONFORMANCE's
    control-flow row) — no completeness theorem is claimed.

    ★ THE IO BOUNDARY (unmissable, by design): [IO A := World -> Outcome A] models ONE
    terminating-or-panicking effect action — never arbitrary Go computation.  Everything that can
    loop or diverge lives HERE, in the relational ([blocks_eval]) and coinductive
    ([blocks_diverge]) layers over those single actions; no total function in this module (or
    anywhere) evaluates a CFG.  The emission-side marker for CFG demos lives in
    GoExtractionHooks.v — a plugin hook, not semantics.  ============================================== *)
Require Import Coq.Lists.List.
From Stdlib Require Import Lia.
From Stdlib Require Import Arith.
From Fido Require Import builtins.

Inductive Next : Type :=
  | Jump : nat -> Next   (* goto block n *)
  | Done : Next.         (* return from the function *)

(** [run_blocks start blocks]: the blocks are given as a list (block [n] is the
    nth entry); start at [start], run each block (IO ending in a [Next]), follow
    [Jump]s until [Done].  The plugin emits the blocks as Go labels + [goto]
    (only labels that are [Jump] targets are emitted, since Go rejects unused labels).

    A backward [Jump] need not terminate, so NO total Rocq function can be the
    semantic authority here.  The AUTHORITY is relational and unfueled:
    [blocks_eval] (the finite runs — done / panic / in-range jump; an
    out-of-range jump or missing block admits NO rule, so invalid control flow
    is UNEVALUABLE — never a fabricated success) and [blocks_diverge] (the
    coinductive infinite jump chains — real divergence, not "did not halt
    within N").  [run_blocks] itself is EMISSION-ONLY: the plugin lowers it BY
    NAME to labels + [goto] and suppresses this body; the model-side body is a
    loud marker panic, so evaluating it in Rocq never fabricates an outcome.
    [blocks_jump_wf] below is the holistic admissibility condition, stated in
    OUTCOME terms only: a CFG is jump-wf iff every block's run on EVERY world
    yields Done, a panic, or an IN-RANGE Jump — membership is decided by
    outcomes, never by which syntactic markers a body contains.
    [blocks_step] is the structural one-step transition, and
    [blocks_jump_wf_progress] is the class-wide theorem: from any in-range pc,
    a jump-wf CFG concludes or makes an explicit [blocks_step].  These relations describe only shallow
    [run_io] behavior; connecting any block to its EMITTED behavior is the
    deep [run_cmd]/emitted-runtime story, a separate claim these relations do
    not make.  Demos are sanity checks, never evidence. *)
(** THE ONE-STEP CFG TRANSITION (structural): configuration [(pc, w)] steps to
    [(pc', w')] when block [pc] runs to an IN-RANGE [Jump pc'].  [blocks_eval]
    and [blocks_diverge] both consume THIS relation — the transition shape
    exists exactly once. *)
Inductive blocks_step (blocks : list (IO Next)) : nat -> World -> nat -> World -> Prop :=
  | bs_jump : forall pc w b pc' w',
      nth_error blocks pc = Some b ->
      run_io b w = ORet (Jump pc') w' ->
      (pc' < List.length blocks)%nat ->
      blocks_step blocks pc w pc' w'.
Inductive blocks_eval (blocks : list (IO Next)) : nat -> World -> Outcome unit -> Prop :=
  | be_done : forall pc w b w',
      nth_error blocks pc = Some b ->
      run_io b w = ORet Done w' ->
      blocks_eval blocks pc w (ORet tt w')
  | be_panic : forall pc w b v w',
      nth_error blocks pc = Some b ->
      run_io b w = OPanic v w' ->
      blocks_eval blocks pc w (OPanic v w')
  | be_jump : forall pc w pc' w' out,
      blocks_step blocks pc w pc' w' ->
      blocks_eval blocks pc' w' out ->
      blocks_eval blocks pc w out.
CoInductive blocks_diverge (blocks : list (IO Next)) : nat -> World -> Prop :=
  | bd_jump : forall pc w pc' w',
      blocks_step blocks pc w pc' w' ->
      blocks_diverge blocks pc' w' ->
      blocks_diverge blocks pc w.

(** HOLISTIC ADMISSIBILITY (outcome terms only): every block's run, on every
    world, is Done, a panic, or an in-range Jump. *)
Definition blocks_jump_wf (blocks : list (IO Next)) : Prop :=
  forall n b (w : World), nth_error blocks n = Some b ->
    match run_io b w with
    | ORet (Jump pc') _ => (pc' < List.length blocks)%nat
    | _ => True
    end.

(** CLASS-WIDE PROGRESS: from any in-range pc, a jump-wf CFG is NEVER STUCK —
    it concludes ([blocks_eval] done/panic) or makes an explicit [blocks_step]
    to another in-range configuration.  Holds for the WHOLE class, not per demo. *)
Lemma blocks_jump_wf_progress : forall blocks pc (w : World),
  blocks_jump_wf blocks -> (pc < List.length blocks)%nat ->
     (exists w', blocks_eval blocks pc w (ORet tt w'))
  \/ (exists v w', blocks_eval blocks pc w (OPanic v w'))
  \/ (exists pc' w', blocks_step blocks pc w pc' w').
Proof.
  intros blocks pc w Hwf Hpc.
  destruct (nth_error blocks pc) as [b|] eqn:Hnth.
  - destruct (run_io b w) as [[pc'|] w' | v w'] eqn:Hrun.
    + right. right. exists pc', w'.
      pose proof (Hwf pc b w Hnth) as H. rewrite Hrun in H.
      exact (bs_jump blocks pc w b pc' w' Hnth Hrun H).
    + left. exists w'. exact (be_done blocks pc w b w' Hnth Hrun).
    + right. left. exists v, w'. exact (be_panic blocks pc w b v w' Hnth Hrun).
  - exfalso. apply nth_error_Some in Hpc. congruence.
Qed.

(** ONE-STEP DETERMINISM: [run_io] is a function, so a configuration steps to at
    most one successor.  Class-wide — no well-formedness premise needed. *)
Lemma blocks_step_det : forall blocks pc (w : World) pc1 w1 pc2 w2,
  blocks_step blocks pc w pc1 w1 -> blocks_step blocks pc w pc2 w2 ->
  pc1 = pc2 /\ w1 = w2.
Proof.
  intros blocks pc w pc1 w1 pc2 w2 H1 H2.
  inversion H1 as [ ? ? b1 ? ? Hn1 Hr1 Hlt1 ]; subst.
  inversion H2 as [ ? ? b2 ? ? Hn2 Hr2 Hlt2 ]; subst.
  rewrite Hn1 in Hn2. injection Hn2 as <-.
  rewrite Hr1 in Hr2. inversion Hr2; subst. split; reflexivity.
Qed.

(** TERMINATING OUTCOMES ARE UNIQUE: [blocks_eval] is deterministic — from one
    configuration there is at most one evaluation outcome.  Induction on the
    first derivation; the second is pinned step-by-step by [run_io]'s
    functionality (a Done/Panic conclusion and a Jump step are mutually
    exclusive at the same configuration). *)
Theorem blocks_eval_det : forall blocks pc (w : World) out1 out2,
  blocks_eval blocks pc w out1 -> blocks_eval blocks pc w out2 -> out1 = out2.
Proof.
  intros blocks pc w out1 out2 H1. revert out2.
  induction H1 as [ pc w b w' Hn Hr | pc w b v w' Hn Hr | pc w pc' w' out Hstep H1 IH ];
    intros out2 H2.
  - inversion H2 as [ ? ? b2 w2 Hn2 Hr2 | ? ? b2 v2 w2 Hn2 Hr2 | ? ? pc2 w2 out2' Hstep2 Hrest ]; subst.
    + rewrite Hn in Hn2. injection Hn2 as <-. rewrite Hr in Hr2. inversion Hr2; subst. reflexivity.
    + rewrite Hn in Hn2. injection Hn2 as <-. rewrite Hr in Hr2. discriminate Hr2.
    + inversion Hstep2 as [ ? ? b2 ? ? Hn2 Hr2 Hlt2 ]; subst.
      rewrite Hn in Hn2. injection Hn2 as <-. rewrite Hr in Hr2. discriminate Hr2.
  - inversion H2 as [ ? ? b2 w2 Hn2 Hr2 | ? ? b2 v2 w2 Hn2 Hr2 | ? ? pc2 w2 out2' Hstep2 Hrest ]; subst.
    + rewrite Hn in Hn2. injection Hn2 as <-. rewrite Hr in Hr2. discriminate Hr2.
    + rewrite Hn in Hn2. injection Hn2 as <-. rewrite Hr in Hr2. inversion Hr2; subst. reflexivity.
    + inversion Hstep2 as [ ? ? b2 ? ? Hn2 Hr2 Hlt2 ]; subst.
      rewrite Hn in Hn2. injection Hn2 as <-. rewrite Hr in Hr2. discriminate Hr2.
  - inversion H2 as [ ? ? b2 w2 Hn2 Hr2 | ? ? b2 v2 w2 Hn2 Hr2 | ? ? pc2 w2 out2' Hstep2 Hrest ]; subst.
    + inversion Hstep as [ ? ? b1 ? ? Hn1 Hr1 Hlt1 ]; subst.
      rewrite Hn1 in Hn2. injection Hn2 as <-. rewrite Hr1 in Hr2. discriminate Hr2.
    + inversion Hstep as [ ? ? b1 ? ? Hn1 Hr1 Hlt1 ]; subst.
      rewrite Hn1 in Hn2. injection Hn2 as <-. rewrite Hr1 in Hr2. discriminate Hr2.
    + destruct (blocks_step_det _ _ _ _ _ _ _ Hstep Hstep2) as [ E1 E2 ]. subst.
      exact (IH out2 Hrest).
Qed.

(** TERMINATION AND DIVERGENCE ARE DISJOINT: no configuration both evaluates to
    an outcome and diverges.  Induction on the evaluation; each divergence step
    must agree with the evaluation's step ([run_io] functionality), so the
    divergence is pushed past the whole finite run and dies at the conclusion. *)
Theorem blocks_eval_diverge_disjoint : forall blocks pc (w : World) out,
  blocks_eval blocks pc w out -> blocks_diverge blocks pc w -> False.
Proof.
  intros blocks pc w out Heval.
  induction Heval as [ pc w b w' Hn Hr | pc w b v w' Hn Hr | pc w pc' w' out Hstep Heval IH ];
    intro Hdiv.
  - inversion Hdiv as [ ? ? pc2 w2 Hstep2 Hrest ]; subst.
    inversion Hstep2 as [ ? ? b2 ? ? Hn2 Hr2 Hlt2 ]; subst.
    rewrite Hn in Hn2. injection Hn2 as <-. rewrite Hr in Hr2. discriminate Hr2.
  - inversion Hdiv as [ ? ? pc2 w2 Hstep2 Hrest ]; subst.
    inversion Hstep2 as [ ? ? b2 ? ? Hn2 Hr2 Hlt2 ]; subst.
    rewrite Hn in Hn2. injection Hn2 as <-. rewrite Hr in Hr2. discriminate Hr2.
  - inversion Hdiv as [ ? ? pc2 w2 Hstep2 Hrest ]; subst.
    destruct (blocks_step_det _ _ _ _ _ _ _ Hstep Hstep2) as [ E1 E2 ]. subst.
    exact (IH Hrest).
Qed.

(** TERMINATION CERTIFICATE — a RANKING function: every jump strictly decreases [rank].
    The certificate is PER-PROGRAM evidence (each accepted CFG supplies its own [rank]
    and discharges the two obligations); the soundness theorem below is CLASS-WIDE and
    fuel-free — termination follows for EVERY world, by well-founded descent, never by
    stepping a budget. *)
Definition blocks_ranked (blocks : list (IO Next)) (rank : nat -> World -> nat) : Prop :=
  forall pc (w : World) b, nth_error blocks pc = Some b ->
    match run_io b w with
    | ORet (Jump pc') w' => (rank pc' w' < rank pc w)%nat
    | _ => True
    end.

Theorem blocks_ranked_terminates : forall blocks rank,
  blocks_jump_wf blocks -> blocks_ranked blocks rank ->
  forall pc (w : World), (pc < List.length blocks)%nat ->
  exists out, blocks_eval blocks pc w out.
Proof.
  intros blocks rank Hwf Hrank.
  assert (H : forall n pc (w : World), (rank pc w < n)%nat -> (pc < List.length blocks)%nat ->
              exists out, blocks_eval blocks pc w out).
  { induction n as [ | n IH ]; intros pc w Hr Hpc; [ lia | ].
    destruct (nth_error blocks pc) as [ b | ] eqn:Hnth.
    2: { exfalso. apply nth_error_Some in Hpc. congruence. }
    destruct (run_io b w) as [ [ pc' | ] w' | v w' ] eqn:Hrun.
    - (* Jump: in range by [blocks_jump_wf], smaller by [blocks_ranked] — recurse *)
      pose proof (Hwf pc b w Hnth) as Hin. rewrite Hrun in Hin.
      pose proof (Hrank pc w b Hnth) as Hdec. rewrite Hrun in Hdec.
      destruct (IH pc' w' ltac:(lia) Hin) as [ out Hout ].
      exists out. exact (be_jump blocks pc w pc' w' out (bs_jump blocks pc w b pc' w' Hnth Hrun Hin) Hout).
    - exists (ORet tt w'). exact (be_done blocks pc w b w' Hnth Hrun).
    - exists (OPanic v w'). exact (be_panic blocks pc w b v w' Hnth Hrun). }
  intros pc w Hpc. exact (H (S (rank pc w)) pc w (Nat.lt_succ_diag_r _) Hpc).
Qed.

(** DIVERGENCE CERTIFICATE — a SPIN invariant: a property every configuration in which
    STEPS and re-establishes it.  Per-program evidence; the soundness theorem is the
    class-wide coinductive counterpart of [blocks_ranked_terminates]. *)
Definition blocks_spinning (blocks : list (IO Next)) (inv : nat -> World -> Prop) : Prop :=
  forall pc (w : World), inv pc w ->
    exists pc' w', blocks_step blocks pc w pc' w' /\ inv pc' w'.

Theorem blocks_spinning_diverges : forall blocks inv,
  blocks_spinning blocks inv ->
  forall pc (w : World), inv pc w -> blocks_diverge blocks pc w.
Proof.
  intros blocks inv Hspin. cofix CIH.
  intros pc w Hinv.
  destruct (Hspin pc w Hinv) as [ pc' [ w' [ Hstep Hinv' ] ] ].
  exact (bd_jump blocks pc w pc' w' Hstep (CIH pc' w' Hinv')).
Qed.

(** ---- The STATIC-TARGET CFG core class ---- the constructor boundary for blocks: a
    body plus terminators that are SYNTAX, not computed values.  [CBSeq] runs a
    straight-line effect and terminates unconditionally; [CBIf] lets the body choose
    between TWO static targets — loops-with-exit become representable while target
    admissibility stays DECIDED by boolean checkers with soundness theorems.  Bodies
    stay opaque effects; anything whose TARGETS are computed remains outside the class
    (the general class keeps its per-program certificate route above). *)
Inductive CBlock :=
| CBSeq : IO unit -> Next -> CBlock
| CBIf  : IO bool -> Next -> Next -> CBlock.
Definition cblock_denote (b : CBlock) : IO Next :=
  match b with
  | CBSeq body t => bind body (fun _ => ret t)
  | CBIf body t1 t2 => bind body (fun v => ret (if v then t1 else t2))
  end.
Definition cb_targets (b : CBlock) : list Next :=
  match b with CBSeq _ t => (t :: nil)%list | CBIf _ t1 t2 => (t1 :: t2 :: nil)%list end.

(** a returned terminator is always one of the block's SYNTACTIC targets. *)
Lemma cblock_denote_ret : forall b (w : World) (t : Next) (w' : World),
  run_io (cblock_denote b) w = ORet t w' -> List.In t (cb_targets b).
Proof.
  intros b w t w' H. destruct b as [ body t0 | body t1 t2 ]; cbn [cblock_denote cb_targets] in *.
  - unfold bind, run_io in H. destruct (body w) as [ [] w0 | v w0 ]; [ | discriminate H ].
    injection H as <- _. left. reflexivity.
  - unfold bind, run_io in H. destruct (body w) as [ v w0 | v w0 ]; [ | discriminate H ].
    injection H as <- _. destruct v; [ left; reflexivity | right; left; reflexivity ].
Qed.

(** every target lands in range — decidable, sound for [blocks_jump_wf]. *)
Definition check_target (len : nat) (t : Next) : bool :=
  match t with Done => true | Jump pc => Nat.ltb pc len end.
Definition check_targets (cbs : list CBlock) : bool :=
  List.forallb (fun b => List.forallb (check_target (List.length cbs)) (cb_targets b)) cbs.

Theorem check_targets_jump_wf : forall cbs,
  check_targets cbs = true ->
  blocks_jump_wf (List.map cblock_denote cbs).
Proof.
  intros cbs Hc n b w Hnth.
  rewrite List.nth_error_map in Hnth.
  destruct (nth_error cbs n) as [ cb | ] eqn:Hn; [ | discriminate Hnth ].
  injection Hnth as <-.
  destruct (run_io (cblock_denote cb) w) as [ [ pc' | ] w' | v w' ] eqn:Hrun; [ | exact I | exact I ].
  pose proof (cblock_denote_ret cb w (Jump pc') w' Hrun) as Ht.
  pose proof (proj1 (List.forallb_forall _ cbs) Hc cb (List.nth_error_In cbs n Hn)) as Hok.
  cbv beta in Hok.
  pose proof (proj1 (List.forallb_forall _ (cb_targets cb)) Hok (Jump pc') Ht) as Hok'.
  cbn [check_target] in Hok'.
  rewrite List.length_map. apply Nat.ltb_lt. exact Hok'.
Qed.

(** every target of every block goes strictly FORWARD — decidable.  TOGETHER WITH
    [check_targets] it is a CHECKED termination certificate: [fun pc _ => len - pc] is
    a ranking function, so every IN-RANGE configuration of a target-checked forward CFG
    evaluates (for EVERY world) — [cblocks_forward_terminates] states exactly that,
    with BOTH checks as premises.  Loops-with-exit fail this check by construction and
    keep the per-program [blocks_ranked] route. *)
Fixpoint check_forward_from (i : nat) (cbs : list CBlock) : bool :=
  match cbs with
  | nil => true
  | b :: r => (List.forallb (fun t => match t with Done => true | Jump pc => Nat.ltb i pc end)
                            (cb_targets b)
               && check_forward_from (S i) r)%bool
  end.
Definition check_forward (cbs : list CBlock) : bool := check_forward_from 0 cbs.

Lemma check_forward_from_nth : forall cbs i n b pc,
  check_forward_from i cbs = true -> nth_error cbs n = Some b -> List.In (Jump pc) (cb_targets b) ->
  (i + n < pc)%nat.
Proof.
  induction cbs as [ | b0 r IH ]; intros i n b pc Hc Hn Ht.
  - destruct n; discriminate Hn.
  - cbn [check_forward_from] in Hc. apply andb_prop in Hc. destruct Hc as [ Hb Hr ].
    destruct n as [ | n ].
    + injection Hn as ->.
      pose proof (proj1 (List.forallb_forall _ (cb_targets b)) Hb (Jump pc) Ht) as Hj.
      cbv beta in Hj. apply Nat.ltb_lt in Hj. lia.
    + cbn [nth_error] in Hn. pose proof (IH (S i) n b pc Hr Hn Ht). lia.
Qed.

Theorem cblocks_forward_terminates : forall cbs,
  check_targets cbs = true -> check_forward cbs = true ->
  forall pc (w : World), (pc < List.length cbs)%nat ->
  exists out, blocks_eval (List.map cblock_denote cbs) pc w out.
Proof.
  intros cbs Hct Hcf pc w Hpc.
  apply (blocks_ranked_terminates (List.map cblock_denote cbs)
           (fun pc _ => List.length cbs - pc)).
  - apply check_targets_jump_wf. exact Hct.
  - intros n w0 b Hnth.
    rewrite List.nth_error_map in Hnth.
    destruct (nth_error cbs n) as [ cb | ] eqn:Hn; [ | discriminate Hnth ].
    injection Hnth as <-.
    destruct (run_io (cblock_denote cb) w0) as [ [ pc' | ] w' | v w' ] eqn:Hrun; [ | exact I | exact I ].
    pose proof (cblock_denote_ret cb w0 (Jump pc') w' Hrun) as Ht.
    pose proof (check_forward_from_nth cbs 0 n cb pc' Hcf Hn Ht) as Hfwd.
    pose proof (proj1 (List.forallb_forall _ cbs) Hct cb (List.nth_error_In cbs n Hn)) as Hok.
    cbv beta in Hok.
    pose proof (proj1 (List.forallb_forall _ (cb_targets cb)) Hok (Jump pc') Ht) as Hok'.
    cbn [check_target] in Hok'. apply Nat.ltb_lt in Hok'.
    lia.
  - rewrite List.length_map. exact Hpc.
Qed.

(** ---- The static-cycle DIVERGENCE certificate ---- over the DETERMINISTIC fragment:
    [snext] follows only unconditional static jumps (a [CBIf] on the trail makes the
    walk FAIL — conservative, no divergence claim).  A static cycle alone does NOT
    certify divergence: a body may PANIC, and [OPanic] is an outcome, not a step.  The
    certificate pairs the DECIDED graph fact — following static jumps from [pc0],
    [Done] is never reached, decided by walking [S (length cbs)] static steps: the walk
    visits more pcs than the finite pc space holds, so PIGEONHOLE yields a revisit and
    the deterministic trail is ultimately periodic (a completeness THEOREM about a
    finite graph, never a semantic budget) — with a PER-PROGRAM totality obligation for
    the bodies. *)
Definition snext (cbs : list CBlock) (pc : nat) : option nat :=
  match nth_error cbs pc with
  | Some (CBSeq _ (Jump pc')) => Some pc'
  | _ => None
  end.
Fixpoint swalk (cbs : list CBlock) (pc : nat) (i : nat) : option nat :=
  match i with
  | O => Some pc
  | S i' => match snext cbs pc with Some pc' => swalk cbs pc' i' | None => None end
  end.

Lemma swalk_split : forall cbs a b pc,
  swalk cbs pc (a + b) = match swalk cbs pc a with Some p => swalk cbs p b | None => None end.
Proof.
  induction a as [ | a IH ]; intros b pc; cbn [swalk Nat.add]; [ reflexivity | ].
  destruct (snext cbs pc) as [ pc' | ]; [ apply IH | reflexivity ].
Qed.
Lemma swalk_defined_le : forall cbs m m' pc q,
  swalk cbs pc m = Some q -> (m' <= m)%nat -> exists q', swalk cbs pc m' = Some q'.
Proof.
  intros cbs m m' pc q H Hle. replace m with (m' + (m - m'))%nat in H by lia.
  rewrite swalk_split in H.
  destruct (swalk cbs pc m') as [ p | ] eqn:E; [ eexists; reflexivity | discriminate H ].
Qed.
Lemma swalk_step_range : forall cbs pc m p q,
  swalk cbs pc m = Some p -> swalk cbs pc (S m) = Some q -> (p < List.length cbs)%nat.
Proof.
  intros cbs pc m p q Hm HSm. replace (S m) with (m + 1)%nat in HSm by lia.
  rewrite swalk_split, Hm in HSm. cbn [swalk] in HSm. unfold snext in HSm.
  destruct (nth_error cbs p) eqn:En; [ | discriminate HSm ].
  apply nth_error_Some. congruence.
Qed.

(** constructive pigeonhole over the finite pc space: a duplicate FINDER plus its
    soundness/completeness — never a classical extraction from a negated forall. *)
Fixpoint find_dup (l : list nat) : option nat :=
  match l with
  | nil => None
  | x :: r => if List.existsb (Nat.eqb x) r then Some x else find_dup r
  end.
Lemma find_dup_none_nodup : forall l, find_dup l = None -> List.NoDup l.
Proof.
  induction l as [ | x r IH ]; intros H; [ constructor | ].
  cbn in H. destruct (List.existsb (Nat.eqb x) r) eqn:E; [ discriminate H | ].
  constructor.
  - intro Hin. assert (Ht : List.existsb (Nat.eqb x) r = true).
    { apply List.existsb_exists. exists x. split; [ exact Hin | apply Nat.eqb_refl ]. }
    congruence.
  - apply IH. exact H.
Qed.
Lemma find_dup_some_split : forall l x, find_dup l = Some x ->
  exists l1 l2, l = (l1 ++ x :: l2)%list /\ List.In x l2.
Proof.
  induction l as [ | y r IH ]; intros x H; [ discriminate H | ].
  cbn in H. destruct (List.existsb (Nat.eqb y) r) eqn:E.
  - injection H as <-. exists nil, r. split; [ reflexivity | ].
    apply List.existsb_exists in E. destruct E as [ z [ Hz He ] ].
    apply Nat.eqb_eq in He. subst z. exact Hz.
  - destruct (IH x H) as [ l1 [ l2 [ Heq Hin ] ] ].
    exists (y :: l1)%list, l2. split; [ cbn; rewrite Heq; reflexivity | exact Hin ].
Qed.
Lemma bounded_long_dup : forall (l : list nat) bound,
  (forall x, List.In x l -> (x < bound)%nat) -> (bound < List.length l)%nat ->
  exists x, find_dup l = Some x.
Proof.
  intros l bound Hb Hlen. destruct (find_dup l) eqn:E; [ eexists; reflexivity | exfalso ].
  pose proof (find_dup_none_nodup l E) as Hnd.
  assert (Hincl : List.incl l (List.seq 0 bound)).
  { intros x Hx. apply List.in_seq. split; [ lia | ]. cbn. apply Hb. exact Hx. }
  pose proof (List.NoDup_incl_length Hnd Hincl) as Hle.
  rewrite List.length_seq in Hle. lia.
Qed.
Lemma seq_nth_error_local : forall sz start k, (k < sz)%nat ->
  List.nth_error (List.seq start sz) k = Some (start + k)%nat.
Proof.
  induction sz as [ | sz IH ]; intros start k Hk; [ lia | ].
  destruct k as [ | k ]; cbn; [ f_equal; lia | ].
  rewrite (IH (S start) k) by lia. f_equal. lia.
Qed.

(** the pigeonhole completeness: a successful [S (length cbs)]-walk means the walk is
    defined at EVERY length — the deterministic trail revisits a pc and is periodic
    from there on. *)
Lemma swalk_all_defined : forall cbs pc0 i j x, (i < j)%nat ->
  swalk cbs pc0 i = Some x -> swalk cbs pc0 j = Some x ->
  forall m, exists q, swalk cbs pc0 m = Some q.
Proof.
  intros cbs pc0 i j x Hij Hi Hj.
  assert (Hstep : forall m, (j <= m)%nat -> swalk cbs pc0 m = swalk cbs pc0 (m - (j - i))).
  { intros m Hm. replace m with (j + (m - j))%nat at 1 by lia. rewrite swalk_split, Hj.
    replace (m - (j - i))%nat with (i + (m - j))%nat by lia. rewrite swalk_split, Hi. reflexivity. }
  intro m. induction m as [ m IH ] using lt_wf_ind.
  destruct (Nat.le_gt_cases j m) as [ Hge | Hlt ].
  - rewrite (Hstep m Hge). apply IH. lia.
  - eapply swalk_defined_le; [ exact Hj | lia ].
Qed.
Lemma swalk_window_all : forall cbs pc0 q,
  swalk cbs pc0 (S (List.length cbs)) = Some q ->
  forall m, exists q', swalk cbs pc0 m = Some q'.
Proof.
  intros cbs pc0 q Hw.
  set (n := List.length cbs) in *.
  set (f := fun k => match swalk cbs pc0 k with Some p => p | None => 0%nat end).
  set (tr := List.map f (List.seq 0 (S n))).
  assert (Hdef : forall k, (k <= S n)%nat -> exists p, swalk cbs pc0 k = Some p).
  { intros k Hk. eapply swalk_defined_le; [ exact Hw | lia ]. }
  assert (Htr_at : forall idx v, List.nth_error tr idx = Some v ->
            (idx <= n)%nat /\ swalk cbs pc0 idx = Some v).
  { intros idx v Hnth.
    assert (Hlt : (idx < List.length tr)%nat) by (apply List.nth_error_Some; congruence).
    unfold tr in Hlt. rewrite List.length_map, List.length_seq in Hlt.
    unfold tr in Hnth. rewrite List.nth_error_map, (seq_nth_error_local (S n) 0 idx Hlt) in Hnth.
    cbn in Hnth. injection Hnth as <-.
    destruct (Hdef idx ltac:(lia)) as [ p Hp ].
    unfold f. rewrite Hp. split; [ lia | reflexivity ]. }
  assert (Hbnd : forall x, List.In x tr -> (x < n)%nat).
  { intros x Hx. destruct (List.In_nth_error tr x Hx) as [ idx Hnth ].
    destruct (Htr_at idx x Hnth) as [ Hle Hsw ].
    destruct (Hdef (S idx) ltac:(lia)) as [ p1 Hp1 ].
    exact (swalk_step_range cbs pc0 idx x p1 Hsw Hp1). }
  assert (Hlen : (n < List.length tr)%nat)
    by (unfold tr; rewrite List.length_map, List.length_seq; lia).
  destruct (bounded_long_dup tr n Hbnd Hlen) as [ x Hfd ].
  destruct (find_dup_some_split tr x Hfd) as [ l1 [ l2 [ Htr Hin2 ] ] ].
  destruct (List.In_nth_error l2 x Hin2) as [ k2 Hk2 ].
  assert (Hi_tr : List.nth_error tr (List.length l1) = Some x).
  { rewrite Htr. rewrite List.nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. }
  assert (Hj_tr : List.nth_error tr (List.length l1 + S k2)%nat = Some x).
  { rewrite Htr. rewrite List.nth_error_app2 by lia.
    replace (List.length l1 + S k2 - List.length l1)%nat with (S k2) by lia. cbn. exact Hk2. }
  destruct (Htr_at _ _ Hi_tr) as [ _ Hwi ].
  destruct (Htr_at _ _ Hj_tr) as [ _ Hwj ].
  exact (swalk_all_defined cbs pc0 (List.length l1) (List.length l1 + S k2)%nat x ltac:(lia) Hwi Hwj).
Qed.

(** the PER-PROGRAM totality obligation: every body returns on every world (no panic,
    no divergence inside a block).  NOT decidable from [CBlock] syntax — each accepted
    program discharges it by proof. *)
Definition cblocks_total (cbs : list CBlock) : Prop :=
  forall b, List.In b cbs ->
    match b with
    | CBSeq body _ => forall (w : World), exists w', run_io body w = ORet tt w'
    | CBIf body _ _ => forall (w : World), exists v w', run_io body w = ORet v w'
    end.

Theorem cblocks_static_diverges : forall cbs pc0,
  (match swalk cbs pc0 (S (List.length cbs)) with Some _ => true | None => false end) = true ->
  cblocks_total cbs ->
  forall w : World, blocks_diverge (List.map cblock_denote cbs) pc0 w.
Proof.
  intros cbs pc0 Hchk Htot w.
  destruct (swalk cbs pc0 (S (List.length cbs))) as [ qend | ] eqn:Hwalk; [ | discriminate Hchk ].
  pose proof (swalk_window_all cbs pc0 qend Hwalk) as ALL.
  apply (blocks_spinning_diverges _ (fun pc _ => exists m, swalk cbs pc0 m = Some pc)).
  2: { exists 0%nat. reflexivity. }
  intros pc w0 [ m Hm ].
  destruct (ALL (S m)) as [ pc' Hm1 ].
  assert (Hsn : snext cbs pc = Some pc').
  { replace (S m) with (m + 1)%nat in Hm1 by lia. rewrite swalk_split, Hm in Hm1.
    cbn [swalk] in Hm1. destruct (snext cbs pc) as [ p | ] eqn:E; [ | discriminate Hm1 ].
    injection Hm1 as <-. reflexivity. }
  unfold snext in Hsn.
  destruct (nth_error cbs pc) as [ b | ] eqn:Hb; [ | discriminate Hsn ].
  destruct b as [ body t | body t1 t2 ]; [ | discriminate Hsn ].
  destruct t as [ pcT | ] eqn:Hterm; [ | discriminate Hsn ].
  injection Hsn as ->.
  destruct (ALL (S (S m))) as [ q2 Hm2 ].
  assert (Hrange : (pc' < List.length cbs)%nat)
    by (exact (swalk_step_range cbs pc0 (S m) pc' q2 Hm1 Hm2)).
  destruct (Htot _ (List.nth_error_In cbs pc Hb) w0) as [ w' Hrun ].
  exists pc', w'. split.
  - apply (bs_jump _ pc w0 (cblock_denote (CBSeq body (Jump pc'))) pc' w').
    + rewrite List.nth_error_map, Hb. reflexivity.
    + cbn [cblock_denote]. unfold bind, run_io. unfold run_io in Hrun. rewrite Hrun. reflexivity.
    + rewrite List.length_map. exact Hrange.
  - exists (S m). exact Hm1.
Qed.

(** The CFG semantics surface, manifest-gated (PROGRESS "Current gates"): class-wide
    progress + one-step determinism + unique terminating outcomes + termination/divergence
    disjointness + the two certificate-soundness theorems + the static-target core class's CHECKED
    admissibility, termination, and divergence, certified zero-axiom as a bundle. *)
Definition blocks_cfg_surface :=
  (blocks_jump_wf_progress, blocks_step_det, blocks_eval_det, blocks_eval_diverge_disjoint,
   blocks_ranked_terminates, blocks_spinning_diverges,
   check_targets_jump_wf, cblocks_forward_terminates, cblocks_static_diverges).
Print Assumptions blocks_cfg_surface.

