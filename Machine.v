From Stdlib Require Import List.
Import ListNotations.

(* The one labelled-transition base every later runtime milestone shares; it fixes no Go feature. *)
Record T : Type := Make {
  State  : Type;
  Start  : Type;
  Label  : Type;
  Result : Type;

  initial : Start -> State;
  step    : State -> Label -> State -> Prop;
  final   : State -> Result -> Prop
}.

Definition Trace (m : T) : Type := list (Label m).

(* A finite run is built only from real steps, so its trace is exactly the labels it consumed. *)
Inductive FiniteRun (m : T) : State m -> Trace m -> State m -> Prop :=
| FiniteRefl :
    forall s,
      FiniteRun m s [] s
| FiniteStep :
    forall s l s' trace s'',
      step m s l s' ->
      FiniteRun m s' trace s'' ->
      FiniteRun m s (l :: trace) s''.

(* An infinite run observes one real step at a time and never terminates. *)
CoInductive InfiniteRun (m : T) : State m -> Prop :=
| InfiniteStep :
    forall s l s',
      step m s l s' ->
      InfiniteRun m s' ->
      InfiniteRun m s.

Definition Reachable (m : T) (s : State m) : Prop :=
  exists start trace,
    FiniteRun m (initial m start) trace s.

(* Enabledness carries the witnessing label and successor, so a decision procedure can return them. *)
Definition Enabled (m : T) (s : State m) : Type :=
  { l : Label m & { s' : State m & step m s l s' } }.

Definition Disabled (m : T) (s : State m) : Prop :=
  forall l s', ~ step m s l s'.

(* The one decision shape later machines must prove from the same relational step. *)
Definition EnabledDecision (m : T) : Type :=
  forall s,
    Reachable m s ->
    (Enabled m s + Disabled m s)%type.

Definition FinalAbsorbing (m : T) : Prop :=
  forall s r,
    final m s r ->
    Disabled m s.

Definition Stuck (m : T) (s : State m) : Prop :=
  Disabled m s /\ forall r, ~ final m s r.

Theorem finite_run_app :
  forall m s trace1 s' trace2 s'',
    FiniteRun m s trace1 s' ->
    FiniteRun m s' trace2 s'' ->
    FiniteRun m s (trace1 ++ trace2) s''.
Proof.
  intros m s trace1 s' trace2 s'' Hrun1.
  induction Hrun1 as [s0 | s0 l s1 tr s2 Hstep Hrun IH]; intros Hrun2.
  - exact Hrun2.
  - simpl. apply FiniteStep with (s' := s1).
    + exact Hstep.
    + apply IH. exact Hrun2.
Qed.

Theorem initial_reachable :
  forall m start,
    Reachable m (initial m start).
Proof.
  intros m start. exists start, []. apply FiniteRefl.
Qed.

Theorem reachable_step :
  forall m s l s',
    Reachable m s ->
    step m s l s' ->
    Reachable m s'.
Proof.
  intros m s l s' [start [trace Hrun]] Hstep.
  exists start, (trace ++ [l]).
  apply finite_run_app with (s' := s).
  - exact Hrun.
  - apply FiniteStep with (s' := s').
    + exact Hstep.
    + apply FiniteRefl.
Qed.

Theorem final_absorbing_no_step :
  forall m s r l s',
    FinalAbsorbing m ->
    final m s r ->
    ~ step m s l s'.
Proof.
  intros m s r l s' Habsorbing Hfinal. exact (Habsorbing s r Hfinal l s').
Qed.

Theorem finite_run_from_absorbing_final :
  forall m s r trace s',
    FinalAbsorbing m ->
    final m s r ->
    FiniteRun m s trace s' ->
    trace = [] /\ s' = s.
Proof.
  intros m s r trace s' Habsorbing Hfinal Hrun.
  destruct Hrun as [s0 | s0 l s1 tr s2 Hstep Hrest].
  - split; reflexivity.
  - exact (match Habsorbing s0 r Hfinal l s1 Hstep with end).
Qed.

Theorem infinite_run_from_absorbing_final :
  forall m s r,
    FinalAbsorbing m ->
    final m s r ->
    ~ InfiniteRun m s.
Proof.
  intros m s r Habsorbing Hfinal Hrun.
  destruct Hrun as [s0 l s1 Hstep Hrest].
  exact (Habsorbing s0 r Hfinal l s1 Hstep).
Qed.
