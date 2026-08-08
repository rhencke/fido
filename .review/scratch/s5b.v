
(* ── The retained type-phase result ────────────────────────────────────────── *)
(* Two branches, not because there are two outcomes but because acyclicity is the only question the graph
   itself answers.  An acyclic phase whose nodes fail, are outside C6 scope, or are blocked is represented
   here exactly as well as a ready one: readiness is a property of the node table, not a third branch.
   `type U uintptr; type T U` is acyclic and never ready, and this result represents it. *)
Inductive TypePhaseResult {p} {i : Input p} (ph : Phase i) : Type :=
| PhaseCyclic  : TypeCycle (phase_equations ph) -> TypePhaseResult ph
| PhaseAcyclic : AcyclicEquations (phase_equations ph) -> TypePhaseResult ph.

Definition IsTypeReady {p} {i : Input p} {ph : Phase i} (res : TypePhaseResult ph) : Prop :=
  match res with
  | PhaseCyclic _ _ => False
  | PhaseAcyclic _ acyc => forall n : TypeNode p, NodeIsSupported (node_outcome ph acyc n)
  end.

Definition ready_of {p} {i : Input p} {ph : Phase i} (res : TypePhaseResult ph)
  : IsTypeReady res -> TypeReady ph :=
  match res return IsTypeReady res -> TypeReady ph with
  | PhaseCyclic _ _ => fun h => match h return TypeReady ph with end
  | PhaseAcyclic _ acyc => fun h => @MakeTypeReady p i ph acyc h
  end.

Parameter phase_type_result : forall {p} {i : Input p} (ph : Phase i), TypePhaseResult ph.
