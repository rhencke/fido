
(* ── §6 Capabilities are phase families; accepted views are their projections ── *)
Parameter PhaseTypeMeaning PhaseConstantMeaning PhaseValueMeaning
          PhaseIotaMeaning PhaseNilMeaning PhaseStaticVariable :
  forall {p} {i : Input p} (ph : Phase i), ObjectRef ph -> Type.

Definition TypeMeaning (cp : Program) (o : Object cp) : Type :=
  PhaseTypeMeaning (accepted_phase cp) o.
Definition ConstantMeaning (cp : Program) (o : Object cp) : Type :=
  PhaseConstantMeaning (accepted_phase cp) o.
Definition ValueMeaning (cp : Program) (o : Object cp) : Type :=
  PhaseValueMeaning (accepted_phase cp) o.
Definition IotaMeaning (cp : Program) (o : Object cp) : Type :=
  PhaseIotaMeaning (accepted_phase cp) o.
Definition NilMeaning (cp : Program) (o : Object cp) : Type :=
  PhaseNilMeaning (accepted_phase cp) o.
Definition StaticVariable (cp : Program) (o : Object cp) : Type :=
  PhaseStaticVariable (accepted_phase cp) o.

Parameter type_meaning_type : forall {cp} {o}, TypeMeaning cp o -> AcceptedType cp.
Parameter value_meaning_type : forall {cp} {o}, ValueMeaning cp o -> AcceptedType cp.
Parameter static_variable_type : forall {cp} {o}, StaticVariable cp o -> AcceptedType cp.
(* One intrinsic correspondence: the variable fact retains both its exact site and its exact object. *)
Parameter static_variable_site : forall {cp} {o},
  StaticVariable cp o -> VariableSiteRef (source cp).

Inductive ConstantContent (cp : Program) : Type :=
| UntypedConstantMeaning : Constant -> ConstantContent cp
| TypedConstantMeaning : forall t : AcceptedType cp,
    AcceptedTypedConstant cp t -> ConstantContent cp.

Parameter constant_content : forall {cp} {o}, ConstantMeaning cp o -> ConstantContent cp.

(* A callable fact carries its identity as a function, so it cannot be relabelled as another builtin. *)
Parameter PhaseHeadCallable : forall {p} {i : Input p} {ph : Phase i} {r},
  PhaseExpressionFact ph r -> Type.
Parameter callable_name : forall {p} {i : Input p} {ph : Phase i} {r}
  {f : PhaseExpressionFact ph r}, PhaseHeadCallable f -> PredeclaredName.

Definition HeadCallable {cp : Program} {r} (f : ExpressionFact cp r) : Type :=
  PhaseHeadCallable f.

(* ── §7 Result atoms, forms and the one intrinsic occurrence ───────────────── *)
Inductive ResultAtom (cp : Program) : Type :=
| UntypedConstant   : Constant -> ResultAtom cp
| TypedConstantAtom : forall t : AcceptedType cp, AcceptedTypedConstant cp t -> ResultAtom cp
| ValueResult       : AcceptedType cp -> ResultAtom cp.

Inductive ResultForm (cp : Program) : Type :=
| FixedResults  : list (ResultAtom cp) -> ResultForm cp
| Contextual    : ContextualResult -> ResultForm cp
| NoStandalone  : ResultForm cp.

Definition erase_atom {cp : Program} (a : ResultAtom cp) : ErasedAtom :=
  match a with
  | UntypedConstant _ c => EAUntyped (constant_kind c)
  | TypedConstantAtom _ t _ => EATyped (accepted_type_view cp t)
  | ValueResult _ t => EAValue (accepted_type_view cp t)
  end.

Definition erase_result_form {cp : Program} (rf : ResultForm cp) : ErasedResultForm :=
  match rf with
  | FixedResults _ l => ERFixed (List.map erase_atom l)
  | Contextual _ c => ERContextual c
  | NoStandalone _ => ERNoStandalone
  end.

Parameter referenced_object : forall {cp} {r}, ExpressionFact cp r -> option (Object cp).
Parameter result_form : forall {cp} {r}, ExpressionFact cp r -> ResultForm cp.

Definition ResultUseFact (cp : Program) (u : ExprUseRef (source cp)) : Type :=
  PhaseResultUseFact (accepted_phase cp) u.

Definition as_result_use (cp : Program) (u : ExprUseRef (source cp))
  (h : use_refinement u = ResultRefinement) (f : UseFact cp u) : ResultUseFact cp u :=
  eq_rect (use_refinement u) (refinement_fact (accepted_phase cp) u) f ResultRefinement h.

Definition result_use_fact (cp : Program) (u : ExprUseRef (source cp))
  (h : use_refinement u = ResultRefinement) : ResultUseFact cp u :=
  as_result_use cp u h (use_fact cp u).

Parameter result_use_expression : forall {cp} {u},
  ResultUseFact cp u -> ExpressionFact cp (expression_of_use u).
Parameter result_use_atoms : forall {cp} {u}, ResultUseFact cp u -> list (ResultAtom cp).
Parameter result_use_target : forall {cp} {u}, ResultUseFact cp u -> option (AcceptedType cp).

(* The atom is not stored beside the vector: the split equation forces it to BE the element at the
   position, and the position is derived from the split.  No independent fact or atom field survives. *)
Record ResultOccurrence (cp : Program) : Type := MakeOccurrence {
  occ_use : ExprUseRef (source cp);
  occ_is_result : use_refinement occ_use = ResultRefinement;
  occ_before : list (ResultAtom cp);
  occ_atom : ResultAtom cp;
  occ_after : list (ResultAtom cp);
  occ_splits : result_use_atoms (result_use_fact cp occ_use occ_is_result)
                 = occ_before ++ occ_atom :: occ_after
}.

Definition occurrence_atom {cp : Program} (o : ResultOccurrence cp) : ResultAtom cp :=
  occ_atom cp o.
Definition occurrence_position {cp : Program} (o : ResultOccurrence cp) : nat :=
  List.length (occ_before cp o).

(* Head and statement uses carry no selected result at all. *)
Definition HeadUseFact (cp : Program) (u : ExprUseRef (source cp)) : Type :=
  PhaseHeadUseFact (accepted_phase cp) u.
Definition StatementUseFact (cp : Program) (u : ExprUseRef (source cp)) : Type :=
  PhaseStatementUseFact (accepted_phase cp) u.
Parameter head_use_expression : forall {cp} {u},
  HeadUseFact cp u -> ExpressionFact cp (expression_of_use u).
Parameter statement_use_expression : forall {cp} {u},
  StatementUseFact cp u -> ExpressionFact cp (expression_of_use u).
