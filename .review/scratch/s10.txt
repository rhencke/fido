
(* ── §8 Applications: rules consume the exact argument occurrences ─────────── *)
Parameter HeadDenotesType : forall {cp : Program} {r},
  ExpressionFact cp r -> AcceptedType cp -> Prop.

Definition app_head_fact (cp : Program) (a : ApplicationRef (source cp))
  : ExpressionFact cp (application_head a) := expression_fact cp (application_head a).
Definition app_parent_fact (cp : Program) (a : ApplicationRef (source cp))
  : ExpressionFact cp (application_expr a) := expression_fact cp (application_expr a).
Definition app_argument_uses (cp : Program) (a : ApplicationRef (source cp))
  : list (ExprUseRef (source cp)) :=
  List.map (DirectUse (source cp)) (application_argument_uses a).

(* Every argument use has the argument role, so its refinement is a result refinement. *)
Parameter application_argument_role : forall {p} (a : ApplicationRef p) (u : DirectExprUseRef p),
  In u (application_argument_uses a) -> direct_role u = RApplicationArgument.

(* The ordered argument occurrences; §Theorems freeze length, order, parent, role and child exactness. *)
Parameter app_argument_occurrences : forall (cp : Program) (a : ApplicationRef (source cp)),
  list (ResultOccurrence cp).

Definition app_profile (cp : Program) (a : ApplicationRef (source cp)) : ErasedProfile :=
  List.map (fun o => ERFixed [erase_atom (occurrence_atom o)]) (app_argument_occurrences cp a).

Inductive AppTarget {cp : Program} {r} (f : ExpressionFact cp r) : Type :=
| ConversionTarget : forall t : AcceptedType cp, HeadDenotesType f t -> AppTarget f
| CallableTarget   : HeadCallable f -> AppTarget f
| NotApplicable    : AppTarget f.

Parameter app_target : forall (cp : Program) (a : ApplicationRef (source cp)),
  AppTarget (app_head_fact cp a).

Definition predeclared_type_of (cp : Program) (t : PredeclaredBasicType) : AcceptedType cp :=
  PredeclaredType (accepted_environment cp) t.

(* §8.2 A conversion consumes exactly one argument occurrence. *)
Inductive ConversionRule (cp : Program) (a : ApplicationRef (source cp))
  (dst : AcceptedType cp) : Type :=
| ConvConstant : forall (o : ResultOccurrence cp) (b : BasicType) (c c' : Constant),
    app_argument_occurrences cp a = [o] ->
    occurrence_atom o = UntypedConstant cp c ->
    AcceptedUnderlying cp dst b -> convert_constant_to b c = Some c' ->
    ConversionRule cp a dst
| ConvTypedConstant : forall (o : ResultOccurrence cp) (src : AcceptedType cp)
    (sc : AcceptedTypedConstant cp src) (b : BasicType) (c c' : Constant),
    app_argument_occurrences cp a = [o] ->
    occurrence_atom o = TypedConstantAtom cp src sc ->
    AcceptedUnderlying cp dst b -> convert_constant_to b c = Some c' ->
    ConversionRule cp a dst
| ConvValue : forall (o : ResultOccurrence cp) (src : AcceptedType cp),
    app_argument_occurrences cp a = [o] ->
    occurrence_atom o = ValueResult cp src ->
    AcceptedConvertible cp src dst -> ConversionRule cp a dst.

Parameter typed_constant_of : forall (cp : Program) (t : AcceptedType cp) (b : BasicType),
  AcceptedUnderlying cp t b -> Constant -> option (AcceptedTypedConstant cp t).

Definition conversion_results (cp : Program) (a : ApplicationRef (source cp))
  (dst : AcceptedType cp) (r : ConversionRule cp a dst) : list (ResultAtom cp) :=
  match r with
  | ConvConstant _ _ _ _ b _ c' _ _ hu _ =>
      match typed_constant_of cp dst b hu c' with
      | Some tc => [TypedConstantAtom cp dst tc]
      | None => []
      end
  | ConvTypedConstant _ _ _ _ _ _ b _ c' _ _ hu _ =>
      match typed_constant_of cp dst b hu c' with
      | Some tc => [TypedConstantAtom cp dst tc]
      | None => []
      end
  | ConvValue _ _ _ _ _ _ _ _ => [ValueResult cp dst]
  end.

(* §8.3 `complex` consumes exactly two argument occurrences; the result is computed from them. *)
Inductive ComplexRule (cp : Program) (a : ApplicationRef (source cp)) : Type :=
| CxUntypedPair : forall (o1 o2 : ResultOccurrence cp) (c1 c2 cr : Constant),
    app_argument_occurrences cp a = [o1; o2] ->
    occurrence_atom o1 = UntypedConstant cp c1 ->
    occurrence_atom o2 = UntypedConstant cp c2 ->
    NumericConstantKind (constant_kind c1) -> NumericConstantKind (constant_kind c2) ->
    complex_of_constants c1 c2 = Some cr -> ComplexRule cp a
| CxTypedPair : forall (o1 o2 : ResultOccurrence cp) (t : AcceptedType cp) (f : FloatKind),
    app_argument_occurrences cp a = [o1; o2] ->
    AcceptedUnderlying cp t (predeclared_basic_form (float_named_basic f)) ->
    ComplexRule cp a.

Definition complex_results (cp : Program) (a : ApplicationRef (source cp))
  (r : ComplexRule cp a) : list (ResultAtom cp) :=
  match r with
  | CxUntypedPair _ _ _ _ _ _ cr _ _ _ _ _ _ => [UntypedConstant cp cr]
  | CxTypedPair _ _ _ _ _ f _ _ =>
      [ValueResult cp (predeclared_type_of cp (complex_named_basic f))]
  end.

(* §8.4 `println` consumes the exact ordered occurrences; its result vector is empty. *)
Inductive PrintlnArgOk (cp : Program) : ResultAtom cp -> Prop :=
| PAUntyped : forall c,
    AcceptedRepresentable cp (predeclared_type_of cp (default_basic (constant_kind c))) c ->
    PrintlnArgOk cp (UntypedConstant cp c)
| PATyped : forall (t : AcceptedType cp) (ct : AcceptedTypedConstant cp t) b,
    AcceptedUnderlying cp t b -> PrintlnArgOk cp (TypedConstantAtom cp t ct)
| PAValue : forall (t : AcceptedType cp) b,
    AcceptedUnderlying cp t b -> PrintlnArgOk cp (ValueResult cp t).

Definition PrintlnRule (cp : Program) (a : ApplicationRef (source cp)) : Prop :=
  List.Forall (fun o => PrintlnArgOk cp (occurrence_atom o)) (app_argument_occurrences cp a).

Inductive ApplicationRule (cp : Program) (a : ApplicationRef (source cp)) : Type :=
| ARConversion : forall (t : AcceptedType cp) (h : HeadDenotesType (app_head_fact cp a) t),
    app_target cp a = ConversionTarget (app_head_fact cp a) t h ->
    ConversionRule cp a t -> ApplicationRule cp a
| ARComplex : forall c : HeadCallable (app_head_fact cp a),
    app_target cp a = CallableTarget (app_head_fact cp a) c ->
    callable_name c = PComplex -> ComplexRule cp a -> ApplicationRule cp a
| ARPrintln : forall c : HeadCallable (app_head_fact cp a),
    app_target cp a = CallableTarget (app_head_fact cp a) c ->
    callable_name c = PPrintln -> PrintlnRule cp a -> ApplicationRule cp a.

Definition application_results (cp : Program) (a : ApplicationRef (source cp))
  (r : ApplicationRule cp a) : list (ResultAtom cp) :=
  match r with
  | ARConversion _ _ t _ _ cr => conversion_results cp a t cr
  | ARComplex _ _ _ _ _ cr => complex_results cp a cr
  | ARPrintln _ _ _ _ _ _ => []
  end.

Parameter accepted_application_rule : forall (cp : Program) (a : ApplicationRef (source cp)),
  ApplicationRule cp a.

(* §8.5 Unary minus consumes the exact operand occurrence; the result is the exact negation. *)
Parameter unary_operand_occurrence : forall (cp : Program) (n : UnaryRef (source cp)),
  ResultOccurrence cp.

Inductive UnaryRule (cp : Program) (n : UnaryRef (source cp)) : Type :=
| URUntyped : forall c c' : Constant,
    occurrence_atom (unary_operand_occurrence cp n) = UntypedConstant cp c ->
    NumericConstantKind (constant_kind c) -> negate_constant c = Some c' ->
    UnaryRule cp n
| URTypedConstant : forall (t : AcceptedType cp) (ct : AcceptedTypedConstant cp t)
    (b : BasicType) (c c' : Constant) (hu : AcceptedUnderlying cp t b),
    occurrence_atom (unary_operand_occurrence cp n) = TypedConstantAtom cp t ct ->
    NumericBasic b -> negate_constant c = Some c' -> UnaryRule cp n
| URValue : forall (t : AcceptedType cp) (b : BasicType),
    occurrence_atom (unary_operand_occurrence cp n) = ValueResult cp t ->
    AcceptedUnderlying cp t b -> NumericBasic b -> UnaryRule cp n.

Definition unary_results (cp : Program) (n : UnaryRef (source cp)) (r : UnaryRule cp n)
  : list (ResultAtom cp) :=
  match r with
  | URUntyped _ _ _ c' _ _ _ => [UntypedConstant cp c']
  | URTypedConstant _ _ t _ b _ c' hu _ _ _ =>
      match typed_constant_of cp t b hu c' with
      | Some tc => [TypedConstantAtom cp t tc]
      | None => []
      end
  | URValue _ _ t _ _ _ _ => [ValueResult cp t]
  end.

Parameter accepted_unary_rule : forall (cp : Program) (n : UnaryRef (source cp)),
  UnaryRule cp n.
