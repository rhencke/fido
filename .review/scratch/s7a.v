
(* ── §5 The expression-fact algebra ────────────────────────────────────────── *)
(* One sealed dependent judgment. A failed, outside or blocked expression has no `ExprFact` at all — it has
  the corresponding exact site outcome. Every family below is indexed by the exact result it computes, so
  the result is never a field a constructor could be handed. *)

(* Result atoms over the retained phase, so every rule can compute its own vector. *)
Inductive ResultAtomAt {p} {i : Input p} (ph : Phase i)
  : Type :=
| RAUntyped : Constant -> ResultAtomAt ph
| RATyped  : forall t : SemanticType p, TypedConstant ph t -> ResultAtomAt ph
| RAValue  : SemanticType p -> ResultAtomAt ph.

Inductive ResultFormAt {p} {i : Input p} (ph : Phase i)
  : Type :=
| RFFixed    : list (ResultAtomAt ph) -> ResultFormAt ph
| RFContextual  : ContextualResult -> ResultFormAt ph
| RFNoStandalone : ResultFormAt ph.

(* The result a bound name yields is decided by its one exact meaning, not supplied beside it. A type or
  callable name has no standalone result; `iota` and `nil` are contextual and resolved at the exact use. *)
Definition name_result {p} {i : Input p} {ph : Phase i} {o}
 (m : ObjectMeaning ph o) : ResultFormAt ph :=
 match m with
 | MeaningConstant _ _ cm =>
   match cm with
   | CMPredeclaredBool _ _ b _ => RFFixed ph [RAUntyped ph (BoolConstant b)]
   | CMDeclared _ _ _ df =>
     match constant_declared df with
     | DeclaredUntyped _ k => RFFixed ph [RAUntyped ph k]
     | DeclaredTyped _ t tc => RFFixed ph [RATyped ph t tc]
     end
   end
 | MeaningVariable _ _ sv => RFFixed ph [RAValue ph (static_type sv)]
 | MeaningIota _ _ _ => RFContextual ph IotaResult
 | MeaningNil _ _ _ => RFContextual ph NilResult
 | MeaningType _ _ _ => RFNoStandalone ph
 | MeaningCallable _ _ _ => RFNoStandalone ph
 end.

(* Atom builders, so the `complex` cases below read as rules rather than as record plumbing. *)
Definition float_atom_typed {p} {i : Input p} {ph : Phase i}
 (t : SemanticType p) (f : FloatKind)
 (hu : Underlying ph t (predeclared_basic_form (float_named_basic f)))
 (v : BasicTypedConstant (predeclared_basic_form (float_named_basic f)))
 : ResultAtomAt ph :=
 RATyped ph t (@MakeTypedConstant p i ph t _ hu v).

Definition complex_atom_typed {p} {i : Input p} {ph : Phase i} (f : FloatKind)
 (vr : BasicTypedConstant (predeclared_basic_form (complex_named_basic f)))
 : ResultAtomAt ph :=
 RATyped ph (PredeclaredType p (complex_named_basic f))
  (@MakeTypedConstant p i ph (PredeclaredType p (complex_named_basic f)) _
   (UnderlyingPredeclared ph (complex_named_basic f)) vr).

Definition complex_atom_value {p} {i : Input p} {ph : Phase i} (f : FloatKind)
 : ResultAtomAt ph :=
 RAValue ph (PredeclaredType p (complex_named_basic f)).

(* ── The rule-coverage relations ───────────────────────────────────────────── *)
(* These are the one authority for "C6 has a rule for operands of this exact shape". The rule families
  below carry a coverage witness rather than restating its premises, and a requirement's satisfaction is
  stated over these — never over whether the successful fact happens to be inhabited. *)
Inductive UnaryRuleCovers {p} {i : Input p} {ph : Phase i}
 : ResultAtomAt ph -> Prop :=
| URUntyped : forall c, NumericConstantKind (constant_kind c) ->
  UnaryRuleCovers (RAUntyped ph c)
| URTyped : forall t tc b, Underlying ph t b -> NumericBasic b ->
  UnaryRuleCovers (RATyped ph t tc)
| URValue : forall t b, Underlying ph t b -> NumericBasic b ->
  UnaryRuleCovers (RAValue ph t).

(* `println` admits an argument whose underlying form exists; an untyped constant is defaulted first. *)
Inductive PrintlnArg {p} {i : Input p} {ph : Phase i}
 : ResultAtomAt ph -> Prop :=
| PAUntyped : forall c, Representable ph (default_type (constant_kind c)) c ->
  PrintlnArg (RAUntyped ph c)
| PATyped  : forall t tc b, Underlying ph t b -> PrintlnArg (RATyped ph t tc)
| PAValue  : forall t b, Underlying ph t b -> PrintlnArg (RAValue ph t).

Definition PrintlnRuleCovers {p} {i : Input p} {ph : Phase i}
 (args : list (ResultAtomAt ph)) : Prop := List.Forall (PrintlnArg ) args.

Inductive ConvRuleCovers {p} {i : Input p} {ph : Phase i}
 : SemanticType p -> ResultAtomAt ph -> Prop :=
| CCConstant : forall dst b c, Underlying ph dst b ->
  (exists c', convert_constant_to b c = Some c') ->
  ConvRuleCovers dst (RAUntyped ph c)
| CCTypedConstant : forall dst src (tc : TypedConstant ph src),
    ValueConvertible ph src dst -> ConvRuleCovers dst (RATyped ph src tc)
| CCValue : forall dst src, ValueConvertible ph src dst ->
  ConvRuleCovers dst (RAValue ph src).

(* A floating operand of an exact kind, constant or not: what the `complex` combinations quantify over. *)
Inductive FloatOperand {p} {i : Input p} {ph : Phase i}
 : ResultAtomAt ph -> FloatKind -> Prop :=
| FOTyped : forall t tc f, Underlying ph t (predeclared_basic_form (float_named_basic f)) ->
  FloatOperand (RATyped ph t tc) f
| FOValue : forall t f, Underlying ph t (predeclared_basic_form (float_named_basic f)) ->
  FloatOperand (RAValue ph t) f.

Inductive ComplexRuleCovers {p} {i : Input p} {ph : Phase i}
 : ResultAtomAt ph -> ResultAtomAt ph -> Prop :=
| CxCBothUntyped : forall c1 c2,
  NumericConstantKind (constant_kind c1) -> NumericConstantKind (constant_kind c2) ->
  ComplexRuleCovers (RAUntyped ph c1) (RAUntyped ph c2)
| CxCUntypedLeft : forall c y f, NumericConstantKind (constant_kind c) -> FloatOperand y f ->
  ComplexRuleCovers (RAUntyped ph c) y
| CxCUntypedRight : forall x c f, FloatOperand x f -> NumericConstantKind (constant_kind c) ->
  ComplexRuleCovers x (RAUntyped ph c)
| CxCBothKinded : forall x y f, FloatOperand x f -> FloatOperand y f ->
  ComplexRuleCovers x y.

(* The application target, derived from the exact head rather than guessed from the argument count. *)
Inductive ApplicationTarget {p} {i : Input p} (ph : Phase i) : Type :=
| ConversionTarget : SemanticType p -> ApplicationTarget ph
| BuiltinTarget  : forall o : ObjectRef ph, CallableMeaning ph o -> ApplicationTarget ph
| NotApplicable  : HeadView -> ApplicationTarget ph.

(* Coverage is asked of the exact target, never of the arity alone. *)
Definition ApplicationRuleCovers {p} {i : Input p} {ph : Phase i}
 (tgt : ApplicationTarget ph) (args : list (ResultAtomAt ph)) : Prop :=
 match tgt with
 | ConversionTarget _ dst => exists a1, args = [a1] /\ ConvRuleCovers dst a1
 | BuiltinTarget _ o _ =>
   (o = predeclared_object ph PComplex /\
    exists a1 a2, args = [a1; a2] /\ ComplexRuleCovers a1 a2) \/
   (o = predeclared_object ph PPrintln /\ PrintlnRuleCovers args)
 | NotApplicable _ _ => False
 end.

(* Statement eligibility is `println` and nothing else: `complex` is callable and still cannot stand as a
  statement, which is why callability alone was never the right question. *)
Definition StatementRuleCovers {p} {i : Input p} (ph : Phase i) (a : ApplicationRef p) : Prop :=
 exists (hu : NameUseRef p) (bf : BindingFact ph hu),
  application_head a = name_use_expr hu /\
  bound_object ph hu bf = predeclared_object ph PPrintln.

(* A contextual expression is resolved at the exact use. `iota` takes the index of its own const spec.
  There is deliberately no `nil` constructor: pinned `gc` rejects `nil` in every C6-representable context,
  so a `nil` use produces its exact requirement or diagnostic and never a resolved atom. *)
Inductive ContextResolvesAt {p} {i : Input p} (ph : Phase i)
 : ExprUseRef p -> ContextualResult -> ResultAtomAt ph -> Prop :=
| IotaResolves : forall (ih : InheritedConstUseRef p),
  ContextResolvesAt ph (InheritedUse p ih) IotaResult
   (RAUntyped ph (IntegerConstant (Z.of_nat (ic_iota p ih)))).

Inductive ExprFact {p} {i : Input p} (ph : Phase i)
  : ExprRef p -> ResultFormAt ph -> Type :=
| EFLiteral : forall (l : LiteralRef p),
  ExprFact ph (literal_expr l) (RFFixed ph [RAUntyped ph (literal_constant l)])
| EFName : forall (u : NameUseRef p)
  (bf : BindingFact ph u) (m : ObjectMeaning ph (bound_object ph u bf)),
  ExprFact ph (name_use_expr u) (name_result m)
| EFUnary : forall (n : UnaryRef p)
  (opa : ResultAtomAt ph) (res : list (ResultAtomAt ph)),
  ResultUseFactAt ph (DirectUse p (unary_operand_use n)) opa ->
  UnaryFact ph n opa res ->
  ExprFact ph (unary_expr n) (RFFixed ph res)
| EFApplication : forall (a : ApplicationRef p)
  (hf : ResultFormAt ph) (res : list (ResultAtomAt ph)),
  ExprFact ph (application_head a) hf -> AppFact ph a res ->
  ExprFact ph (application_expr_of a) (RFFixed ph res)

(* §10 A result use selects exactly one atom BY CONSTRUCTION. A head or statement use cannot inhabit it,
  and neither can an expression whose form is contextual-unresolved or no-standalone. *)
with ResultUseFactAt {p} {i : Input p} (ph : Phase i)
  : ExprUseRef p -> ResultAtomAt ph -> Type :=
| RUFFixed : forall (u : ExprUseRef p) (a : ResultAtomAt ph),
  use_refinement u = ResultRefinement ->
  ExprFact ph (expression_of_use u) (RFFixed ph [a]) ->
  ResultUseFactAt ph u a
| RUFContextual : forall (u : ExprUseRef p) (cr : ContextualResult) (a : ResultAtomAt ph),
  use_refinement u = ResultRefinement ->
  ExprFact ph (expression_of_use u) (RFContextual ph cr) ->
  ContextResolvesAt ph u cr a ->
  ResultUseFactAt ph u a

(* §7.1 Argument facts are indexed by the EXACT ordered source use list and the exact ordered atoms they
  consume, so there is one fact per source argument, in source order, with no duplicate and no omission. *)
with ArgFacts {p} {i : Input p} (ph : Phase i)
  : list (DirectExprUseRef p) -> list (ResultAtomAt ph) -> Type :=
| ArgsNil : ArgFacts ph [] []
| ArgsCons : forall (u : DirectExprUseRef p) (rest : list (DirectExprUseRef p))
  (a : ResultAtomAt ph) (arest : list (ResultAtomAt ph)),
  ResultUseFactAt ph (DirectUse p u) a -> ArgFacts ph rest arest ->
  ArgFacts ph (u :: rest) (a :: arest)

(* §11 The unary rule is indexed by the exact operand atom and computes its result from it. There is no
  free input constant and no unrelated output typed constant. *)
with UnaryFact {p} {i : Input p} (ph : Phase i)
  : UnaryRef p -> ResultAtomAt ph -> list (ResultAtomAt ph) -> Type :=
| UFUntyped : forall (n : UnaryRef p) (c c' : Constant),
  UnaryRuleCovers (RAUntyped ph c) -> negate_constant c = Some c' ->
  UnaryFact ph n (RAUntyped ph c) [RAUntyped ph c']
| UFTypedConstant : forall (n : UnaryRef p) (t : SemanticType p) (b : BasicType)
  (hu : Underlying ph t b) (v v' : BasicTypedConstant b),
  UnaryRuleCovers (RATyped ph t (@MakeTypedConstant p i ph t b hu v)) ->
  negate_basic_typed b v = Some v' ->
  UnaryFact ph n
   (RATyped ph t (@MakeTypedConstant p i ph t b hu v))
   [RATyped ph t (@MakeTypedConstant p i ph t b hu v')]
| UFValue : forall (n : UnaryRef p) (t : SemanticType p),
  UnaryRuleCovers (RAValue ph t) ->
  UnaryFact ph n (RAValue ph t) [RAValue ph t]

(* Arity is a constructor constraint, not a separate theorem: a conversion demands a one-element source
  argument list and `complex` a two-element one, so a wrong-arity application cannot build a fact. *)
with AppFact {p} {i : Input p} (ph : Phase i)
  : ApplicationRef p -> list (ResultAtomAt ph) -> Type :=
(* The destination is the head's own type meaning, not a free type beside it. *)
| AFConversion : forall (a : ApplicationRef p) (hu : NameUseRef p) (bf : BindingFact ph hu)
  (tm : TypeMeaning ph (bound_object ph hu bf))
  (u : DirectExprUseRef p) (arg : ResultAtomAt ph) (res : list (ResultAtomAt ph)),
  application_head a = name_use_expr hu ->
  application_argument_uses a = [u] ->
  ArgFacts ph [u] [arg] ->
  ConvRule ph a (type_meaning_type tm) arg res -> AppFact ph a res
| AFComplex : forall (a : ApplicationRef p) (hu : NameUseRef p) (bf : BindingFact ph hu)
  (u1 u2 : DirectExprUseRef p) (a1 a2 : ResultAtomAt ph)
  (res : list (ResultAtomAt ph)),
  application_head a = name_use_expr hu ->
  bound_object ph hu bf = predeclared_object ph PComplex ->
  application_argument_uses a = [u1; u2] ->
  ArgFacts ph [u1; u2] [a1; a2] -> ComplexRuleF ph a a1 a2 res -> AppFact ph a res
| AFPrintln : forall (a : ApplicationRef p) (hu : NameUseRef p) (bf : BindingFact ph hu)
  (args : list (ResultAtomAt ph)),
  application_head a = name_use_expr hu ->
  bound_object ph hu bf = predeclared_object ph PPrintln ->
  ArgFacts ph (application_argument_uses a) args ->
  PrintlnRuleF ph a args -> AppFact ph a []

(* §12.2 The conversion consumes the one exact argument atom and computes the exact result atom. *)
with ConvRule {p} {i : Input p} (ph : Phase i)

 : ApplicationRef p -> SemanticType p -> ResultAtomAt ph -> list (ResultAtomAt ph) -> Type :=
| CRConstant : forall (a : ApplicationRef p) (dst : SemanticType p) (b : BasicType)
  (hu : Underlying ph dst b) (c c' : Constant) (v : BasicTypedConstant b),
  convert_constant_to b c = Some c' -> basic_typed_of b c' = Some v ->
  ConvRule ph a dst (RAUntyped ph c) [RATyped ph dst (@MakeTypedConstant p i ph dst b hu v)]
| CRTypedConstant : forall (a : ApplicationRef p) (dst src : SemanticType p)
    (b_dst : BasicType) (hu_dst : Underlying ph dst b_dst)
    (tc : TypedConstant ph src) (tc' : TypedConstant ph dst),
    ValueConvertible ph src dst ->
    ConvRule ph a dst (RATyped ph src tc) [RATyped ph dst tc']
| CRValue : forall (a : ApplicationRef p) (dst src : SemanticType p),
    ValueConvertible ph src dst ->
    ConvRule ph a dst (RAValue ph src) [RAValue ph dst]

(* §12.3 `complex` consumes its two exact argument atoms. The result's constantness follows the operands'
  and its kind follows the exact floating kind they share. *)
with ComplexRuleF {p} {i : Input p} (ph : Phase i)

 : ApplicationRef p -> ResultAtomAt ph -> ResultAtomAt ph ->
  list (ResultAtomAt ph) -> Type :=
(* Two untyped numeric constants give an untyped complex constant. *)
| CxUntypedUntyped : forall (a : ApplicationRef p) (c1 c2 cr : Constant),
  NumericConstantKind (constant_kind c1) -> NumericConstantKind (constant_kind c2) ->
  complex_of_constants c1 c2 = Some cr ->
  ComplexRuleF ph a (RAUntyped ph c1) (RAUntyped ph c2) [RAUntyped ph cr]
(* One untyped constant with one typed floating constant: the untyped operand converts to the typed
  operand's exact kind, and the result is a typed complex constant of the matching kind. *)
| CxUntypedTypedL : forall (a : ApplicationRef p) (c : Constant) (t : SemanticType p) (f : FloatKind)
  (hu : Underlying ph t (predeclared_basic_form (float_named_basic f)))
  (v vc : BasicTypedConstant (predeclared_basic_form (float_named_basic f)))
  (vr : BasicTypedConstant (predeclared_basic_form (complex_named_basic f))),
  NumericConstantKind (constant_kind c) ->
  basic_typed_of (predeclared_basic_form (float_named_basic f)) c = Some vc ->
  complex_typed_of f vc v = Some vr ->
  ComplexRuleF ph a (RAUntyped ph c) (float_atom_typed t f hu v)
   [complex_atom_typed f vr]
| CxUntypedTypedR : forall (a : ApplicationRef p) (c : Constant) (t : SemanticType p) (f : FloatKind)
  (hu : Underlying ph t (predeclared_basic_form (float_named_basic f)))
  (v vc : BasicTypedConstant (predeclared_basic_form (float_named_basic f)))
  (vr : BasicTypedConstant (predeclared_basic_form (complex_named_basic f))),
  NumericConstantKind (constant_kind c) ->
  basic_typed_of (predeclared_basic_form (float_named_basic f)) c = Some vc ->
  complex_typed_of f v vc = Some vr ->
  ComplexRuleF ph a (float_atom_typed t f hu v) (RAUntyped ph c)
   [complex_atom_typed f vr]
(* One untyped constant with one floating value: the result is a value, not a constant. *)
| CxUntypedValueL : forall (a : ApplicationRef p) (c : Constant) (t : SemanticType p) (f : FloatKind),
  NumericConstantKind (constant_kind c) ->
  Underlying ph t (predeclared_basic_form (float_named_basic f)) ->
  ComplexRuleF ph a (RAUntyped ph c) (RAValue ph t) [complex_atom_value f]
| CxUntypedValueR : forall (a : ApplicationRef p) (c : Constant) (t : SemanticType p) (f : FloatKind),
  NumericConstantKind (constant_kind c) ->
  Underlying ph t (predeclared_basic_form (float_named_basic f)) ->
  ComplexRuleF ph a (RAValue ph t) (RAUntyped ph c) [complex_atom_value f]
(* Two typed floating constants of one identical type give a typed complex constant. *)
| CxTypedTyped : forall (a : ApplicationRef p) (t : SemanticType p) (f : FloatKind)
  (hu : Underlying ph t (predeclared_basic_form (float_named_basic f)))
  (v1 v2 : BasicTypedConstant (predeclared_basic_form (float_named_basic f)))
  (vr : BasicTypedConstant (predeclared_basic_form (complex_named_basic f))),
  complex_typed_of f v1 v2 = Some vr ->
  ComplexRuleF ph a (float_atom_typed t f hu v1) (float_atom_typed t f hu v2)
   [complex_atom_typed f vr]
(* A typed floating constant with a floating value of the same type gives a value. *)
| CxTypedValueL : forall (a : ApplicationRef p) (t : SemanticType p) (f : FloatKind)
  (hu : Underlying ph t (predeclared_basic_form (float_named_basic f)))
  (v : BasicTypedConstant (predeclared_basic_form (float_named_basic f))),
  ComplexRuleF ph a (float_atom_typed t f hu v) (RAValue ph t) [complex_atom_value f]
| CxTypedValueR : forall (a : ApplicationRef p) (t : SemanticType p) (f : FloatKind)
  (hu : Underlying ph t (predeclared_basic_form (float_named_basic f)))
  (v : BasicTypedConstant (predeclared_basic_form (float_named_basic f))),
  ComplexRuleF ph a (RAValue ph t) (float_atom_typed t f hu v) [complex_atom_value f]
(* Two floating values of one identical type give a value. *)
| CxValues : forall (a : ApplicationRef p) (t : SemanticType p) (f : FloatKind),
  Underlying ph t (predeclared_basic_form (float_named_basic f)) ->
  ComplexRuleF ph a (RAValue ph t) (RAValue ph t) [complex_atom_value f]

with PrintlnRuleF {p} {i : Input p} (ph : Phase i)
  : ApplicationRef p -> list (ResultAtomAt ph) -> Type :=
| PrFAdmitted : forall (a : ApplicationRef p) (args : list (ResultAtomAt ph)),
  PrintlnRuleCovers args -> PrintlnRuleF ph a args.

(* ── §5 The one remaining projection ───────────────────────────────────────── *)
(* `result_form` is now the index itself, so there is nothing left to project. Only the referenced object
  is a genuine view of the fact. *)
Definition expr_referenced_object {p} {i : Input p} {ph : Phase i} {r} {form}
 (f : ExprFact ph r form) : option (ObjectRef ph) :=
 match f with
 | EFName _ u bf _ => Some (bound_object ph u bf)
 | _ => None
 end.

(* ── §8 A statement fact exists only for an eligible statement ─────────────── *)
Definition IsPrintlnApp {p} {i : Input p} {ph : Phase i} {a} {res}
 (f : AppFact ph a res) : Prop :=
 match f with AFPrintln _ _ _ _ _ _ _ _ _ => True | _ => False end.

Definition IsConversionApp {p} {i : Input p} {ph : Phase i} {a} {res}
 (f : AppFact ph a res) : Prop :=
 match f with AFConversion _ _ _ _ _ _ _ _ _ _ _ _ => True | _ => False end.

Definition IsComplexApp {p} {i : Input p} {ph : Phase i} {a} {res}
 (f : AppFact ph a res) : Prop :=
 match f with AFComplex _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True | _ => False end.

Inductive StmtFact {p} {i : Input p} (ph : Phase i)
  : ExpressionStatementRef p -> Type :=
| SFPrintln : forall (s : ExpressionStatementRef p) (a : ApplicationRef p)
  (res : list (ResultAtomAt ph)) (f : AppFact ph a res),
  statement_application s = Some a -> IsPrintlnApp f -> StmtFact ph s.

Definition statement_application_of {p} {i : Input p} {ph : Phase i} {s}
 (f : StmtFact ph s) : ApplicationRef p :=
 match f with SFPrintln _ _ a _ _ _ _ => a end.
