# C6 — the static semantic foundation

Review: contract

Goal: ordinary source names acquire meaning only through binding. C6 lands the complete predeclared identity
catalog, one type environment, exact constants, expression/use/application facts, one intrinsic
result-consumption plan, compiler-owned static variable identity, both dependency objects, and a three-way
decision that never calls unmodelled Go a rejection.

**C6 is entirely static.** No `Runtime` module, no value, place, store, environment or `Machine.T`. C7
introduces all of them as one vertical, per `ARCH-11`. `ARCHITECTURE.md` §1 owns the ownership law;
`ROADMAP.md` owns the milestone sequence.

Every signature below elaborates under the pinned Rocq; `make contract-surface` is the check.

## 1. Module order

```text
Decimal Integer Float Complex FilePath ModulePath Version Collections Names Syntax Index Typing
Compilable Machine Safe Render Emit
```

## 2. Names — the exact pinned catalog

```coq
Inductive PredeclaredName : Type :=
| PAny | PBool | PByte | PComparable | PComplex64 | PComplex128 | PError | PFloat32 | PFloat64
| PInt | PInt8 | PInt16 | PInt32 | PInt64 | PRune | PString | PUint | PUint8 | PUint16 | PUint32
| PUint64 | PUintptr | PTrue | PFalse | PIota | PNil | PAppend | PCap | PClear | PClose | PComplex
| PCopy | PDelete | PImag | PLen | PMake | PMax | PMin | PNew | PPanic | PPrint | PPrintln | PReal
| PRecover.

Parameter predeclared_spelling : PredeclaredName -> string.
Parameter all_predeclared : list PredeclaredName.
Parameter classify_spelling : string -> option PredeclaredName.
Parameter predeclared_eqb : PredeclaredName -> PredeclaredName -> bool.

Record OrdinaryIdentifier : Type := MakeOrdinary {
  ordinary_identifier : Identifier;
  ordinary_not_blank  : spelling ordinary_identifier <> "_"%string }.
```

One constructor per pinned `PRE-*` row, in ledger order. C6 establishes identity and shadowing for every
member; later milestones add semantic rules to these exact identities.

## 3. Collections, Float, Syntax

```coq
Record NonEmpty (A : Type) : Type := MakeNonEmpty { ne_first : A; ne_rest : list A }.
Record NonNegativeDecimal : Type := MakeNonNegDecimal {
  nnd_decimal : Decimal;
  nnd_nonneg  : (0 <= coefficient nnd_decimal)%Z }.

Inductive BindingName : Type := Named (n : Names.OrdinaryIdentifier) | Blank.
Inductive UnaryOp : Type := UnaryMinus.

Inductive Literal : Type :=
| IntegerLiteral : N -> Literal
| FloatLiteral   : Float.NonNegativeDecimal -> Literal
| StringLiteral  : string -> Literal.

Inductive TypeExpr : Type := NamedType (n : Names.OrdinaryIdentifier).

Inductive Expr : Type :=
| Name        : Names.OrdinaryIdentifier -> Expr
| LiteralExpr : Literal -> Expr
| Unary       : UnaryOp -> Expr -> Expr
| Application : Expr -> list Expr -> Expr.

Inductive ConstInitializer : Type :=
| ExplicitConstInit  : option TypeExpr -> NonEmpty Expr -> ConstInitializer
| InheritedConstInit : ConstInitializer.
Record ConstSpec : Type := MakeConstSpec {
  const_names : NonEmpty BindingName; const_init : ConstInitializer }.

Inductive VarInitializer : Type :=
| VarTypeOnly : TypeExpr -> VarInitializer
| VarValues   : option TypeExpr -> NonEmpty Expr -> VarInitializer.
Record VarSpec : Type := MakeVarSpec {
  var_names : NonEmpty BindingName; var_init : VarInitializer }.

Inductive TypeSpec : Type :=
| AliasSpec : BindingName -> TypeExpr -> TypeSpec
| DefSpec   : BindingName -> TypeExpr -> TypeSpec.

Inductive Declaration : Type :=
| ConstDecl : list ConstSpec -> Declaration
| VarDecl   : list VarSpec   -> Declaration
| TypeDecl  : list TypeSpec  -> Declaration.

Inductive Stmt : Type :=
| ExprStmt        : Expr -> Stmt
| DeclarationStmt : Declaration -> Stmt
| ShortVarDecl    : NonEmpty BindingName -> NonEmpty Expr -> Stmt.

Inductive Block : Type := MakeBlock : list Stmt -> Block.

Inductive TopLevelDecl : Type :=
| TopDeclaration : Declaration -> TopLevelDecl
| Main           : Block -> TopLevelDecl.
```

C9 introduces the one general function-declaration root and deletes `Main` in the same milestone, migrating
every source value. No compatibility constructor survives.

## 4. Index

```coq
Inductive UseRole : Type := TypeNameRole | ValueNameRole | HeadNameRole.

Parameter ObjectSiteRef   : Syntax.Program -> Type.
Parameter VariableSiteRef : Syntax.Program -> Type.
Parameter object_site_key : forall {p}, ObjectSiteRef p -> Index.Key.
Parameter variable_site_object_site : forall {p}, VariableSiteRef p -> ObjectSiteRef p.

Parameter DirectExprUseRef : Syntax.Program -> Type.
Parameter direct_parent : forall {p}, DirectExprUseRef p -> Index.Snapshot.NodeRef p.
Parameter direct_child  : forall {p}, DirectExprUseRef p -> Index.ExprRef p.
Parameter direct_role   : forall {p}, DirectExprUseRef p -> Index.Role p.
Parameter direct_occupies : forall {p} (u : DirectExprUseRef p),
  Index.OccupiesRole (direct_parent u) (direct_child u) (direct_role u).

Parameter InheritedConstUseRef : Syntax.Program -> Type.
Parameter ic_decl        : forall {p}, InheritedConstUseRef p -> Index.ConstDeclRef p.
Parameter ic_current     : forall {p}, InheritedConstUseRef p -> Index.ConstSpecRef p.
Parameter ic_name        : forall {p}, InheritedConstUseRef p -> Index.BindingNameRef p.
Parameter ic_predecessor : forall {p}, InheritedConstUseRef p -> Index.ConstSpecRef p.
Parameter ic_expr        : forall {p}, InheritedConstUseRef p -> Index.ExprRef p.
Parameter ic_type        : forall {p}, InheritedConstUseRef p -> option (Index.TypeUseRef p).
Parameter ic_iota        : forall {p}, InheritedConstUseRef p -> nat.
Parameter ic_position    : forall {p}, InheritedConstUseRef p -> nat.

Parameter SpecInDecl : forall {p}, Index.ConstDeclRef p -> Index.ConstSpecRef p -> Prop.
Parameter NearestPrecedingExplicit :
  forall {p}, Index.ConstDeclRef p -> Index.ConstSpecRef p -> Index.ConstSpecRef p -> Prop.
Parameter NameAtPosition : forall {p}, Index.ConstSpecRef p -> Index.BindingNameRef p -> nat -> Prop.
Parameter ExprAtPosition : forall {p}, Index.ConstSpecRef p -> Index.ExprRef p -> nat -> Prop.
Parameter SpecTypeUse    : forall {p}, Index.ConstSpecRef p -> option (Index.TypeUseRef p) -> Prop.
Parameter StructuralIota : forall {p}, Index.ConstSpecRef p -> nat -> Prop.

Inductive ExprUseRef (p : Syntax.Program) : Type :=
| DirectUse    : DirectExprUseRef p -> ExprUseRef p
| InheritedUse : InheritedConstUseRef p -> ExprUseRef p.

Definition expression_of_use {p} (u : ExprUseRef p) : Index.ExprRef p :=
  match u with DirectUse d => direct_child d | InheritedUse i => ic_expr i end.
```

`ic_position` is a derived projection of the exact occurrences, not the identity authority. `ObjectSiteRef`
denotes any source occurrence establishing a semantic object; at C6 its inhabitants are named binding sites
and `Main`, and C9 extends the underlying views without changing `ObjectOrigin`.

Kinds and roles:

```text
kinds  FileKind PackageClauseKind MainKind DeclarationKind BlockKind StatementKind
       ConstSpecKind VarSpecKind TypeSpecKind BindingNameKind ExpressionKind TypeUseKind

roles  FilePackage  FileTopLevel n  MainBlock  BlockStatement n  StatementDeclaration
       DeclarationSpec n  BindingNameOccurrence n  ConstSpecType  ConstInitializerExpression n
       VarSpecType  VarInitializerExpression n  TypeSpecTarget  TypeNameUse
       ShortRightExpression n  StatementExpression  UnaryOperand
       ApplicationHead  ApplicationArgument n
```

## 5. Typing

```coq
Inductive BasicType : Type :=
| BoolBasic | IntegerBasic (k : Integer.Kind) | FloatBasic (k : Float.Kind)
| ComplexBasic (k : Complex.Kind) | StringBasic.

Inductive TypeView : Type :=
| BasicView   : BasicType -> TypeView
| DefinedView : Index.Key -> TypeView.

Inductive RawTypeTarget (p : Syntax.Program) : Type :=
| PredeclaredRaw : BasicType -> RawTypeTarget p
| AliasRaw       : Index.AliasSpecRef p -> RawTypeTarget p
| DefinedRaw     : Index.BoundDefinedTypeRef p -> RawTypeTarget p.

Parameter ResolvedTypeEquations : Syntax.Program -> Type.
Parameter TypeGraphEvidence : forall {p}, ResolvedTypeEquations p -> Type.
Parameter TypeCycle : forall {p}, ResolvedTypeEquations p -> Type.
Parameter AcyclicEquations : forall {p}, ResolvedTypeEquations p -> Prop.

Inductive GraphOutcome {p} (eqs : ResolvedTypeEquations p) : Type :=
| GraphAcyclic : TypeGraphEvidence eqs -> GraphOutcome eqs
| GraphCyclic  : TypeCycle eqs -> GraphOutcome eqs.

Parameter resolve_graph : forall {p} (eqs : ResolvedTypeEquations p), GraphOutcome eqs.
Parameter Env : forall {p} (eqs : ResolvedTypeEquations p), TypeGraphEvidence eqs -> Type.
Parameter build_env : forall {p} (eqs : ResolvedTypeEquations p) (ev : TypeGraphEvidence eqs), Env eqs ev.

Inductive TypeForm {p} {eqs : ResolvedTypeEquations p} {ev} (env : Env eqs ev) : Type :=
| BasicForm : BasicType -> TypeForm env.

Parameter SemanticType : forall {p} {eqs} {ev}, Env eqs ev -> Type.
Parameter form_type : forall {p} {eqs} {ev} {env : Env eqs ev}, TypeForm env -> SemanticType env.

Parameter AliasResolvesTo : forall {p} {eqs} {ev} (env : Env eqs ev),
  Index.AliasSpecRef p -> RawTypeTarget p -> Prop.
Parameter DefinedInEnv : forall {p} {eqs} {ev} (env : Env eqs ev),
  Index.BoundDefinedTypeRef p -> Prop.

Inductive ResolvedTypeTarget {p} {eqs} {ev} (env : Env eqs ev) : RawTypeTarget p -> Type :=
| ResolvedPredeclared (b : BasicType) : ResolvedTypeTarget env (PredeclaredRaw b)
| ResolvedAlias (a : Index.AliasSpecRef p) (t : RawTypeTarget p)
    (h : AliasResolvesTo env a t) (r : ResolvedTypeTarget env t)
  : ResolvedTypeTarget env (AliasRaw a)
| ResolvedDefined (d : Index.BoundDefinedTypeRef p) (h : DefinedInEnv env d)
  : ResolvedTypeTarget env (DefinedRaw d).

Parameter denote : forall {p} {eqs} {ev} {env : Env eqs ev} {t : RawTypeTarget p},
  ResolvedTypeTarget env t -> SemanticType env.

Parameter underlying     : forall {p} {eqs} {ev} (env : Env eqs ev), SemanticType env -> TypeForm env.
Parameter type_view      : forall {p} {eqs} {ev} {env : Env eqs ev}, SemanticType env -> TypeView.
Parameter identicalb     : forall {p} {eqs} {ev} (env : Env eqs ev), SemanticType env -> SemanticType env -> bool.
Parameter assignableb    : forall {p} {eqs} {ev} (env : Env eqs ev), SemanticType env -> SemanticType env -> bool.
Parameter convertibleb   : forall {p} {eqs} {ev} (env : Env eqs ev), SemanticType env -> SemanticType env -> bool.
Parameter representableb : forall {p} {eqs} {ev} (env : Env eqs ev), SemanticType env -> Constant -> bool.
Parameter Underlying   : forall {p} {eqs} {ev} (env : Env eqs ev), SemanticType env -> TypeForm env -> Prop.
Parameter Identical    : forall {p} {eqs} {ev} (env : Env eqs ev), SemanticType env -> SemanticType env -> Prop.
Parameter Assignable   : forall {p} {eqs} {ev} (env : Env eqs ev), SemanticType env -> SemanticType env -> Prop.
Parameter Convertible  : forall {p} {eqs} {ev} (env : Env eqs ev), SemanticType env -> SemanticType env -> Prop.
Parameter Representable : forall {p} {eqs} {ev} (env : Env eqs ev), SemanticType env -> Constant -> Prop.
Parameter TypedConstant : forall {p} {eqs} {ev} (env : Env eqs ev), SemanticType env -> Type.
Parameter convert_constant : forall {p} {eqs} {ev} (env : Env eqs ev) (s : SemanticType env) (c : Constant),
  Representable env s c -> TypedConstant env s.
Parameter default_type : forall {p} {eqs} {ev} (env : Env eqs ev), Constant -> SemanticType env.
```

`build_env` accepts only `GraphAcyclic` evidence. `ResolvedDefined` requires `DefinedInEnv`, so a cyclic,
rejected or blocked declaration mints no semantic type. `ResolvedAlias` returns its target's semantic type and
creates no identity. C6's `TypeForm` is closed at `BasicForm`; later milestones amend that one algebra.

## 6. The retained static phase

The exact expression `Phase` inside the exact `Core` is generalized into the permanent static-analysis object.
No peer analyzer is added; the existing work forest, member index, outcome trace and suffix provenance are
generalized.

```coq
Parameter Phase : forall {p}, Input p -> Type.
Parameter phase : forall {p} (core : Core p), Phase (core_input core).
Parameter phase_equations : forall {p} {i : Input p} (ph : Phase i), Typing.ResolvedTypeEquations p.
Parameter phase_graph : forall {p} {i : Input p} (ph : Phase i),
  Typing.TypeGraphEvidence (phase_equations ph).

Inductive ObjectKind : Type :=
| TypeObject | ConstantObject | VariableObject | FunctionObject | BuiltinObject | NilObject.

Inductive ObjectOrigin (p : Syntax.Program) : Type :=
| Predeclared  : Names.PredeclaredName -> ObjectOrigin p
| SourceObject : Index.ObjectSiteRef p -> ObjectOrigin p.

Parameter ObjectRef : forall {p} {i : Input p}, Phase i -> Type.
Parameter object_origin : forall {p} {i} {ph : Phase i}, ObjectRef ph -> ObjectOrigin p.
Parameter object_kind   : forall {p} {i} {ph : Phase i}, ObjectRef ph -> ObjectKind.

Parameter PhaseBindingFact : forall {p} {i : Input p} (ph : Phase i), Index.NameUseRef p -> Type.
Parameter bound_object : forall {p} {i} {ph : Phase i} {u}, PhaseBindingFact ph u -> ObjectRef ph.
Parameter PhaseApplicationSite : forall {p} {i : Input p} (ph : Phase i), Index.ApplicationRef p -> Type.
Parameter PhaseStatementSite : forall {p} {i : Input p} (ph : Phase i),
  Index.ExpressionStatementRef p -> Type.
Parameter PhaseUnarySite : forall {p} {i : Input p} (ph : Phase i), Index.UnaryRef p -> Type.

Inductive SemanticRequirement {p} {i : Input p} (ph : Phase i) : Type :=
| TypeMeaningReq  (u : Index.NameUseRef p) (b : PhaseBindingFact ph u)
| ValueMeaningReq (u : Index.NameUseRef p) (b : PhaseBindingFact ph u)
| ApplicationReq  (a : Index.ApplicationRef p) (site : PhaseApplicationSite ph a)
| StatementReq    (s : Index.ExpressionStatementRef p) (site : PhaseStatementSite ph s)
| UnaryReq        (n : Index.UnaryRef p) (site : PhaseUnarySite ph n).

Parameter RequirementSatisfied : forall {p} {i} {ph : Phase i}, SemanticRequirement ph -> Prop.
Parameter requirement_dec : forall {p} {i} {ph : Phase i} (r : SemanticRequirement ph),
  { RequirementSatisfied r } + { ~ RequirementSatisfied r }.
Parameter RootRequirement : forall {p} {i : Input p} (ph : Phase i), SemanticRequirement ph -> Prop.

Parameter ScopeBoundary : forall {p} {i : Input p} (ph : Phase i), SemanticRequirement ph -> Type.
Parameter boundary_missing : forall {p} {i} {ph : Phase i} {r : SemanticRequirement ph},
  ScopeBoundary ph r -> ~ RequirementSatisfied r.
Parameter PackedBoundary : forall {p} {i : Input p}, Phase i -> Type.
Parameter boundary_requirement : forall {p} {i} {ph : Phase i},
  PackedBoundary ph -> SemanticRequirement ph.
Parameter boundary_evidence : forall {p} {i} {ph : Phase i} (b : PackedBoundary ph),
  ScopeBoundary ph (boundary_requirement b).
```

No requirement constructor accepts an object or profile beside the fact that established it: the object is
`bound_object b`, and the target and profile are projections of `site`. Only the negative branch of
`requirement_dec` mints a boundary, whose constructor is private.

Internal partial site results are private. Each retains its exact site, its exact predecessor object, and one
of: the exact supported fact, the exact root diagnostic, the exact root boundary, or the exact dependency edge
plus the exact predecessor result that blocked it. A blocked site mints no placeholder fact, diagnostic or
boundary.

Phase order — declaration elaboration is interleaved, because an initializer determines the type of
`var x = e` and `x := e`, and scope construction depends only on the early binder disposition:

```text
Input → scopes + early binder disposition + object identities → all bindings + structural uses
      → type equations → GraphOutcome → Env or exact cycle
      → package dependency graph → exact order or exact cycle
      → declaration elaboration in dependency then source order:
          initializer expression facts → use facts → result plan → semantic fact → typed variable
      → remaining expression and application facts → unused-local result
      → root diagnostics + root boundaries
```

| declaration | scope begins |
|---|---|
| package `const`, `var`, `type`, `main` | the package block |
| local `const` spec | after the `ConstSpec` |
| local `var` spec | after the `VarSpec` |
| short-variable new binding | after the `ShortVarDecl` |
| **local `type` spec** | **at the identifier in the `TypeSpec`** |
| predeclared object | the outer universe block |
| blank | never |

## 7. Erased payloads and the faithful boundary key

```coq
Inductive RequirementKind : Type := KTypeMeaning | KValueMeaning | KApplication | KStatement | KUnary.

Inductive ErasedObjectOrigin : Type :=
| EPredeclared  : Names.PredeclaredName -> ErasedObjectOrigin
| ESourceObject : Index.Key -> ErasedObjectOrigin.

Inductive ContextualResult : Type := IotaResult | NilResult.

Inductive ErasedForm : Type :=
| EFConstant | EFValue (v : Typing.TypeView) | EFContextual (c : ContextualResult) | EFNone.

Inductive ErasedTarget : Type :=
| ETConversion (v : Typing.TypeView) | ETCallable (o : ErasedObjectOrigin)
| ETNotApplicable (k : ObjectKind).

Definition ErasedProfile : Type := list ErasedForm.

Record ErasedRequirement : Type := MakeErasedRequirement {
  er_site : Index.Key; er_kind : RequirementKind;
  er_object : option ErasedObjectOrigin; er_target : option ErasedTarget;
  er_profile : option ErasedProfile; er_form : option ErasedForm }.

Record RequirementKey : Type := MakeRequirementKey {
  rk_site : Index.Key; rk_kind : RequirementKind;
  rk_object : option ErasedObjectOrigin; rk_target : option ErasedTarget;
  rk_profile : option ErasedProfile }.

Parameter erased_requirement : forall {p} {i} {ph : Phase i}, SemanticRequirement ph -> ErasedRequirement.
Parameter requirement_key : forall {p} {i} {ph : Phase i}, SemanticRequirement ph -> RequirementKey.
Parameter boundary_key : forall {p} {i} {ph : Phase i}, PackedBoundary ph -> RequirementKey.
Parameter requirement_key_eqb : RequirementKey -> RequirementKey -> bool.
Parameter requirement_key_compare : RequirementKey -> RequirementKey -> comparison.
Definition key_lt (a b : RequirementKey) : Prop := requirement_key_compare a b = Lt.

Inductive BoundaryView : Type :=
| MissingTypeMeaning     (site : Index.Key) (obj : ErasedObjectOrigin)
| MissingValueMeaning    (site : Index.Key) (obj : ErasedObjectOrigin)
| MissingApplicationRule (site : Index.Key) (tgt : ErasedTarget) (prof : ErasedProfile)
| MissingStatementRule   (site : Index.Key) (form : ErasedForm)
| MissingUnaryRule       (site : Index.Key) (op : Syntax.UnaryOp) (form : ErasedForm).
Parameter boundary_view : forall {p} {i} {ph : Phase i}, PackedBoundary ph -> BoundaryView.
```

No certified value contains a roadmap or ledger identifier; `.review/closure.csv` maps a `BoundaryView` to the
milestone that owes its rule.

## 8. Outcome

```coq
Parameter core_diagnostics : forall {p}, Core p -> list (DiagnosticReason p).
Parameter core_boundaries : forall {p} (core : Core p), list (PackedBoundary (phase core)).

Inductive Decision {p} (core : Core p) : Type :=
| AcceptedDecision (Hd : core_diagnostics core = nil) (Hb : core_boundaries core = nil)
| RejectedDecision (Hd : core_diagnostics core <> nil)
| OutsideDecision  (Hd : core_diagnostics core = nil) (Hb : core_boundaries core <> nil).

Parameter decision : forall {p} (a : Elaboration p), Decision (elaboration_core a).

Parameter Program : Type.
Parameter source : Program -> Syntax.Program.
Parameter core : forall cp : Program, Core (source cp).
Parameter accepted : forall cp : Program, core_diagnostics (core cp) = nil.
Parameter in_scope : forall cp : Program, core_boundaries (core cp) = nil.

Parameter Failure : Syntax.Program -> Type.
Parameter failure_core : forall {p}, Failure p -> Core p.
Parameter rejected : forall {p} (f : Failure p), core_diagnostics (failure_core f) <> nil.

Parameter Outside : Syntax.Program -> Type.
Parameter outside_core : forall {p}, Outside p -> Core p.
Parameter outside_clean : forall {p} (o : Outside p), core_diagnostics (outside_core o) = nil.
Parameter outside_blocked : forall {p} (o : Outside p), core_boundaries (outside_core o) <> nil.

Inductive Outcome (p : Syntax.Program) : Type :=
| Compiled     (cp : Program) (Hcp : source cp = p)
| Rejected     (fail : Failure p)
| OutsideScope (out : Outside p).

Parameter compile : forall p : Syntax.Program, Outcome p.
Definition InScope (p : Syntax.Program) : Prop :=
  core_boundaries (elaboration_core (elaborate p)) = nil.
```

Only the internal mint constructs `Program`, `Failure` or `Outside`; only `Compiled` reaches `Safe.Program`
or `Emit.Image`.

## 9. Accepted facts — definitions projected from the exact phase

```coq
Definition accepted_phase (cp : Program) : Phase (core_input (core cp)) := phase (core cp).
Definition accepted_equations (cp : Program) : Typing.ResolvedTypeEquations (source cp) :=
  phase_equations (accepted_phase cp).
Definition accepted_graph (cp : Program) : Typing.TypeGraphEvidence (accepted_equations cp) :=
  phase_graph (accepted_phase cp).
Definition accepted_environment (cp : Program)
  : Typing.Env (accepted_equations cp) (accepted_graph cp) :=
  Typing.build_env (accepted_equations cp) (accepted_graph cp).

Definition Object (cp : Program) : Type := ObjectRef (accepted_phase cp).
Definition AcceptedType (cp : Program) : Type := Typing.SemanticType (accepted_environment cp).
Definition AcceptedTypedConstant (cp : Program) (t : AcceptedType cp) : Type :=
  Typing.TypedConstant (accepted_environment cp) t.
Definition AcceptedIdentical (cp : Program) (s t : AcceptedType cp) : Prop :=
  Typing.Identical (accepted_environment cp) s t.
Definition AcceptedAssignable (cp : Program) (s t : AcceptedType cp) : Prop :=
  Typing.Assignable (accepted_environment cp) s t.
Definition AcceptedUnderlying (cp : Program) (t : AcceptedType cp)
  (f : Typing.TypeForm (accepted_environment cp)) : Prop :=
  Typing.Underlying (accepted_environment cp) t f.
Definition accepted_type_view (cp : Program) (t : AcceptedType cp) : Typing.TypeView := Typing.type_view t.
Definition object_kind_of {cp} (o : Object cp) : ObjectKind := object_kind o.
Definition object_origin_of {cp} (o : Object cp) : ObjectOrigin (source cp) := object_origin o.

Parameter bound_object_at : forall (cp : Program) (u : Index.NameUseRef (source cp)), Object cp.
Parameter use_role_at : forall (cp : Program) (u : Index.NameUseRef (source cp)), UseRole.

Parameter StaticVariable : forall (cp : Program), Object cp -> Type.
Parameter static_variable_at : forall (cp : Program) (s : Index.VariableSiteRef (source cp)),
  { o : Object cp & StaticVariable cp o }.
Parameter static_variable_type : forall {cp} {o}, StaticVariable cp o -> AcceptedType cp.
Parameter static_variable_site : forall {cp} {o},
  StaticVariable cp o -> Index.VariableSiteRef (source cp).

Inductive BinderDisposition (cp : Program) : Type :=
| DispBlank
| DispDeclares (o : Object cp)
| DispReuses   (o : Object cp) (v : StaticVariable cp o).
Parameter binder_disposition : forall (cp : Program) (s : Index.BindingSiteRef (source cp)),
  BinderDisposition cp.

Inductive ResultAtom (cp : Program) : Type :=
| UntypedConstant   (c : Typing.Constant)
| TypedConstantAtom (t : AcceptedType cp) (k : AcceptedTypedConstant cp t)
| ValueResult       (t : AcceptedType cp).

Inductive ResultForm (cp : Program) : Type :=
| FixedResults   (v : list (ResultAtom cp))
| ContextualForm (c : ContextualResult)
| NoStandaloneResult.

Parameter ExpressionFact : forall (cp : Program), Index.ExprRef (source cp) -> Type.
Parameter expression_fact : forall cp r, ExpressionFact cp r.
Parameter referenced_object : forall {cp} {r}, ExpressionFact cp r -> option (Object cp).
Parameter result_form : forall {cp} {r}, ExpressionFact cp r -> ResultForm cp.

Parameter UseFact : forall (cp : Program), ExprUseRef (source cp) -> Type.
Parameter use_fact : forall cp u, UseFact cp u.
Parameter use_expression_fact : forall {cp} {u} (f : UseFact cp u),
  ExpressionFact cp (expression_of_use u).
Parameter use_target_type : forall {cp} {u}, UseFact cp u -> option (AcceptedType cp).
Parameter use_defaulted : forall {cp} {u}, UseFact cp u -> option (AcceptedType cp).
Parameter use_selected : forall {cp} {u}, UseFact cp u -> list (ResultAtom cp).

Parameter HeadDenotesType : forall {cp} {r}, ExpressionFact cp r -> AcceptedType cp -> Prop.
Parameter HeadCallable : forall {cp} {r}, ExpressionFact cp r -> Type.
Inductive AppTarget {cp} {r} (f : ExpressionFact cp r) : Type :=
| ConversionTarget (t : AcceptedType cp) (Ht : HeadDenotesType f t)
| CallableTarget   (c : HeadCallable f).

Definition ArgumentProfile (cp : Program) : Type := list (ResultForm cp).

Parameter ApplicationFact : forall (cp : Program) (a : Index.ApplicationRef (source cp)),
  ExpressionFact cp (Index.application_expr a) -> Type.
Parameter application_fact : forall cp a,
  ApplicationFact cp a (expression_fact cp (Index.application_expr a)).
Parameter app_head_fact : forall {cp} {a} {pf}, ApplicationFact cp a pf ->
  ExpressionFact cp (Index.application_head a).
Parameter app_target : forall {cp} {a} {pf} (af : ApplicationFact cp a pf), AppTarget (app_head_fact af).
Parameter app_arg_uses : forall {cp} {a} {pf}, ApplicationFact cp a pf ->
  list (DirectExprUseRef (source cp)).
Parameter app_profile : forall {cp} {a} {pf}, ApplicationFact cp a pf -> ArgumentProfile cp.
Parameter app_results : forall {cp} {a} {pf}, ApplicationFact cp a pf -> list (ResultAtom cp).
Parameter target_results : forall {cp} {r} {f : ExpressionFact cp r},
  AppTarget f -> ArgumentProfile cp -> list (ResultAtom cp).

Parameter StatementEligible : forall (cp : Program), Index.ExpressionStatementRef (source cp) -> Prop.
Parameter statement_eligible_dec : forall cp s,
  { StatementEligible cp s } + { ~ StatementEligible cp s }.

Parameter DependencyFact : forall (cp : Program), Index.PackageRef (source cp) -> Type.
Parameter dependency_fact : forall cp k, DependencyFact cp k.
Parameter dependency_order : forall {cp} {k}, DependencyFact cp k -> list (Index.BindingSiteRef (source cp)).
Parameter dependency_graph : forall (cp : Program), Index.PackageRef (source cp) ->
  DependencyGraph (source cp).
Parameter Acyclic : forall {p} (g : DependencyGraph p), list (Index.BindingSiteRef p) -> Prop.
Parameter acyclicb : forall {p}, DependencyGraph p -> bool.
Parameter order_of : forall {p} (g : DependencyGraph p), list (Index.BindingSiteRef p).
Parameter DependencyEdgesFromBindings : forall {cp} {k}, DependencyFact cp k -> Prop.
```

`Object`, `AcceptedType` and every accepted type relation are **definitions** over the environment the phase
retained; there is no second object or type authority to disagree with it. `ApplicationFact` is indexed by
the parent expression fact, so the application result vector and the expression result form cannot diverge.

## 10. One intrinsic result plan

```coq
Inductive PlanTarget (cp : Program) : Type :=
| NamedTarget : Index.BindingSiteRef (source cp) -> PlanTarget cp
| BlankTarget : Index.Key -> PlanTarget cp.

Record PlanEntry (cp : Program) : Type := MakePlanEntry {
  pe_target      : PlanTarget cp;
  pe_atom        : ResultAtom cp;
  pe_source      : DirectExprUseRef (source cp);
  pe_result_pos  : nat;
  pe_target_type : option (AcceptedType cp);
  pe_defaulted   : option (AcceptedType cp);
  pe_binder      : option (BinderDisposition cp) }.

Parameter PairwiseShape : forall (cp : Program), Index.PlanSiteRef (source cp) ->
  list (PlanEntry cp) -> Prop.
Parameter SingleMultiShape : forall (cp : Program), Index.PlanSiteRef (source cp) ->
  DirectExprUseRef (source cp) -> list (PlanEntry cp) -> Prop.

Inductive ResultPlan (cp : Program) (s : Index.PlanSiteRef (source cp)) : Type :=
| PairwisePlan    (entries : list (PlanEntry cp)) (h : PairwiseShape cp s entries)
| SingleMultiPlan (src : DirectExprUseRef (source cp)) (entries : list (PlanEntry cp))
                  (h : SingleMultiShape cp s src entries).

Parameter result_plan : forall cp s, ResultPlan cp s.
Definition plan_entries {cp} {s} (rp : ResultPlan cp s) : list (PlanEntry cp) :=
  match rp with PairwisePlan e _ => e | SingleMultiPlan _ e _ => e end.

Parameter SiteTargets : forall (cp : Program), Index.PlanSiteRef (source cp) ->
  list (PlanTarget cp) -> Prop.
Parameter SiteResults : forall (cp : Program), Index.PlanSiteRef (source cp) ->
  list (ResultAtom cp) -> Prop.
```

One ordered entry list, in source order, is the whole plan: a blank is a `BlankTarget` entry in its actual
position, never an appended list. Const, var and short declarations consume this same root; later assignment
and return contexts extend it.

## 11. Render

```coq
Inductive Prec : Type := PrimaryPrec | UnaryPrec.
Definition prec (e : Syntax.Expr) : Prec :=
  match e with Syntax.Unary _ _ => UnaryPrec | _ => PrimaryPrec end.
Parameter render_at : Prec -> Syntax.Expr -> string.
Parameter render_expr : Syntax.Expr -> string.
Parameter render_file : list Syntax.TopLevelDecl -> string.
Parameter NoAdjacentMinus AsciiOnly NoTrailingBlank Parenthesized : string -> Prop.
Parameter PrecLooser : Prec -> Prec -> Prop.
```

```text
render (Unary UnaryMinus e) = "-" ++ render_at PrimaryPrec e
render (Application h args) = render_at PrimaryPrec h ++ "(" ++ join(", ", map render args) ++ ")"
render_stmt (ExprStmt e, n) = indent(n) ++ render e ++ NL
```

Frozen outputs: `-1`; `-(-x)`; `-T(x)`; `f(x)`; `f(-x)`; `(-f)(x)`. There is no parser, tokenizer,
round-trip authority or public legacy renderer. File level keeps the existing bytes: the header line, a blank
line, the package clause, a blank line before each top-level declaration, and the exact final newline; within
a declaration one tab per block depth, comma-space separators, no trailing whitespace, direct source
spelling, an inherited const spec rendering names only, one spec ungrouped, and zero or two-or-more grouped
with the zero branches exactly `const ()`, `var ()`, `type ()`.

## 12. Application rules

- **conversion** — one argument, one result, through `convertibleb`/`representableb`, retaining
  constant-versus-nonconstant status and rerunning no resolution.
- **`complex`** — two arguments:

  | arguments | result |
  |---|---|
  | two untyped numeric constants valid for the real/imaginary rule | one untyped complex constant |
  | one untyped, one typed floating | the untyped operand converts to the **exact type** of the typed one |
  | two typed with `identicalb env s t = true`, underlying `float32` | `complex64` |
  | two typed with `identicalb env s t = true`, underlying `float64` | `complex128` |
  | two typed with `identicalb env s t = false` | rejected |

- **`println`** — a variadic list, each argument an untyped constant or a value whose underlying form is an
  admitted basic form, untyped constants defaulted first. Zero results, no C6 runtime effect.

`HeadCallable` is the one lasting refinement; C9's function-valued heads inhabit it and add no `AppTarget`
constructor. Every other predeclared callable resolves and raises an `ApplicationReq` boundary for the exact
missing profile; `main()` is the same case.

## 13. Diagnostics

```coq
Inductive DiagnosticReason (p : Syntax.Program) : Type :=
| InvalidConversion (primary : Index.ApplicationRef p) (head : Index.ExprRef p)
    (operand : Index.ExprRef p) (outer : list (Index.ApplicationRef p))
    (target : Typing.TypeView) (operand_status : Typing.ConstantInfo)
| DefaultNotRepresentable (primary : Index.ExprRef p) (exact_constant : Typing.Constant)
    (default_target : Typing.TypeView)
| MainRedeclared (later : Index.ObjectSiteRef p) (earlier : Index.ObjectSiteRef p)
| MissingMainEntry (pkg : Index.PackageRef p)
| BuildOutputIsDirectory (pkg : Index.PackageRef p) (output_name : string)
| DuplicateBinding (later : Index.BindingSiteRef p) (earlier : Index.BindingSiteRef p)
| InitMisuse (site : Index.BindingSiteRef p)
| UnresolvedName (u : Index.NameUseRef p)
| WrongRole (u : Index.NameUseRef p) (required : UseRole) (actual : ObjectKind)
| NotApplicable (a : Index.ApplicationRef p) (head : HeadView)
| TypeCycleDiag (eqs : Typing.ResolvedTypeEquations p) (c : Typing.TypeCycle eqs)
| DependencyCycleDiag (g : DependencyGraph p) (c : DependencyCycle g)
| FirstSpecInherited (s : Index.ConstSpecRef p)
| ResultMismatch (site : Index.PlanSiteRef p) (targets : nat) (observed : list ErasedResultVector)
| ShortDeclNoNew (s : Index.StatementRef p)
| ShortRedeclType (site : Index.BindingSiteRef p) (existing : Typing.TypeView) (found : Typing.TypeView)
| NilNoTarget (r : Index.ExprRef p)
| IotaNoContext (r : Index.ExprRef p)
| NotAssignable (u : ExprUseRef p) (target : AssignmentTargetAnchor p)
    (from : Typing.TypeView) (to : Typing.TypeView)
| UnusedLocal (site : Index.BindingSiteRef p)
| BadArgument (u : DirectExprUseRef p) (why : ArgumentReason)
| BadOperand (u : DirectExprUseRef p) (why : OperandReason)
| NotStatement (s : Index.ExpressionStatementRef p) (why : IneligibleReason).
```

| code | constructor | status |
|---|---|---|
| `CodeInvalidConversion` | `InvalidConversion` | restated: anchors an `Application`; `TypeNameRef` becomes the head `ExprRef`; `SemanticType` becomes `TypeView` |
| `CodeDefaultNotRepresentable` | `DefaultNotRepresentable` | restated: payload becomes `TypeView` |
| `CodeMainRedeclared` | `MainRedeclared` | restated: `Index.DeclRef` is deleted, so anchors become `ObjectSiteRef`; code and meaning unchanged |
| `CodeMissingMainEntry` | `MissingMainEntry` | unchanged |
| `CodeBuildOutputIsDirectory` | `BuildOutputIsDirectory` | unchanged |
| `CodeDuplicateBinding` … `CodeNotStatement` | the remaining eighteen | new |

`AssignmentTargetAnchor` is a sum over an explicit `TypeUseRef` and an inferred or short-declaration target
that has none. Cycle evidence is indexed by its own graph. A failed preflight precedes a package's semantic
errors; otherwise one canonical source order per package. Boundaries have their own erased view and `key_lt`
ordering and never enter `DiagnosticReason`.

## 14. Migration of accepted guarantees

| declaration | disposition |
|---|---|
| `Safe.Property`, `Safe.Program`, `compiled`, `certify`, `certify_retains`, `Safe.source`, `Safe.core`, `certify_source`, `certify_retains_capability`, `certify_retains_core` | retained unchanged |
| `Safe.Value`, `value_type`, `ValueWellFormed`, `value_well_formedb`, `typed_constant_to_value`, `resolved_constant_value` | moved to C7 `Runtime` |
| `value_well_formedb_iff`, `typed_constant_to_value_type`, `typed_constant_to_value_well_formed`, `typed_constant_to_value_float`, `typed_constant_to_value_complex`, `typed_constant_to_value_denotes`, `resolved_constant_value_float`, `resolved_constant_value_complex` | moved to C7 `Runtime` |
| `ValueDenotesConstant`, `value_denotes_constant_runtime`, `value_denotes_complex_runtime`, `float_nonconstant_no_denotes`, `complex_nonconstant_no_denotes` | moved to C7 `Runtime` |
| `Safe.eval_expr` and every evaluation lemma and corollary | moved to C7 `Machine`; `SPEC-X034` owns them |
| `Safe.eval_stmt`, `eval_decl`, `eval_file` | deleted; subsumed by the C7 run relation |
| `Typing.resolve_constant_info`, `convert_constant`, `ConstantRepresentable` | restated in §5, environment-indexed |
| `Render.const_info_denotes` | restated with the `Application` carrier; retained at C6 |
| `Render.const_info_denotes_functional` | retained unchanged |
| `Render.resolved_expr_denotes` | split: the constant/spelling half retained at C6; the value half moves to C7 |
| `Render.resolved_string_denotes`, `boundary_max`, `boundary_min` | moved to C7 with the value half |
| `Render` type-expression spelling and injectivity | restated over `Syntax.TypeExpr` |
| `Render` expression, argument, statement and declaration rendering | restated over the new source roots |
| `Render` ASCII and newline-safety; integer, string, float and complex decoding | retained unchanged; the complex decoder reads an `Application` |
| `Compilable.predeclared_type`, `predeclared_type_of_name` | deleted; subsumed by the phase binding relation |
| `Names.TypeName`, `SupportedType`, `classify`, `supported_of`, `all_type_names` | deleted; subsumed by `PredeclaredName` |
| `compile_complete` | restated: `Admissible p -> InScope p -> exists cp Hcp, compile p = Compiled cp Hcp` |
| `compile_rejected_of_inadmissible` | restated: `InScope p -> ~ Admissible p -> exists fail, …` |
| `elaboration_accepted_iff_admissible`, `elaboration_rejected_iff_inadmissible` | restated with the `InScope` premise |
| `compile_ok_valid`, `compile_rejected_not_admissible` | retained unchanged |
| `compile_program_typed`, `compile_ok_of_source_spec_valid_b` | restated over the phase judgment with the `InScope` premise |
| `program_of_admissible`, `capability_of_admissible`, `capability_source`, `capability_is_compile_outcome` | restated with the `InScope` premise |

Proof-only helpers become `Local` rather than migrating. No compatibility alias survives.

## 15. Theorems

Written in the post-`Arguments` spelling the implementation declares:

```coq
Arguments MakeNonEmpty {A} _ _.
Arguments Predeclared {p} _.  Arguments SourceObject {p} _.
Arguments PredeclaredRaw {p} _.  Arguments AliasRaw {p} _.  Arguments DefinedRaw {p} _.
Arguments DirectUse {p} _.  Arguments InheritedUse {p} _.
Arguments GraphAcyclic {p eqs} _.  Arguments GraphCyclic {p eqs} _.
Arguments BasicForm {p eqs ev env} _.
Arguments TypeMeaningReq {p i ph} _ _.  Arguments ValueMeaningReq {p i ph} _ _.
Arguments ApplicationReq {p i ph} _ _.  Arguments StatementReq {p i ph} _ _.
Arguments UnaryReq {p i ph} _ _.
Arguments AcceptedDecision {p core} _ _.
Arguments RejectedDecision {p core} _.  Arguments OutsideDecision {p core} _ _.
Arguments Compiled {p} _ _.  Arguments Rejected {p} _.  Arguments OutsideScope {p} _.
Arguments DispBlank {cp}.  Arguments DispDeclares {cp} _.  Arguments DispReuses {cp} _ _.
Arguments UntypedConstant {cp} _.  Arguments TypedConstantAtom {cp} _ _.  Arguments ValueResult {cp} _.
Arguments FixedResults {cp} _.  Arguments ContextualForm {cp} _.  Arguments NoStandaloneResult {cp}.
Arguments ConversionTarget {cp r f} _ _.  Arguments CallableTarget {cp r f} _.
Arguments NamedTarget {cp} _.  Arguments BlankTarget {cp} _.
Arguments PairwisePlan {cp s} _ _.  Arguments SingleMultiPlan {cp s} _ _ _.
Arguments UnusedLocal {p} _.
```

```coq
(* the pinned catalog *)
Theorem all_predeclared_nodup : NoDup all_predeclared.
Theorem all_predeclared_complete : forall n, In n all_predeclared.
Theorem predeclared_spelling_injective : forall a b,
  predeclared_spelling a = predeclared_spelling b -> a = b.
Theorem classify_spelling_roundtrip : forall n, classify_spelling (predeclared_spelling n) = Some n.
Theorem classify_spelling_sound : forall s n, classify_spelling s = Some n -> s = predeclared_spelling n.
Theorem predeclared_eqb_spec : forall a b, predeclared_eqb a b = true <-> a = b.

(* the outcome *)
Theorem decision_accepted_iff : forall p (a : Elaboration p),
  (exists Hd Hb, decision a = AcceptedDecision Hd Hb)
  <-> core_diagnostics (elaboration_core a) = nil /\ core_boundaries (elaboration_core a) = nil.
Theorem decision_rejected_iff : forall p (a : Elaboration p),
  (exists Hd, decision a = RejectedDecision Hd) <-> core_diagnostics (elaboration_core a) <> nil.
Theorem decision_outside_iff : forall p (a : Elaboration p),
  (exists Hd Hb, decision a = OutsideDecision Hd Hb)
  <-> core_diagnostics (elaboration_core a) = nil /\ core_boundaries (elaboration_core a) <> nil.
Theorem compiled_retains_core : forall p cp (Hcp : source cp = p),
  compile p = Compiled cp Hcp ->
  eq_rect (source cp) Core (core cp) p Hcp = elaboration_core (elaborate p).
Theorem rejected_retains_core : forall p (fail : Failure p),
  compile p = Rejected fail -> failure_core fail = elaboration_core (elaborate p).
Theorem outside_retains_core : forall p (out : Outside p),
  compile p = OutsideScope out -> outside_core out = elaboration_core (elaborate p).
Theorem in_scope_accepted_iff : forall p, InScope p ->
  (core_diagnostics (elaboration_core (elaborate p)) = nil <-> Admissible p).
Theorem in_scope_inadmissible_rejected : forall p, InScope p -> ~ Admissible p ->
  exists fail, compile p = Rejected fail.
Theorem in_scope_admissible_compiled : forall p, Admissible p -> InScope p ->
  exists cp Hcp, compile p = Compiled cp Hcp.
Theorem rejected_not_admissible : forall p (fail : Failure p),
  compile p = Rejected fail -> ~ Admissible p.

(* requirements and boundaries *)
Theorem requirement_dec_reflects : forall p (i : Input p) (ph : Phase i) (r : SemanticRequirement ph),
  (exists h, requirement_dec r = left h) <-> RequirementSatisfied r.
Theorem requirement_key_eqb_spec : forall a b, requirement_key_eqb a b = true <-> a = b.
Theorem requirement_key_compare_spec : forall a b, requirement_key_compare a b = Eq <-> a = b.
Theorem requirement_key_faithful : forall p (i : Input p) (ph : Phase i) (r1 r2 : SemanticRequirement ph),
  requirement_key r1 = requirement_key r2 -> erased_requirement r1 = erased_requirement r2.
Theorem key_lt_strict_order :
  (forall a, ~ key_lt a a) /\ (forall a b c, key_lt a b -> key_lt b c -> key_lt a c).
Theorem key_lt_total : forall a b, key_lt a b \/ a = b \/ key_lt b a.
Theorem boundary_key_sound : forall p (i : Input p) (ph : Phase i) (b : PackedBoundary ph),
  boundary_key b = requirement_key (boundary_requirement b).
Theorem root_boundary_complete : forall p (c : Core p) (r : SemanticRequirement (phase c)),
  RootRequirement (phase c) r -> ~ RequirementSatisfied r ->
  exists b, In b (core_boundaries c)
         /\ erased_requirement (boundary_requirement b) = erased_requirement r.
Theorem boundary_keys_nodup : forall p (c : Core p), NoDup (map boundary_key (core_boundaries c)).
Theorem boundary_order_canonical : forall p (c : Core p),
  Sorted key_lt (map boundary_key (core_boundaries c)).
Theorem listed_boundary_is_root : forall p (c : Core p) b,
  In b (core_boundaries c) -> RootRequirement (phase c) (boundary_requirement b).

(* scope and binding *)
Theorem predeclared_complete : forall p (i : Input p) (ph : Phase i) (n : Names.PredeclaredName),
  exists o : ObjectRef ph, object_origin o = Predeclared n.
Theorem predeclared_shadowed : forall cp (u : Index.NameUseRef (source cp)) s o,
  binder_disposition cp s = DispDeclares o -> InnermostDeclaring cp u s -> bound_object_at cp u = o.

(* the type graph and targets *)
Theorem resolve_graph_acyclic_iff : forall p (eqs : Typing.ResolvedTypeEquations p),
  (exists ev, resolve_graph eqs = GraphAcyclic ev) <-> AcyclicEquations eqs.
Theorem resolve_graph_cyclic_iff : forall p (eqs : Typing.ResolvedTypeEquations p),
  (exists c, resolve_graph eqs = GraphCyclic c) <-> ~ AcyclicEquations eqs.
Theorem graph_evidence_disjoint : forall p (eqs : Typing.ResolvedTypeEquations p),
  Typing.TypeGraphEvidence eqs -> Typing.TypeCycle eqs -> False.
Theorem denote_proof_independent : forall p eqs ev (env : Typing.Env eqs ev) t
    (r1 r2 : ResolvedTypeTarget env t), denote r1 = denote r2.
Theorem alias_no_identity : forall p eqs ev (env : Typing.Env eqs ev) a t
    (h : AliasResolvesTo env a t) (r : ResolvedTypeTarget env t),
  denote (ResolvedAlias env a t h r) = denote r.
Theorem defined_identity_exact : forall p eqs ev (env : Typing.Env eqs ev) d1 d2 h1 h2,
  identicalb env (denote (ResolvedDefined env d1 h1)) (denote (ResolvedDefined env d2 h2)) = true
  <-> d1 = d2.
Theorem underlying_reflect : forall p eqs ev (env : Typing.Env eqs ev) s f,
  underlying env s = f <-> Underlying env s f.
Theorem identical_reflect : forall p eqs ev (env : Typing.Env eqs ev) s t,
  identicalb env s t = true <-> Identical env s t.
Theorem assignable_reflect : forall p eqs ev (env : Typing.Env eqs ev) s t,
  assignableb env s t = true <-> Assignable env s t.
Theorem convertible_reflect : forall p eqs ev (env : Typing.Env eqs ev) s t,
  convertibleb env s t = true <-> Convertible env s t.
Theorem representable_reflect : forall p eqs ev (env : Typing.Env eqs ev) s c,
  representableb env s c = true <-> Representable env s c.
Theorem c6_forms_are_basic : forall cp (t : AcceptedType cp),
  exists b : Typing.BasicType, AcceptedUnderlying cp t (BasicForm b).

(* use provenance *)
Theorem direct_use_provenance : forall p (u : DirectExprUseRef p),
  Index.OccupiesRole (direct_parent u) (direct_child u) (direct_role u).
Theorem inherited_same_declaration : forall p (u : InheritedConstUseRef p),
  SpecInDecl (ic_decl u) (ic_current u) /\ SpecInDecl (ic_decl u) (ic_predecessor u).
Theorem inherited_nearest_preceding : forall p (u : InheritedConstUseRef p),
  NearestPrecedingExplicit (ic_decl u) (ic_current u) (ic_predecessor u).
Theorem inherited_same_position : forall p (u : InheritedConstUseRef p),
  NameAtPosition (ic_current u) (ic_name u) (ic_position u)
  /\ ExprAtPosition (ic_predecessor u) (ic_expr u) (ic_position u).
Theorem inherited_type_is_predecessors : forall p (u : InheritedConstUseRef p),
  SpecTypeUse (ic_predecessor u) (ic_type u).
Theorem inherited_iota_is_current : forall p (u : InheritedConstUseRef p),
  StructuralIota (ic_current u) (ic_iota u).
Theorem use_retains_expression : forall cp u (f : UseFact cp u),
  use_expression_fact f = expression_fact cp (expression_of_use u).

(* expression object/result coherence, one theorem per object kind *)
Theorem constant_name_one_constant : forall cp r (f : ExpressionFact cp r) o,
  referenced_object f = Some o -> object_kind_of o = ConstantObject ->
  (exists c, result_form f = FixedResults (UntypedConstant c :: nil))
  \/ (exists t k, result_form f = FixedResults (TypedConstantAtom t k :: nil))
  \/ result_form f = ContextualForm IotaResult.
Theorem variable_name_one_value : forall cp r (f : ExpressionFact cp r) o,
  referenced_object f = Some o -> object_kind_of o = VariableObject ->
  exists t, result_form f = FixedResults (ValueResult t :: nil).
Theorem type_name_no_result : forall cp r (f : ExpressionFact cp r) o,
  referenced_object f = Some o -> object_kind_of o = TypeObject -> result_form f = NoStandaloneResult.
Theorem builtin_name_no_result : forall cp r (f : ExpressionFact cp r) o,
  referenced_object f = Some o -> object_kind_of o = BuiltinObject -> result_form f = NoStandaloneResult.
Theorem nil_name_contextual : forall cp r (f : ExpressionFact cp r) o,
  referenced_object f = Some o -> object_kind_of o = NilObject ->
  result_form f = ContextualForm NilResult.
Theorem function_name_no_c6_result : forall cp r (f : ExpressionFact cp r) o,
  referenced_object f = Some o -> object_kind_of o = FunctionObject ->
  result_form f = NoStandaloneResult.

(* application *)
Theorem app_results_are_parent_results : forall cp a,
  result_form (expression_fact cp (Index.application_expr a))
  = FixedResults (app_results (application_fact cp a)).
Theorem app_results_from_target : forall cp a,
  app_results (application_fact cp a)
  = target_results (app_target (application_fact cp a)) (app_profile (application_fact cp a)).
Theorem complex_needs_identical_types : forall cp a s t,
  ComplexApplication cp a -> TypedOperandTypes cp a s t -> AcceptedIdentical cp s t.
Theorem statement_eligible_reflect : forall cp s,
  (exists h, statement_eligible_dec cp s = left h) <-> StatementEligible cp s.

(* the result plan *)
Theorem plan_covers_targets : forall cp s targets,
  SiteTargets cp s targets -> map pe_target (plan_entries (result_plan cp s)) = targets.
Theorem plan_consumes_results : forall cp s results,
  SiteResults cp s results -> map pe_atom (plan_entries (result_plan cp s)) = results.
Theorem plan_forms_disjoint : forall cp s e src e',
  PairwiseShape cp s e -> SingleMultiShape cp s src e' -> False.
Theorem plan_short_class_aligned : forall cp s (en : PlanEntry cp),
  ShortDeclSite cp s -> In en (plan_entries (result_plan cp s)) -> exists d, pe_binder en = Some d.

(* short declarations and static variables *)
Theorem short_decl_has_new_name : forall cp s,
  ShortDeclSite cp s ->
  exists b, In b (short_left_sites cp s) /\ exists o, binder_disposition cp b = DispDeclares o.
Theorem short_reuse_is_same_block : forall cp b o v,
  binder_disposition cp b = DispReuses o v -> SameBlockEarlier cp b o.
Theorem static_variable_at_site : forall cp s,
  static_variable_site (projT2 (static_variable_at cp s)) = s.

(* the dependency graph *)
Theorem dependency_order_acyclic : forall cp k,
  Acyclic (dependency_graph cp k) (dependency_order (dependency_fact cp k)).
Theorem dependency_edges_from_bindings : forall cp k, DependencyEdgesFromBindings (dependency_fact cp k).
Theorem dependency_cycle_reflect : forall p (g : DependencyGraph p),
  acyclicb g = true <-> Acyclic g (order_of g).

(* unused locals, guarded by full analysis *)
Theorem unused_local_iff : forall p (c : Core p) site,
  FullyAnalyzedLocal (phase c) site ->
  (In (UnusedLocal site) (core_diagnostics c) <-> ~ PhaseReadsVariableAt (phase c) site).
Theorem blocked_site_no_unused_local : forall p (c : Core p) site,
  ~ FullyAnalyzedLocal (phase c) site -> ~ In (UnusedLocal site) (core_diagnostics c).

(* rendering *)
Theorem unary_never_merges : forall e, NoAdjacentMinus (render_expr (Syntax.Unary Syntax.UnaryMinus e)).
Theorem parens_exactly_when_needed : forall r e, Parenthesized (render_at r e) <-> PrecLooser (prec e) r.
Theorem render_ascii : forall e, AsciiOnly (render_expr e).
Theorem render_no_trailing_blank : forall f, NoTrailingBlank (render_file f).
```

Prior-byte preservation is migration evidence, discharged by the existing goldens and the generated-artifact
byte-compare at the semantic-root review, not by a retained public legacy renderer.

## 16. Review boundaries

**Semantic-root review** stops only when the repository is green and contains: the corrected source and index
roots; the generalized exact phase as a predecessor-indexed chain; phase-indexed objects, facts and
requirements; the core-indexed three-way decision; requirement-indexed sealed boundaries with faithful keys;
the `GraphOutcome` sum, `build_env` and evidence-gated `denote`; accepted facts as definitions over the
retained environment; `HeadCallable`; object-indexed `StaticVariable`; the intrinsic `ResultPlan`; the old
fixed resolver and old expression phase deleted; `Safe.Value` and `Safe.eval_expr` deleted; no `Runtime`
module or machine; prior generated bytes unchanged.

**Final C6 review** then completes declaration and shadowing behaviour, diagnostics and boundaries, direct
rendering, C6 fixtures, `LAT-077`, generated-artifact evidence, and current document and ledger truth.

C7 is forbidden until Rob accepts C6.

## Done

Package and local `const`/`type`/`var` accepted; a local variable read by `println`; unused local rejected;
cross-file package declarations independent of file order; two packages sharing a spelling without collision;
duplicate package names rejected; local shadowing of package and predeclared names.

```text
type complex int; complex(x)     conversion, accepted
var complex int;  complex(x)     NotApplicable — definite invalidity
type println int; println(x)     conversion, and NotStatement in statement position
var println int;  println(x)     NotApplicable — definite invalidity
```

An unshadowed `len(s)`, a `var x uintptr` and a recursive `main()` each give `OutsideScope` with the exact
unmet requirement and no diagnostic; `type U uintptr; type T U; var x T` gives exactly one root boundary and
two blocked sites, and its `var x T` site raises **no** unused-local diagnostic. Two defined types with
identical underlying `float32` but distinct identity are rejected by `complex`; one such type used twice
yields `complex64`. Short declaration with no new nonblank name rejected; short redeclaration returning the
exact existing object; `_, y := f()` placing the blank entry in its own position; blank declarations creating
no object; `true`, `false`, `byte` and `rune` resolving through ordinary binding; alias preserving identity; a
local type spec naming itself rejected as a cycle; package constant and variable cycles rejected; a package
expression depending on a forward constant accepted; a first const spec with an inherited initializer
rejected; an inherited spec taking the predecessor expression under its own `iota`; unshadowed `nil` and
out-of-context `iota` rejected; a `println` argument of a defined type whose underlying form is `string`
accepted; unary minus on a constant and a variable accepted and on a string rejected; `-(-x)` rendering with
its parentheses; every currently accepted program rendering byte-identically after migration; generated C6
programs passing the pinned Go build with their exact expected observation.

## Preserve

`Syntax.Program` as the sole source authority and the AST as the one IR; `Program` as the opaque C4
capability, with `Failure` and `Outside` retaining the exact core; the retained input, work forest, member
index, outcome trace and sealed core; `Machine.T` uninstantiated; direct rendering and the one
`Emit.Mint.issue` authority; certified-module coverage, the whole-theory audit and controls A-E; every
sealed-capability, mint, transport and positive client control; working-tree and staged-index separation;
no-host-Python; `life.md`.

## Stop

A static identity cannot be indexed by the exact phase without reaching a core field; a requirement
constructor cannot be built from site objects alone; the boundary key cannot be made faithful and totally
ordered; a blocked site cannot be recorded without minting a root, or can still raise an unused-local
diagnostic; an accepted fact cannot be defined over the retained environment without a peer authority;
`ApplicationFact` cannot be indexed by the parent expression fact; the `InScope` premise cannot be discharged
where an accepted guarantee needs it; `Typing` cannot be closed without a `Compilable` type; `denote` cannot
be gated on resolution evidence; `AppTarget` would need a C9 constructor; `complex` cannot decide identity
without a second type authority; the intrinsic `ResultPlan` cannot carry blank consumption in position; a §15
theorem cannot be stated over the names defined here; rendering cannot be proved safe without a tokenizer;
`LAT-077` needs a diagnostic the phase cannot produce; a run relation, value, store, environment or machine is
needed for a C6 row; implementation needs a placeholder, compatibility path, trusted shortcut, fuel, bound or
premature future state.
