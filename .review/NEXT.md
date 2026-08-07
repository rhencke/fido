# C6 — the static semantic foundation

Review: contract

Goal: ordinary source names acquire meaning only through binding. C6 lands the pinned predeclared identity
catalog, a closed type algebra, exact constants, expression/use/application facts, one result-consumption
mapping, compiler-owned static variable identity, the package dependency outcome, and a three-way decision
that never calls unmodelled Go a rejection.

**C6 is entirely static.** No `Runtime`, value, place, store, environment or `Machine.T`; C7 introduces them
as one vertical. `ARCHITECTURE.md` owns the ownership law, `ROADMAP.md` the milestone sequence.

Every signature and theorem below elaborates under the pinned Rocq — `make contract-surface`.

## 1. Module order

```text
Decimal Integer Float Complex FilePath ModulePath Version Collections Names Syntax Index Typing
Compilable Machine Safe Render Emit
```

## 2. Names

```coq
Inductive PredeclaredName : Type :=
| PAny | PBool | PByte | PComparable | PComplex64 | PComplex128 | PError | PFloat32 | PFloat64
| PInt | PInt8 | PInt16 | PInt32 | PInt64 | PRune | PString | PUint | PUint8 | PUint16 | PUint32
| PUint64 | PUintptr | PTrue | PFalse | PIota | PNil | PAppend | PCap | PClear | PClose | PComplex
| PCopy | PDelete | PImag | PLen | PMake | PMax | PMin | PNew | PPanic | PPrint | PPrintln | PReal
| PRecover.

Definition predeclared_spelling (n : PredeclaredName) : string :=
  match n with
  | PAny => "any" | PBool => "bool" | PByte => "byte" | PComparable => "comparable"
  | PComplex64 => "complex64" | PComplex128 => "complex128" | PError => "error"
  | PFloat32 => "float32" | PFloat64 => "float64" | PInt => "int" | PInt8 => "int8"
  | PInt16 => "int16" | PInt32 => "int32" | PInt64 => "int64" | PRune => "rune"
  | PString => "string" | PUint => "uint" | PUint8 => "uint8" | PUint16 => "uint16"
  | PUint32 => "uint32" | PUint64 => "uint64" | PUintptr => "uintptr" | PTrue => "true"
  | PFalse => "false" | PIota => "iota" | PNil => "nil" | PAppend => "append" | PCap => "cap"
  | PClear => "clear" | PClose => "close" | PComplex => "complex" | PCopy => "copy"
  | PDelete => "delete" | PImag => "imag" | PLen => "len" | PMake => "make" | PMax => "max"
  | PMin => "min" | PNew => "new" | PPanic => "panic" | PPrint => "print" | PPrintln => "println"
  | PReal => "real" | PRecover => "recover"
  end%string.

Definition all_predeclared : list PredeclaredName :=
  [ PAny; PBool; PByte; PComparable; PComplex64; PComplex128; PError; PFloat32; PFloat64;
    PInt; PInt8; PInt16; PInt32; PInt64; PRune; PString; PUint; PUint8; PUint16; PUint32;
    PUint64; PUintptr; PTrue; PFalse; PIota; PNil; PAppend; PCap; PClear; PClose; PComplex;
    PCopy; PDelete; PImag; PLen; PMake; PMax; PMin; PNew; PPanic; PPrint; PPrintln; PReal;
    PRecover ].

Parameter classify_spelling : string -> option PredeclaredName.
Parameter predeclared_eqb : PredeclaredName -> PredeclaredName -> bool.

Record OrdinaryIdentifier : Type := MakeOrdinary {
  ordinary_identifier : Identifier;
  ordinary_not_blank  : spelling ordinary_identifier <> "_"%string }.
```

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

`Syntax.File`, `Syntax.Files`, `ModuleSpec` and `FilePath.T` are unchanged; `file_decls`, `program_module`
and `program_files` are their existing projections. C9 introduces the general function-declaration root and
deletes `Main` in the same milestone.

## 4. Index

Roles are structural and carry no program-dependent fact, so `Role` is **not** program-indexed.

```coq
Inductive Role : Type :=
| RFilePackage | RFileTopLevel | RMainBlock | RBlockStatement | RStatementDeclaration
| RDeclarationSpec | RBindingNameOccurrence | RConstSpecType | RConstInitializerExpression
| RVarSpecType | RVarInitializerExpression | RTypeSpecTarget | RTypeNameUse
| RShortRightExpression | RStatementExpression | RUnaryOperand
| RApplicationHead | RApplicationArgument.

Inductive UseRole : Type := TypeNameRole | ValueNameRole | HeadNameRole.

Parameter NodeRef : Syntax.Program -> Type.
Parameter node_key : forall {p}, NodeRef p -> Index.Key.
Parameter ExprRef ConstDeclRef ConstSpecRef BindingNameRef BlankRef : Syntax.Program -> Type.
Parameter TypeUseRef NameUseRef UnaryRef ApplicationRef : Syntax.Program -> Type.
Parameter ExpressionStatementRef BindingSiteRef VariableSiteRef : Syntax.Program -> Type.
Parameter ObjectSiteRef PlanSiteRef StatementRef : Syntax.Program -> Type.
Parameter AliasSpecRef BoundDefinedTypeRef : Syntax.Program -> Type.

Parameter expr_node : forall {p}, ExprRef p -> NodeRef p.
Parameter object_site_key : forall {p}, ObjectSiteRef p -> Index.Key.
Parameter binding_site_object_site : forall {p}, BindingSiteRef p -> ObjectSiteRef p.
Parameter variable_site_binding_site : forall {p}, VariableSiteRef p -> BindingSiteRef p.
Parameter application_expr : forall {p}, ApplicationRef p -> ExprRef p.
Parameter application_head : forall {p}, ApplicationRef p -> ExprRef p.
Parameter application_arguments : forall {p}, ApplicationRef p -> list (ExprRef p).
Parameter statement_expression : forall {p}, ExpressionStatementRef p -> ExprRef p.
Parameter unary_operand : forall {p}, UnaryRef p -> ExprRef p.
Parameter OccupiesRole : forall {p}, NodeRef p -> ExprRef p -> Role -> Prop.

Parameter DirectExprUseRef : Syntax.Program -> Type.
Parameter direct_parent : forall {p}, DirectExprUseRef p -> NodeRef p.
Parameter direct_child  : forall {p}, DirectExprUseRef p -> ExprRef p.
Parameter direct_role   : forall {p}, DirectExprUseRef p -> Role.
Parameter direct_occupies : forall {p} (u : DirectExprUseRef p),
  OccupiesRole (direct_parent u) (direct_child u) (direct_role u).
Parameter application_head_use : forall {p}, ApplicationRef p -> DirectExprUseRef p.
Parameter application_argument_uses : forall {p}, ApplicationRef p -> list (DirectExprUseRef p).

Parameter InheritedConstUseRef : Syntax.Program -> Type.
Parameter ic_decl        : forall {p}, InheritedConstUseRef p -> ConstDeclRef p.
Parameter ic_current     : forall {p}, InheritedConstUseRef p -> ConstSpecRef p.
Parameter ic_name        : forall {p}, InheritedConstUseRef p -> BindingNameRef p.
Parameter ic_predecessor : forall {p}, InheritedConstUseRef p -> ConstSpecRef p.
Parameter ic_expr        : forall {p}, InheritedConstUseRef p -> ExprRef p.
Parameter ic_type        : forall {p}, InheritedConstUseRef p -> option (TypeUseRef p).
Parameter ic_iota        : forall {p}, InheritedConstUseRef p -> nat.
Parameter ic_position    : forall {p}, InheritedConstUseRef p -> nat.
Parameter SpecInDecl : forall {p}, ConstDeclRef p -> ConstSpecRef p -> Prop.
Parameter NearestPrecedingExplicit :
  forall {p}, ConstDeclRef p -> ConstSpecRef p -> ConstSpecRef p -> Prop.
Parameter NameAtPosition : forall {p}, ConstSpecRef p -> BindingNameRef p -> nat -> Prop.
Parameter ExprAtPosition : forall {p}, ConstSpecRef p -> ExprRef p -> nat -> Prop.
Parameter SpecTypeUse : forall {p}, ConstSpecRef p -> option (TypeUseRef p) -> Prop.
Parameter StructuralIota : forall {p}, ConstSpecRef p -> nat -> Prop.

Inductive ExprUseRef (p : Syntax.Program) : Type :=
| DirectUse    : DirectExprUseRef p -> ExprUseRef p
| InheritedUse : InheritedConstUseRef p -> ExprUseRef p.

Definition expression_of_use {p} (u : ExprUseRef p) : ExprRef p :=
  match u with DirectUse _ d => direct_child d | InheritedUse _ i => ic_expr i end.
```

Every refinement is minted only from its exact validated source occurrence and, where it has a parent, its
exact role; `direct_occupies` is the proof no foreign occurrence inhabits a `DirectExprUseRef`. A parent plus
an unchecked natural is never a public child reference. **Package identity is a compiler grouping over
parent-directory identity, not one source occurrence, so it lives in `Compilable` (§8) and `Index.PackageRef`
does not exist.**

## 5. Typing — a closed algebra

```coq
Inductive BasicType : Type :=
| BoolBasic | IntegerBasic (k : Integer.Kind) | FloatBasic (k : Float.Kind)
| ComplexBasic (k : Complex.Kind) | StringBasic.

Inductive NumericBasic : BasicType -> Prop :=
| NumInteger : forall k, NumericBasic (IntegerBasic k)
| NumFloat   : forall k, NumericBasic (FloatBasic k)
| NumComplex : forall k, NumericBasic (ComplexBasic k).

Inductive TypeView : Type := BasicView : BasicType -> TypeView | DefinedView : Index.Key -> TypeView.

Inductive RawTypeTarget (p : Syntax.Program) : Type :=
| PredeclaredRaw : BasicType -> RawTypeTarget p
| AliasRaw       : AliasSpecRef p -> RawTypeTarget p
| DefinedRaw     : BoundDefinedTypeRef p -> RawTypeTarget p.

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
Parameter DefinedInEnv : forall {p} {eqs} {ev}, Env eqs ev -> BoundDefinedTypeRef p -> Prop.
Parameter defined_key : forall {p}, BoundDefinedTypeRef p -> Index.Key.

Inductive TypeForm {p} {eqs} {ev} (env : Env eqs ev) : Type := BasicForm : BasicType -> TypeForm env.

Inductive SemanticType {p} {eqs} {ev} (env : Env eqs ev) : Type :=
| FormType    : TypeForm env -> SemanticType env
| DefinedType : forall d : BoundDefinedTypeRef p, DefinedInEnv env d -> SemanticType env.

Parameter defined_underlying : forall {p} {eqs} {ev} (env : Env eqs ev)
  (d : BoundDefinedTypeRef p), DefinedInEnv env d -> TypeForm env.
Parameter AliasResolvesTo : forall {p} {eqs} {ev},
  Env eqs ev -> AliasSpecRef p -> RawTypeTarget p -> Prop.

Inductive ResolvedTypeTarget {p} {eqs} {ev} (env : Env eqs ev) : RawTypeTarget p -> Type :=
| ResolvedPredeclared : forall b, ResolvedTypeTarget env (PredeclaredRaw p b)
| ResolvedAlias : forall (a : AliasSpecRef p) (t : RawTypeTarget p),
    AliasResolvesTo env a t -> ResolvedTypeTarget env t -> ResolvedTypeTarget env (AliasRaw p a)
| ResolvedDefined : forall d, DefinedInEnv env d -> ResolvedTypeTarget env (DefinedRaw p d).

Fixpoint denote {p} {eqs} {ev} {env : Env eqs ev} {t} (r : ResolvedTypeTarget env t)
  : SemanticType env :=
  match r with
  | ResolvedPredeclared _ b  => FormType env (BasicForm env b)
  | ResolvedAlias _ _ _ _ r' => denote r'
  | ResolvedDefined _ d h    => DefinedType env d h
  end.

Definition type_view {p} {eqs} {ev} {env : Env eqs ev} (s : SemanticType env) : TypeView :=
  match s with
  | FormType _ (BasicForm _ b) => BasicView b
  | DefinedType _ d _          => DefinedView (defined_key d)
  end.

Inductive Underlying {p} {eqs} {ev} (env : Env eqs ev) : SemanticType env -> TypeForm env -> Prop :=
| UnderlyingForm    : forall f, Underlying env (FormType env f) f
| UnderlyingDefined : forall d h, Underlying env (DefinedType env d h) (defined_underlying env d h).

Inductive Identical {p} {eqs} {ev} (env : Env eqs ev) : SemanticType env -> SemanticType env -> Prop :=
| IdenticalBasic   : forall b,
    Identical env (FormType env (BasicForm env b)) (FormType env (BasicForm env b))
| IdenticalDefined : forall d h1 h2, Identical env (DefinedType env d h1) (DefinedType env d h2).

Inductive Assignable {p} {eqs} {ev} (env : Env eqs ev) : SemanticType env -> SemanticType env -> Prop :=
| AssignIdentical     : forall s t, Identical env s t -> Assignable env s t
| AssignFormToDefined : forall d h,
    Assignable env (FormType env (defined_underlying env d h)) (DefinedType env d h)
| AssignDefinedToForm : forall d h,
    Assignable env (DefinedType env d h) (FormType env (defined_underlying env d h)).

Inductive Convertible {p} {eqs} {ev} (env : Env eqs ev) : SemanticType env -> SemanticType env -> Prop :=
| ConvertAssignable : forall s t, Assignable env s t -> Convertible env s t
| ConvertNumeric    : forall s t bs bt,
    Underlying env s (BasicForm env bs) -> Underlying env t (BasicForm env bt) ->
    NumericBasic bs -> NumericBasic bt -> Convertible env s t.

Inductive Representable {p} {eqs} {ev} (env : Env eqs ev) : SemanticType env -> Constant -> Prop :=
| RepresentableUnder : forall s b c,
    Underlying env s (BasicForm env b) -> Typing.ConstantRepresentableIn b c -> Representable env s c.

Parameter underlyingb : forall {p} {eqs} {ev} (env : Env eqs ev), SemanticType env -> TypeForm env.
Parameter identicalb     : forall {p} {eqs} {ev} (env : Env eqs ev), SemanticType env -> SemanticType env -> bool.
Parameter assignableb    : forall {p} {eqs} {ev} (env : Env eqs ev), SemanticType env -> SemanticType env -> bool.
Parameter convertibleb   : forall {p} {eqs} {ev} (env : Env eqs ev), SemanticType env -> SemanticType env -> bool.
Parameter representableb : forall {p} {eqs} {ev} (env : Env eqs ev), SemanticType env -> Constant -> bool.
Parameter TypedConstant  : forall {p} {eqs} {ev} (env : Env eqs ev), SemanticType env -> Type.
Parameter typed_constant_of : forall {p} {eqs} {ev} (env : Env eqs ev) (s : SemanticType env)
  (c : Constant), Representable env s c -> TypedConstant env s.
Parameter typed_constant_exact : forall {p} {eqs} {ev} {env : Env eqs ev} {s},
  TypedConstant env s -> Constant.
Parameter default_type : forall {p} {eqs} {ev} (env : Env eqs ev), Constant -> SemanticType env.
```

`SemanticType` is closed: a C6 type is a basic form or a defined type carrying its own `DefinedInEnv`
evidence, so a cyclic, rejected or blocked declaration has no inhabitant. An alias has no constructor —
`denote` returns its resolved target. `ConstantRepresentableIn` is the existing integer/float/complex/string
authority.

## 6. The retained phase

```coq
Inductive TypePhaseResult {p} (eqs : Typing.ResolvedTypeEquations p) : Type :=
| TypeReady  : forall g : Typing.TypeGraphEvidence eqs, Typing.Env eqs g -> TypePhaseResult eqs
| TypeCyclic : Typing.TypeCycle eqs -> TypePhaseResult eqs.

Parameter Phase : forall {p}, Input p -> Type.
Parameter phase : forall {p} (core : Core p), Phase (core_input core).
Parameter phase_equations : forall {p} {i} (ph : Phase i), Typing.ResolvedTypeEquations p.
Parameter phase_type_result : forall {p} {i} (ph : Phase i), TypePhaseResult (phase_equations ph).

Inductive ObjectKind : Type :=
| TypeObject | ConstantObject | VariableObject | FunctionObject | BuiltinObject | NilObject.

Inductive ObjectOrigin (p : Syntax.Program) : Type :=
| Predeclared  : Names.PredeclaredName -> ObjectOrigin p
| SourceObject : Index.ObjectSiteRef p -> ObjectOrigin p.

Parameter ObjectRef : forall {p} {i : Input p}, Phase i -> Type.
Parameter object_origin : forall {p} {i} {ph : Phase i}, ObjectRef ph -> ObjectOrigin p.
Parameter object_kind   : forall {p} {i} {ph : Phase i}, ObjectRef ph -> ObjectKind.
Parameter object_key    : forall {p} {i} {ph : Phase i}, ObjectRef ph -> Index.Key.
Parameter object_eqb    : forall {p} {i} {ph : Phase i}, ObjectRef ph -> ObjectRef ph -> bool.
Parameter predeclared_object : forall {p} {i} (ph : Phase i), Names.PredeclaredName -> ObjectRef ph.
Parameter source_object : forall {p} {i} (ph : Phase i), Index.ObjectSiteRef p -> ObjectRef ph.

Definition predeclared_kind (n : Names.PredeclaredName) : ObjectKind :=
  match n with
  | PAny | PBool | PByte | PComparable | PComplex64 | PComplex128 | PError | PFloat32 | PFloat64
  | PInt | PInt8 | PInt16 | PInt32 | PInt64 | PRune | PString | PUint | PUint8 | PUint16
  | PUint32 | PUint64 | PUintptr => TypeObject
  | PTrue | PFalse | PIota => ConstantObject
  | PNil => NilObject
  | _ => BuiltinObject
  end.
```

A cyclic phase has no acyclic evidence and no environment — that is what `TypePhaseResult` forbids. The
environment in `TypeReady` is the exact object built during the phase and is never rebuilt.

The private causal chain, frozen in dependency order — each object indexed by or structurally retaining its
exact predecessor:

```text
Input → scope/object phase → binding and structural-use phase → type-equation phase
      → TypePhaseResult → package dependency outcome
      → declaration elaboration in dependency then source order
      → expression, use, application and result-consumption facts → static-variable facts
      → unused-local result → canonical diagnostics and canonical root boundaries → Phase
```

Internal partial site outcomes stay private with this exact topology: `Supported` exact fact,
`DefiniteFailure` exact root diagnostic, `Outside` exact root requirement, `Blocked` exact dependency edge
plus exact predecessor outcome. A blocked site mints no fact, diagnostic or duplicate boundary.

| declaration | scope begins |
|---|---|
| package `const`, `var`, `type`, `main` | the package block |
| local `const` spec | after the `ConstSpec` |
| local `var` spec | after the `VarSpec` |
| short-variable new binding | after the `ShortVarDecl` |
| **local `type` spec** | **at the identifier in the `TypeSpec`** |
| predeclared object | the outer universe block |
| blank | never |

## 7. Requirements and the one erased view

```coq
Inductive ContextualResult : Type := IotaResult | NilResult.
Inductive UntypedConstantKind : Type := UCBool | UCInteger | UCRune | UCFloat | UCComplex | UCString.

Inductive ErasedForm : Type :=
| EFUntypedConstant : UntypedConstantKind -> ErasedForm
| EFTypedConstant   : Typing.TypeView -> ErasedForm
| EFValue           : Typing.TypeView -> ErasedForm
| EFContextual      : ContextualResult -> ErasedForm
| EFNone            : ErasedForm.
Definition ErasedProfile : Type := list ErasedForm.

Inductive ErasedObjectOrigin : Type :=
| EPredeclared : Names.PredeclaredName -> ErasedObjectOrigin
| ESourceObject : Index.Key -> ErasedObjectOrigin.

Inductive ErasedTarget : Type :=
| ETConversion : Typing.TypeView -> ErasedTarget
| ETCallable : ErasedObjectOrigin -> ErasedTarget
| ETNotApplicable : ObjectKind -> ErasedTarget.

Inductive RequirementView : Type :=
| RVTypeMeaning  : Index.Key -> ErasedObjectOrigin -> RequirementView
| RVValueMeaning : Index.Key -> ErasedObjectOrigin -> RequirementView
| RVApplication  : Index.Key -> ErasedTarget -> ErasedProfile -> RequirementView
| RVStatement    : Index.Key -> ErasedForm -> RequirementView
| RVUnary        : Index.Key -> Syntax.UnaryOp -> ErasedForm -> RequirementView.

Parameter requirement_view_eqb : RequirementView -> RequirementView -> bool.
Parameter requirement_view_compare : RequirementView -> RequirementView -> comparison.
Definition view_lt (a b : RequirementView) : Prop := requirement_view_compare a b = Lt.

Parameter PhaseBindingFact : forall {p} {i} (ph : Phase i), Index.NameUseRef p -> Type.
Parameter PhaseApplicationSite : forall {p} {i} (ph : Phase i), Index.ApplicationRef p -> Type.
Parameter PhaseStatementSite : forall {p} {i} (ph : Phase i), Index.ExpressionStatementRef p -> Type.
Parameter PhaseUnarySite : forall {p} {i} (ph : Phase i), Index.UnaryRef p -> Type.

Inductive SemanticRequirement {p} {i : Input p} (ph : Phase i) : Type :=
| TypeMeaningReq  : forall u, PhaseBindingFact ph u -> SemanticRequirement ph
| ValueMeaningReq : forall u, PhaseBindingFact ph u -> SemanticRequirement ph
| ApplicationReq  : forall a, PhaseApplicationSite ph a -> SemanticRequirement ph
| StatementReq    : forall s, PhaseStatementSite ph s -> SemanticRequirement ph
| UnaryReq        : forall n, PhaseUnarySite ph n -> SemanticRequirement ph.

Parameter requirement_view : forall {p} {i} {ph : Phase i}, SemanticRequirement ph -> RequirementView.
Parameter RequirementSatisfied : forall {p} {i} {ph : Phase i}, SemanticRequirement ph -> Prop.
Parameter requirement_dec : forall {p} {i} {ph : Phase i} (r : SemanticRequirement ph),
  { RequirementSatisfied r } + { ~ RequirementSatisfied r }.
Parameter RootRequirement : forall {p} {i} (ph : Phase i), SemanticRequirement ph -> Prop.
Parameter ScopeBoundary : forall {p} {i} (ph : Phase i), SemanticRequirement ph -> Type.
Parameter boundary_missing : forall {p} {i} {ph : Phase i} {r},
  ScopeBoundary ph r -> ~ RequirementSatisfied r.
Parameter PackedBoundary : forall {p} {i : Input p}, Phase i -> Type.
Parameter boundary_requirement : forall {p} {i} {ph : Phase i},
  PackedBoundary ph -> SemanticRequirement ph.
Parameter boundary_evidence : forall {p} {i} {ph : Phase i} (b : PackedBoundary ph),
  ScopeBoundary ph (boundary_requirement b).
Definition boundary_view {p} {i} {ph : Phase i} (b : PackedBoundary ph) : RequirementView :=
  requirement_view (boundary_requirement b).
```

`RequirementView` is the **one** proof-free authority: erased requirement, public boundary view, and
canonical sort/dedup key. Only the negative branch of `requirement_dec` mints a boundary, whose constructor is
private. No certified value contains a roadmap or ledger identifier.

## 8. Package identity and the dependency outcome

```coq
Parameter PackageRef : Syntax.Program -> Type.
Parameter DependencyGraph : forall {p} {i : Input p}, Phase i -> PackageRef p -> Type.
Parameter DependencyCycle : forall {p} {i} {ph : Phase i} {k}, DependencyGraph ph k -> Type.
Parameter AcyclicOrder : forall {p} {i} {ph : Phase i} {k} (g : DependencyGraph ph k),
  list (Index.BindingSiteRef p) -> Prop.

Inductive DependencyOutcome {p} {i} {ph : Phase i} {k} (g : DependencyGraph ph k) : Type :=
| DependencyAcyclic : forall order, AcyclicOrder g order -> DependencyOutcome g
| DependencyCyclic  : DependencyCycle g -> DependencyOutcome g.

Parameter phase_dependency_graph : forall {p} {i} (ph : Phase i) (k : PackageRef p),
  DependencyGraph ph k.
Parameter phase_dependency_outcome : forall {p} {i} (ph : Phase i) (k : PackageRef p),
  DependencyOutcome (phase_dependency_graph ph k).
Parameter EdgesFromBindings : forall {p} {i} {ph : Phase i} {k}, DependencyGraph ph k -> Prop.
```

Edges are built once from exact binding and use facts. C11 consumes and extends this same object and builds
no peer graph.

## 9. Outcome

```coq
Parameter core_diagnostics : forall {p} (core : Core p), list (DiagnosticReason (phase core)).
Parameter core_boundaries : forall {p} (core : Core p), list (PackedBoundary (phase core)).

Inductive Decision {p} (core : Core p) : Type :=
| AcceptedDecision : core_diagnostics core = nil -> core_boundaries core = nil -> Decision core
| RejectedDecision : core_diagnostics core <> nil -> Decision core
| OutsideDecision  : core_diagnostics core = nil -> core_boundaries core <> nil -> Decision core.

Parameter decision : forall {p} (a : Elaboration p), Decision (elaboration_core a).

Parameter Program : Type.
Parameter source : Program -> Syntax.Program.
Parameter core : forall cp : Program, Core (source cp).
Parameter accepted : forall cp, core_diagnostics (core cp) = nil.
Parameter in_scope : forall cp, core_boundaries (core cp) = nil.

Parameter Failure : Syntax.Program -> Type.
Parameter failure_core : forall {p}, Failure p -> Core p.
Parameter rejected : forall {p} (f : Failure p), core_diagnostics (failure_core f) <> nil.
Parameter Outside : Syntax.Program -> Type.
Parameter outside_core : forall {p}, Outside p -> Core p.
Parameter outside_clean : forall {p} (o : Outside p), core_diagnostics (outside_core o) = nil.
Parameter outside_blocked : forall {p} (o : Outside p), core_boundaries (outside_core o) <> nil.

Inductive Outcome (p : Syntax.Program) : Type :=
| Compiled     : forall cp : Program, source cp = p -> Outcome p
| Rejected     : Failure p -> Outcome p
| OutsideScope : Outside p -> Outcome p.

Parameter compile : forall p : Syntax.Program, Outcome p.
Definition InScope (p : Syntax.Program) : Prop :=
  core_boundaries (elaboration_core (elaborate p)) = nil.
```

## 10. Accepted facts — definitions over the exact phase

```coq
Definition accepted_phase (cp : Program) : Phase (core_input (core cp)) := phase (core cp).
Definition accepted_equations (cp : Program) : Typing.ResolvedTypeEquations (source cp) :=
  phase_equations (accepted_phase cp).

Parameter accepted_type_ready : forall cp : Program,
  { g : Typing.TypeGraphEvidence (accepted_equations cp) & Typing.Env (accepted_equations cp) g }.
Definition accepted_environment (cp : Program) := projT2 (accepted_type_ready cp).

Definition Object (cp : Program) : Type := ObjectRef (accepted_phase cp).
Definition AcceptedType (cp : Program) : Type := Typing.SemanticType (accepted_environment cp).
Definition AcceptedTypedConstant (cp : Program) (t : AcceptedType cp) : Type :=
  Typing.TypedConstant (accepted_environment cp) t.
Definition AcceptedIdentical (cp : Program) (s t : AcceptedType cp) : Prop :=
  Typing.Identical (accepted_environment cp) s t.
Definition AcceptedAssignable (cp : Program) (s t : AcceptedType cp) : Prop :=
  Typing.Assignable (accepted_environment cp) s t.
Definition AcceptedUnderlying (cp : Program) (t : AcceptedType cp) f : Prop :=
  Typing.Underlying (accepted_environment cp) t f.
Definition accepted_type_view (cp : Program) (t : AcceptedType cp) : Typing.TypeView := type_view t.
Definition object_kind_of {cp} (o : Object cp) : ObjectKind := object_kind o.
Definition object_origin_of {cp} (o : Object cp) : ObjectOrigin (source cp) := object_origin o.
Definition object_key_of {cp} (o : Object cp) : Index.Key := object_key o.

Inductive ResultAtom (cp : Program) : Type :=
| UntypedConstant   : UntypedConstantKind -> Typing.Constant -> ResultAtom cp
| TypedConstantAtom : forall t : AcceptedType cp, AcceptedTypedConstant cp t -> ResultAtom cp
| ValueResult       : AcceptedType cp -> ResultAtom cp.

Inductive ResultForm (cp : Program) : Type :=
| FixedResults       : list (ResultAtom cp) -> ResultForm cp
| ContextualForm     : ContextualResult -> ResultForm cp
| NoStandaloneResult : ResultForm cp.

Parameter PhaseObjectFact : forall {p} {i} (ph : Phase i), ObjectRef ph -> Type.
Parameter PhaseExpressionFact : forall {p} {i} (ph : Phase i), Index.ExprRef p -> Type.
Parameter PhaseUseFact : forall {p} {i} (ph : Phase i), Index.ExprUseRef p -> Type.
Parameter PhaseStaticVariable : forall {p} {i} (ph : Phase i), ObjectRef ph -> Type.
Parameter PhaseResultPlan : forall {p} {i} (ph : Phase i), Index.PlanSiteRef p -> Type.
Parameter phase_binding_fact : forall {p} {i} (ph : Phase i) u, PhaseBindingFact ph u.
Parameter phase_object_fact : forall {p} {i} (ph : Phase i) o, PhaseObjectFact ph o.
Parameter phase_expression_fact : forall {p} {i} (ph : Phase i) r, PhaseExpressionFact ph r.
Parameter phase_use_fact : forall {p} {i} (ph : Phase i) u, PhaseUseFact ph u.
Parameter phase_result_plan : forall {p} {i} (ph : Phase i) s, PhaseResultPlan ph s.

Definition BindingFact cp u := PhaseBindingFact (accepted_phase cp) u.
Definition binding_fact cp u : BindingFact cp u := phase_binding_fact (accepted_phase cp) u.
Definition ObjectFact cp o := PhaseObjectFact (accepted_phase cp) o.
Definition object_fact cp o : ObjectFact cp o := phase_object_fact (accepted_phase cp) o.
Definition ExpressionFact cp r := PhaseExpressionFact (accepted_phase cp) r.
Definition expression_fact cp r : ExpressionFact cp r := phase_expression_fact (accepted_phase cp) r.
Definition UseFact cp u := PhaseUseFact (accepted_phase cp) u.
Definition use_fact cp u : UseFact cp u := phase_use_fact (accepted_phase cp) u.
Definition StaticVariable cp o := PhaseStaticVariable (accepted_phase cp) o.
Definition ResultPlan cp s := PhaseResultPlan (accepted_phase cp) s.
Definition result_plan cp s : ResultPlan cp s := phase_result_plan (accepted_phase cp) s.

Parameter bound_object : forall {cp} {u}, BindingFact cp u -> Object cp.
Parameter binding_use_role : forall {cp} {u}, BindingFact cp u -> UseRole.
Parameter binding_package : forall {cp} {u}, BindingFact cp u -> PackageRef (source cp).
Definition bound_object_at cp u : Object cp := bound_object (binding_fact cp u).
Definition use_role_at cp u : UseRole := binding_use_role (binding_fact cp u).

Inductive ObjectMeaning (cp : Program) : Type :=
| MeansType     : AcceptedType cp -> ObjectMeaning cp
| MeansConstant : forall t : AcceptedType cp, AcceptedTypedConstant cp t -> ObjectMeaning cp
| MeansUntyped  : UntypedConstantKind -> Typing.Constant -> ObjectMeaning cp
| MeansVariable : forall o : Object cp, StaticVariable cp o -> ObjectMeaning cp
| MeansCallable : Names.PredeclaredName -> ObjectMeaning cp
| MeansIota     : ObjectMeaning cp
| MeansNil      : ObjectMeaning cp
| MeansOutside  : ObjectMeaning cp.
Parameter object_meaning : forall {cp} {o}, ObjectFact cp o -> ObjectMeaning cp.

Parameter static_variable_at : forall (cp : Program) (s : Index.VariableSiteRef (source cp)),
  { o : Object cp & StaticVariable cp o }.
Parameter static_variable_type : forall {cp} {o}, StaticVariable cp o -> AcceptedType cp.

Inductive BinderDisposition (cp : Program) : Type :=
| DispBlank    : BinderDisposition cp
| DispDeclares : Object cp -> BinderDisposition cp
| DispReuses   : forall o : Object cp, StaticVariable cp o -> BinderDisposition cp.
Parameter binder_disposition : forall cp s, BinderDisposition cp.

Parameter referenced_object : forall {cp} {r}, ExpressionFact cp r -> option (Object cp).
Parameter result_form : forall {cp} {r}, ExpressionFact cp r -> ResultForm cp.
Parameter use_expression_fact : forall {cp} {u} (f : UseFact cp u),
  ExpressionFact cp (expression_of_use u).
Parameter use_target_type : forall {cp} {u}, UseFact cp u -> option (AcceptedType cp).
Parameter use_selected : forall {cp} {u}, UseFact cp u -> list (ResultAtom cp).
Parameter ResultAt : forall {cp} {u}, UseFact cp u -> nat -> ResultAtom cp -> Prop.
```

`iota` is one exact object; an ordinary declared constant cannot acquire its contextual meaning, which is why
`ObjectMeaning` separates `MeansConstant`, `MeansUntyped` and `MeansIota`.

## 11. Application

```coq
Parameter HeadDenotesType : forall {cp} {r}, ExpressionFact cp r -> AcceptedType cp -> Prop.
Parameter HeadCallable : forall {cp} {r}, ExpressionFact cp r -> Type.
Inductive AppTarget {cp} {r} (f : ExpressionFact cp r) : Type :=
| ConversionTarget : forall t : AcceptedType cp, HeadDenotesType f t -> AppTarget f
| CallableTarget   : HeadCallable f -> AppTarget f.

Definition erase_result_form {cp} (rf : ResultForm cp) : ErasedForm :=
  match rf with
  | FixedResults _ (UntypedConstant _ k _ :: nil)   => EFUntypedConstant k
  | FixedResults _ (TypedConstantAtom _ t _ :: nil) => EFTypedConstant (accepted_type_view cp t)
  | FixedResults _ (ValueResult _ t :: nil)         => EFValue (accepted_type_view cp t)
  | FixedResults _ _                                => EFNone
  | ContextualForm _ c                              => EFContextual c
  | NoStandaloneResult _                            => EFNone
  end.
Definition ArgumentProfile (cp : Program) : Type := list ErasedForm.

Parameter ApplicationFact : forall (cp : Program) (a : Index.ApplicationRef (source cp)),
  ExpressionFact cp (Index.application_expr a) -> Type.
Parameter application_fact : forall cp a,
  ApplicationFact cp a (expression_fact cp (Index.application_expr a)).
Parameter app_head_fact : forall {cp} {a} {pf}, ApplicationFact cp a pf ->
  ExpressionFact cp (Index.application_head a).
Parameter app_target : forall {cp} {a} {pf} (af : ApplicationFact cp a pf), AppTarget (app_head_fact af).
Parameter app_arg_uses : forall {cp} {a} {pf}, ApplicationFact cp a pf ->
  list (Index.DirectExprUseRef (source cp)).
Parameter app_arg_facts : forall {cp} {a} {pf}, ApplicationFact cp a pf ->
  list (Index.ExprUseRef (source cp)).
Parameter app_profile : forall {cp} {a} {pf}, ApplicationFact cp a pf -> ArgumentProfile cp.
Parameter app_results : forall {cp} {a} {pf}, ApplicationFact cp a pf -> list (ResultAtom cp).

Inductive AppRule (cp : Program) : Type :=
| RuleConversion : AppRule cp | RuleComplex : AppRule cp | RulePrintln : AppRule cp.
Parameter AppAccepts : forall {cp} {a} {pf}, ApplicationFact cp a pf -> AppRule cp ->
  list (ResultAtom cp) -> Prop.

Parameter StatementEligible : forall cp, Index.ExpressionStatementRef (source cp) -> Prop.
Parameter statement_eligible_dec : forall cp s,
  { StatementEligible cp s } + { ~ StatementEligible cp s }.
```

`AppAccepts` is the one closed application relation; there is no free `target_results` function beside it. Its
C6 rules:

| rule | arguments | result |
|---|---|---|
| `RuleConversion` | one, `Convertible` and `Representable` through §5 | one, constant status retained |
| `RuleComplex` | two untyped numeric constants | one untyped complex constant |
| `RuleComplex` | one untyped, one typed floating | untyped converts to the typed operand's **exact type** |
| `RuleComplex` | two typed with `identicalb = true`, underlying `float32`/`float64` | `complex64`/`complex128` |
| `RuleComplex` | two typed with `identicalb = false` | rejected |
| `RulePrintln` | variadic, each an untyped constant or a value whose underlying form is basic | zero results |

Every other predeclared callable resolves and raises an `ApplicationReq` boundary carrying the exact profile;
`main()` is the same case. `HeadCallable` is the lasting refinement — C9 adds inhabitants, not an
AppTarget constructor.

## 12. One result-consumption mapping

```coq
Inductive PlanTarget (p : Syntax.Program) : Type :=
| NamedTarget : Index.BindingSiteRef p -> PlanTarget p
| BlankTarget : Index.BlankRef p -> PlanTarget p.

Record ResultOccurrence (cp : Program) : Type := MakeResultOccurrence {
  ro_use   : Index.ExprUseRef (source cp);
  ro_fact  : UseFact cp ro_use;
  ro_index : nat;
  ro_atom  : ResultAtom cp;
  ro_at    : ResultAt ro_fact ro_index ro_atom }.

Record PlanEntry (cp : Program) : Type := MakePlanEntry {
  pe_target : PlanTarget (source cp);
  pe_result : ResultOccurrence cp }.

Parameter plan_entries : forall {cp} {s}, ResultPlan cp s -> list (PlanEntry cp).
Parameter plan_sources : forall {cp} {s}, ResultPlan cp s -> list (Index.ExprUseRef (source cp)).
Parameter SiteTargets : forall cp s, list (PlanTarget (source cp)) -> Prop.

Inductive PlanShape (cp : Program)
  : list (Index.ExprUseRef (source cp)) -> list (PlanEntry cp) -> Prop :=
| ShapeOnePerSource : forall srcs entries,
    List.length srcs = List.length entries ->
    (forall e, In e entries -> ro_index cp (pe_result cp e) = 0) ->
    PlanShape cp srcs entries
| ShapeOneMultiSource : forall src entries,
    (forall e, In e entries -> ro_use cp (pe_result cp e) = src) ->
    PlanShape cp (src :: nil) entries.
```

One ordered mapping, no `Pairwise | SingleMulti` public sum. A blank is a `BlankTarget` entry in its source
position. A source is any `ExprUseRef`, so inherited const uses need no reconstruction. Each entry's atom is
tied by `ro_at` to an exact position in an exact use fact — never supplied independently. Defaulting,
assignability, representability and short-declaration classification are read from `ro_fact` and the binder
fact; they are not duplicated as plan fields. Application arguments consume this same root.

## 13. Diagnostics

```coq
Inductive OperandResultView : Type :=
| ORUntypedConstant : UntypedConstantKind -> Typing.Constant -> OperandResultView
| ORTypedConstant   : Typing.TypeView -> Typing.Constant -> OperandResultView
| ORValue           : Typing.TypeView -> OperandResultView.

Inductive HeadView : Type :=
| HVObject : ErasedObjectOrigin -> ObjectKind -> HeadView
| HVValue  : Typing.TypeView -> HeadView.

Definition ErasedResultVector : Type := list ErasedForm.

Inductive AssignmentTargetAnchor (p : Syntax.Program) : Type :=
| ExplicitTypeTarget : Index.TypeUseRef p -> AssignmentTargetAnchor p
| InferredTarget     : Index.BindingSiteRef p -> AssignmentTargetAnchor p.

Inductive ArgumentReason : Type :=
| ArgWrongCount : nat -> nat -> ArgumentReason
| ArgNotAssignable : Typing.TypeView -> Typing.TypeView -> ArgumentReason
| ArgNotRepresentable : Typing.TypeView -> ArgumentReason
| ArgProfileRejected : ErasedForm -> ArgumentReason.

Inductive OperandReason : Type :=
| OperandNotNumeric : Typing.TypeView -> OperandReason
| OperandNoResult   : OperandReason.

Inductive IneligibleReason : Type :=
| NotAnApplication : IneligibleReason
| NotCallableTarget : ErasedTarget -> IneligibleReason.

Inductive DiagnosticCode : Type :=
| CodeInvalidConversion | CodeDefaultNotRepresentable | CodeMainRedeclared | CodeMissingMainEntry
| CodeBuildOutputIsDirectory | CodeDuplicateBinding | CodeInitMisuse | CodeUnresolvedName
| CodeWrongRole | CodeNotApplicable | CodeTypeCycle | CodeDependencyCycle
| CodeFirstSpecInherited | CodeResultMismatch | CodeShortDeclNoNew | CodeShortRedeclType
| CodeNilNoTarget | CodeIotaNoContext | CodeNotAssignable | CodeUnusedLocal
| CodeBadArgument | CodeBadOperand | CodeNotStatement.

Inductive DiagnosticReason {p} {i : Input p} (ph : Phase i) : Type :=
| InvalidConversion : Index.ApplicationRef p -> Index.ExprRef p -> Index.ExprRef p ->
    list (Index.ApplicationRef p) -> Typing.TypeView -> OperandResultView -> DiagnosticReason ph
| DefaultNotRepresentable : Index.ExprRef p -> Typing.Constant -> Typing.TypeView -> DiagnosticReason ph
| MainRedeclared : Index.ObjectSiteRef p -> Index.ObjectSiteRef p -> DiagnosticReason ph
| MissingMainEntry : PackageRef p -> DiagnosticReason ph
| BuildOutputIsDirectory : PackageRef p -> string -> DiagnosticReason ph
| DuplicateBinding : Index.BindingSiteRef p -> Index.BindingSiteRef p -> DiagnosticReason ph
| InitMisuse : Index.BindingSiteRef p -> DiagnosticReason ph
| UnresolvedName : Index.NameUseRef p -> string -> DiagnosticReason ph
| WrongRole : Index.NameUseRef p -> UseRole -> ObjectKind -> DiagnosticReason ph
| NotApplicable : Index.ApplicationRef p -> HeadView -> DiagnosticReason ph
| TypeCycleDiag : Typing.TypeCycle (phase_equations ph) -> DiagnosticReason ph
| DependencyCycleDiag : forall k, DependencyCycle (phase_dependency_graph ph k) -> DiagnosticReason ph
| FirstSpecInherited : Index.ConstSpecRef p -> DiagnosticReason ph
| ResultMismatch : Index.PlanSiteRef p -> nat -> list ErasedResultVector -> DiagnosticReason ph
| ShortDeclNoNew : Index.StatementRef p -> DiagnosticReason ph
| ShortRedeclType : Index.BindingSiteRef p -> Typing.TypeView -> Typing.TypeView -> DiagnosticReason ph
| NilNoTarget : Index.ExprRef p -> DiagnosticReason ph
| IotaNoContext : Index.ExprRef p -> DiagnosticReason ph
| NotAssignable : Index.ExprUseRef p -> AssignmentTargetAnchor p -> Typing.TypeView ->
    Typing.TypeView -> DiagnosticReason ph
| UnusedLocal : Index.BindingSiteRef p -> DiagnosticReason ph
| BadArgument : Index.DirectExprUseRef p -> ArgumentReason -> DiagnosticReason ph
| BadOperand : Index.DirectExprUseRef p -> OperandReason -> DiagnosticReason ph
| NotStatement : Index.ExpressionStatementRef p -> IneligibleReason -> DiagnosticReason ph.

Parameter diagnostic_code : forall {p} {i} {ph : Phase i}, DiagnosticReason ph -> DiagnosticCode.
Parameter diagnostic_primary : forall {p} {i} {ph : Phase i}, DiagnosticReason ph -> Index.Key.
```

The constructor-to-code map is the identity on names: `InvalidConversion ↦ CodeInvalidConversion` through
`NotStatement ↦ CodeNotStatement`. `InvalidConversion` carries an `OperandResultView`, so a nonconstant
variable operand is representable without inventing a runtime value. Cycle evidence is indexed by its own
graph. A failed preflight precedes a package's semantic errors; otherwise one canonical source order per
package. Every constructor expresses definite Go invalidity; a missing semantic rule is a boundary and never
enters `DiagnosticReason`.

## 14. Render

```coq
Inductive Prec : Type := PrimaryPrec | UnaryPrec.
Definition prec (e : Syntax.Expr) : Prec :=
  match e with Syntax.Unary _ _ => UnaryPrec | _ => PrimaryPrec end.
Definition PrecLooser (child required : Prec) : Prop :=
  match child, required with UnaryPrec, PrimaryPrec => True | _, _ => False end.

Parameter render_at : Prec -> Syntax.Expr -> string.
Parameter render_expr : Syntax.Expr -> string.
Parameter render_file : Syntax.File -> string.
Parameter render_program : Syntax.Program -> list (FilePath.T * string).
Parameter render_gomod : Syntax.ModuleSpec -> string.

Fixpoint InString (c : ascii) (s : string) : Prop :=
  match s with EmptyString => False | String d s' => d = c \/ InString c s' end.
Fixpoint HasPrefix (pre s : string) : Prop :=
  match pre, s with
  | EmptyString, _ => True
  | String _ _, EmptyString => False
  | String a pre', String b s' => a = b /\ HasPrefix pre' s'
  end.
Fixpoint HasSubstring (sub s : string) : Prop :=
  match s with
  | EmptyString => HasPrefix sub EmptyString
  | String _ s' => HasPrefix sub s \/ HasSubstring sub s'
  end.

Definition AsciiOnly (s : string) : Prop := forall c, InString c s -> (nat_of_ascii c < 128)%nat.
Definition NoAdjacentMinus (s : string) : Prop := ~ HasSubstring "--" s.
Definition Parenthesized (s : string) : Prop := exists inner, s = ("(" ++ inner ++ ")")%string.
Definition NoTrailingBlank (s : string) : Prop :=
  ~ HasSubstring (String " " (String (ascii_of_nat 10) EmptyString)) s
  /\ ~ HasSubstring (String (ascii_of_nat 9) (String (ascii_of_nat 10) EmptyString)) s.
```

`render_file` consumes the exact `Syntax.File`, so its own package clause and intrinsically empty import
section are preserved; `render_program` walks the exact `Syntax.Program` and pairs each `FilePath.T` with its
bytes, and `render_gomod` renders the exact `ModuleSpec`. Rendering performs no binding, type lookup or fact
reconstruction. Frozen expression outputs: `-1`, `-(-x)`, `-T(x)`, `f(x)`, `f(-x)`, `(-f)(x)`. There is no
parser and no second renderer. File level keeps the existing bytes: header line, blank line, package clause,
blank line before each top-level declaration, exact final newline; within a declaration one tab per block
depth, comma-space separators, no trailing whitespace, direct source spelling, an inherited const spec
rendering names only, one spec ungrouped, zero or two-or-more grouped with the zero branches exactly
`const ()`, `var ()`, `type ()`.

## 15. Migration of accepted guarantees

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
| `Render.resolved_expr_denotes` | split: constant/spelling half retained at C6; the value half moves to C7 |
| `Render.resolved_string_denotes`, `boundary_max`, `boundary_min` | moved to C7 with the value half |
| `Render` type-expression spelling and injectivity | restated over `Syntax.TypeExpr` |
| `Render` expression, argument, statement and declaration rendering | restated over the new source roots |
| `Render` ASCII and newline-safety; integer, string, float and complex decoding | retained; the complex decoder reads an `Application` |
| `Compilable.predeclared_type`, `predeclared_type_of_name` | deleted; subsumed by the phase binding relation |
| `Names.TypeName`, `SupportedType`, `classify`, `supported_of`, `all_type_names` | deleted; subsumed by `PredeclaredName` |
| `compile_complete` | restated: `Admissible p -> InScope p -> exists cp Hcp, compile p = Compiled cp Hcp` |
| `compile_rejected_of_inadmissible`, `elaboration_accepted_iff_admissible`, `elaboration_rejected_iff_inadmissible` | restated with the `InScope` premise |
| `compile_ok_valid`, `compile_rejected_not_admissible` | retained unchanged |
| `compile_program_typed`, `compile_ok_of_source_spec_valid_b` | restated over the phase judgment with `InScope` |
| `program_of_admissible`, `capability_of_admissible`, `capability_source`, `capability_is_compile_outcome` | restated with the `InScope` premise |

Proof-only helpers become `Local`. No compatibility alias survives.

## 16. Theorems

```coq
(* the pinned catalog and its objects *)
Theorem all_predeclared_nodup : NoDup all_predeclared.
Theorem all_predeclared_complete : forall n, In n all_predeclared.
Theorem predeclared_spelling_injective : forall a b,
  predeclared_spelling a = predeclared_spelling b -> a = b.
Theorem classify_spelling_roundtrip : forall n, classify_spelling (predeclared_spelling n) = Some n.
Theorem classify_spelling_sound : forall s n,
  classify_spelling s = Some n -> s = predeclared_spelling n.
Theorem predeclared_eqb_spec : forall a b, predeclared_eqb a b = true <-> a = b.
Theorem predeclared_object_origin : forall p (i : Input p) (ph : Phase i) n,
  object_origin (predeclared_object ph n) = Predeclared p n.
Theorem source_object_origin : forall p (i : Input p) (ph : Phase i) s,
  object_origin (source_object ph s) = SourceObject p s.
Theorem object_origin_injective : forall p (i : Input p) (ph : Phase i) (o1 o2 : ObjectRef ph),
  object_origin o1 = object_origin o2 -> o1 = o2.
Theorem predeclared_object_kind : forall p (i : Input p) (ph : Phase i) n,
  object_kind (predeclared_object ph n) = predeclared_kind n.
Theorem object_eqb_spec : forall p (i : Input p) (ph : Phase i) (o1 o2 : ObjectRef ph),
  object_eqb o1 o2 = true <-> o1 = o2.

(* the outcome *)
Theorem decision_accepted_iff : forall p (a : Elaboration p),
  (exists Hd Hb, decision a = AcceptedDecision (elaboration_core a) Hd Hb)
  <-> core_diagnostics (elaboration_core a) = nil /\ core_boundaries (elaboration_core a) = nil.
Theorem decision_rejected_iff : forall p (a : Elaboration p),
  (exists Hd, decision a = RejectedDecision (elaboration_core a) Hd)
  <-> core_diagnostics (elaboration_core a) <> nil.
Theorem decision_outside_iff : forall p (a : Elaboration p),
  (exists Hd Hb, decision a = OutsideDecision (elaboration_core a) Hd Hb)
  <-> core_diagnostics (elaboration_core a) = nil /\ core_boundaries (elaboration_core a) <> nil.
Theorem compiled_retains_core : forall p cp (Hcp : source cp = p),
  compile p = Compiled p cp Hcp ->
  eq_rect (source cp) Core (core cp) p Hcp = elaboration_core (elaborate p).
Theorem rejected_retains_core : forall p (f : Failure p),
  compile p = Rejected p f -> failure_core f = elaboration_core (elaborate p).
Theorem outside_retains_core : forall p (o : Outside p),
  compile p = OutsideScope p o -> outside_core o = elaboration_core (elaborate p).
Theorem in_scope_accepted_iff : forall p, InScope p ->
  (core_diagnostics (elaboration_core (elaborate p)) = nil <-> Admissible p).
Theorem in_scope_inadmissible_rejected : forall p, InScope p -> ~ Admissible p ->
  exists f, compile p = Rejected p f.
Theorem in_scope_admissible_compiled : forall p, Admissible p -> InScope p ->
  exists cp Hcp, compile p = Compiled p cp Hcp.
Theorem rejected_not_admissible : forall p (f : Failure p),
  compile p = Rejected p f -> ~ Admissible p.

(* type provenance and the closed rules *)
Theorem accepted_env_is_phase_env : forall cp : Program,
  phase_type_result (accepted_phase cp)
  = TypeReady (accepted_equations cp) (projT1 (accepted_type_ready cp)) (accepted_environment cp).
Theorem resolve_graph_acyclic_iff : forall p (eqs : Typing.ResolvedTypeEquations p),
  (exists ev, resolve_graph eqs = GraphAcyclic eqs ev) <-> AcyclicEquations eqs.
Theorem graph_evidence_disjoint : forall p (eqs : Typing.ResolvedTypeEquations p),
  Typing.TypeGraphEvidence eqs -> Typing.TypeCycle eqs -> False.
Theorem denote_alias_is_target : forall p eqs ev (env : Typing.Env eqs ev) a t h r,
  denote (ResolvedAlias env a t h r) = denote r.
Theorem identical_defined_iff : forall p eqs ev (env : Typing.Env eqs ev) d1 h1 d2 h2,
  Identical env (DefinedType env d1 h1) (DefinedType env d2 h2) -> d1 = d2.
Theorem underlyingb_reflect : forall p eqs ev (env : Typing.Env eqs ev) s f,
  underlyingb env s = f <-> Underlying env s f.
Theorem identicalb_reflect : forall p eqs ev (env : Typing.Env eqs ev) s t,
  identicalb env s t = true <-> Identical env s t.
Theorem assignableb_reflect : forall p eqs ev (env : Typing.Env eqs ev) s t,
  assignableb env s t = true <-> Assignable env s t.
Theorem convertibleb_reflect : forall p eqs ev (env : Typing.Env eqs ev) s t,
  convertibleb env s t = true <-> Convertible env s t.
Theorem representableb_reflect : forall p eqs ev (env : Typing.Env eqs ev) s c,
  representableb env s c = true <-> Representable env s c.
Theorem typed_constant_exact_roundtrip : forall p eqs ev (env : Typing.Env eqs ev) s c h,
  typed_constant_exact (typed_constant_of env s c h) = c.

(* scope and binding *)
Theorem scopes_file_order_independent : forall p (i : Input p) (ph : Phase i),
  ScopesFileOrderIndependent ph.
Theorem predeclared_shadowed : forall cp u s o,
  binder_disposition cp s = DispDeclares cp o -> InnermostDeclaring cp u s ->
  bound_object_at cp u = o.

(* requirements and boundaries *)
Theorem requirement_dec_reflects : forall p (i : Input p) (ph : Phase i) (r : SemanticRequirement ph),
  (exists h, requirement_dec r = left h) <-> RequirementSatisfied r.
Theorem requirement_view_eqb_spec : forall a b, requirement_view_eqb a b = true <-> a = b.
Theorem view_lt_strict :
  (forall a, ~ view_lt a a) /\ (forall a b c, view_lt a b -> view_lt b c -> view_lt a c).
Theorem view_lt_total : forall a b, view_lt a b \/ a = b \/ view_lt b a.
Theorem root_boundary_complete : forall p (c : Core p) (r : SemanticRequirement (phase c)),
  RootRequirement (phase c) r -> ~ RequirementSatisfied r ->
  exists b, In b (core_boundaries c) /\ boundary_view b = requirement_view r.
Theorem boundary_views_nodup : forall p (c : Core p),
  NoDup (map boundary_view (core_boundaries c)).
Theorem boundary_order_canonical : forall p (c : Core p),
  Sorted view_lt (map boundary_view (core_boundaries c)).
Theorem listed_boundary_is_root : forall p (c : Core p) b,
  In b (core_boundaries c) -> RootRequirement (phase c) (boundary_requirement b).

(* use provenance *)
Theorem direct_use_provenance : forall p (u : DirectExprUseRef p),
  OccupiesRole (direct_parent u) (direct_child u) (direct_role u).
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

(* expression object/result coherence, one theorem per exact case *)
Theorem iota_object_is_contextual : forall cp r (f : ExpressionFact cp r) o,
  referenced_object f = Some o -> object_origin_of o = Predeclared (source cp) PIota ->
  result_form f = ContextualForm cp IotaResult.
Theorem nil_object_is_contextual : forall cp r (f : ExpressionFact cp r) o,
  referenced_object f = Some o -> object_origin_of o = Predeclared (source cp) PNil ->
  result_form f = ContextualForm cp NilResult.
Theorem ordinary_constant_is_fixed : forall cp r (f : ExpressionFact cp r) o,
  referenced_object f = Some o -> object_kind_of o = ConstantObject ->
  object_origin_of o <> Predeclared (source cp) PIota ->
  exists atom, result_form f = FixedResults cp (atom :: nil).
Theorem variable_name_one_value : forall cp r (f : ExpressionFact cp r) o,
  referenced_object f = Some o -> object_kind_of o = VariableObject ->
  exists t, result_form f = FixedResults cp (ValueResult cp t :: nil).
Theorem type_name_no_result : forall cp r (f : ExpressionFact cp r) o,
  referenced_object f = Some o -> object_kind_of o = TypeObject ->
  result_form f = NoStandaloneResult cp.
Theorem builtin_name_no_result : forall cp r (f : ExpressionFact cp r) o,
  referenced_object f = Some o -> object_kind_of o = BuiltinObject ->
  result_form f = NoStandaloneResult cp.
Theorem function_name_no_result : forall cp r (f : ExpressionFact cp r) o,
  referenced_object f = Some o -> object_kind_of o = FunctionObject ->
  result_form f = NoStandaloneResult cp.

(* application coherence *)
Theorem app_args_match_source : forall cp a,
  app_arg_uses (application_fact cp a) = application_argument_uses a.
Theorem app_profile_from_args : forall cp a,
  app_profile (application_fact cp a)
  = map (fun u => erase_result_form (result_form (use_expression_fact (use_fact cp u))))
        (app_arg_facts (application_fact cp a)).
Theorem app_results_are_parent_results : forall cp a,
  result_form (expression_fact cp (Index.application_expr a))
  = FixedResults cp (app_results (application_fact cp a)).
Theorem app_results_from_rule : forall cp a,
  exists rule, AppAccepts (application_fact cp a) rule (app_results (application_fact cp a)).
Theorem complex_needs_identical_types : forall cp a s t,
  ComplexApplication cp a -> TypedOperandTypes cp a s t -> AcceptedIdentical cp s t.
Theorem statement_eligible_iff_callable : forall cp s,
  StatementEligible cp s <->
  (exists a (h : Index.application_expr a = Index.statement_expression s) c,
     app_target (application_fact cp a) = CallableTarget _ c).

(* result consumption *)
Theorem plan_covers_targets : forall cp s targets,
  SiteTargets cp s targets -> map (pe_target cp) (plan_entries (result_plan cp s)) = targets.
Theorem plan_is_legal : forall cp s,
  PlanShape cp (plan_sources (result_plan cp s)) (plan_entries (result_plan cp s)).
Theorem c6_plans_are_one_per_source : forall cp s entries,
  PlanShape cp (plan_sources (result_plan cp s)) entries ->
  List.length (plan_sources (result_plan cp s)) = List.length entries \/
  List.length (plan_sources (result_plan cp s)) = 1.

(* short declarations and static variables *)
Theorem short_decl_has_new_name : forall cp s,
  ShortDeclSite cp s ->
  exists b, In b (short_left_sites cp s)
         /\ exists o, binder_disposition cp b = DispDeclares cp o.
Theorem short_reuse_is_same_block : forall cp b o v,
  binder_disposition cp b = DispReuses cp o v -> SameBlockEarlier cp b o.
Theorem static_variable_origin : forall cp s,
  object_origin_of (projT1 (static_variable_at cp s))
  = SourceObject (source cp) (binding_site_object_site (variable_site_binding_site s)).

(* dependency outcome *)
Theorem dependency_edges_from_bindings : forall p (i : Input p) (ph : Phase i) k,
  EdgesFromBindings (phase_dependency_graph ph k).
Theorem accepted_dependency_acyclic : forall cp k,
  exists order h, phase_dependency_outcome (accepted_phase cp) k
                = DependencyAcyclic (phase_dependency_graph (accepted_phase cp) k) order h.

(* diagnostics *)
Theorem unused_local_iff : forall p (c : Core p) site,
  FullyAnalyzedLocal (phase c) site ->
  (In (UnusedLocal (phase c) site) (core_diagnostics c) <-> ~ PhaseReadsVariableAt (phase c) site).
Theorem blocked_site_no_unused_local : forall p (c : Core p) site,
  ~ FullyAnalyzedLocal (phase c) site -> ~ In (UnusedLocal (phase c) site) (core_diagnostics c).
Theorem diagnostics_nodup : forall p (c : Core p),
  NoDup (map diagnostic_primary (core_diagnostics c)).

(* rendering *)
Theorem unary_never_merges : forall e,
  NoAdjacentMinus (render_expr (Syntax.Unary Syntax.UnaryMinus e)).
Theorem parens_exactly_when_needed : forall r e,
  Parenthesized (render_at r e) <-> PrecLooser (prec e) r.
Theorem render_ascii : forall e, AsciiOnly (render_expr e).
Theorem render_file_no_trailing_blank : forall f, NoTrailingBlank (render_file f).
Theorem render_bytes_preserved : forall p, PreC6Program p -> render_program p = legacy_bytes p.
```

`ScopesFileOrderIndependent`, `InnermostDeclaring`, `ComplexApplication`, `TypedOperandTypes`,
`ShortDeclSite`, `short_left_sites`, `SameBlockEarlier`, `FullyAnalyzedLocal`, `PhaseReadsVariableAt`,
`PreC6Program` and `legacy_bytes` are frozen alongside these statements; `legacy_bytes` is migration evidence
consumed by the semantic-root review, not a retained second renderer.

## 17. Review boundaries

**Semantic-root review** stops only when the repository is green and contains: the corrected source and index
roots with `Role` unindexed and package identity in `Compilable`; the retained phase with `TypePhaseResult`
and no unconditional acyclic evidence; phase-indexed objects, facts and requirements; the core-indexed
three-way decision; requirement-indexed sealed boundaries with `RequirementView` as their one key; the closed
`SemanticType` and its closed rules with reflected decisions; accepted facts as definitions over the exact
phase; `HeadCallable` and the closed `AppAccepts`; the one result-consumption mapping; the dependency
outcome; the old fixed resolver and old expression phase deleted; `Safe.Value` and `Safe.eval_expr` deleted;
no `Runtime` module or machine; prior generated bytes unchanged.

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
unmet requirement and no diagnostic; `type U uintptr; type T U; var x T` gives exactly one root boundary, two
blocked sites, and **no** unused-local diagnostic for `x`. Two defined types with identical underlying
`float32` but distinct identity are rejected by `complex`; one such type used twice yields `complex64`.
`_, y := 1, 2` places the blank entry in its own source position. Short declaration with no new nonblank name
rejected; short redeclaration returning the exact existing object; blank declarations creating no object;
`true`, `false`, `byte` and `rune` resolving through ordinary binding; an ordinary declared constant **not**
acquiring `iota`'s contextual result; alias preserving identity; a local type spec naming itself rejected as a
cycle; package constant and variable cycles rejected; a package expression depending on a forward constant
accepted; a first const spec with an inherited initializer rejected; an inherited spec taking the predecessor
expression under its own `iota`; unshadowed `nil` and out-of-context `iota` rejected; a `println` argument of
a defined type whose underlying form is `string` accepted; unary minus on a constant and a variable accepted
and on a string rejected; `-(-x)` rendering with its parentheses; every currently accepted program rendering
byte-identically after migration; generated C6 programs passing the pinned Go build with their exact expected
observation.

The multi-result `_, y := f()` case belongs to C9, which introduces functions and multi-results.

## Preserve

`Syntax.Program` as the sole source authority and the AST as the one IR; `Program` as the opaque C4
capability, with `Failure` and `Outside` retaining the exact core; the retained input, work forest, member
index, outcome trace and sealed core; `Machine.T` uninstantiated; direct rendering and the one
`Emit.Mint.issue` authority; certified-module coverage, the whole-theory audit and controls A-E; every
sealed-capability, mint, transport and positive client control; working-tree and staged-index separation;
no-host-Python; `life.md`.

## Stop

A `Phase` cannot retain `TypePhaseResult` without exposing acyclic evidence unconditionally; the accepted
environment cannot be projected from the phase without a rebuild; an accepted fact cannot be defined over a
phase family; a requirement constructor cannot be built from site objects alone; `RequirementView` cannot
carry every distinction the missing-rule decision uses; `SemanticType` cannot be closed; a closed type rule
cannot be stated as constructors; `AppAccepts` cannot replace a free result function; the one plan mapping
cannot carry inherited uses or blanks in position; package identity cannot leave `Index`; a diagnostic
payload type cannot be defined; `render_file` cannot consume `Syntax.File`; a §16 theorem cannot be stated
over the names defined here; `LAT-077` needs a diagnostic the phase cannot produce; a run relation, value,
store, environment or machine is needed for a C6 row; implementation needs a placeholder, compatibility path,
trusted shortcut, fuel, bound or premature future state.
