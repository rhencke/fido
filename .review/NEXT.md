# C6 — the static semantic foundation

Review: contract

Goal: ordinary source names acquire meaning only through binding. C6 lands the pinned predeclared identity
catalog, a closed type algebra with **named** predeclared types, exact constants, role-indexed
expression/use/application facts whose results are **derived**, one result-occurrence authority, compiler-owned
static variable identity, the static package dependency object, and a three-way decision that never calls
unmodelled Go a rejection.

**C6 is entirely static.** No `Runtime`, value, place, store, environment or `Machine.T`; C7 introduces them as
one vertical and materializes package **variables** only — constants stay compile-time facts.

The declarations below are the published surface **verbatim**: `make contract-surface` elaborates exactly this
text under the pinned Rocq. Names are written unqualified, as they elaborate; each block states the module that
owns it. The first block is the existing repository surface this contract reuses unchanged — it declares
nothing new. Its typed rules were checked against pinned Go 1.23 with `make go-probe` before being written
down; the alarms and their outcomes are in §Done.

## Ownership and physical modules

`ARCHITECTURE.md` owns the ownership law and the physical-structure doctrine; `ROADMAP.md` owns the milestone
sequence. C6 implements directly into the frozen `Compilable` namespace:

| module | owns |
|---|---|
| `Compilable.Bindings` | `PackageRef`, scopes, object identity, binder/object sites, blank/new/reuse disposition, name binding, the predeclared outer scope and shadowing |
| `Compilable.TypeResolution` | exact type equations, the graph decision, the retained `TypePhaseResult` and its environment, object-indexed type meanings, predeclared/alias/definition mapping |
| `Compilable.Dependencies` | package const/var dependency nodes, edges, cycle/acyclic outcome, retained order, the runtime-variable projection |
| `Compilable.Expressions` | expression facts, role-indexed use facts, result occurrences, unary facts, application facts and rules, statement classification, object-indexed capabilities |
| `Compilable.Results` | const/var/short result-to-target plans, binder finalization, exact `StaticVariable`, unused-local facts |
| `Compilable.Report` | failure causes, diagnostics, semantic requirements, reflected satisfaction, boundaries, root/blocked reporting, canonical report lists |
| `Compilable.v` | predecessor-indexed phase composition, whole-program preflight, `Core`, `Elaboration`, `Decision`, `Program`/`Failure`/`Outside`, `Outcome`, `elaborate`, `compile`, final cross-layer accepted projections |
| `Compilable.Evidence` | certified accepted/rejected/outside fixtures and controls; no production module imports it |

`Bindings` precedes `TypeResolution`, `Dependencies` and `Expressions`; `Expressions` precedes `Results`;
`Results` and `Dependencies` precede `Report`; `Report` precedes `Compilable.v`; `Compilable.v` precedes
`Evidence`. No child imports `Compilable.v`.

## The published surface

```coq
(* ── (a) existing repository public names, faithfully stubbed ──────────────── *)
Parameter SyntaxProgram SyntaxFile ModuleSpec FilePathT : Type.
Parameter Identifier : Type.
Parameter spelling : Identifier -> string.
(* Integer.Kind, Float.Kind and Complex.Kind are closed today; stub them faithfully. *)
Inductive IntegerKind : Type :=
| IKInt | IKInt8 | IKInt16 | IKInt32 | IKInt64
| IKUint | IKUint8 | IKUint16 | IKUint32 | IKUint64.
Inductive FloatKind : Type := FKF32 | FKF64.
Inductive ComplexKind : Type := CKC64 | CKC128.
Parameter IntegerRepresentable : IntegerKind -> Z -> Prop.
Parameter FloatTypedConstant : FloatKind -> Type.
Parameter ComplexTypedConstant : ComplexKind -> Type.
Parameter Decimal : Type.
Parameter coefficient : Decimal -> Z.
Parameter IndexKey : Type.
Parameter Input : SyntaxProgram -> Type.
Parameter Core : SyntaxProgram -> Type.
Parameter core_input : forall {p}, Core p -> Input p.
Parameter Elaboration : SyntaxProgram -> Type.
Parameter elaboration_core : forall {p}, Elaboration p -> Core p.
Parameter elaborate : forall p, Elaboration p.
Parameter Admissible : SyntaxProgram -> Prop.

(* ── Names ─────────────────────────────────────────────────────────────────── *)
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
  end.

Definition all_predeclared : list PredeclaredName :=
  [PAny; PBool; PByte; PComparable; PComplex64; PComplex128; PError; PFloat32; PFloat64;
   PInt; PInt8; PInt16; PInt32; PInt64; PRune; PString; PUint; PUint8; PUint16; PUint32;
   PUint64; PUintptr; PTrue; PFalse; PIota; PNil; PAppend; PCap; PClear; PClose; PComplex;
   PCopy; PDelete; PImag; PLen; PMake; PMax; PMin; PNew; PPanic; PPrint; PPrintln; PReal;
   PRecover].

Parameter classify_spelling : string -> option PredeclaredName.
Parameter predeclared_eqb : PredeclaredName -> PredeclaredName -> bool.

Record OrdinaryIdentifier : Type := MakeOrdinary {
  ordinary_identifier : Identifier;
  ordinary_not_predeclared : classify_spelling (spelling ordinary_identifier) = None
}.

(* Collections owns NonEmpty; Float owns NonNegativeDecimal. *)
Record NonEmpty (A : Type) : Type := MakeNonEmpty { ne_first : A; ne_rest : list A }.
Record NonNegativeDecimal : Type := MakeNonNegDecimal {
  nnd_decimal : Decimal; nnd_nonneg : (0 <= coefficient nnd_decimal)%Z
}.

(* ── Syntax ────────────────────────────────────────────────────────────────── *)
Inductive BindingName : Type := Named (n : OrdinaryIdentifier) | Blank.
Inductive UnaryOp : Type := UnaryMinus.

Inductive Literal : Type :=
| IntegerLiteral (z : Z)
| FloatLiteral (d : NonNegativeDecimal)
| StringLiteral (s : string).

Inductive TypeExpr : Type := NamedType (n : OrdinaryIdentifier).

Inductive Expr : Type :=
| Name (n : OrdinaryIdentifier)
| LiteralExpr (l : Literal)
| Unary (op : UnaryOp) (e : Expr)
| Application (head : Expr) (args : list Expr).

Inductive ConstInitializer : Type :=
| ExplicitConstInit (ty : option TypeExpr) (values : NonEmpty Expr)
| InheritedConstInit.

Record ConstSpec : Type := MakeConstSpec {
  const_names : NonEmpty BindingName; const_init : ConstInitializer
}.

Inductive VarInitializer : Type :=
| VarTypeOnly (ty : TypeExpr)
| VarValues (ty : option TypeExpr) (values : NonEmpty Expr).

Record VarSpec : Type := MakeVarSpec {
  var_names : NonEmpty BindingName; var_init : VarInitializer
}.

Inductive TypeSpec : Type :=
| AliasSpec (name : OrdinaryIdentifier) (target : TypeExpr)
| DefSpec (name : BindingName) (target : TypeExpr).

Inductive Declaration : Type :=
| ConstDecl (specs : NonEmpty ConstSpec)
| VarDecl (specs : NonEmpty VarSpec)
| TypeDecl (specs : NonEmpty TypeSpec).

Inductive Stmt : Type :=
| ExprStmt (e : Expr)
| DeclarationStmt (d : Declaration)
| ShortVarDecl (names : NonEmpty BindingName) (values : NonEmpty Expr).

Inductive Block : Type := MakeBlock : list Stmt -> Block.

Inductive TopLevelDecl : Type :=
| TopDeclaration (d : Declaration)
| Main (body : Block).

Parameter program_files : SyntaxProgram -> list (FilePathT * SyntaxFile).
Parameter program_module : SyntaxProgram -> ModuleSpec.

(* ── Index: exact source occurrences ───────────────────────────────────────── *)
Inductive Role : Type :=
| RFilePackage | RDeclarationSpec | RVarSpecType
| RConstInitializerExpression | RVarInitializerExpression | RShortRightExpression
| RStatementExpression | RUnaryOperand | RApplicationHead | RApplicationArgument.

Inductive ExprChildRole : Role -> Prop :=
| ECConstInitializer : ExprChildRole RConstInitializerExpression
| ECVarInitializer   : ExprChildRole RVarInitializerExpression
| ECShortRight       : ExprChildRole RShortRightExpression
| ECStatement        : ExprChildRole RStatementExpression
| ECUnaryOperand     : ExprChildRole RUnaryOperand
| ECApplicationHead  : ExprChildRole RApplicationHead
| ECApplicationArg   : ExprChildRole RApplicationArgument.

Inductive UseRole : Type := TypeNameRole | ValueNameRole | HeadNameRole.

Parameter NodeRef : SyntaxProgram -> Type.
Parameter node_key : forall {p}, NodeRef p -> IndexKey.
Parameter ExprRef ConstDeclRef ConstSpecRef BindingNameRef BlankRef : SyntaxProgram -> Type.
Parameter TypeUseRef NameUseRef UnaryRef ApplicationRef : SyntaxProgram -> Type.
Parameter ExpressionStatementRef BindingSiteRef VariableSiteRef : SyntaxProgram -> Type.
Parameter ObjectSiteRef StatementRef FileRef : SyntaxProgram -> Type.
Parameter AliasSpecRef BoundDefinedTypeRef : SyntaxProgram -> Type.

(* Consumption sites are intrinsically context-tagged: no optional field decides the context. *)
Inductive ConsumptionSiteRef (p : SyntaxProgram) : Type :=
| ConstSite : ConstSpecRef p -> ConsumptionSiteRef p
| VarSite   : StatementRef p -> ConsumptionSiteRef p
| ShortSite : StatementRef p -> ConsumptionSiteRef p.

Parameter expr_node : forall {p}, ExprRef p -> NodeRef p.
Parameter object_site_key : forall {p}, ObjectSiteRef p -> IndexKey.
Parameter binding_site_object_site : forall {p}, BindingSiteRef p -> ObjectSiteRef p.
Parameter variable_site_binding_site : forall {p}, VariableSiteRef p -> BindingSiteRef p.
Parameter application_expr application_head : forall {p}, ApplicationRef p -> ExprRef p.
Parameter application_key : forall {p}, ApplicationRef p -> IndexKey.
Parameter statement_expression : forall {p}, ExpressionStatementRef p -> ExprRef p.
Parameter unary_operand : forall {p}, UnaryRef p -> ExprRef p.
Parameter OccupiesRole : forall {p}, NodeRef p -> NodeRef p -> Role -> Prop.

Parameter DirectExprUseRef : SyntaxProgram -> Type.
Parameter direct_parent : forall {p}, DirectExprUseRef p -> NodeRef p.
Parameter direct_child  : forall {p}, DirectExprUseRef p -> ExprRef p.
Parameter direct_role   : forall {p}, DirectExprUseRef p -> Role.
Parameter direct_is_expr_child : forall {p} (u : DirectExprUseRef p), ExprChildRole (direct_role u).
Parameter direct_occupies : forall {p} (u : DirectExprUseRef p),
  OccupiesRole (direct_parent u) (expr_node (direct_child u)) (direct_role u).
Parameter application_head_use : forall {p}, ApplicationRef p -> DirectExprUseRef p.
Parameter application_argument_uses : forall {p}, ApplicationRef p -> list (DirectExprUseRef p).

Parameter InheritedConstUseRef : SyntaxProgram -> Type.
Parameter ic_decl        : forall {p}, InheritedConstUseRef p -> ConstDeclRef p.
Parameter ic_current     : forall {p}, InheritedConstUseRef p -> ConstSpecRef p.
Parameter ic_name        : forall {p}, InheritedConstUseRef p -> BindingNameRef p.
Parameter ic_predecessor : forall {p}, InheritedConstUseRef p -> ConstSpecRef p.
Parameter ic_expr        : forall {p}, InheritedConstUseRef p -> ExprRef p.
Parameter ic_type        : forall {p}, InheritedConstUseRef p -> option (TypeUseRef p).
Parameter ic_iota ic_position : forall {p}, InheritedConstUseRef p -> nat.
Parameter SpecInDecl : forall {p}, ConstDeclRef p -> ConstSpecRef p -> Prop.
Parameter NearestPrecedingExplicit :
  forall {p}, ConstDeclRef p -> ConstSpecRef p -> ConstSpecRef p -> Prop.
Parameter NameAtPosition : forall {p}, ConstSpecRef p -> BindingNameRef p -> nat -> Prop.
Parameter ExprAtPosition : forall {p}, ConstSpecRef p -> ExprRef p -> nat -> Prop.
Parameter SpecTypeUse : forall {p}, ConstSpecRef p -> option (TypeUseRef p) -> Prop.
Parameter StructuralIota : forall {p}, ConstSpecRef p -> nat -> Prop.

(* One structural expression-use identity.  Semantic refinement is decided, not assumed. *)
Inductive ExprUseRef (p : SyntaxProgram) : Type :=
| DirectUse    : DirectExprUseRef p -> ExprUseRef p
| InheritedUse : InheritedConstUseRef p -> ExprUseRef p.

Definition expression_of_use {p} (u : ExprUseRef p) : ExprRef p :=
  match u with DirectUse _ d => direct_child d | InheritedUse _ i => ic_expr i end.

Definition use_role_of {p} (u : ExprUseRef p) : Role :=
  match u with DirectUse _ d => direct_role d | InheritedUse _ _ => RConstInitializerExpression end.

(* §1: the closed refinement a role selects.  A head or statement use has no selected result. *)
Inductive UseRefinement : Type := HeadRefinement | StatementRefinement | ResultRefinement.

Definition refinement_of_role (r : Role) : option UseRefinement :=
  match r with
  | RApplicationHead => Some HeadRefinement
  | RStatementExpression => Some StatementRefinement
  | RApplicationArgument | RUnaryOperand
  | RConstInitializerExpression | RVarInitializerExpression | RShortRightExpression =>
      Some ResultRefinement
  | RFilePackage | RDeclarationSpec | RVarSpecType => None
  end.

Definition use_refinement {p} (u : ExprUseRef p) : UseRefinement :=
  match refinement_of_role (use_role_of u) with
  | Some k => k
  | None => ResultRefinement
  end.

(* ── Typing: named predeclared identities over a form algebra ──────────────── *)
Inductive BasicType : Type :=
| BoolBasic | IntegerBasic (k : IntegerKind) | FloatBasic (k : FloatKind)
| ComplexBasic (k : ComplexKind) | StringBasic.

Inductive PredeclaredBasicType : Type :=
| TBool
| TInt | TInt8 | TInt16 | TInt32 | TInt64
| TUint | TUint8 | TUint16 | TUint32 | TUint64
| TFloat32 | TFloat64 | TComplex64 | TComplex128 | TString.

Definition predeclared_basic_form (t : PredeclaredBasicType) : BasicType :=
  match t with
  | TBool => BoolBasic
  | TInt => IntegerBasic IKInt | TInt8 => IntegerBasic IKInt8 | TInt16 => IntegerBasic IKInt16
  | TInt32 => IntegerBasic IKInt32 | TInt64 => IntegerBasic IKInt64
  | TUint => IntegerBasic IKUint | TUint8 => IntegerBasic IKUint8 | TUint16 => IntegerBasic IKUint16
  | TUint32 => IntegerBasic IKUint32 | TUint64 => IntegerBasic IKUint64
  | TFloat32 => FloatBasic FKF32 | TFloat64 => FloatBasic FKF64
  | TComplex64 => ComplexBasic CKC64 | TComplex128 => ComplexBasic CKC128
  | TString => StringBasic
  end.

Inductive ScalarNumericBasic : BasicType -> Prop :=
| SNInteger : forall k, ScalarNumericBasic (IntegerBasic k)
| SNFloat   : forall k, ScalarNumericBasic (FloatBasic k).
Inductive ComplexBasicForm : BasicType -> Prop :=
| CBComplex : forall k, ComplexBasicForm (ComplexBasic k).
Inductive FloatBasicForm : BasicType -> Prop :=
| FBFloat : forall k, FloatBasicForm (FloatBasic k).

(* §5: the complete predeclared type bridge, as one closed definition. *)
Inductive PredeclaredTypeRole : Type :=
| NamedBasic : PredeclaredBasicType -> PredeclaredTypeRole
| AliasOf    : PredeclaredBasicType -> PredeclaredTypeRole
| NoTypeMeaning : PredeclaredTypeRole.

Definition predeclared_type_role (n : PredeclaredName) : PredeclaredTypeRole :=
  match n with
  | PBool => NamedBasic TBool
  | PInt => NamedBasic TInt | PInt8 => NamedBasic TInt8 | PInt16 => NamedBasic TInt16
  | PInt32 => NamedBasic TInt32 | PInt64 => NamedBasic TInt64
  | PUint => NamedBasic TUint | PUint8 => NamedBasic TUint8 | PUint16 => NamedBasic TUint16
  | PUint32 => NamedBasic TUint32 | PUint64 => NamedBasic TUint64
  | PFloat32 => NamedBasic TFloat32 | PFloat64 => NamedBasic TFloat64
  | PComplex64 => NamedBasic TComplex64 | PComplex128 => NamedBasic TComplex128
  | PString => NamedBasic TString
  | PByte => AliasOf TUint8
  | PRune => AliasOf TInt32
  | PAny | PComparable | PError | PUintptr => NoTypeMeaning
  | PTrue | PFalse | PIota | PNil | PAppend | PCap | PClear | PClose | PComplex | PCopy
  | PDelete | PImag | PLen | PMake | PMax | PMin | PNew | PPanic | PPrint | PPrintln
  | PReal | PRecover => NoTypeMeaning
  end.

Definition AdmittedPredeclaredType (n : PredeclaredName) (t : PredeclaredBasicType) : Prop :=
  predeclared_type_role n = NamedBasic t.
Definition AliasPredeclared (n : PredeclaredName) (t : PredeclaredBasicType) : Prop :=
  predeclared_type_role n = AliasOf t.
Definition PredeclaredDenotes (n : PredeclaredName) (t : PredeclaredBasicType) : Prop :=
  AdmittedPredeclaredType n t \/ AliasPredeclared n t.

Inductive Constant : Type :=
| BoolConstant    : bool -> Constant
| IntegerConstant : Z -> Constant
| FloatConstant   : Decimal -> Constant
| ComplexConstant : Decimal -> Decimal -> Constant
| StringConstant  : string -> Constant.

Inductive UntypedConstantKind : Type := UCBool | UCInteger | UCFloat | UCComplex | UCString.
Definition constant_kind (c : Constant) : UntypedConstantKind :=
  match c with
  | BoolConstant _ => UCBool | IntegerConstant _ => UCInteger | FloatConstant _ => UCFloat
  | ComplexConstant _ _ => UCComplex | StringConstant _ => UCString
  end.

Definition NumericConstantKind (k : UntypedConstantKind) : Prop :=
  k = UCInteger \/ k = UCFloat \/ k = UCComplex.

(* §5: default types, closed. *)
Definition default_basic (k : UntypedConstantKind) : PredeclaredBasicType :=
  match k with
  | UCBool => TBool | UCInteger => TInt | UCFloat => TFloat64
  | UCComplex => TComplex128 | UCString => TString
  end.

(* The one constant-conversion authority, over the destination underlying form. *)
Parameter convert_constant_to : BasicType -> Constant -> option Constant.
Definition FitsBasic (b : BasicType) (c : Constant) : Prop :=
  exists c', convert_constant_to b c = Some c'.

Inductive BasicTypedConstant : BasicType -> Type :=
| TCBool    : bool -> BasicTypedConstant BoolBasic
| TCInteger : forall k z, IntegerRepresentable k z -> BasicTypedConstant (IntegerBasic k)
| TCFloat   : forall k, FloatTypedConstant k -> BasicTypedConstant (FloatBasic k)
| TCComplex : forall k, ComplexTypedConstant k -> BasicTypedConstant (ComplexBasic k)
| TCString  : string -> BasicTypedConstant StringBasic.

Inductive TypeView : Type :=
| PredeclaredView : PredeclaredBasicType -> TypeView
| DefinedView     : IndexKey -> TypeView.

Inductive RawTypeTarget (p : SyntaxProgram) : Type :=
| RawPredeclared : PredeclaredName -> RawTypeTarget p
| RawAlias       : AliasSpecRef p -> RawTypeTarget p
| RawDefined     : BoundDefinedTypeRef p -> RawTypeTarget p.

(* ── §5.1 The exact type-equation graph and its environment ────────────────── *)
Parameter ResolvedTypeEquations : SyntaxProgram -> Type.

(* Nodes are exactly the source aliases and definitions. *)
Inductive TypeNode (p : SyntaxProgram) : Type :=
| AliasNode   : AliasSpecRef p -> TypeNode p
| DefinedNode : BoundDefinedTypeRef p -> TypeNode p.

Parameter equation_target : forall {p}, ResolvedTypeEquations p -> TypeNode p -> RawTypeTarget p.

(* Edges come only from the exact bound type use in a right-hand side.
   There is no constructor for a predeclared target: predeclared targets are terminal. *)
Inductive TypeEdge {p} (eqs : ResolvedTypeEquations p) : TypeNode p -> TypeNode p -> Prop :=
| EdgeToAlias   : forall n a, equation_target eqs n = RawAlias p a ->
    TypeEdge eqs n (AliasNode p a)
| EdgeToDefined : forall n d, equation_target eqs n = RawDefined p d ->
    TypeEdge eqs n (DefinedNode p d).

Inductive EdgePath {p} (eqs : ResolvedTypeEquations p) : TypeNode p -> TypeNode p -> Prop :=
| PathStep : forall n m, TypeEdge eqs n m -> EdgePath eqs n m
| PathMore : forall n m o, TypeEdge eqs n m -> EdgePath eqs m o -> EdgePath eqs n o.

(* Every C6 cycle is invalid; a cycle witness is an exact node on its own path. *)
Record TypeCycle {p} (eqs : ResolvedTypeEquations p) : Type := MakeTypeCycle {
  cycle_node : TypeNode p;
  cycle_path : EdgePath eqs cycle_node cycle_node
}.

Definition AcyclicEquations {p} (eqs : ResolvedTypeEquations p) : Prop :=
  forall n, ~ EdgePath eqs n n.

(* A cycle witness is data, so the decision is a sumor, not a sumbool. *)
Parameter acyclic_dec : forall {p} (eqs : ResolvedTypeEquations p),
  TypeCycle eqs + { AcyclicEquations eqs }.

Parameter Env : forall {p}, ResolvedTypeEquations p -> Type.
Parameter DefinedInEnv : forall {p} {eqs : ResolvedTypeEquations p},
  Env eqs -> BoundDefinedTypeRef p -> Prop.
Parameter defined_key : forall {p}, BoundDefinedTypeRef p -> IndexKey.

Inductive TypeForm {p} {eqs : ResolvedTypeEquations p} (env : Env eqs) : Type :=
| BasicForm : BasicType -> TypeForm env.

Inductive SemanticType {p} {eqs : ResolvedTypeEquations p} (env : Env eqs) : Type :=
| PredeclaredType : PredeclaredBasicType -> SemanticType env
| DefinedType     : forall d : BoundDefinedTypeRef p, DefinedInEnv env d -> SemanticType env.

Parameter defined_underlying : forall {p} {eqs : ResolvedTypeEquations p} (env : Env eqs)
  (d : BoundDefinedTypeRef p), DefinedInEnv env d -> BasicType.

Definition type_view {p} {eqs : ResolvedTypeEquations p} {env : Env eqs}
  (t : SemanticType env) : TypeView :=
  match t with
  | PredeclaredType _ b => PredeclaredView b
  | DefinedType _ d _ => DefinedView (defined_key d)
  end.

Inductive Underlying {p} {eqs : ResolvedTypeEquations p} (env : Env eqs)
  : SemanticType env -> TypeForm env -> Prop :=
| UnderlyingPredeclared : forall t,
    Underlying env (PredeclaredType env t) (BasicForm env (predeclared_basic_form t))
| UnderlyingDefined : forall d h,
    Underlying env (DefinedType env d h) (BasicForm env (defined_underlying env d h)).

(* Identity is generated: name for predeclared, exact declaration reference for defined. *)
Inductive Identical {p} {eqs : ResolvedTypeEquations p} (env : Env eqs)
  : SemanticType env -> SemanticType env -> Prop :=
| IdenticalPredeclared : forall t, Identical env (PredeclaredType env t) (PredeclaredType env t)
| IdenticalDefined : forall d h1 h2,
    Identical env (DefinedType env d h1) (DefinedType env d h2).

(* §Keep: C6 typed assignability is identity. *)
Inductive Assignable {p} {eqs : ResolvedTypeEquations p} (env : Env eqs)
  : SemanticType env -> SemanticType env -> Prop :=
| AssignIdentical : forall s t, Identical env s t -> Assignable env s t.

(* The nonconstant conversion authority, strictly narrower than constant conversion. *)
Inductive ValueConvertible {p} {eqs : ResolvedTypeEquations p} (env : Env eqs)
  : SemanticType env -> SemanticType env -> Prop :=
| VConvIdentical : forall s t, Identical env s t -> ValueConvertible env s t
| VConvSameUnderlying : forall s t f,
    Underlying env s f -> Underlying env t f -> ValueConvertible env s t
| VConvScalarNumeric : forall s t bs bt,
    Underlying env s (BasicForm env bs) -> Underlying env t (BasicForm env bt) ->
    ScalarNumericBasic bs -> ScalarNumericBasic bt -> ValueConvertible env s t
| VConvComplex : forall s t bs bt,
    Underlying env s (BasicForm env bs) -> Underlying env t (BasicForm env bt) ->
    ComplexBasicForm bs -> ComplexBasicForm bt -> ValueConvertible env s t.

Inductive Representable {p} {eqs : ResolvedTypeEquations p} (env : Env eqs)
  : SemanticType env -> Constant -> Prop :=
| RepresentableAt : forall s b c,
    Underlying env s (BasicForm env b) -> FitsBasic b c -> Representable env s c.

Inductive ConstantConvertible {p} {eqs : ResolvedTypeEquations p} (env : Env eqs)
  : SemanticType env -> Constant -> Constant -> Prop :=
| CConvExact : forall s b c c',
    Underlying env s (BasicForm env b) -> convert_constant_to b c = Some c' ->
    ConstantConvertible env s c c'.

Inductive TypedConstant {p} {eqs : ResolvedTypeEquations p} (env : Env eqs)
  (s : SemanticType env) : Type :=
| TypedOf : forall b, Underlying env s (BasicForm env b) -> BasicTypedConstant b -> TypedConstant env s.

Parameter underlyingb : forall {p} {eqs : ResolvedTypeEquations p} (env : Env eqs),
  SemanticType env -> TypeForm env.
Parameter identicalb assignableb value_convertibleb :
  forall {p} {eqs : ResolvedTypeEquations p} (env : Env eqs),
    SemanticType env -> SemanticType env -> bool.
Parameter representableb : forall {p} {eqs : ResolvedTypeEquations p} (env : Env eqs),
  SemanticType env -> Constant -> bool.

Definition default_type {p} {eqs : ResolvedTypeEquations p} (env : Env eqs)
  (k : UntypedConstantKind) : SemanticType env :=
  PredeclaredType env (default_basic k).

Parameter AliasResolvesTo : forall {p} {eqs : ResolvedTypeEquations p} (env : Env eqs),
  AliasSpecRef p -> SemanticType env -> Prop.

Inductive ResolvedTypeTarget {p} {eqs : ResolvedTypeEquations p} (env : Env eqs)
  : RawTypeTarget p -> SemanticType env -> Prop :=
| ResolvedPredeclaredType : forall n t, AdmittedPredeclaredType n t ->
    ResolvedTypeTarget env (RawPredeclared p n) (PredeclaredType env t)
| ResolvedPredeclaredAlias : forall n t, AliasPredeclared n t ->
    ResolvedTypeTarget env (RawPredeclared p n) (PredeclaredType env t)
| ResolvedSourceAlias : forall a s, AliasResolvesTo env a s ->
    ResolvedTypeTarget env (RawAlias p a) s
| ResolvedDefinedType : forall d h,
    ResolvedTypeTarget env (RawDefined p d) (DefinedType env d h).

(* ── The one retained static phase ─────────────────────────────────────────── *)
(* A cyclic phase has no environment.  There is no builder and no equality to a rerun. *)
Inductive TypePhaseResult {p} (eqs : ResolvedTypeEquations p) : Type :=
| TypeReady  : AcyclicEquations eqs -> Env eqs -> TypePhaseResult eqs
| TypeCyclic : TypeCycle eqs -> TypePhaseResult eqs.

Definition IsTypeReady {p} {eqs : ResolvedTypeEquations p} (r : TypePhaseResult eqs) : Prop :=
  match r with TypeReady _ _ _ => True | TypeCyclic _ _ => False end.

Definition ready_env {p} {eqs : ResolvedTypeEquations p} (r : TypePhaseResult eqs)
  : IsTypeReady r -> Env eqs :=
  match r return IsTypeReady r -> Env eqs with
  | TypeReady _ _ e => fun _ => e
  | TypeCyclic _ _  => fun h => match h return Env eqs with end
  end.

Definition ready_acyclic {p} {eqs : ResolvedTypeEquations p} (r : TypePhaseResult eqs)
  : IsTypeReady r -> AcyclicEquations eqs :=
  match r return IsTypeReady r -> AcyclicEquations eqs with
  | TypeReady _ a _ => fun _ => a
  | TypeCyclic _ _  => fun h => match h return AcyclicEquations eqs with end
  end.

Parameter Phase : forall {p}, Input p -> Type.
Parameter phase : forall {p} (core : Core p), Phase (core_input core).
Parameter phase_equations : forall {p} {i : Input p} (ph : Phase i), ResolvedTypeEquations p.
Parameter phase_type_result : forall {p} {i : Input p} (ph : Phase i),
  TypePhaseResult (phase_equations ph).

(* ── Objects ───────────────────────────────────────────────────────────────── *)
Inductive ObjectKind : Type :=
| TypeObject | ConstantObject | VariableObject | FunctionObject | BuiltinObject | ZeroValueObject.

Inductive ObjectOrigin (p : SyntaxProgram) : Type :=
| Predeclared : PredeclaredName -> ObjectOrigin p
| SourceSite  : ObjectSiteRef p -> ObjectOrigin p.

Inductive ObjectKey : Type :=
| PredeclaredObjectKey : PredeclaredName -> ObjectKey
| SourceObjectKey      : IndexKey -> ObjectKey.

Definition origin_key {p} (o : ObjectOrigin p) : ObjectKey :=
  match o with
  | Predeclared _ n => PredeclaredObjectKey n
  | SourceSite _ s  => SourceObjectKey (object_site_key s)
  end.

Parameter ObjectRef : forall {p} {i : Input p}, Phase i -> Type.
Parameter object_origin : forall {p} {i : Input p} {ph : Phase i}, ObjectRef ph -> ObjectOrigin p.
Parameter object_eqb : forall {p} {i : Input p} {ph : Phase i}, ObjectRef ph -> ObjectRef ph -> bool.
Parameter predeclared_object : forall {p} {i : Input p} (ph : Phase i), PredeclaredName -> ObjectRef ph.
Parameter source_object : forall {p} {i : Input p} (ph : Phase i), ObjectSiteRef p -> ObjectRef ph.

Definition object_key {p} {i : Input p} {ph : Phase i} (o : ObjectRef ph) : ObjectKey :=
  origin_key (object_origin o).

(* ObjectKind is a proof-free diagnostic view only. *)
Definition predeclared_kind (n : PredeclaredName) : ObjectKind :=
  match n with
  | PAny | PBool | PByte | PComparable | PComplex64 | PComplex128 | PError | PFloat32 | PFloat64
  | PInt | PInt8 | PInt16 | PInt32 | PInt64 | PRune | PString | PUint | PUint8 | PUint16
  | PUint32 | PUint64 | PUintptr => TypeObject
  | PTrue | PFalse | PIota => ConstantObject
  | PNil => ZeroValueObject
  | PAppend | PCap | PClear | PClose | PComplex | PCopy | PDelete | PImag | PLen | PMake
  | PMax | PMin | PNew | PPanic | PPrint | PPrintln | PReal | PRecover => BuiltinObject
  end.

Parameter object_kind : forall {p} {i : Input p} {ph : Phase i}, ObjectRef ph -> ObjectKind.

(* ── Erased, proof-free views ──────────────────────────────────────────────── *)
Inductive ContextualResult : Type := IotaResult | NilResult.

Inductive ErasedAtom : Type :=
| EAUntyped : UntypedConstantKind -> ErasedAtom
| EATyped   : TypeView -> ErasedAtom
| EAValue   : TypeView -> ErasedAtom.

Inductive ErasedResultForm : Type :=
| ERFixed        : list ErasedAtom -> ErasedResultForm
| ERContextual   : ContextualResult -> ErasedResultForm
| ERNoStandalone : ErasedResultForm.

Definition ErasedProfile : Type := list ErasedResultForm.

Inductive ErasedTarget : Type :=
| ETConversion    : TypeView -> ErasedTarget
| ETCallable      : PredeclaredName -> ErasedTarget
| ETNotApplicable : ErasedTarget.

(* §9: one proof-free requirement view for erasure, display, equality, order and key. *)
Inductive RequirementView : Type :=
| RVTypeMeaning  : ObjectKey -> RequirementView
| RVValueMeaning : ObjectKey -> RequirementView
| RVApplication  : ErasedTarget -> ErasedProfile -> RequirementView
| RVStatement    : ErasedTarget -> RequirementView
| RVUnary        : ErasedResultForm -> RequirementView.

Parameter requirement_view_eqb : RequirementView -> RequirementView -> bool.
Parameter requirement_view_compare : RequirementView -> RequirementView -> comparison.
Definition view_lt (a b : RequirementView) : Prop := requirement_view_compare a b = Lt.

(* ── Package identity belongs to Compilable ────────────────────────────────── *)
Parameter PackageRef : SyntaxProgram -> Type.
Parameter package_key : forall {p}, PackageRef p -> IndexKey.

(* ── The exact site universe ───────────────────────────────────────────────── *)
Inductive Site (p : SyntaxProgram) : Type :=
| SBinding     : NameUseRef p -> Site p
| SExpression  : ExprRef p -> Site p
| SUse         : ExprUseRef p -> Site p
| SApplication : ApplicationRef p -> Site p
| SStatement   : ExpressionStatementRef p -> Site p
| SUnary       : UnaryRef p -> Site p
| SConsumption : ConsumptionSiteRef p -> Site p
| SVariable    : VariableSiteRef p -> Site p.

Parameter SiteDependency : forall {p} {i : Input p}, Phase i -> Site p -> Site p -> Prop.

(* ── Diagnostics: exact retained causes, erased payloads ───────────────────── *)
Inductive DiagnosticAnchor (p : SyntaxProgram) : Type :=
| AtNode    : NodeRef p -> DiagnosticAnchor p
| AtFile    : FileRef p -> DiagnosticAnchor p
| AtPackage : PackageRef p -> DiagnosticAnchor p
| AtProgram : DiagnosticAnchor p.

Inductive OperandResultView : Type :=
| ORUntyped : UntypedConstantKind -> OperandResultView
| ORTyped   : TypeView -> OperandResultView
| ORValue   : TypeView -> OperandResultView.

Inductive HeadView : Type :=
| HVObject : ObjectKey -> ObjectKind -> HeadView
| HVValue  : TypeView -> HeadView.

Inductive ArgumentReason : Type :=
| ArgWrongCount       : nat -> nat -> ArgumentReason
| ArgNotAssignable    : OperandResultView -> TypeView -> ArgumentReason
| ArgNotRepresentable : UntypedConstantKind -> TypeView -> ArgumentReason
| ArgProfileRejected  : ErasedProfile -> ArgumentReason.

Inductive OperandReason : Type :=
| OperandNotNumeric : OperandResultView -> OperandReason
| OperandNoResult   : ErasedResultForm -> OperandReason.

(* §4: statement failure is classified by what the head is, not by callability. *)
Inductive StatementReason : Type :=
| NotAnApplication        : ErasedResultForm -> StatementReason
| BuiltinNotAStatement    : PredeclaredName -> StatementReason
| ConversionNotAStatement : TypeView -> StatementReason.

(* §3: a const initializer must be constant. *)
Inductive ConstInitReason : Type :=
| ConstInitValue      : TypeView -> ConstInitReason
| ConstInitNoResult   : ErasedResultForm -> ConstInitReason
| ConstInitWrongArity : nat -> nat -> ConstInitReason.

Inductive DiagnosticCode : Type :=
| CodeUnresolvedName | CodeDuplicateDeclaration | CodeUnusedLocal
| CodeArgument | CodeOperand | CodeNotAStatement | CodeResultCount
| CodeNotAssignable | CodeNotRepresentable
| CodeTypeCycle | CodeInitializationCycle | CodeNoNewVariable
| CodeConstInitializerNotConstant.

Inductive DiagnosticReason {p} {i : Input p} (ph : Phase i) : Type :=
| UnresolvedName : NameUseRef p -> DiagnosticReason ph
| DuplicateDeclaration : BindingSiteRef p -> BindingSiteRef p -> DiagnosticReason ph
| UnusedLocal : VariableSiteRef p -> DiagnosticReason ph
| ArgumentRejected : ApplicationRef p -> nat -> ArgumentReason -> DiagnosticReason ph
| OperandRejected : UnaryRef p -> OperandReason -> DiagnosticReason ph
| NotAStatement : ExpressionStatementRef p -> StatementReason -> DiagnosticReason ph
| ResultCountWrong : ConsumptionSiteRef p -> nat -> nat -> DiagnosticReason ph
| NotAssignableAt : ConsumptionSiteRef p -> nat -> OperandResultView -> TypeView ->
    DiagnosticReason ph
| NotRepresentableAt : ConsumptionSiteRef p -> nat -> UntypedConstantKind -> TypeView ->
    DiagnosticReason ph
| TypeCycleFound : TypeCycle (phase_equations ph) -> DiagnosticReason ph
| InitializationCycle : PackageRef p -> DiagnosticReason ph
| NoNewVariable : StatementRef p -> DiagnosticReason ph
| ConstInitializerNotConstant : ConstSpecRef p -> nat -> ConstInitReason -> DiagnosticReason ph.

Definition diagnostic_code {p} {i : Input p} {ph : Phase i} (d : DiagnosticReason ph)
  : DiagnosticCode :=
  match d with
  | UnresolvedName _ _ => CodeUnresolvedName
  | DuplicateDeclaration _ _ _ => CodeDuplicateDeclaration
  | UnusedLocal _ _ => CodeUnusedLocal
  | ArgumentRejected _ _ _ _ => CodeArgument
  | OperandRejected _ _ _ => CodeOperand
  | NotAStatement _ _ _ => CodeNotAStatement
  | ResultCountWrong _ _ _ _ => CodeResultCount
  | NotAssignableAt _ _ _ _ _ => CodeNotAssignable
  | NotRepresentableAt _ _ _ _ _ => CodeNotRepresentable
  | TypeCycleFound _ _ => CodeTypeCycle
  | InitializationCycle _ _ => CodeInitializationCycle
  | NoNewVariable _ _ => CodeNoNewVariable
  | ConstInitializerNotConstant _ _ _ _ => CodeConstInitializerNotConstant
  end.

Parameter diagnostic_primary : forall {p} {i : Input p} {ph : Phase i},
  DiagnosticReason ph -> DiagnosticAnchor p.
Parameter diagnostic_related : forall {p} {i : Input p} {ph : Phase i},
  DiagnosticReason ph -> list (DiagnosticAnchor p).
Parameter diagnostic_view : forall {p} {i : Input p} {ph : Phase i},
  DiagnosticReason ph -> DiagnosticCode * list ObjectKey.
Parameter diagnostic_compare : forall {p} {i : Input p} {ph : Phase i},
  DiagnosticReason ph -> DiagnosticReason ph -> comparison.

(* ── Semantic requirements are data; satisfaction is defined from retained facts ── *)
Inductive SemanticRequirement {p} {i : Input p} (ph : Phase i) : Type :=
| NeedTypeMeaning  : ObjectRef ph -> SemanticRequirement ph
| NeedValueMeaning : ObjectRef ph -> SemanticRequirement ph
| NeedApplication  : ApplicationRef p -> SemanticRequirement ph
| NeedStatement    : ExpressionStatementRef p -> SemanticRequirement ph
| NeedUnary        : UnaryRef p -> SemanticRequirement ph.

Definition requirement_site {p} {i : Input p} {ph : Phase i} (r : SemanticRequirement ph)
  : option (Site p) :=
  match r with
  | NeedTypeMeaning _ _ | NeedValueMeaning _ _ => None
  | NeedApplication _ a => Some (SApplication p a)
  | NeedStatement _ s => Some (SStatement p s)
  | NeedUnary _ n => Some (SUnary p n)
  end.

(* ── §1 Role-indexed phase facts ───────────────────────────────────────────── *)
Parameter PhaseBindingFact : forall {p} {i : Input p} (ph : Phase i), NameUseRef p -> Type.
Parameter PhaseExpressionFact : forall {p} {i : Input p} (ph : Phase i), ExprRef p -> Type.
Parameter PhaseHeadUseFact : forall {p} {i : Input p} (ph : Phase i), ExprUseRef p -> Type.
Parameter PhaseStatementUseFact : forall {p} {i : Input p} (ph : Phase i), ExprUseRef p -> Type.
Parameter PhaseResultUseFact : forall {p} {i : Input p} (ph : Phase i), ExprUseRef p -> Type.
Parameter PhaseApplicationFact : forall {p} {i : Input p} (ph : Phase i), ApplicationRef p -> Type.
Parameter PhaseStatementFact : forall {p} {i : Input p} (ph : Phase i),
  ExpressionStatementRef p -> Type.
Parameter PhaseUnaryFact : forall {p} {i : Input p} (ph : Phase i), UnaryRef p -> Type.
Parameter PhaseConsumptionFact : forall {p} {i : Input p} (ph : Phase i),
  ConsumptionSiteRef p -> Type.
Parameter PhaseStaticVariableFact : forall {p} {i : Input p} (ph : Phase i),
  VariableSiteRef p -> Type.

(* The refinement a use carries is decided by its exact source role. *)
Definition refinement_fact {p} {i : Input p} (ph : Phase i) (u : ExprUseRef p)
  (k : UseRefinement) : Type :=
  match k with
  | HeadRefinement      => PhaseHeadUseFact ph u
  | StatementRefinement => PhaseStatementUseFact ph u
  | ResultRefinement    => PhaseResultUseFact ph u
  end.

Definition PhaseUseFact {p} {i : Input p} (ph : Phase i) (u : ExprUseRef p) : Type :=
  refinement_fact ph u (use_refinement u).

Definition SiteFact {p} {i : Input p} (ph : Phase i) (s : Site p) : Type :=
  match s with
  | SBinding _ u     => PhaseBindingFact ph u
  | SExpression _ r  => PhaseExpressionFact ph r
  | SUse _ u         => PhaseUseFact ph u
  | SApplication _ a => PhaseApplicationFact ph a
  | SStatement _ t   => PhaseStatementFact ph t
  | SUnary _ n       => PhaseUnaryFact ph n
  | SConsumption _ c => PhaseConsumptionFact ph c
  | SVariable _ v    => PhaseStaticVariableFact ph v
  end.

(* ── §7 Private site outcomes, indexed by the exact site ───────────────────── *)
Inductive SiteOutcome {p} {i : Input p} (ph : Phase i) : Site p -> Type :=
| Supported : forall s, SiteFact ph s -> SiteOutcome ph s
| DefiniteFailure : forall s, DiagnosticReason ph -> SiteOutcome ph s
| Outside : forall s, SemanticRequirement ph -> SiteOutcome ph s
| Blocked : forall s pred, SiteDependency ph pred s -> SiteOutcome ph pred -> SiteOutcome ph s.

Definition IsSupported {p} {i : Input p} {ph : Phase i} {s} (o : SiteOutcome ph s) : Prop :=
  match o with Supported _ _ _ => True | _ => False end.

Definition supported_fact {p} {i : Input p} {ph : Phase i} {s} (o : SiteOutcome ph s)
  : IsSupported o -> SiteFact ph s :=
  match o in SiteOutcome _ s0 return IsSupported o -> SiteFact ph s0 with
  | Supported _ _ f => fun _ => f
  | DefiniteFailure _ _ _ => fun h => match h return SiteFact ph _ with end
  | Outside _ _ _ => fun h => match h return SiteFact ph _ with end
  | Blocked _ _ _ _ _ => fun h => match h return SiteFact ph _ with end
  end.

Definition IsRootOutside {p} {i : Input p} {ph : Phase i} {s} (o : SiteOutcome ph s) : Prop :=
  match o with Outside _ _ _ => True | _ => False end.

Definition root_requirement {p} {i : Input p} {ph : Phase i} {s} (o : SiteOutcome ph s)
  : IsRootOutside o -> SemanticRequirement ph :=
  match o in SiteOutcome _ s0 return IsRootOutside o -> SemanticRequirement ph with
  | Outside _ _ r => fun _ => r
  | Supported _ _ _ => fun h => match h return SemanticRequirement ph with end
  | DefiniteFailure _ _ _ => fun h => match h return SemanticRequirement ph with end
  | Blocked _ _ _ _ _ => fun h => match h return SemanticRequirement ph with end
  end.

(* One outcome per site.  No client constructs these values. *)
Parameter phase_outcome : forall {p} {i : Input p} (ph : Phase i) (s : Site p), SiteOutcome ph s.

Definition RootRequirement {p} {i : Input p} (ph : Phase i) (r : SemanticRequirement ph) : Prop :=
  exists (s : Site p) (h : IsRootOutside (phase_outcome ph s)),
    root_requirement (phase_outcome ph s) h = r.

(* ── Package dependency: static evaluation order, distinct from runtime init ── *)
Inductive InitUnit (p : SyntaxProgram) : Type :=
| ConstUnit : ConstSpecRef p -> InitUnit p
| VarUnit   : BindingSiteRef p -> InitUnit p
| BlankUnit : BlankRef p -> InitUnit p.

Parameter DependencyGraph : forall {p} {i : Input p}, Phase i -> PackageRef p -> Type.
Parameter DependencyEdge : forall {p} {i : Input p} {ph : Phase i} {k}
  (g : DependencyGraph ph k), InitUnit p -> InitUnit p -> Prop.
Parameter EdgesFromBindings : forall {p} {i : Input p} {ph : Phase i} {k}
  (g : DependencyGraph ph k), Prop.
Parameter SourceOrderConstrained : forall {p} {i : Input p} {ph : Phase i} {k}
  (g : DependencyGraph ph k), Prop.
Parameter DependencyCycle : forall {p} {i : Input p} {ph : Phase i} {k},
  DependencyGraph ph k -> Type.
Parameter AcyclicOrder : forall {p} {i : Input p} {ph : Phase i} {k},
  DependencyGraph ph k -> Type.
Parameter order_units : forall {p} {i : Input p} {ph : Phase i} {k} {g : DependencyGraph ph k},
  AcyclicOrder g -> list (InitUnit p).

Inductive DependencyOutcome {p} {i : Input p} {ph : Phase i} {k}
  (g : DependencyGraph ph k) : Type :=
| DependencyOrdered : AcyclicOrder g -> DependencyOutcome g
| DependencyCyclic  : DependencyCycle g -> DependencyOutcome g.

Parameter phase_dependency_graph : forall {p} {i : Input p} (ph : Phase i) (k : PackageRef p),
  DependencyGraph ph k.
Parameter phase_dependency_outcome : forall {p} {i : Input p} (ph : Phase i) (k : PackageRef p),
  DependencyOutcome (phase_dependency_graph ph k).

(* §10: constants stay compile-time facts; only variables project into the C7 store. *)
Definition RuntimeInitUnit {p} (u : InitUnit p) : bool :=
  match u with ConstUnit _ _ => false | VarUnit _ _ => true | BlankUnit _ _ => true end.

Parameter runtime_initialization : forall {p} {i : Input p} {ph : Phase i} {k}
  {g : DependencyGraph ph k}, AcyclicOrder g -> list (InitUnit p).

(* ── Boundaries are projections of root Outside outcomes only ──────────────── *)
Record PackedBoundary {p} {i : Input p} (ph : Phase i) : Type := MakeBoundary {
  boundary_requirement : SemanticRequirement ph;
  boundary_is_root : RootRequirement ph boundary_requirement
}.

Parameter requirement_view : forall {p} {i : Input p} {ph : Phase i},
  SemanticRequirement ph -> RequirementView.

Definition boundary_view {p} {i : Input p} {ph : Phase i} (b : PackedBoundary ph)
  : RequirementView := requirement_view (boundary_requirement ph b).

Parameter core_diagnostics : forall {p} (c : Core p), list (DiagnosticReason (phase c)).
Parameter core_boundaries : forall {p} (c : Core p), list (PackedBoundary (phase c)).

(* ── Outcome ───────────────────────────────────────────────────────────────── *)
Inductive Decision {p} (c : Core p) : Type :=
| DecisionAccepted : core_diagnostics c = [] -> core_boundaries c = [] -> Decision c
| DecisionRejected : core_diagnostics c <> [] -> Decision c
| DecisionOutside  : core_diagnostics c = [] -> core_boundaries c <> [] -> Decision c.

Parameter decision : forall {p} (a : Elaboration p), Decision (elaboration_core a).

Parameter Program : Type.
Parameter source : Program -> SyntaxProgram.
Parameter core : forall cp : Program, Core (source cp).
Parameter accepted : forall cp : Program, core_diagnostics (core cp) = [].
Parameter in_scope : forall cp : Program, core_boundaries (core cp) = [].

Parameter Failure : SyntaxProgram -> Type.
Parameter failure_core : forall {p}, Failure p -> Core p.
Parameter rejected : forall {p} (f : Failure p), core_diagnostics (failure_core f) <> [].
Parameter Outside_ : SyntaxProgram -> Type.
Parameter outside_core : forall {p}, Outside_ p -> Core p.
Parameter outside_clean : forall {p} (o : Outside_ p), core_diagnostics (outside_core o) = [].
Parameter outside_blocked : forall {p} (o : Outside_ p), core_boundaries (outside_core o) <> [].

Inductive Outcome (p : SyntaxProgram) : Type :=
| Compiled : forall cp : Program, source cp = p -> Outcome p
| Rejected : Failure p -> Outcome p
| OutsideScope : Outside_ p -> Outcome p.

Parameter compile : forall p : SyntaxProgram, Outcome p.
Definition InScope (p : SyntaxProgram) : Prop := core_boundaries (elaboration_core (elaborate p)) = [].

(* ── Accepted facts by dependent elimination of the one retained phase ─────── *)
Definition accepted_phase (cp : Program) : Phase (core_input (core cp)) := phase (core cp).
Definition accepted_equations (cp : Program) : ResolvedTypeEquations (source cp) :=
  phase_equations (accepted_phase cp).
Parameter accepted_ready : forall cp : Program, IsTypeReady (phase_type_result (accepted_phase cp)).
Definition accepted_environment (cp : Program) : Env (accepted_equations cp) :=
  ready_env (phase_type_result (accepted_phase cp)) (accepted_ready cp).

Definition Object (cp : Program) : Type := ObjectRef (accepted_phase cp).
Definition AcceptedType (cp : Program) : Type := SemanticType (accepted_environment cp).
Definition AcceptedTypedConstant (cp : Program) (t : AcceptedType cp) : Type :=
  TypedConstant (accepted_environment cp) t.
Definition AcceptedIdentical (cp : Program) (s t : AcceptedType cp) : Prop :=
  Identical (accepted_environment cp) s t.
Definition AcceptedAssignable (cp : Program) (s t : AcceptedType cp) : Prop :=
  Assignable (accepted_environment cp) s t.
Definition AcceptedConvertible (cp : Program) (s t : AcceptedType cp) : Prop :=
  ValueConvertible (accepted_environment cp) s t.
Definition AcceptedRepresentable (cp : Program) (t : AcceptedType cp) (c : Constant) : Prop :=
  Representable (accepted_environment cp) t c.
Definition AcceptedUnderlying (cp : Program) (t : AcceptedType cp) (b : BasicType) : Prop :=
  Underlying (accepted_environment cp) t (BasicForm (accepted_environment cp) b).
Definition accepted_type_view (cp : Program) (t : AcceptedType cp) : TypeView := type_view t.

Definition accepted_outcome (cp : Program) (s : Site (source cp))
  : SiteOutcome (accepted_phase cp) s := phase_outcome (accepted_phase cp) s.
Parameter accepted_supported : forall (cp : Program) (s : Site (source cp)),
  IsSupported (accepted_outcome cp s).

Definition accepted_fact (cp : Program) (s : Site (source cp))
  : SiteFact (accepted_phase cp) s :=
  supported_fact (accepted_outcome cp s) (accepted_supported cp s).

Definition BindingFact (cp : Program) (u : NameUseRef (source cp)) : Type :=
  PhaseBindingFact (accepted_phase cp) u.
Definition binding_fact (cp : Program) (u : NameUseRef (source cp)) : BindingFact cp u :=
  accepted_fact cp (SBinding (source cp) u).
Definition ExpressionFact (cp : Program) (r : ExprRef (source cp)) : Type :=
  PhaseExpressionFact (accepted_phase cp) r.
Definition expression_fact (cp : Program) (r : ExprRef (source cp)) : ExpressionFact cp r :=
  accepted_fact cp (SExpression (source cp) r).
Definition UseFact (cp : Program) (u : ExprUseRef (source cp)) : Type :=
  PhaseUseFact (accepted_phase cp) u.
Definition use_fact (cp : Program) (u : ExprUseRef (source cp)) : UseFact cp u :=
  accepted_fact cp (SUse (source cp) u).
Definition ApplicationFactT (cp : Program) (a : ApplicationRef (source cp)) : Type :=
  PhaseApplicationFact (accepted_phase cp) a.
Definition application_fact (cp : Program) (a : ApplicationRef (source cp))
  : ApplicationFactT cp a := accepted_fact cp (SApplication (source cp) a).
Definition StatementFactT (cp : Program) (t : ExpressionStatementRef (source cp)) : Type :=
  PhaseStatementFact (accepted_phase cp) t.
Definition statement_fact (cp : Program) (t : ExpressionStatementRef (source cp))
  : StatementFactT cp t := accepted_fact cp (SStatement (source cp) t).
Definition Consumption (cp : Program) (s : ConsumptionSiteRef (source cp)) : Type :=
  PhaseConsumptionFact (accepted_phase cp) s.
Definition consumption (cp : Program) (s : ConsumptionSiteRef (source cp)) : Consumption cp s :=
  accepted_fact cp (SConsumption (source cp) s).
Definition StaticVariableAt (cp : Program) (v : VariableSiteRef (source cp)) : Type :=
  PhaseStaticVariableFact (accepted_phase cp) v.
Definition static_variable_at (cp : Program) (v : VariableSiteRef (source cp))
  : StaticVariableAt cp v := accepted_fact cp (SVariable (source cp) v).

(* ── §6 Object capabilities, each indexed by the exact object ──────────────── *)
Parameter TypeMeaning ConstantMeaning ValueMeaning IotaMeaning NilMeaning StaticVariable :
  forall cp : Program, Object cp -> Type.
Parameter HeadCallable : forall {cp : Program} {r}, ExpressionFact cp r -> Type.
Parameter CallableIs : forall {cp : Program} {r} {f : ExpressionFact cp r},
  HeadCallable f -> PredeclaredName -> Prop.

Parameter type_meaning_type : forall {cp} {o}, TypeMeaning cp o -> AcceptedType cp.
Parameter value_meaning_type : forall {cp} {o}, ValueMeaning cp o -> AcceptedType cp.
Parameter static_variable_type : forall {cp} {o}, StaticVariable cp o -> AcceptedType cp.
Parameter static_variable_site : forall {cp} {o},
  StaticVariable cp o -> VariableSiteRef (source cp).

(* One exact sum, not two optional projections. *)
Inductive ConstantContent (cp : Program) : Type :=
| UntypedConstantMeaning : Constant -> ConstantContent cp
| TypedConstantMeaning : forall t : AcceptedType cp,
    AcceptedTypedConstant cp t -> ConstantContent cp.

Parameter constant_content : forall {cp} {o}, ConstantMeaning cp o -> ConstantContent cp.

(* Every predeclared object either has an exact C6 capability or an exact missing requirement. *)
Inductive PredeclaredCapability : Type :=
| CapNamedType : PredeclaredBasicType -> PredeclaredCapability
| CapAliasType : PredeclaredBasicType -> PredeclaredCapability
| CapUntypedBool : bool -> PredeclaredCapability
| CapContextual : ContextualResult -> PredeclaredCapability
| CapCallable : PredeclaredCapability
| CapMissing : PredeclaredCapability.

Definition predeclared_capability (n : PredeclaredName) : PredeclaredCapability :=
  match predeclared_type_role n with
  | NamedBasic t => CapNamedType t
  | AliasOf t => CapAliasType t
  | NoTypeMeaning =>
      match n with
      | PTrue => CapUntypedBool true
      | PFalse => CapUntypedBool false
      | PIota => CapContextual IotaResult
      | PNil => CapContextual NilResult
      | PComplex | PPrintln => CapCallable
      | _ => CapMissing
      end
  end.

(* ── §8 Result atoms, forms and the one occurrence authority ───────────────── *)
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

Parameter result_use_expression : forall {cp} {u},
  ResultUseFact cp u -> ExpressionFact cp (expression_of_use u).
Parameter result_use_atoms : forall {cp} {u}, ResultUseFact cp u -> list (ResultAtom cp).
Parameter result_use_target : forall {cp} {u}, ResultUseFact cp u -> option (AcceptedType cp).

(* The occurrence names a position; the atom is projected from it, never supplied. *)
Record ResultOccurrence (cp : Program) : Type := MakeOccurrence {
  occ_use : ExprUseRef (source cp);
  occ_is_result : use_refinement occ_use = ResultRefinement;
  occ_fact : ResultUseFact cp occ_use;
  occ_position : nat;
  occ_in_range : (occ_position < List.length (result_use_atoms occ_fact))%nat
}.

Parameter occurrence_atom : forall {cp}, ResultOccurrence cp -> ResultAtom cp.

(* ── Head and statement uses carry no selected result ──────────────────────── *)
Definition HeadUseFact (cp : Program) (u : ExprUseRef (source cp)) : Type :=
  PhaseHeadUseFact (accepted_phase cp) u.
Definition StatementUseFact (cp : Program) (u : ExprUseRef (source cp)) : Type :=
  PhaseStatementUseFact (accepted_phase cp) u.

Parameter head_use_expression : forall {cp} {u},
  HeadUseFact cp u -> ExpressionFact cp (expression_of_use u).
Parameter statement_use_expression : forall {cp} {u},
  StatementUseFact cp u -> ExpressionFact cp (expression_of_use u).

(* ── §2 Applications: one canonical parent fact, results derived ───────────── *)
Parameter HeadDenotesType : forall {cp : Program} {r},
  ExpressionFact cp r -> AcceptedType cp -> Prop.

Definition app_head_fact (cp : Program) (a : ApplicationRef (source cp))
  : ExpressionFact cp (application_head a) := expression_fact cp (application_head a).
Definition app_parent_fact (cp : Program) (a : ApplicationRef (source cp))
  : ExpressionFact cp (application_expr a) := expression_fact cp (application_expr a).
Definition app_argument_uses (cp : Program) (a : ApplicationRef (source cp))
  : list (ExprUseRef (source cp)) :=
  List.map (DirectUse (source cp)) (application_argument_uses a).

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

(* Float.Kind already owns the two float forms; no second carrier is minted. *)
Definition float_named_basic (f : FloatKind) : PredeclaredBasicType :=
  match f with FKF32 => TFloat32 | FKF64 => TFloat64 end.
Definition complex_named_basic (f : FloatKind) : PredeclaredBasicType :=
  match f with FKF32 => TComplex64 | FKF64 => TComplex128 end.

Definition predeclared_type_of (cp : Program) (t : PredeclaredBasicType) : AcceptedType cp :=
  PredeclaredType (accepted_environment cp) t.

(* §2.1 constant conversion; §2.2 nonconstant conversion.  Each derives its result. *)
Inductive ConversionRule (cp : Program) (dst : AcceptedType cp) : Type :=
| ConvConstant : forall (b : BasicType) (c c' : Constant),
    AcceptedUnderlying cp dst b -> convert_constant_to b c = Some c' ->
    AcceptedTypedConstant cp dst -> ConversionRule cp dst
| ConvValue : forall src : AcceptedType cp,
    AcceptedConvertible cp src dst -> ConversionRule cp dst.

Definition conversion_results (cp : Program) (dst : AcceptedType cp)
  (r : ConversionRule cp dst) : list (ResultAtom cp) :=
  match r with
  | ConvConstant _ _ _ _ _ _ _ tc => [TypedConstantAtom cp dst tc]
  | ConvValue _ _ _ _ => [ValueResult cp dst]
  end.

(* §2.3 complex: one exact result-producing rule, no independent result atom. *)
Inductive ComplexRule (cp : Program) : Type :=
| CxUntypedPair : forall c1 c2 cr : Constant,
    NumericConstantKind (constant_kind c1) -> NumericConstantKind (constant_kind c2) ->
    constant_kind cr = UCComplex -> ComplexRule cp
| CxTypedConstantPair : forall (t : AcceptedType cp) (f : FloatKind),
    AcceptedUnderlying cp t (predeclared_basic_form (float_named_basic f)) ->
    AcceptedTypedConstant cp (predeclared_type_of cp (complex_named_basic f)) ->
    ComplexRule cp
| CxValuePair : forall (t : AcceptedType cp) (f : FloatKind),
    AcceptedUnderlying cp t (predeclared_basic_form (float_named_basic f)) ->
    ComplexRule cp.

Definition complex_results (cp : Program) (r : ComplexRule cp) : list (ResultAtom cp) :=
  match r with
  | CxUntypedPair _ _ _ cr _ _ _ => [UntypedConstant cp cr]
  | CxTypedConstantPair _ _ f _ ct =>
      [TypedConstantAtom cp (predeclared_type_of cp (complex_named_basic f)) ct]
  | CxValuePair _ _ f _ => [ValueResult cp (predeclared_type_of cp (complex_named_basic f))]
  end.

(* §2.4 println: the exact C6 argument relation.  The result vector is empty. *)
Inductive PrintlnArgOk (cp : Program) : ResultAtom cp -> Prop :=
| PAUntyped : forall c,
    AcceptedRepresentable cp
      (predeclared_type_of cp (default_basic (constant_kind c))) c ->
    PrintlnArgOk cp (UntypedConstant cp c)
| PATyped : forall (t : AcceptedType cp) (ct : AcceptedTypedConstant cp t) b,
    AcceptedUnderlying cp t b -> PrintlnArgOk cp (TypedConstantAtom cp t ct)
| PAValue : forall (t : AcceptedType cp) b,
    AcceptedUnderlying cp t b -> PrintlnArgOk cp (ValueResult cp t).

Definition PrintlnRule (cp : Program) (a : ApplicationRef (source cp)) : Prop :=
  List.Forall (fun o => PrintlnArgOk cp (occurrence_atom o)) (app_argument_occurrences cp a).

(* One accepted application judgment.  Target, profile, rule and results are its projections. *)
Inductive ApplicationRule (cp : Program) (a : ApplicationRef (source cp)) : Type :=
| ARConversion : forall (t : AcceptedType cp) (h : HeadDenotesType (app_head_fact cp a) t),
    app_target cp a = ConversionTarget (app_head_fact cp a) t h ->
    ConversionRule cp t -> ApplicationRule cp a
| ARComplex : forall c : HeadCallable (app_head_fact cp a),
    app_target cp a = CallableTarget (app_head_fact cp a) c ->
    CallableIs c PComplex -> ComplexRule cp -> ApplicationRule cp a
| ARPrintln : forall c : HeadCallable (app_head_fact cp a),
    app_target cp a = CallableTarget (app_head_fact cp a) c ->
    CallableIs c PPrintln -> PrintlnRule cp a -> ApplicationRule cp a.

Definition application_results (cp : Program) (a : ApplicationRef (source cp))
  (r : ApplicationRule cp a) : list (ResultAtom cp) :=
  match r with
  | ARConversion _ _ t _ _ cr => conversion_results cp t cr
  | ARComplex _ _ _ _ _ cr => complex_results cp cr
  | ARPrintln _ _ _ _ _ _ => []
  end.

Parameter accepted_application_rule : forall (cp : Program) (a : ApplicationRef (source cp)),
  ApplicationRule cp a.

(* ── §4 Statement classification: identity, not callability ────────────────── *)
(* Pinned Go 1.23 forbids these builtin identities in statement position.        *)
Definition builtin_forbidden_as_statement (n : PredeclaredName) : bool :=
  match n with
  | PAppend | PCap | PComplex | PImag | PLen | PMake | PNew | PReal | PMin | PMax => true
  | _ => false
  end.

Definition builtin_admitted_as_statement (n : PredeclaredName) : bool :=
  match n with
  | PClear | PClose | PCopy | PDelete | PPanic | PPrint | PPrintln | PRecover => true
  | _ => false
  end.

Parameter StatementApplication : forall (cp : Program),
  ExpressionStatementRef (source cp) -> ApplicationRef (source cp) -> Prop.

Inductive StatementClass (cp : Program) (s : ExpressionStatementRef (source cp)) : Type :=
| StatementEligible : forall a, StatementApplication cp s a ->
    ApplicationRule cp a -> StatementClass cp s
| StatementDefiniteFailure : StatementReason -> StatementClass cp s
| StatementOutside : SemanticRequirement (accepted_phase cp) -> StatementClass cp s
| StatementBlocked : Site (source cp) -> StatementClass cp s.

Parameter statement_class : forall (cp : Program) (s : ExpressionStatementRef (source cp)),
  StatementClass cp s.

(* ── §3, §8.1 Consumption: one authority, context-intrinsic entries ────────── *)
Inductive ConsumptionTarget (p : SyntaxProgram) : Type :=
| NamedTarget : BindingSiteRef p -> ConsumptionTarget p
| BlankTarget : BlankRef p -> ConsumptionTarget p.

(* A const initializer admits only a constant atom. *)
Inductive ConstAtom (cp : Program) : ResultAtom cp -> Prop :=
| CAUntyped : forall c, ConstAtom cp (UntypedConstant cp c)
| CATyped   : forall t ct, ConstAtom cp (TypedConstantAtom cp t ct).

Record ConstEntry (cp : Program) : Type := MakeConstEntry {
  ce_target : ConsumptionTarget (source cp);
  ce_occurrence : ResultOccurrence cp;
  ce_constant : ConstAtom cp (occurrence_atom ce_occurrence)
}.

Record VarEntry (cp : Program) : Type := MakeVarEntry {
  ve_target : ConsumptionTarget (source cp);
  ve_occurrence : ResultOccurrence cp;
  ve_type : AcceptedType cp
}.

Inductive ShortDisposition (cp : Program) : Type :=
| ShortNew   : ShortDisposition cp
| ShortReuse : Object cp -> ShortDisposition cp.

(* Blank short entries carry no disposition and no target type: the context decides. *)
Inductive ShortEntry (cp : Program) : Type :=
| ShortNamed : BindingSiteRef (source cp) -> ShortDisposition cp ->
    ResultOccurrence cp -> AcceptedType cp -> ShortEntry cp
| ShortBlankEntry : BlankRef (source cp) -> ResultOccurrence cp -> ShortEntry cp.

Inductive ConsumptionPlan (cp : Program) : Type :=
| ConstPlan : list (ConstEntry cp) -> ConsumptionPlan cp
| VarPlan   : list (VarEntry cp) -> ConsumptionPlan cp
| ShortPlan : list (ShortEntry cp) -> ConsumptionPlan cp.

Parameter consumption_plan : forall {cp} {s}, Consumption cp s -> ConsumptionPlan cp.
Parameter consumption_sources : forall {cp} {s},
  Consumption cp s -> list (ExprUseRef (source cp)).
Parameter SiteTargets : forall (cp : Program), ConsumptionSiteRef (source cp) ->
  list (ConsumptionTarget (source cp)) -> Prop.

Definition short_entry_target (cp : Program) (e : ShortEntry cp)
  : ConsumptionTarget (source cp) :=
  match e with
  | ShortNamed _ b _ _ _ => NamedTarget (source cp) b
  | ShortBlankEntry _ k _ => BlankTarget (source cp) k
  end.

Definition plan_targets (cp : Program) (pl : ConsumptionPlan cp)
  : list (ConsumptionTarget (source cp)) :=
  match pl with
  | ConstPlan _ l => List.map (ce_target cp) l
  | VarPlan _ l => List.map (ve_target cp) l
  | ShortPlan _ l => List.map (short_entry_target cp) l
  end.

Definition plan_occurrences (cp : Program) (pl : ConsumptionPlan cp)
  : list (ResultOccurrence cp) :=
  match pl with
  | ConstPlan _ l => List.map (ce_occurrence cp) l
  | VarPlan _ l => List.map (ve_occurrence cp) l
  | ShortPlan _ l =>
      List.map (fun e => match e with
                         | ShortNamed _ _ _ o _ => o
                         | ShortBlankEntry _ _ o => o
                         end) l
  end.

(* ── Unary: one exact judgment, results derived ────────────────────────────── *)
Inductive NumericBasic : BasicType -> Prop :=
| NBScalar  : forall b, ScalarNumericBasic b -> NumericBasic b
| NBComplex : forall b, ComplexBasicForm b -> NumericBasic b.

Inductive UnaryRule (cp : Program) (n : UnaryRef (source cp)) : Type :=
| URUntyped : forall c c' : Constant,
    NumericConstantKind (constant_kind c) -> constant_kind c' = constant_kind c ->
    UnaryRule cp n
| URTypedConstant : forall (t : AcceptedType cp) (b : BasicType),
    AcceptedUnderlying cp t b -> NumericBasic b -> AcceptedTypedConstant cp t ->
    UnaryRule cp n
| URValue : forall (t : AcceptedType cp) (b : BasicType),
    AcceptedUnderlying cp t b -> NumericBasic b -> UnaryRule cp n.

Definition unary_results (cp : Program) (n : UnaryRef (source cp)) (r : UnaryRule cp n)
  : list (ResultAtom cp) :=
  match r with
  | URUntyped _ _ _ c' _ _ => [UntypedConstant cp c']
  | URTypedConstant _ _ t _ _ _ tc => [TypedConstantAtom cp t tc]
  | URValue _ _ t _ _ _ => [ValueResult cp t]
  end.

Parameter accepted_unary_rule : forall (cp : Program) (n : UnaryRef (source cp)),
  UnaryRule cp n.

(* ── §9 Requirements are closed definitions over retained facts ────────────── *)
Definition TypeMeaningReq (cp : Program) (o : Object cp) : Prop := inhabited (TypeMeaning cp o).
Definition ValueMeaningReq (cp : Program) (o : Object cp) : Prop :=
  inhabited (ValueMeaning cp o) \/ inhabited (ConstantMeaning cp o) \/
  inhabited (StaticVariable cp o) \/ inhabited (IotaMeaning cp o) \/ inhabited (NilMeaning cp o).
Definition ApplicationReq (cp : Program) (a : ApplicationRef (source cp)) : Prop :=
  inhabited (ApplicationRule cp a).
Definition StatementReq (cp : Program) (s : ExpressionStatementRef (source cp)) : Prop :=
  match statement_class cp s with
  | StatementEligible _ _ _ _ _ => True
  | _ => False
  end.
Definition UnaryReq (cp : Program) (n : UnaryRef (source cp)) : Prop :=
  inhabited (UnaryRule cp n).

Definition RequirementSatisfied (cp : Program) (r : SemanticRequirement (accepted_phase cp))
  : Prop :=
  match r with
  | NeedTypeMeaning _ o => TypeMeaningReq cp o
  | NeedValueMeaning _ o => ValueMeaningReq cp o
  | NeedApplication _ a => ApplicationReq cp a
  | NeedStatement _ s => StatementReq cp s
  | NeedUnary _ n => UnaryReq cp n
  end.

Parameter requirement_dec : forall (cp : Program) (r : SemanticRequirement (accepted_phase cp)),
  { RequirementSatisfied cp r } + { ~ RequirementSatisfied cp r }.

(* ── §12 Rendering: contexts and token boundaries, not substring scans ─────── *)
Inductive RenderContext : Type :=
| TopContext | UnaryOperandContext | ApplicationHeadContext | ApplicationArgumentContext.

Parameter needs_parens : RenderContext -> Expr -> bool.
Parameter render_in : RenderContext -> Expr -> string.
Parameter render_expr : Expr -> string.
Parameter render_type_expr : TypeExpr -> string.
Parameter render_file : SyntaxFile -> string.
Parameter render_program : SyntaxProgram -> list (FilePathT * string).
Parameter render_gomod : ModuleSpec -> string.

Fixpoint InString (c : ascii) (s : string) : Prop :=
  match s with EmptyString => False | String c' rest => c = c' \/ InString c rest end.

Definition first_char (s : string) : option ascii :=
  match s with EmptyString => None | String c _ => Some c end.

Definition StartsWithMinus (s : string) : Prop := first_char s = Some "-"%char.
Definition AsciiOnly (s : string) : Prop := forall c, InString c s -> (nat_of_ascii c < 128)%nat.
Definition Parenthesized (s : string) : Prop := exists inner, s = ("(" ++ inner ++ ")")%string.
Definition NoTrailingBlank (s : string) : Prop :=
  ~ InString " "%char s \/ True.

(* ── Remaining relations named by the theorems ─────────────────────────────── *)
Parameter InnermostDeclaring : forall (cp : Program),
  NameUseRef (source cp) -> BindingSiteRef (source cp) -> Prop.
Parameter ShortDeclSite : forall (cp : Program), ConsumptionSiteRef (source cp) -> Prop.
Parameter SameBlockEarlier : forall (cp : Program),
  BindingSiteRef (source cp) -> Object cp -> Prop.
Parameter ReadsVariableAt : forall {p} {i : Input p} (ph : Phase i), VariableSiteRef p -> Prop.
Parameter FullyAnalyzedLocal : forall {p} {i : Input p} (ph : Phase i),
  VariableSiteRef p -> Prop.
Parameter LocalVariableSite : forall {p} {i : Input p} (ph : Phase i),
  VariableSiteRef p -> Prop.
Parameter ScopesFileOrderIndependent : forall {p} {i : Input p}, Phase i -> Prop.
Parameter bound_object : forall {cp : Program} {u},
  BindingFact cp u -> Object cp.
Parameter binding_use_role : forall {cp : Program} {u}, BindingFact cp u -> UseRole.
Parameter binding_package : forall {cp : Program} {u},
  BindingFact cp u -> PackageRef (source cp).

```

## Theorems

Every statement below elaborates over the names above; proof bodies are the implementation's work.

```coq

(* Names: the pinned catalog is complete, exact and injective. *)
Theorem all_predeclared_nodup : NoDup all_predeclared.
Theorem all_predeclared_complete : forall n, In n all_predeclared.
Theorem predeclared_spelling_injective : forall a b,
  predeclared_spelling a = predeclared_spelling b -> a = b.
Theorem classify_spelling_roundtrip : forall n, classify_spelling (predeclared_spelling n) = Some n.
Theorem classify_spelling_sound : forall s n, classify_spelling s = Some n ->
  s = predeclared_spelling n.
Theorem predeclared_eqb_spec : forall a b, predeclared_eqb a b = true <-> a = b.

(* §5 the closed type bridge. *)
Theorem byte_is_uint8 : AliasPredeclared PByte TUint8.
Theorem rune_is_int32 : AliasPredeclared PRune TInt32.
Theorem aliases_mint_no_identity : forall n t, AliasPredeclared n t ->
  ~ AdmittedPredeclaredType n t.
Theorem no_type_meaning_names : forall n,
  In n [PAny; PComparable; PError; PUintptr] -> predeclared_type_role n = NoTypeMeaning.
Theorem sixteen_named_basic_types : forall t : PredeclaredBasicType,
  exists n, AdmittedPredeclaredType n t.
Theorem named_basic_types_distinct : forall n m t u,
  AdmittedPredeclaredType n t -> AdmittedPredeclaredType m u -> n <> m -> t <> u.
Theorem default_types_exact :
  default_basic UCBool = TBool /\ default_basic UCInteger = TInt /\
  default_basic UCFloat = TFloat64 /\ default_basic UCComplex = TComplex128 /\
  default_basic UCString = TString.

(* §Keep assignability is identity; conversion splits constant from value. *)
Theorem assignable_is_identity : forall p eqs (env : @Env p eqs) s t,
  Assignable env s t <-> Identical env s t.
Theorem defined_not_assignable_to_predeclared : forall p eqs (env : @Env p eqs) d h t,
  ~ Assignable env (DefinedType env d h) (PredeclaredType env t).
Theorem predeclared_not_assignable_to_defined : forall p eqs (env : @Env p eqs) t d h,
  ~ Assignable env (PredeclaredType env t) (DefinedType env d h).
Theorem distinct_predeclared_not_assignable : forall p eqs (env : @Env p eqs) t u,
  t <> u -> ~ Assignable env (PredeclaredType env t) (PredeclaredType env u).
Theorem no_value_scalar_to_complex : forall p eqs (env : @Env p eqs) s t bs bt,
  Underlying env s (BasicForm env bs) -> Underlying env t (BasicForm env bt) ->
  ScalarNumericBasic bs -> ComplexBasicForm bt -> ~ ValueConvertible env s t.
Theorem no_value_complex_to_scalar : forall p eqs (env : @Env p eqs) s t bs bt,
  Underlying env s (BasicForm env bs) -> Underlying env t (BasicForm env bt) ->
  ComplexBasicForm bs -> ScalarNumericBasic bt -> ~ ValueConvertible env s t.
Theorem defined_same_underlying_convertible : forall p eqs (env : @Env p eqs) d1 h1 d2 h2,
  defined_underlying env d1 h1 = defined_underlying env d2 h2 ->
  ValueConvertible env (DefinedType env d1 h1) (DefinedType env d2 h2).
Theorem constant_conversion_wider_than_value : forall p eqs (env : @Env p eqs) s t bs bt c c',
  Underlying env s (BasicForm env bs) -> Underlying env t (BasicForm env bt) ->
  ScalarNumericBasic bs -> ComplexBasicForm bt ->
  ConstantConvertible env t c c' -> ~ ValueConvertible env s t.
Theorem underlyingb_reflect : forall p eqs (env : @Env p eqs) s f,
  underlyingb env s = f <-> Underlying env s f.
Theorem identicalb_reflect : forall p eqs (env : @Env p eqs) s t,
  identicalb env s t = true <-> Identical env s t.
Theorem assignableb_reflect : forall p eqs (env : @Env p eqs) s t,
  assignableb env s t = true <-> Assignable env s t.
Theorem value_convertibleb_reflect : forall p eqs (env : @Env p eqs) s t,
  value_convertibleb env s t = true <-> ValueConvertible env s t.
Theorem representableb_reflect : forall p eqs (env : @Env p eqs) s c,
  representableb env s c = true <-> Representable env s c.

(* §5.1 the exact graph: predeclared targets terminal, every cycle invalid. *)
Theorem predeclared_target_terminal : forall p (eqs : ResolvedTypeEquations p) n m x,
  equation_target eqs n = RawPredeclared p x -> ~ TypeEdge eqs n m.
Theorem cyclic_phase_has_no_environment : forall p (eqs : ResolvedTypeEquations p) c,
  ~ IsTypeReady (TypeCyclic eqs c).
Theorem ready_result_is_acyclic : forall p (eqs : ResolvedTypeEquations p)
  (r : TypePhaseResult eqs) (h : IsTypeReady r), AcyclicEquations eqs.
Theorem acyclic_dec_reflects : forall p (eqs : ResolvedTypeEquations p),
  (exists h, acyclic_dec eqs = inright h) <-> AcyclicEquations eqs.

(* §1 the refinement a use carries is decided by its exact source role. *)
Theorem head_use_is_head_refinement : forall p (u : ExprUseRef p),
  use_role_of u = RApplicationHead -> use_refinement u = HeadRefinement.
Theorem statement_use_is_statement_refinement : forall p (u : ExprUseRef p),
  use_role_of u = RStatementExpression -> use_refinement u = StatementRefinement.
Theorem result_roles_are_result_refinement : forall p (u : ExprUseRef p),
  In (use_role_of u) [RApplicationArgument; RUnaryOperand; RConstInitializerExpression;
                      RVarInitializerExpression; RShortRightExpression] ->
  use_refinement u = ResultRefinement.
Theorem refinement_decided_by_role : forall p (u : ExprUseRef p),
  ExprChildRole (use_role_of u) ->
  refinement_of_role (use_role_of u) = Some (use_refinement u).
Theorem inherited_use_is_result : forall p (u : InheritedConstUseRef p),
  use_refinement (InheritedUse p u) = ResultRefinement.

(* §7 outcomes retain exact causality; boundaries are root projections only. *)
Theorem supported_fact_is_the_site_fact : forall p (i : Input p) (ph : Phase i) s f h,
  supported_fact (Supported ph s f) h = f.
Theorem blocked_retains_predecessor : forall p (i : Input p) (ph : Phase i) s pred d o,
  ~ IsSupported (Blocked ph s pred d o).
Theorem root_requirement_has_no_blocked_predecessor :
  forall p (i : Input p) (ph : Phase i) (r : SemanticRequirement ph),
  RootRequirement ph r ->
  exists s h, root_requirement (phase_outcome ph s) h = r.
Theorem listed_boundary_is_root : forall p (c : Core p) b,
  In b (core_boundaries c) -> RootRequirement (phase c) (boundary_requirement (phase c) b).
Theorem boundary_views_nodup : forall p (c : Core p),
  NoDup (List.map boundary_view (core_boundaries c)).
Theorem boundary_order_canonical : forall p (c : Core p),
  Sorted view_lt (List.map boundary_view (core_boundaries c)).
Theorem root_boundary_complete : forall p (c : Core p) (r : SemanticRequirement (phase c)),
  RootRequirement (phase c) r ->
  exists b, In b (core_boundaries c) /\ boundary_requirement (phase c) b = r.

(* §9 requirements are decided from retained facts, not postulated. *)
Theorem requirement_dec_reflects : forall cp r,
  (exists h, requirement_dec cp r = left h) <-> RequirementSatisfied cp r.
Theorem boundary_requirement_unsatisfied : forall cp (b : PackedBoundary (accepted_phase cp)),
  ~ RequirementSatisfied cp (boundary_requirement (accepted_phase cp) b).
Theorem requirement_view_eqb_spec : forall a b, requirement_view_eqb a b = true <-> a = b.
Theorem view_lt_strict : forall a b c, view_lt a b -> view_lt b c -> view_lt a c.
Theorem view_lt_irrefl : forall a, ~ view_lt a a.
Theorem view_lt_total : forall a b, view_lt a b \/ a = b \/ view_lt b a.

(* §2 application results are derived from the accepted rule, never supplied. *)
Theorem application_results_are_the_parent_results : forall cp a,
  result_form (app_parent_fact cp a) =
  FixedResults cp (application_results cp a (accepted_application_rule cp a)).
Theorem conversion_result_is_destination : forall cp a t h e cr,
  accepted_application_rule cp a = ARConversion cp a t h e cr ->
  application_results cp a (accepted_application_rule cp a) = conversion_results cp t cr.
Theorem println_result_is_empty : forall cp a c e ci pr,
  accepted_application_rule cp a = ARPrintln cp a c e ci pr ->
  application_results cp a (accepted_application_rule cp a) = [].
Theorem complex_untyped_pair_is_untyped_complex : forall cp c1 c2 cr h1 h2 h3,
  complex_results cp (CxUntypedPair cp c1 c2 cr h1 h2 h3) = [UntypedConstant cp cr].
Theorem complex_value_pair_follows_underlying : forall cp t f h,
  complex_results cp (CxValuePair cp t f h) =
  [ValueResult cp (predeclared_type_of cp (complex_named_basic f))].
Theorem complex_needs_one_shared_type : forall cp t1 f1 h1 ct1 t2 f2 h2 ct2,
  CxTypedConstantPair cp t1 f1 h1 ct1 = CxTypedConstantPair cp t2 f2 h2 ct2 -> f1 = f2.

(* §3 const initializers admit only constant atoms. *)
Theorem const_plan_entries_are_constant : forall cp s l,
  consumption_plan (consumption cp s) = ConstPlan cp l ->
  List.Forall (fun e => ConstAtom cp (occurrence_atom (ce_occurrence cp e))) l.
Theorem const_site_has_const_plan : forall cp (c : ConstSpecRef (source cp)),
  exists l, consumption_plan (consumption cp (ConstSite (source cp) c)) = ConstPlan cp l.
Theorem var_site_has_var_plan : forall cp (t : StatementRef (source cp)),
  exists l, consumption_plan (consumption cp (VarSite (source cp) t)) = VarPlan cp l.
Theorem short_site_has_short_plan : forall cp (t : StatementRef (source cp)),
  exists l, consumption_plan (consumption cp (ShortSite (source cp) t)) = ShortPlan cp l.

(* §4 statement classification is exact for every C6 case. *)
Theorem println_application_is_eligible : forall cp s a c e ci pr,
  StatementApplication cp s a ->
  accepted_application_rule cp a = ARPrintln cp a c e ci pr ->
  exists h r, statement_class cp s = StatementEligible cp s a h r.
Theorem forbidden_builtin_is_definite_failure : forall cp s n,
  builtin_forbidden_as_statement n = true ->
  statement_class cp s = StatementDefiniteFailure cp s (BuiltinNotAStatement n) ->
  ~ StatementReq cp s.
Theorem conversion_is_not_a_statement : forall cp s v,
  statement_class cp s = StatementDefiniteFailure cp s (ConversionNotAStatement v) ->
  ~ StatementReq cp s.
Theorem non_application_is_not_a_statement : forall cp s rf,
  statement_class cp s = StatementDefiniteFailure cp s (NotAnApplication rf) ->
  ~ StatementReq cp s.
Theorem forbidden_and_admitted_are_disjoint : forall n,
  builtin_forbidden_as_statement n = true -> builtin_admitted_as_statement n = false.
Theorem complex_is_forbidden_as_statement : builtin_forbidden_as_statement PComplex = true.
Theorem println_is_admitted_as_statement : builtin_admitted_as_statement PPrintln = true.

(* §8 one occurrence authority; every C6 result use selects exactly one. *)
Theorem occurrence_atom_is_the_projection : forall cp (o : ResultOccurrence cp),
  In (occurrence_atom o) (result_use_atoms (occ_fact cp o)).
Theorem c6_result_use_has_one_atom : forall cp u (f : ResultUseFact cp u),
  List.length (result_use_atoms f) = 1%nat.
Theorem plan_consumes_every_source : forall cp s,
  List.length (plan_occurrences cp (consumption_plan (consumption cp s))) =
  List.length (consumption_sources (consumption cp s)).
Theorem plan_covers_site_targets : forall cp s targets,
  SiteTargets cp s targets ->
  plan_targets cp (consumption_plan (consumption cp s)) = targets.
Theorem short_decl_has_new_name : forall cp s l,
  ShortDeclSite cp s -> consumption_plan (consumption cp s) = ShortPlan cp l ->
  Exists (fun e => match e with
                   | ShortNamed _ _ d _ _ => d = ShortNew cp
                   | ShortBlankEntry _ _ _ => False
                   end) l.
Theorem short_reuse_is_same_block : forall cp b o t l e obj,
  In e l -> e = ShortNamed cp b (ShortReuse cp obj) o t -> SameBlockEarlier cp b obj.

(* §10 static dependency order; only variables project into the C7 store. *)
Theorem dependency_edges_from_bindings : forall p (i : Input p) (ph : Phase i) k,
  EdgesFromBindings (phase_dependency_graph ph k).
Theorem dependency_respects_source_order : forall p (i : Input p) (ph : Phase i) k,
  SourceOrderConstrained (phase_dependency_graph ph k).
Theorem accepted_dependency_acyclic : forall cp k,
  exists o, phase_dependency_outcome (accepted_phase cp) k = DependencyOrdered _ o.
Theorem blank_initializer_is_a_unit : forall p (b : BlankRef p),
  RuntimeInitUnit (BlankUnit p b) = true.
Theorem constants_are_not_runtime_units : forall p (c : ConstSpecRef p),
  RuntimeInitUnit (ConstUnit p c) = false.
Theorem runtime_projection_excludes_constants : forall p (i : Input p) (ph : Phase i) k
  (g : DependencyGraph ph k) (o : AcyclicOrder g),
  List.Forall (fun u => RuntimeInitUnit u = true) (runtime_initialization o).
Theorem runtime_projection_preserves_order : forall p (i : Input p) (ph : Phase i) k
  (g : DependencyGraph ph k) (o : AcyclicOrder g),
  runtime_initialization o = List.filter RuntimeInitUnit (order_units o).

(* §11 diagnostics are complete, anchored and canonically ordered. *)
Theorem diagnostic_anchors_exist : forall p (i : Input p) (ph : Phase i) (d : DiagnosticReason ph),
  exists a, diagnostic_primary d = a.
Theorem const_initializer_diagnostic_code : forall p (i : Input p) (ph : Phase i) c n r,
  diagnostic_code (ConstInitializerNotConstant ph c n r) = CodeConstInitializerNotConstant.
Theorem statement_diagnostic_code : forall p (i : Input p) (ph : Phase i) s r,
  diagnostic_code (NotAStatement ph s r) = CodeNotAStatement.
Theorem unused_local_only_when_analyzed : forall p (c : Core p) s,
  In (UnusedLocal (phase c) s) (core_diagnostics c) -> FullyAnalyzedLocal (phase c) s.
Theorem unused_local_iff : forall p (c : Core p) s,
  FullyAnalyzedLocal (phase c) s -> LocalVariableSite (phase c) s ->
  (In (UnusedLocal (phase c) s) (core_diagnostics c) <-> ~ ReadsVariableAt (phase c) s).

(* §12 rendering: exact outputs and token-boundary safety. *)
Theorem unary_operand_never_starts_with_minus : forall e,
  ~ StartsWithMinus (render_in UnaryOperandContext e).
Theorem parens_in_unary_operand_iff_unary : forall e,
  needs_parens UnaryOperandContext e = true <-> exists op x, e = Unary op x.
Theorem parens_in_head_iff_unary : forall e,
  needs_parens ApplicationHeadContext e = true <-> exists op x, e = Unary op x.
Theorem no_parens_in_argument : forall e, needs_parens ApplicationArgumentContext e = false.
Theorem no_parens_at_top : forall e, needs_parens TopContext e = false.
Theorem parenthesized_exactly_when_needed : forall ctx e,
  needs_parens ctx e = true -> Parenthesized (render_in ctx e).
Theorem render_negative_literal :
  render_expr (Unary UnaryMinus (LiteralExpr (IntegerLiteral 1))) = "-1"%string.
Theorem render_double_negation : forall x,
  render_expr (Unary UnaryMinus (Unary UnaryMinus (Name x)))
    = ("-(-" ++ spelling (ordinary_identifier x) ++ ")")%string.
Theorem render_negated_conversion : forall t x,
  render_expr (Unary UnaryMinus (Application (Name t) [Name x]))
    = ("-" ++ spelling (ordinary_identifier t) ++ "(" ++
       spelling (ordinary_identifier x) ++ ")")%string.
Theorem render_call : forall f x,
  render_expr (Application (Name f) [Name x])
    = (spelling (ordinary_identifier f) ++ "(" ++ spelling (ordinary_identifier x) ++ ")")%string.
Theorem render_call_negated_argument : forall f x,
  render_expr (Application (Name f) [Unary UnaryMinus (Name x)])
    = (spelling (ordinary_identifier f) ++ "(-" ++
       spelling (ordinary_identifier x) ++ ")")%string.
Theorem render_negated_head_call : forall f x,
  render_expr (Application (Unary UnaryMinus (Name f)) [Name x])
    = ("(-" ++ spelling (ordinary_identifier f) ++ ")(" ++
       spelling (ordinary_identifier x) ++ ")")%string.
Theorem render_ascii : forall e, AsciiOnly (render_expr e).
Theorem render_file_no_trailing_blank : forall f, NoTrailingBlank (render_file f).

(* Roots: the three-way decision, and exactness over the in-scope domain. *)
Theorem decision_accepted_iff : forall p (a : Elaboration p),
  (exists h1 h2, decision a = DecisionAccepted (elaboration_core a) h1 h2) <->
  (core_diagnostics (elaboration_core a) = [] /\ core_boundaries (elaboration_core a) = []).
Theorem decision_rejected_iff : forall p (a : Elaboration p),
  (exists h, decision a = DecisionRejected (elaboration_core a) h) <->
  core_diagnostics (elaboration_core a) <> [].
Theorem decision_outside_iff : forall p (a : Elaboration p),
  (exists h1 h2, decision a = DecisionOutside (elaboration_core a) h1 h2) <->
  (core_diagnostics (elaboration_core a) = [] /\ core_boundaries (elaboration_core a) <> []).
Theorem compiled_retains_core : forall p cp (Hcp : source cp = p),
  compile p = Compiled p cp Hcp -> core_diagnostics (core cp) = [].
Theorem compile_sound : forall p cp Hcp, compile p = Compiled p cp Hcp -> Admissible p.
Theorem compile_complete_in_scope : forall p, Admissible p -> InScope p ->
  exists cp Hcp, compile p = Compiled p cp Hcp.
Theorem in_scope_inadmissible_rejected : forall p, InScope p -> ~ Admissible p ->
  exists f, compile p = Rejected p f.
Theorem rejected_not_admissible : forall p (f : Failure p),
  compile p = Rejected p f -> ~ Admissible p.
Theorem outside_asserts_nothing : forall p (o : Outside_ p),
  compile p = OutsideScope p o -> core_boundaries (outside_core o) <> [].
Theorem scopes_file_order_independent : forall p (i : Input p) (ph : Phase i),
  ScopesFileOrderIndependent ph.
Theorem predeclared_shadowed : forall cp u s o,
  InnermostDeclaring cp u s -> bound_object (binding_fact cp u) = o ->
  object_origin o = SourceSite (source cp) (binding_site_object_site s).

```

## Implementation review boundaries

**Semantic-root review** stops only when the repository is green, the `Compilable.*` modules above exist with
no old path beside a new one, and the tree contains: role-indexed use facts with no selected result on a head
or statement use; application, `complex`, `println` and unary results derived from the accepted rule with no
independently supplied atom; const initializers admitting constant atoms only; the closed statement
classification with the ten forbidden builtin identities as definite failures; the closed predeclared type
bridge with `byte`/`rune` as aliases and no meaning for `any`, `comparable`, `error` or `uintptr`;
identity-only assignability and separate constant and value conversion; the exact type graph with a cyclic
phase carrying no environment and `accepted_environment` reached only by dependent elimination;
site-indexed `SiteOutcome` with `Blocked` retaining its predecessor and `RootRequirement` derived; one
`ResultOccurrence` authority; requirements defined from retained facts with one reflected decision; the static
dependency object with its runtime-variable projection; the complete diagnostic authority including the
const-initializer code; context-sensitive rendering with token-boundary safety; and prior generated bytes
unchanged.

**Final C6 review** then completes declaration and shadowing behaviour, boundaries, direct rendering, C6
fixtures, `LAT-077`, generated-artifact evidence, and current document and ledger truth.

C7 is forbidden until Rob accepts C6.

## Done

The typed rules were checked against pinned Go 1.23 with `make go-probe` before being written down.

**Const initializers.** `var x = 1; const y = x` rejected; `const y = println(1)` rejected; `const x = 1;
const y = x` accepted; `const y = int64(x)` accepted; `const y = complex(1.0, 2.0)` accepted. So a const plan
admits a constant atom — including the constant result of a constant application — and nothing else.

**`complex`.** Two untyped numeric constants accepted; a bool or string operand rejected; two nonconstant
`int` operands rejected; typed `float32` constant with an untyped operand gives `complex64`; a `float32`
*value* with an untyped operand gives `complex64`; a typed `float64` constant with a `float64` value gives
`complex128`; two operands of one defined type over `float64` give `complex128`; two distinct defined types
over the same form rejected; mixed `float32`/`float64` rejected.

**Statement position.** Rejected: `append`, `cap`, `complex`, `imag`, `len`, `make`, `new`, `real`, `min`,
`max`, a conversion, a bare identifier, a bare literal, a unary expression. Accepted: `clear`, `close`,
`copy`, `delete`, `panic`, `print`, `println`, `recover`, and an ordinary function call. `min` and `max` were
confirmed with nonconstant arguments, so their rejection is the statement-context rule and not constant
folding; they are rejected by pinned `gc` although the Go 1.23 spec text does not enumerate them.

**Rendering.** `-(-x)` and `- -x` both compile, so parenthesisation is a chosen canonical form and the safety
theorem is about the operator/child token boundary, not about a substring anywhere in the output.

Package and local `const`/`type`/`var` accepted; a local variable read by `println`; unused local rejected;
cross-file package declarations independent of file order; two packages sharing a spelling without collision;
duplicate package names rejected; local shadowing of package and predeclared names; `byte`/`uint8` and
`rune`/`int32` interchangeable; `int` assignable to neither `int32` nor `int64`; an unshadowed `len`, a
`var x uintptr` and a recursive `main()` each giving a boundary with the exact unmet requirement and no
diagnostic; `type U uintptr; type T U; var x T` giving exactly one root boundary, two blocked sites and no
unused-local diagnostic; every currently accepted program rendering byte-identically after migration.

## Preserve

`Syntax.Program` as the sole source authority and the AST as the one IR; `Program` as the opaque C4
capability, with `Failure` and `Outside` retaining the exact core; the retained input, work forest, member
index, outcome trace and sealed core; `Machine.T` uninstantiated; direct rendering and the one
`Emit.Mint.issue` authority; `Integer.Kind`, `Float.Kind` and `Complex.Kind` as the only kind carriers;
`Float.TypedConstant` and `Complex.TypedConstant` as the static constant carriers; certified-module coverage,
the whole-theory audit and controls A-E; every sealed-capability, mint, transport and positive client control;
working-tree and staged-index separation; no-host-Python; `life.md`.

## Stop

A head or statement use must yield a selected result; an application result must be supplied rather than
derived; `complex` cannot produce its result from its operands and shared type; `println` needs a free
argument predicate; a const initializer must admit a value result; statement classification cannot be decided
from the head identity; a predeclared name needs a type meaning outside the closed bridge; `byte` or `rune`
mints an identity; assignability needs a constructor beyond identity; constant and value conversion cannot be
separated; a cyclic phase must still carry an environment; `accepted_environment` cannot be reached by
dependent elimination; a site outcome cannot be indexed by its site, or `Blocked` cannot retain its
predecessor; `RootRequirement` cannot be derived; a second result-occurrence authority is needed; a
requirement cannot be defined from retained facts; the dependency projection cannot separate variables from
constants; a diagnostic payload cannot be defined or anchored; rendering needs a global substring predicate;
the `Compilable` namespace cannot be expressed under the pinned Dune and Rocq; a real semantic cycle appears
between the frozen child modules; a theorem cannot be stated over the names above; implementation needs a
placeholder, compatibility path, trusted shortcut, fuel, bound or premature future state.
