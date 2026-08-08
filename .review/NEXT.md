# C6 — the static semantic foundation

Review: contract

Goal: ordinary source names acquire meaning only through binding. Every predeclared spelling is a legal
source identifier and may be shadowed; blank is not an identifier at all. C6 lands the pinned predeclared
catalog, a closed type algebra with named predeclared types, exact constants, role-indexed use facts, rules
that consume their exact operands, one result-occurrence authority, compiler-owned static variable identity,
the static package dependency object, and a three-way decision that never calls unmodelled Go a rejection.

**C6 is entirely static.** No `Runtime`, value, place, store, environment or `Machine.T`; C7 introduces them
as one vertical and materializes package **variables** only — constants stay compile-time facts.

The declarations below are the published surface **verbatim**: `make contract-surface` elaborates exactly
this text under the pinned Rocq. Names are written unqualified, as they elaborate. Its typed rules were
checked against pinned Go 1.23 with `make go-probe`, and the module namespace with `make ns-probe`, before
being written down; both are in §Done.

## Ownership and physical modules

`ARCHITECTURE.md` owns the ownership law and the physical-structure doctrine; `ROADMAP.md` owns the milestone
sequence. `make ns-probe` confirms the pinned Dune and Rocq accept this shape.

| module | owns |
|---|---|
| `Compilable.Bindings` | `PackageRef`, scopes, object identity, binder/object sites, blank/new/reuse disposition, name binding, the predeclared outer scope and shadowing |
| `Compilable.TypeResolution` | exact type equations, the graph decision, the sealed `TypeReady` and its environment, object-indexed type meanings, predeclared/alias/definition resolution |
| `Compilable.Dependencies` | package const/var dependency nodes, edges, cycle/acyclic outcome, retained order, the runtime-variable projection |
| `Compilable.Expressions` | expression facts, role-indexed use facts, result occurrences, unary/application rules, statement classification, object-indexed capabilities |
| `Compilable.Results` | const/var/short consumption plans, binder finalization, exact `StaticVariable`, unused-local facts |
| `Compilable.Report` | site failures, diagnostics, site requirements, reflected satisfaction, boundaries, root/blocked reporting, canonical lists |
| `Compilable.v` | phase composition, whole-program preflight, `Core`, `Elaboration`, `Decision`, `Program`/`Failure`/`Outside`, `Outcome`, `elaborate`, `compile` |
| `Compilable.Evidence` | certified accepted/rejected/outside fixtures and controls; no production module imports it |

`Bindings` precedes `TypeResolution`, `Dependencies` and `Expressions`; `Expressions` precedes `Results`;
`Results` and `Dependencies` precede `Report`; `Report` precedes `Compilable.v`; `Compilable.v` precedes
`Evidence`. No child imports `Compilable.v`.

## Diagnostic migration

Every current public diagnostic survives with its code, primary anchor, related anchors and erasure. Those
with one exact failing site move under `AtSiteFailure`; the package- and program-level reasons keep their own
constructors because they have no single site.

| current public constructor | C6 form |
|---|---|
| `InvalidConversion` | `AtSiteFailure (SApplication a) (FInvalidConversion …)`, retaining the exact application, operand view, target view and outer context |
| `DefaultNotRepresentable` | `AtSiteFailure (SExpression r) (FDefaultNotRepresentable …)`, retaining the exact expression, constant kind and default target |
| `MainRedeclared` | `MainRedeclared later earlier` — unchanged; both object sites retained |
| `MissingMainEntry` | `MissingMainEntry k` — unchanged; the exact `PackageRef` retained |
| `BuildOutputIsDirectory` | `BuildOutputIsDirectory k name` — unchanged |
| `AtNode`/`AtFile`/`AtPackage`/`AtProgram` | retained exactly |
| `diagnostic_code`/`diagnostic_primary`/`diagnostic_related`/`erase_diagnostic` | retained, with `erase_diagnostic_code` and `erase_diagnostic_primary` |

C6 adds, and does not replace: unresolved name, duplicate declaration, argument, operand, not-a-statement,
result count, not-assignable, not-representable, const-initializer-not-constant, no-new-variable, unused
local, type cycle and initialization cycle.

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

(* An ordinary identifier excludes blank and nothing else.  Every predeclared spelling is a legal source
   name and may be shadowed; its meaning comes only from binding. *)
Record OrdinaryIdentifier : Type := MakeOrdinary {
  ordinary_identifier : Identifier;
  ordinary_not_blank : spelling ordinary_identifier <> "_"%string
}.

(* Collections owns NonEmpty; Float owns NonNegativeDecimal. *)
Record NonEmpty (A : Type) : Type := MakeNonEmpty { ne_first : A; ne_rest : list A }.
Record NonNegativeDecimal : Type := MakeNonNegDecimal {
  nnd_decimal : Decimal; nnd_nonneg : (0 <= coefficient nnd_decimal)%Z
}.

(* ── Syntax ────────────────────────────────────────────────────────────────── *)
Inductive BindingName : Type := Named (n : OrdinaryIdentifier) | Blank.
Inductive UnaryOp : Type := UnaryMinus.

(* Magnitudes only: a negative source value is exactly one `Unary UnaryMinus` over a nonnegative literal. *)
Inductive Literal : Type :=
| IntegerLiteral (n : N)
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

(* Both alias and definition admit blank; a blank type spec creates no object and no type identity. *)
Inductive TypeSpec : Type :=
| AliasSpec (name : BindingName) (target : TypeExpr)
| DefSpec (name : BindingName) (target : TypeExpr).

(* Pinned Go accepts `const ()`, `var ()` and `type ()`, so a spec group is a list.  Name lists and explicit
   initializer expression lists stay nonempty. *)
Inductive Declaration : Type :=
| ConstDecl (specs : list ConstSpec)
| VarDecl (specs : list VarSpec)
| TypeDecl (specs : list TypeSpec).

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

(* In Type, not Prop: the refinement is a dependent elimination of this witness, so it carries data. *)
Inductive ExprChildRole : Role -> Type :=
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
(* A package-level var spec is not a statement, and no generic statement can pass for a short declaration. *)
Parameter VarSpecRef ShortDeclRef : SyntaxProgram -> Type.

(* Consumption sites are intrinsically context-tagged: no optional field decides the context. *)
Inductive ConsumptionSiteRef (p : SyntaxProgram) : Type :=
| ConstSite : ConstSpecRef p -> ConsumptionSiteRef p
| VarSite   : VarSpecRef p -> ConsumptionSiteRef p
| ShortSite : ShortDeclRef p -> ConsumptionSiteRef p.

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

(* Total on the expression-child-role proof, so there is no fallback and no impossible case: a role that is
   not an expression-child role cannot reach this function at all. *)
Definition refinement_of_child_role {r : Role} (h : ExprChildRole r) : UseRefinement :=
  match h with
  | ECApplicationHead  => HeadRefinement
  | ECStatement        => StatementRefinement
  | ECConstInitializer | ECVarInitializer | ECShortRight | ECUnaryOperand | ECApplicationArg =>
      ResultRefinement
  end.

Definition use_refinement {p} (u : ExprUseRef p) : UseRefinement :=
  match u with
  | DirectUse _ d    => refinement_of_child_role (direct_is_expr_child d)
  | InheritedUse _ _ => ResultRefinement
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

(* The exact resolution an equation node reaches.  An alias mints no identity, so it resolves to whatever
   its target resolves to; a definition resolves to itself. *)
Inductive Resolution (p : SyntaxProgram) : Type :=
| ResolvedBasic   : PredeclaredBasicType -> Resolution p
| ResolvedDefined : BoundDefinedTypeRef p -> Resolution p.

Parameter ResolvesTo : forall {p} (eqs : ResolvedTypeEquations p),
  TypeNode p -> Resolution p -> Prop.

(* Sealed: there is no public constructor, so the only `TypeReady` is the one the phase built, and an
   environment cannot exist apart from the exact graph decision that produced it. *)
Parameter TypeReady : forall {p}, ResolvedTypeEquations p -> Type.
Parameter ready_acyclic : forall {p} {eqs : ResolvedTypeEquations p},
  TypeReady eqs -> AcyclicEquations eqs.
Parameter Env : forall {p} {eqs : ResolvedTypeEquations p}, TypeReady eqs -> Type.
Parameter ready_environment : forall {p} {eqs : ResolvedTypeEquations p} (r : TypeReady eqs), Env r.

Parameter DefinedInEnv : forall {p} {eqs : ResolvedTypeEquations p} {r : TypeReady eqs},
  Env r -> BoundDefinedTypeRef p -> Prop.
Parameter defined_key : forall {p}, BoundDefinedTypeRef p -> IndexKey.

Inductive TypeForm {p} {eqs : ResolvedTypeEquations p} {r : TypeReady eqs} (env : Env r) : Type :=
| BasicForm : BasicType -> TypeForm env.

Inductive SemanticType {p} {eqs : ResolvedTypeEquations p} {r : TypeReady eqs} (env : Env r) : Type :=
| PredeclaredType : PredeclaredBasicType -> SemanticType env
| DefinedType     : forall d : BoundDefinedTypeRef p, DefinedInEnv env d -> SemanticType env.

Parameter defined_underlying : forall {p} {eqs : ResolvedTypeEquations p} {r : TypeReady eqs} (env : Env r)
  (d : BoundDefinedTypeRef p), DefinedInEnv env d -> BasicType.

Definition type_view {p} {eqs : ResolvedTypeEquations p} {r : TypeReady eqs} {env : Env r}
  (t : SemanticType env) : TypeView :=
  match t with
  | PredeclaredType _ b => PredeclaredView b
  | DefinedType _ d _ => DefinedView (defined_key d)
  end.

Inductive Underlying {p} {eqs : ResolvedTypeEquations p} {r : TypeReady eqs} (env : Env r)
  : SemanticType env -> TypeForm env -> Prop :=
| UnderlyingPredeclared : forall t,
    Underlying env (PredeclaredType env t) (BasicForm env (predeclared_basic_form t))
| UnderlyingDefined : forall d h,
    Underlying env (DefinedType env d h) (BasicForm env (defined_underlying env d h)).

(* Identity is generated: name for predeclared, exact declaration reference for defined. *)
Inductive Identical {p} {eqs : ResolvedTypeEquations p} {r : TypeReady eqs} (env : Env r)
  : SemanticType env -> SemanticType env -> Prop :=
| IdenticalPredeclared : forall t, Identical env (PredeclaredType env t) (PredeclaredType env t)
| IdenticalDefined : forall d h1 h2,
    Identical env (DefinedType env d h1) (DefinedType env d h2).

(* §Keep: C6 typed assignability is identity. *)
Inductive Assignable {p} {eqs : ResolvedTypeEquations p} {r : TypeReady eqs} (env : Env r)
  : SemanticType env -> SemanticType env -> Prop :=
| AssignIdentical : forall s t, Identical env s t -> Assignable env s t.

(* The nonconstant conversion authority, strictly narrower than constant conversion. *)
Inductive ValueConvertible {p} {eqs : ResolvedTypeEquations p} {r : TypeReady eqs} (env : Env r)
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

Inductive Representable {p} {eqs : ResolvedTypeEquations p} {r : TypeReady eqs} (env : Env r)
  : SemanticType env -> Constant -> Prop :=
| RepresentableAt : forall s b c,
    Underlying env s (BasicForm env b) -> FitsBasic b c -> Representable env s c.

Inductive ConstantConvertible {p} {eqs : ResolvedTypeEquations p} {r : TypeReady eqs} (env : Env r)
  : SemanticType env -> Constant -> Constant -> Prop :=
| CConvExact : forall s b c c',
    Underlying env s (BasicForm env b) -> convert_constant_to b c = Some c' ->
    ConstantConvertible env s c c'.

Inductive TypedConstant {p} {eqs : ResolvedTypeEquations p} {r : TypeReady eqs} (env : Env r)
  (s : SemanticType env) : Type :=
| TypedOf : forall b, Underlying env s (BasicForm env b) -> BasicTypedConstant b -> TypedConstant env s.

Parameter underlyingb : forall {p} {eqs : ResolvedTypeEquations p} {r : TypeReady eqs} (env : Env r),
  SemanticType env -> TypeForm env.
Parameter identicalb assignableb value_convertibleb :
  forall {p} {eqs : ResolvedTypeEquations p} {r : TypeReady eqs} (env : Env r),
    SemanticType env -> SemanticType env -> bool.
Parameter representableb : forall {p} {eqs : ResolvedTypeEquations p} {r : TypeReady eqs} (env : Env r),
  SemanticType env -> Constant -> bool.

Definition default_type {p} {eqs : ResolvedTypeEquations p} {r : TypeReady eqs} (env : Env r)
  (k : UntypedConstantKind) : SemanticType env :=
  PredeclaredType env (default_basic k).

Parameter AliasResolvesTo : forall {p} {eqs : ResolvedTypeEquations p} {r : TypeReady eqs} (env : Env r),
  AliasSpecRef p -> SemanticType env -> Prop.

Inductive ResolvedTypeTarget {p} {eqs : ResolvedTypeEquations p} {r : TypeReady eqs} (env : Env r)
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
| PhaseReady  : TypeReady eqs -> TypePhaseResult eqs
| PhaseCyclic : TypeCycle eqs -> TypePhaseResult eqs.

Definition IsTypeReady {p} {eqs : ResolvedTypeEquations p} (res : TypePhaseResult eqs) : Prop :=
  match res with PhaseReady _ _ => True | PhaseCyclic _ _ => False end.

Definition ready_of {p} {eqs : ResolvedTypeEquations p} (res : TypePhaseResult eqs)
  : IsTypeReady res -> TypeReady eqs :=
  match res return IsTypeReady res -> TypeReady eqs with
  | PhaseReady _ r  => fun _ => r
  | PhaseCyclic _ _ => fun h => match h return TypeReady eqs with end
  end.

Parameter Phase : forall {p}, Input p -> Type.
Parameter phase : forall {p} (core : Core p), Phase (core_input core).
Parameter phase_equations : forall {p} {i : Input p} (ph : Phase i), ResolvedTypeEquations p.
Parameter phase_type_result : forall {p} {i : Input p} (ph : Phase i),
  TypePhaseResult (phase_equations ph).

(* ── Objects ───────────────────────────────────────────────────────────────── *)
Inductive ObjectKind : Type :=
| TypeObject | ConstantObject | VariableObject | FunctionObject | BuiltinObject | NilObject.

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
  | PNil => NilObject
  | PAppend | PCap | PClear | PClose | PComplex | PCopy | PDelete | PImag | PLen | PMake
  | PMax | PMin | PNew | PPanic | PPrint | PPrintln | PReal | PRecover => BuiltinObject
  end.

Parameter object_kind : forall {p} {i : Input p} {ph : Phase i}, ObjectRef ph -> ObjectKind.

(* ── Erased, proof-free views ──────────────────────────────────────────────── *)
Inductive ErasedAnchor : Type :=
| EAtNode : IndexKey -> ErasedAnchor
| EAtFile : IndexKey -> ErasedAnchor
| EAtPackage : string -> ErasedAnchor
| EAtProgram : ErasedAnchor.

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

(* ── Package identity: a compiler grouping, not a source occurrence ─────────── *)
(* A package spans files and has no single source occurrence, so its identity is the exact package-directory
   key the compiler already owns.  It is never an `Index` key. *)
Parameter PackageRef : SyntaxProgram -> Type.
Parameter package_ref_key : forall {p}, PackageRef p -> string.

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

(* ── Erased payload views ──────────────────────────────────────────────────── *)
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

Inductive StatementReason : Type :=
| NotAnApplication        : ErasedResultForm -> StatementReason
| BuiltinNotAStatement    : PredeclaredName -> StatementReason
| ConversionNotAStatement : TypeView -> StatementReason.

Inductive ConstInitReason : Type :=
| ConstInitValue      : TypeView -> ConstInitReason
| ConstInitNoResult   : ErasedResultForm -> ConstInitReason
| ConstInitWrongArity : nat -> nat -> ConstInitReason.

(* ── §4 Causes are indexed by the exact site they arise at ─────────────────── *)
Inductive SiteFailure {p} {i : Input p} (ph : Phase i) : Site p -> Type :=
| FUnresolvedName : forall u : NameUseRef p, SiteFailure ph (SBinding p u)
| FDuplicateDeclaration : forall (u : NameUseRef p) (earlier later : BindingSiteRef p),
    SiteFailure ph (SBinding p u)
| FArgumentRejected : forall (a : ApplicationRef p), nat -> ArgumentReason ->
    SiteFailure ph (SApplication p a)
| FOperandRejected : forall n : UnaryRef p, OperandReason -> SiteFailure ph (SUnary p n)
| FNotAStatement : forall t : ExpressionStatementRef p, StatementReason ->
    SiteFailure ph (SStatement p t)
| FResultCountWrong : forall c : ConsumptionSiteRef p, nat -> nat ->
    SiteFailure ph (SConsumption p c)
| FNotAssignableAt : forall c : ConsumptionSiteRef p, nat -> OperandResultView -> TypeView ->
    SiteFailure ph (SConsumption p c)
| FNotRepresentableAt : forall c : ConsumptionSiteRef p, nat -> UntypedConstantKind -> TypeView ->
    SiteFailure ph (SConsumption p c)
| FConstInitNotConstant : forall c : ConsumptionSiteRef p, nat -> ConstInitReason ->
    SiteFailure ph (SConsumption p c)
| FInvalidConversion : forall (a : ApplicationRef p), OperandResultView -> TypeView ->
    list (ExprRef p) -> SiteFailure ph (SApplication p a)
| FDefaultNotRepresentable : forall (r : ExprRef p), UntypedConstantKind -> TypeView ->
    SiteFailure ph (SExpression p r)
| FUnusedLocal : forall v : VariableSiteRef p, SiteFailure ph (SVariable p v)
| FNoNewVariable : forall d : ShortDeclRef p,
    SiteFailure ph (SConsumption p (ShortSite p d)).

(* §4.1 A requirement retains its exact source site, its exact bound object where one exists, and the exact
   semantic relation that is missing. *)
Inductive SiteRequirement {p} {i : Input p} (ph : Phase i) : Site p -> Type :=
| NeedTypeMeaning  : forall (u : NameUseRef p), ObjectRef ph -> SiteRequirement ph (SBinding p u)
| NeedValueMeaning : forall (u : NameUseRef p), ObjectRef ph -> SiteRequirement ph (SBinding p u)
| NeedApplication  : forall a : ApplicationRef p, SiteRequirement ph (SApplication p a)
| NeedStatement    : forall t : ExpressionStatementRef p, SiteRequirement ph (SStatement p t)
| NeedUnary        : forall n : UnaryRef p, SiteRequirement ph (SUnary p n).

(* ── §12 The complete diagnostic authority ─────────────────────────────────── *)
Inductive DiagnosticAnchor (p : SyntaxProgram) : Type :=
| AtNode    : NodeRef p -> DiagnosticAnchor p
| AtFile    : FileRef p -> DiagnosticAnchor p
| AtPackage : PackageRef p -> DiagnosticAnchor p
| AtProgram : DiagnosticAnchor p.

Inductive DiagnosticCode : Type :=
| CodeUnresolvedName | CodeDuplicateDeclaration | CodeUnusedLocal
| CodeArgument | CodeOperand | CodeNotAStatement | CodeResultCount
| CodeNotAssignable | CodeNotRepresentable | CodeConstInitializerNotConstant
| CodeNoNewVariable | CodeTypeCycle | CodeInitializationCycle
| CodeInvalidConversion | CodeDefaultNotRepresentable
| CodeMainRedeclared | CodeMissingMainEntry | CodeBuildOutputIsDirectory.

(* Site failures enter through one constructor; the remaining reasons are package- or program-level and have
   no single site.  Every current public constructor survives. *)
Inductive DiagnosticReason {p} {i : Input p} (ph : Phase i) : Type :=
| AtSiteFailure : forall s : Site p, SiteFailure ph s -> DiagnosticReason ph
| TypeCycleFound : TypeCycle (phase_equations ph) -> DiagnosticReason ph
| InitializationCycle : PackageRef p -> DiagnosticReason ph
| MainRedeclared : forall later earlier : ObjectSiteRef p, DiagnosticReason ph
| MissingMainEntry : PackageRef p -> DiagnosticReason ph
| BuildOutputIsDirectory : PackageRef p -> string -> DiagnosticReason ph.

Definition site_failure_code {p} {i : Input p} {ph : Phase i} {s} (f : SiteFailure ph s)
  : DiagnosticCode :=
  match f with
  | FUnresolvedName _ _ => CodeUnresolvedName
  | FDuplicateDeclaration _ _ _ _ => CodeDuplicateDeclaration
  | FArgumentRejected _ _ _ _ => CodeArgument
  | FOperandRejected _ _ _ => CodeOperand
  | FNotAStatement _ _ _ => CodeNotAStatement
  | FResultCountWrong _ _ _ _ => CodeResultCount
  | FNotAssignableAt _ _ _ _ _ => CodeNotAssignable
  | FNotRepresentableAt _ _ _ _ _ => CodeNotRepresentable
  | FConstInitNotConstant _ _ _ _ => CodeConstInitializerNotConstant
  | FInvalidConversion _ _ _ _ _ => CodeInvalidConversion
  | FDefaultNotRepresentable _ _ _ _ => CodeDefaultNotRepresentable
  | FUnusedLocal _ _ => CodeUnusedLocal
  | FNoNewVariable _ _ => CodeNoNewVariable
  end.

Definition diagnostic_code {p} {i : Input p} {ph : Phase i} (d : DiagnosticReason ph)
  : DiagnosticCode :=
  match d with
  | AtSiteFailure _ _ f => site_failure_code f
  | TypeCycleFound _ _ => CodeTypeCycle
  | InitializationCycle _ _ => CodeInitializationCycle
  | MainRedeclared _ _ _ => CodeMainRedeclared
  | MissingMainEntry _ _ => CodeMissingMainEntry
  | BuildOutputIsDirectory _ _ _ => CodeBuildOutputIsDirectory
  end.

Record ErasedDiagnostic : Type := MakeErasedDiagnostic {
  erased_code : DiagnosticCode;
  erased_primary : ErasedAnchor;
  erased_related : list ErasedAnchor
}.

Parameter diagnostic_primary : forall {p} {i : Input p} {ph : Phase i},
  DiagnosticReason ph -> DiagnosticAnchor p.
Parameter diagnostic_related : forall {p} {i : Input p} {ph : Phase i},
  DiagnosticReason ph -> list (DiagnosticAnchor p).
Parameter erase_anchor : forall {p}, DiagnosticAnchor p -> ErasedAnchor.
Parameter diagnostic_compare : forall {p} {i : Input p} {ph : Phase i},
  DiagnosticReason ph -> DiagnosticReason ph -> comparison.

Definition erase_diagnostic {p} {i : Input p} {ph : Phase i} (d : DiagnosticReason ph)
  : ErasedDiagnostic :=
  MakeErasedDiagnostic (diagnostic_code d) (erase_anchor (diagnostic_primary d))
    (List.map erase_anchor (diagnostic_related d)).

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

(* ── §4 Private site outcomes: every branch is about this exact site ───────── *)
Inductive SiteOutcome {p} {i : Input p} (ph : Phase i) : Site p -> Type :=
| Supported : forall s, SiteFact ph s -> SiteOutcome ph s
| DefiniteFailure : forall s, SiteFailure ph s -> SiteOutcome ph s
| Outside : forall s, SiteRequirement ph s -> SiteOutcome ph s
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
  : IsRootOutside o -> SiteRequirement ph s :=
  match o in SiteOutcome _ s0 return IsRootOutside o -> SiteRequirement ph s0 with
  | Outside _ _ r => fun _ => r
  | Supported _ _ _ => fun h => match h return SiteRequirement ph _ with end
  | DefiniteFailure _ _ _ => fun h => match h return SiteRequirement ph _ with end
  | Blocked _ _ _ _ _ => fun h => match h return SiteRequirement ph _ with end
  end.

(* One outcome per site.  No client constructs these values. *)
Parameter phase_outcome : forall {p} {i : Input p} (ph : Phase i) (s : Site p), SiteOutcome ph s.

Definition RootRequirement {p} {i : Input p} (ph : Phase i) (s : Site p)
  (r : SiteRequirement ph s) : Prop :=
  exists h : IsRootOutside (phase_outcome ph s), root_requirement (phase_outcome ph s) h = r.

(* ── §11 Package dependency: static order, distinct from runtime initialization ── *)
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

(* Constants stay compile-time facts; only variable and blank work projects into the C7 store. *)
Definition RuntimeInitUnit {p} (u : InitUnit p) : bool :=
  match u with ConstUnit _ _ => false | VarUnit _ _ => true | BlankUnit _ _ => true end.

Definition runtime_initialization {p} {i : Input p} {ph : Phase i} {k}
  {g : DependencyGraph ph k} (o : AcyclicOrder g) : list (InitUnit p) :=
  List.filter RuntimeInitUnit (order_units o).

(* ── §4.2 Boundaries and the requirement decision, both before acceptance ──── *)
Record PackedBoundary {p} {i : Input p} (ph : Phase i) : Type := MakeBoundary {
  boundary_site : Site p;
  boundary_requirement : SiteRequirement ph boundary_site;
  boundary_is_root : RootRequirement ph boundary_site boundary_requirement
}.

Parameter requirement_view : forall {p} {i : Input p} {ph : Phase i} {s},
  SiteRequirement ph s -> RequirementView.

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
Definition InScope (p : SyntaxProgram) : Prop :=
  core_boundaries (elaboration_core (elaborate p)) = [].

(* ── Accepted facts by dependent elimination of the one retained phase ─────── *)
Definition accepted_phase (cp : Program) : Phase (core_input (core cp)) := phase (core cp).
Definition accepted_equations (cp : Program) : ResolvedTypeEquations (source cp) :=
  phase_equations (accepted_phase cp).
Parameter accepted_ready : forall cp : Program, IsTypeReady (phase_type_result (accepted_phase cp)).
Definition accepted_type_ready (cp : Program) : TypeReady (accepted_equations cp) :=
  ready_of (phase_type_result (accepted_phase cp)) (accepted_ready cp).
Definition accepted_environment (cp : Program) : Env (accepted_type_ready cp) :=
  ready_environment (accepted_type_ready cp).

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
Definition UnaryFactT (cp : Program) (n : UnaryRef (source cp)) : Type :=
  PhaseUnaryFact (accepted_phase cp) n.
Definition unary_fact (cp : Program) (n : UnaryRef (source cp)) : UnaryFactT cp n :=
  accepted_fact cp (SUnary (source cp) n).
Definition Consumption (cp : Program) (s : ConsumptionSiteRef (source cp)) : Type :=
  PhaseConsumptionFact (accepted_phase cp) s.
Definition consumption (cp : Program) (s : ConsumptionSiteRef (source cp)) : Consumption cp s :=
  accepted_fact cp (SConsumption (source cp) s).
Definition StaticVariableAt (cp : Program) (v : VariableSiteRef (source cp)) : Type :=
  PhaseStaticVariableFact (accepted_phase cp) v.
Definition static_variable_at (cp : Program) (v : VariableSiteRef (source cp))
  : StaticVariableAt cp v := accepted_fact cp (SVariable (source cp) v).

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

(* Float.Kind already owns the two float forms; no second carrier is minted. *)
Definition float_named_basic (f : FloatKind) : PredeclaredBasicType :=
  match f with FKF32 => TFloat32 | FKF64 => TFloat64 end.
Definition complex_named_basic (f : FloatKind) : PredeclaredBasicType :=
  match f with FKF32 => TComplex64 | FKF64 => TComplex128 end.

Definition predeclared_type_of (cp : Program) (t : PredeclaredBasicType) : AcceptedType cp :=
  PredeclaredType (accepted_environment cp) t.

(* Exact constant arithmetic: the result is computed, never supplied. *)
Parameter negate_constant : Constant -> option Constant.
Parameter complex_of_constants : Constant -> Constant -> option Constant.

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

Inductive NumericBasic : BasicType -> Prop :=
| NBScalar  : forall b, ScalarNumericBasic b -> NumericBasic b
| NBComplex : forall b, ComplexBasicForm b -> NumericBasic b.

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

(* ── §9 Statement classification is intrinsic ──────────────────────────────── *)
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

(* One constructor: only a successful `println` application is a C6 statement call.  A conversion or a
   `complex` application cannot inhabit this type at all. *)
Inductive StatementCall (cp : Program) (s : ExpressionStatementRef (source cp)) : Type :=
| StmtPrintln : forall (a : ApplicationRef (source cp))
    (c : HeadCallable (app_head_fact cp a)),
    StatementApplication cp s a ->
    app_target cp a = CallableTarget (app_head_fact cp a) c ->
    callable_name c = PPrintln -> PrintlnRule cp a -> StatementCall cp s.

Inductive StatementClass (cp : Program) (s : ExpressionStatementRef (source cp)) : Type :=
| StatementEligible : StatementCall cp s -> StatementClass cp s
| StatementDefiniteFailure : StatementReason -> StatementClass cp s
| StatementOutside :
    SiteRequirement (accepted_phase cp) (SStatement (source cp) s) -> StatementClass cp s
| StatementBlocked : Site (source cp) -> StatementClass cp s.

Parameter statement_class : forall (cp : Program) (s : ExpressionStatementRef (source cp)),
  StatementClass cp s.

(* ── §10 One result-consumption authority ──────────────────────────────────── *)
Inductive ConsumptionTarget (p : SyntaxProgram) : Type :=
| NamedTarget : BindingSiteRef p -> ConsumptionTarget p
| BlankTarget : BlankRef p -> ConsumptionTarget p.

(* The exact defaulting / representability / assignability evidence an entry must carry. *)
Inductive AtomFitsTarget (cp : Program) : ResultAtom cp -> AcceptedType cp -> Prop :=
| FitUntyped : forall c t, AcceptedRepresentable cp t c ->
    AtomFitsTarget cp (UntypedConstant cp c) t
| FitTyped : forall (s : AcceptedType cp) ct t, AcceptedAssignable cp s t ->
    AtomFitsTarget cp (TypedConstantAtom cp s ct) t
| FitValue : forall (s : AcceptedType cp) t, AcceptedAssignable cp s t ->
    AtomFitsTarget cp (ValueResult cp s) t.

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
  ve_type : AcceptedType cp;
  ve_fits : AtomFitsTarget cp (occurrence_atom ve_occurrence) ve_type
}.

Inductive ShortDisposition (cp : Program) : Type :=
| ShortNew   : ShortDisposition cp
| ShortReuse : Object cp -> ShortDisposition cp.

(* Blank short entries carry no disposition and no target type: the context decides. *)
Inductive ShortEntry (cp : Program) : Type :=
| ShortNamed : forall (b : BindingSiteRef (source cp)) (d : ShortDisposition cp)
    (o : ResultOccurrence cp) (t : AcceptedType cp),
    AtomFitsTarget cp (occurrence_atom o) t -> ShortEntry cp
| ShortBlankEntry : BlankRef (source cp) -> ResultOccurrence cp -> ShortEntry cp.

Inductive ConsumptionPlan (cp : Program) : Type :=
| ConstPlan : list (ConstEntry cp) -> ConsumptionPlan cp
| VarPlan   : list (VarEntry cp) -> ConsumptionPlan cp
| ShortPlan : list (ShortEntry cp) -> ConsumptionPlan cp.

Parameter consumption_plan : forall {cp} {s}, Consumption cp s -> ConsumptionPlan cp.

Definition short_entry_target (cp : Program) (e : ShortEntry cp)
  : ConsumptionTarget (source cp) :=
  match e with
  | ShortNamed _ b _ _ _ _ => NamedTarget (source cp) b
  | ShortBlankEntry _ k _ => BlankTarget (source cp) k
  end.

Definition short_entry_occurrence (cp : Program) (e : ShortEntry cp) : ResultOccurrence cp :=
  match e with
  | ShortNamed _ _ _ o _ _ => o
  | ShortBlankEntry _ _ o => o
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
  | ShortPlan _ l => List.map (short_entry_occurrence cp) l
  end.

(* The plan IS the authority: the source uses it consumes are the uses of its own occurrences. *)
Definition plan_sources (cp : Program) (pl : ConsumptionPlan cp)
  : list (ExprUseRef (source cp)) :=
  List.map (occ_use cp) (plan_occurrences cp pl).

(* ── §4.2 Requirement satisfaction is defined from retained phase facts ────── *)
(* It mentions no `Program`, so it is the decision that can produce an OutsideScope result. *)
Definition RequirementSatisfied {p} {i : Input p} (ph : Phase i) (s : Site p)
  (r : SiteRequirement ph s) : Prop :=
  match r with
  | NeedTypeMeaning _ _ o => inhabited (PhaseTypeMeaning ph o)
  | NeedValueMeaning _ _ o =>
      inhabited (PhaseValueMeaning ph o) \/ inhabited (PhaseConstantMeaning ph o) \/
      inhabited (PhaseStaticVariable ph o) \/ inhabited (PhaseIotaMeaning ph o) \/
      inhabited (PhaseNilMeaning ph o)
  | NeedApplication _ a => IsSupported (phase_outcome ph (SApplication p a))
  | NeedStatement _ t => IsSupported (phase_outcome ph (SStatement p t))
  | NeedUnary _ n => IsSupported (phase_outcome ph (SUnary p n))
  end.

Parameter requirement_dec : forall {p} {i : Input p} (ph : Phase i) (s : Site p)
  (r : SiteRequirement ph s),
  { RequirementSatisfied ph s r } + { ~ RequirementSatisfied ph s r }.

(* ── §14 Rendering: contexts, and predicates that say something ────────────── *)
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

Fixpoint last_char (s : string) : option ascii :=
  match s with
  | EmptyString => None
  | String c EmptyString => Some c
  | String _ rest => last_char rest
  end.

(* Exactly two adjacent bytes, so the property is about a token boundary and not about scanning contents. *)
Fixpoint HasAdjacent (a b : ascii) (s : string) : Prop :=
  match s with
  | EmptyString => False
  | String c rest => (c = a /\ first_char rest = Some b) \/ HasAdjacent a b rest
  end.

Definition NewlineChar : ascii := ascii_of_nat 10.
Definition SpaceChar : ascii := ascii_of_nat 32.
Definition TabChar : ascii := ascii_of_nat 9.

Definition StartsWithMinus (s : string) : Prop := first_char s = Some "-"%char.
Definition AsciiOnly (s : string) : Prop := forall c, InString c s -> (nat_of_ascii c < 128)%nat.
Definition Parenthesized (s : string) : Prop := exists inner, s = ("(" ++ inner ++ ")")%string.

(* No line ends in a space or a tab, and the file's final byte is a newline. *)
Definition NoTrailingBlank (s : string) : Prop :=
  ~ HasAdjacent SpaceChar NewlineChar s /\
  ~ HasAdjacent TabChar NewlineChar s /\
  last_char s = Some NewlineChar.

(* ── Remaining relations named by the theorems ─────────────────────────────── *)
Parameter InnermostDeclaring : forall (cp : Program),
  NameUseRef (source cp) -> BindingSiteRef (source cp) -> Prop.
Parameter SameBlockEarlier : forall (cp : Program),
  BindingSiteRef (source cp) -> Object cp -> Prop.
Parameter ReadsVariableAt : forall {p} {i : Input p} (ph : Phase i), VariableSiteRef p -> Prop.
Parameter FullyAnalyzedLocal : forall {p} {i : Input p} (ph : Phase i),
  VariableSiteRef p -> Prop.
Parameter LocalVariableSite : forall {p} {i : Input p} (ph : Phase i),
  VariableSiteRef p -> Prop.
Parameter ScopesFileOrderIndependent : forall {p} {i : Input p}, Phase i -> Prop.
Parameter bound_object : forall {cp : Program} {u}, BindingFact cp u -> Object cp.
Parameter binding_use_role : forall {cp : Program} {u}, BindingFact cp u -> UseRole.
Parameter binding_package : forall {cp : Program} {u},
  BindingFact cp u -> PackageRef (source cp).

```

## Theorems

Every statement below elaborates over the names above; proof bodies are the implementation's work.

```coq

(* §2.1 the source-name root. *)
Theorem ordinary_excludes_blank_only : forall x : OrdinaryIdentifier,
  spelling (ordinary_identifier x) <> "_"%string.
Theorem predeclared_spellings_are_source_names : forall n : PredeclaredName,
  predeclared_spelling n <> "_"%string ->
  exists x : OrdinaryIdentifier, spelling (ordinary_identifier x) = predeclared_spelling n.
Theorem blank_is_not_an_ordinary_name : forall x : OrdinaryIdentifier,
  Named x <> Blank.

(* Names: the pinned catalog is complete, exact and injective. *)
Theorem all_predeclared_nodup : NoDup all_predeclared.
Theorem all_predeclared_complete : forall n, In n all_predeclared.
Theorem predeclared_spelling_injective : forall a b,
  predeclared_spelling a = predeclared_spelling b -> a = b.
Theorem classify_spelling_roundtrip : forall n, classify_spelling (predeclared_spelling n) = Some n.
Theorem predeclared_eqb_spec : forall a b, predeclared_eqb a b = true <-> a = b.

(* §3.1 the refinement has no fallback: it is an elimination of the child-role witness. *)
Theorem head_role_is_head_refinement :
  refinement_of_child_role ECApplicationHead = HeadRefinement.
Theorem statement_role_is_statement_refinement :
  refinement_of_child_role ECStatement = StatementRefinement.
Theorem argument_role_is_result_refinement :
  refinement_of_child_role ECApplicationArg = ResultRefinement.
Theorem inherited_use_is_result : forall p (u : InheritedConstUseRef p),
  use_refinement (InheritedUse p u) = ResultRefinement.

(* §5 the closed type bridge. *)
Theorem byte_is_uint8 : AliasPredeclared PByte TUint8.
Theorem rune_is_int32 : AliasPredeclared PRune TInt32.
Theorem aliases_mint_no_identity : forall n t, AliasPredeclared n t ->
  ~ AdmittedPredeclaredType n t.
Theorem no_type_meaning_names : forall n,
  In n [PAny; PComparable; PError; PUintptr] -> predeclared_type_role n = NoTypeMeaning.
Theorem sixteen_named_basic_types : forall t : PredeclaredBasicType,
  exists n, AdmittedPredeclaredType n t.
Theorem default_types_exact :
  default_basic UCBool = TBool /\ default_basic UCInteger = TInt /\
  default_basic UCFloat = TFloat64 /\ default_basic UCComplex = TComplex128 /\
  default_basic UCString = TString.

(* §3.2 environment provenance is intrinsic; the alias/definition mapping is frozen. *)
Theorem cyclic_phase_has_no_environment : forall p (eqs : ResolvedTypeEquations p) c,
  ~ IsTypeReady (PhaseCyclic eqs c).
Theorem ready_is_acyclic : forall p (eqs : ResolvedTypeEquations p) (r : TypeReady eqs),
  AcyclicEquations eqs.
Theorem predeclared_target_terminal : forall p (eqs : ResolvedTypeEquations p) n m x,
  equation_target eqs n = RawPredeclared p x -> ~ TypeEdge eqs n m.
Theorem resolution_is_functional : forall p (eqs : ResolvedTypeEquations p) n r1 r2,
  AcyclicEquations eqs -> ResolvesTo eqs n r1 -> ResolvesTo eqs n r2 -> r1 = r2.
Theorem defined_resolves_to_itself : forall p (eqs : ResolvedTypeEquations p) d,
  ResolvesTo eqs (DefinedNode p d) (ResolvedDefined p d).
Theorem alias_resolves_through_target : forall p (eqs : ResolvedTypeEquations p) a n res,
  equation_target eqs (AliasNode p a) = RawAlias p n -> ResolvesTo eqs (AliasNode p n) res ->
  ResolvesTo eqs (AliasNode p a) res.
Theorem defined_underlying_follows_resolution :
  forall p eqs (r : TypeReady eqs) (env : @Env p eqs r) d h t,
  ResolvesTo eqs (DefinedNode p d) (ResolvedBasic p t) ->
  defined_underlying env d h = predeclared_basic_form t.
Theorem alias_resolves_to_exact_type :
  forall p eqs (r : TypeReady eqs) (env : @Env p eqs r) a t,
  ResolvesTo eqs (AliasNode p a) (ResolvedBasic p t) ->
  AliasResolvesTo env a (PredeclaredType env t).

(* §Keep assignability is identity; conversion splits constant from value. *)
Theorem assignable_is_identity : forall p eqs (r : TypeReady eqs) (env : @Env p eqs r) s t,
  Assignable env s t <-> Identical env s t.
Theorem defined_not_assignable_to_predeclared :
  forall p eqs (r : TypeReady eqs) (env : @Env p eqs r) d h t,
  ~ Assignable env (DefinedType env d h) (PredeclaredType env t).
Theorem distinct_predeclared_not_assignable :
  forall p eqs (r : TypeReady eqs) (env : @Env p eqs r) t u,
  t <> u -> ~ Assignable env (PredeclaredType env t) (PredeclaredType env u).
Theorem no_value_scalar_to_complex :
  forall p eqs (r : TypeReady eqs) (env : @Env p eqs r) s t bs bt,
  Underlying env s (BasicForm env bs) -> Underlying env t (BasicForm env bt) ->
  ScalarNumericBasic bs -> ComplexBasicForm bt -> ~ ValueConvertible env s t.
Theorem no_value_complex_to_scalar :
  forall p eqs (r : TypeReady eqs) (env : @Env p eqs r) s t bs bt,
  Underlying env s (BasicForm env bs) -> Underlying env t (BasicForm env bt) ->
  ComplexBasicForm bs -> ScalarNumericBasic bt -> ~ ValueConvertible env s t.
Theorem identicalb_reflect : forall p eqs (r : TypeReady eqs) (env : @Env p eqs r) s t,
  identicalb env s t = true <-> Identical env s t.
Theorem assignableb_reflect : forall p eqs (r : TypeReady eqs) (env : @Env p eqs r) s t,
  assignableb env s t = true <-> Assignable env s t.
Theorem value_convertibleb_reflect : forall p eqs (r : TypeReady eqs) (env : @Env p eqs r) s t,
  value_convertibleb env s t = true <-> ValueConvertible env s t.
Theorem representableb_reflect : forall p eqs (r : TypeReady eqs) (env : @Env p eqs r) s c,
  representableb env s c = true <-> Representable env s c.

(* §4 outcomes: every branch is about the exact site; boundaries are root projections only. *)
Theorem supported_fact_is_the_site_fact : forall p (i : Input p) (ph : Phase i) s f h,
  supported_fact (Supported ph s f) h = f.
Theorem blocked_is_not_supported : forall p (i : Input p) (ph : Phase i) s pred d o,
  ~ IsSupported (Blocked ph s pred d o).
Theorem listed_boundary_is_root : forall p (c : Core p) b,
  In b (core_boundaries c) ->
  RootRequirement (phase c) (boundary_site (phase c) b) (boundary_requirement (phase c) b).
Theorem root_boundary_complete : forall p (c : Core p) s (r : SiteRequirement (phase c) s),
  RootRequirement (phase c) s r ->
  exists b, In b (core_boundaries c) /\ boundary_site (phase c) b = s.
Theorem boundary_views_nodup : forall p (c : Core p),
  NoDup (List.map boundary_view (core_boundaries c)).
Theorem boundary_order_canonical : forall p (c : Core p),
  Sorted view_lt (List.map boundary_view (core_boundaries c)).

(* §4.2 the decision exists before a Program does; accepted views are its projections. *)
Theorem requirement_dec_reflects : forall p (i : Input p) (ph : Phase i) s r,
  (exists h, requirement_dec ph s r = left h) <-> RequirementSatisfied ph s r.
Theorem accepted_satisfies_every_requirement : forall cp s r,
  RequirementSatisfied (accepted_phase cp) s r.
Theorem boundary_requirement_unsatisfied : forall p (c : Core p) b,
  In b (core_boundaries c) ->
  ~ RequirementSatisfied (phase c) (boundary_site (phase c) b) (boundary_requirement (phase c) b).
Theorem view_lt_strict : forall a b c, view_lt a b -> view_lt b c -> view_lt a c.
Theorem view_lt_irrefl : forall a, ~ view_lt a a.
Theorem view_lt_total : forall a b, view_lt a b \/ a = b \/ view_lt b a.

(* §5.1 object laws. *)
Theorem object_origin_injective : forall p (i : Input p) (ph : Phase i) (o1 o2 : ObjectRef ph),
  object_origin o1 = object_origin o2 -> o1 = o2.
Theorem object_eqb_spec : forall p (i : Input p) (ph : Phase i) (o1 o2 : ObjectRef ph),
  object_eqb o1 o2 = true <-> o1 = o2.
Theorem predeclared_object_origin : forall p (i : Input p) (ph : Phase i) n,
  object_origin (predeclared_object ph n) = Predeclared p n.
Theorem source_object_origin : forall p (i : Input p) (ph : Phase i) s,
  object_origin (source_object ph s) = SourceSite p s.
Theorem every_object_has_one_origin : forall p (i : Input p) (ph : Phase i) (o : ObjectRef ph),
  (exists n, object_origin o = Predeclared p n) \/ (exists s, object_origin o = SourceSite p s).
Theorem nil_is_its_own_kind : predeclared_kind PNil = NilObject.

(* §6 the predeclared capability table connects to the exact facts. *)
Theorem admitted_type_object_has_type_meaning : forall cp n t,
  predeclared_capability n = CapNamedType t ->
  inhabited (TypeMeaning cp (predeclared_object (accepted_phase cp) n)).
Theorem alias_object_targets_exact_type : forall cp n t,
  predeclared_capability n = CapAliasType t ->
  inhabited (TypeMeaning cp (predeclared_object (accepted_phase cp) n)).
Theorem callable_names_are_exactly_two : forall n,
  predeclared_capability n = CapCallable -> n = PComplex \/ n = PPrintln.
Theorem missing_capability_is_a_requirement : forall cp n u,
  predeclared_capability n = CapMissing ->
  ~ RequirementSatisfied (accepted_phase cp) (SBinding (source cp) u)
      (NeedValueMeaning (accepted_phase cp) u (predeclared_object (accepted_phase cp) n)).
Theorem static_variable_retains_its_site : forall cp o (v : StaticVariable cp o),
  exists s, static_variable_site v = s.

(* §7 the occurrence atom is the exact nth projection. *)
Theorem occurrence_atom_is_nth : forall cp (o : ResultOccurrence cp),
  List.nth_error
    (result_use_atoms (result_use_fact cp (occ_use cp o) (occ_is_result cp o)))
    (occurrence_position o) = Some (occurrence_atom o).
Theorem c6_result_use_has_one_atom : forall cp u (f : ResultUseFact cp u),
  List.length (result_use_atoms f) = 1%nat.

(* §8 rules consume the exact ordered argument occurrences. *)
Theorem argument_occurrence_count : forall cp a,
  List.length (app_argument_occurrences cp a) =
  List.length (application_argument_uses a).
Theorem argument_occurrence_uses_are_the_source_uses : forall cp a,
  List.map (occ_use cp) (app_argument_occurrences cp a) = app_argument_uses cp a.
Theorem argument_use_parent_is_the_application : forall p (a : ApplicationRef p) u,
  In u (application_argument_uses a) -> direct_parent u = expr_node (application_expr a).
Theorem conversion_takes_one_argument : forall cp a t (r : ConversionRule cp a t),
  List.length (app_argument_occurrences cp a) = 1%nat.
Theorem complex_takes_two_arguments : forall cp a (r : ComplexRule cp a),
  List.length (app_argument_occurrences cp a) = 2%nat.
Theorem application_results_are_the_parent_results : forall cp a,
  result_form (app_parent_fact cp a) =
  FixedResults cp (application_results cp a (accepted_application_rule cp a)).
Theorem println_result_is_empty : forall cp a c e ci pr,
  accepted_application_rule cp a = ARPrintln cp a c e ci pr ->
  application_results cp a (accepted_application_rule cp a) = [].
Theorem unary_untyped_result_is_the_negation : forall cp n c c' h1 h2 h3,
  unary_results cp n (URUntyped cp n c c' h1 h2 h3) = [UntypedConstant cp c'].

(* §9 statement classification is closed: only a println application is eligible. *)
Theorem only_println_is_eligible : forall cp s (k : StatementCall cp s),
  exists a c h1 h2 h3 pr, k = StmtPrintln cp s a c h1 h2 h3 pr.
Theorem forbidden_builtin_is_definite_failure : forall cp s n,
  builtin_forbidden_as_statement n = true ->
  statement_class cp s = StatementDefiniteFailure cp s (BuiltinNotAStatement n) ->
  forall k : StatementCall cp s, False.
Theorem forbidden_and_admitted_are_disjoint : forall n,
  builtin_forbidden_as_statement n = true -> builtin_admitted_as_statement n = false.
Theorem complex_is_forbidden_as_statement : builtin_forbidden_as_statement PComplex = true.

(* §10 one consumption authority. *)
Theorem plan_consumes_every_source : forall cp s,
  List.length (plan_occurrences cp (consumption_plan (consumption cp s))) =
  List.length (plan_sources cp (consumption_plan (consumption cp s))).
Theorem const_site_has_const_plan : forall cp (c : ConstSpecRef (source cp)),
  exists l, consumption_plan (consumption cp (ConstSite (source cp) c)) = ConstPlan cp l.
Theorem var_site_has_var_plan : forall cp (v : VarSpecRef (source cp)),
  exists l, consumption_plan (consumption cp (VarSite (source cp) v)) = VarPlan cp l.
Theorem short_site_has_short_plan : forall cp (d : ShortDeclRef (source cp)),
  exists l, consumption_plan (consumption cp (ShortSite (source cp) d)) = ShortPlan cp l.
Theorem short_reuse_is_same_block : forall cp b o t h l e obj,
  In e l -> e = ShortNamed cp b (ShortReuse cp obj) o t h -> SameBlockEarlier cp b obj.

(* §11 dependency objects. *)
Theorem dependency_edges_from_bindings : forall p (i : Input p) (ph : Phase i) k,
  EdgesFromBindings (phase_dependency_graph ph k).
Theorem dependency_respects_source_order : forall p (i : Input p) (ph : Phase i) k,
  SourceOrderConstrained (phase_dependency_graph ph k).
Theorem accepted_dependency_acyclic : forall cp k,
  exists o, phase_dependency_outcome (accepted_phase cp) k = DependencyOrdered _ o.
Theorem constants_are_not_runtime_units : forall p (c : ConstSpecRef p),
  RuntimeInitUnit (ConstUnit p c) = false.
Theorem runtime_projection_excludes_constants : forall p (i : Input p) (ph : Phase i) k
  (g : DependencyGraph ph k) (o : AcyclicOrder g),
  List.Forall (fun u => RuntimeInitUnit u = true) (runtime_initialization o).

(* §12 the diagnostic authority is complete and canonically ordered. *)
Theorem site_failure_enters_through_one_constructor : forall p (i : Input p) (ph : Phase i) s f,
  diagnostic_code (AtSiteFailure ph s f) = site_failure_code f.
Theorem invalid_conversion_survives : forall p (i : Input p) (ph : Phase i) a v t outer,
  diagnostic_code (AtSiteFailure ph (SApplication p a) (FInvalidConversion ph a v t outer))
    = CodeInvalidConversion.
Theorem missing_main_entry_survives : forall p (i : Input p) (ph : Phase i) k,
  diagnostic_code (MissingMainEntry ph k) = CodeMissingMainEntry.
Theorem build_output_is_directory_survives : forall p (i : Input p) (ph : Phase i) k s,
  diagnostic_code (BuildOutputIsDirectory ph k s) = CodeBuildOutputIsDirectory.
Theorem erase_diagnostic_code : forall p (i : Input p) (ph : Phase i) (d : DiagnosticReason ph),
  erased_code (erase_diagnostic d) = diagnostic_code d.
Theorem erase_diagnostic_primary : forall p (i : Input p) (ph : Phase i) (d : DiagnosticReason ph),
  erased_primary (erase_diagnostic d) = erase_anchor (diagnostic_primary d).
Theorem unused_local_only_when_analyzed : forall p (c : Core p) v,
  In (AtSiteFailure (phase c) (SVariable p v) (FUnusedLocal (phase c) v)) (core_diagnostics c) ->
  FullyAnalyzedLocal (phase c) v.
Theorem unused_local_iff : forall p (c : Core p) v,
  FullyAnalyzedLocal (phase c) v -> LocalVariableSite (phase c) v ->
  (In (AtSiteFailure (phase c) (SVariable p v) (FUnusedLocal (phase c) v)) (core_diagnostics c)
   <-> ~ ReadsVariableAt (phase c) v).

(* §13 exact capability provenance, restored. *)
Theorem compiled_retains_core : forall p cp (Hcp : source cp = p),
  compile p = Compiled p cp Hcp ->
  eq_rect (source cp) Core (core cp) p Hcp = elaboration_core (elaborate p).
Theorem rejected_retains_core : forall p (f : Failure p),
  compile p = Rejected p f -> failure_core f = elaboration_core (elaborate p).
Theorem outside_retains_core : forall p (o : Outside_ p),
  compile p = OutsideScope p o -> outside_core o = elaboration_core (elaborate p).
Theorem compile_sound : forall p cp Hcp, compile p = Compiled p cp Hcp -> Admissible p.
Theorem compile_complete_in_scope : forall p, Admissible p -> InScope p ->
  exists cp Hcp, compile p = Compiled p cp Hcp.
Theorem rejected_not_admissible : forall p (f : Failure p),
  compile p = Rejected p f -> ~ Admissible p.

(* §14 rendering: nontrivial predicates and exact outputs. *)
Theorem unary_operand_never_starts_with_minus : forall e,
  ~ StartsWithMinus (render_in UnaryOperandContext e).
Theorem parens_in_unary_operand_iff_unary : forall e,
  needs_parens UnaryOperandContext e = true <-> exists op x, e = Unary op x.
Theorem parens_in_head_iff_unary : forall e,
  needs_parens ApplicationHeadContext e = true <-> exists op x, e = Unary op x.
Theorem no_parens_in_argument : forall e, needs_parens ApplicationArgumentContext e = false.
Theorem render_double_negation : forall x,
  render_expr (Unary UnaryMinus (Unary UnaryMinus (Name x)))
    = ("-(-" ++ spelling (ordinary_identifier x) ++ ")")%string.
Theorem render_negated_head_call : forall f x,
  render_expr (Application (Unary UnaryMinus (Name f)) [Name x])
    = ("(-" ++ spelling (ordinary_identifier f) ++ ")(" ++
       spelling (ordinary_identifier x) ++ ")")%string.
Theorem render_ascii : forall e, AsciiOnly (render_expr e).
Theorem render_file_no_trailing_blank : forall f, NoTrailingBlank (render_file f).
Theorem scopes_file_order_independent : forall p (i : Input p) (ph : Phase i),
  ScopesFileOrderIndependent ph.
Theorem predeclared_shadowed : forall cp u s o,
  InnermostDeclaring cp u s -> bound_object (binding_fact cp u) = o ->
  object_origin o = SourceSite (source cp) (binding_site_object_site s).

```

## Implementation review boundaries

**Semantic-root review** stops only when the repository is green, the `Compilable.*` modules exist with no
old path beside a new one, and the tree contains: an ordinary identifier that excludes blank and nothing
else, with every predeclared spelling shadowable; blank only as a `BindingName`, admitted by alias and
definition specs; nonnegative literal magnitudes with negation only through `Unary UnaryMinus`; declaration
spec groups as lists; exact `ConstSpecRef`/`VarSpecRef`/`ShortDeclRef` consumption sites; a use refinement
with no fallback; a sealed `TypeReady` no client can construct and whose environment cannot be paired with a
foreign decision; site-indexed failures and requirements with `Blocked` retaining its predecessor;
`requirement_dec` over the phase, decidable before any `Program` exists; every accepted capability a
projection of a phase family, with a callable fact carrying its own identity; result occurrences whose atom
is the exact split projection; conversion, `complex`, `println` and unary rules consuming their exact
argument occurrences and computing their results; a statement judgment only a `println` application can
inhabit; one consumption plan carrying exact fits evidence; the complete diagnostic migration above; exact
core provenance for `Compiled`, `Rejected` and `Outside`; nontrivial render predicates; and prior generated
bytes unchanged.

**Final C6 review** then completes declaration and shadowing behaviour, boundaries, direct rendering, C6
fixtures, `LAT-077`, generated-artifact evidence, and current document and ledger truth.

C7 is forbidden until Rob accepts C6.

## Done

**`make ns-probe`.** A scratch theory with `Compilable.v` beside `Compilable/Bindings.v` under
`(include_subdirs qualified)` builds under the pinned Dune 3.21 and Rocq 9.2.0, producing
`_build/default/Compilable.vo` and `_build/default/Compilable/Bindings.vo`, and `Compilable.v` resolves
`From Fido Require Import Compilable.Bindings`. The module name does not collide with the directory.

**`make go-probe`, source root.** Every predeclared spelling is a legal ordinary source identifier: `int`,
`int32` and `any` as type names, `true`, `iota`, `nil`, `len`, `println` and `complex` as ordinary bindings,
at package level and locally. `_` is rejected as a value and as a type, so blank is exclusively a
`BindingName`. `type _ = int`, `type _ int`, `const _ = 1` and `var _ = 1` all accept. `const ()`, `var ()`
and `type ()` accept at package level and inside a function. `- 1` and `-1` both accept, so a negative value
is a unary application over a magnitude, not a literal.

**Arity and operands.** `int64()` and `int64(1, 2)` rejected; `complex(1)` and `complex(1, 2, 3)` rejected;
`complex(true, 1)` and `complex("a", 1)` rejected; two nonconstant `int` operands rejected. Accepted: two
untyped numeric constants; typed `float32` constant with an untyped operand giving `complex64`; a `float32`
value with an untyped operand; a typed `float64` constant with a `float64` value giving `complex128`; two
operands of one defined type over `float64`. Two distinct defined types over the same form rejected; mixed
`float32`/`float64` rejected.

**Const initializers.** `var x = 1; const y = x` rejected; `const y = println(1)` rejected; `const x = 1;
const y = x`, `const y = int64(x)` and `const y = complex(1.0, 2.0)` accepted.

**Statement position.** Rejected: `append`, `cap`, `complex`, `imag`, `len`, `make`, `new`, `real`, `min`,
`max`, a conversion, a bare identifier, a bare literal, a unary expression. Accepted: `clear`, `close`,
`copy`, `delete`, `panic`, `print`, `println`, `recover`, and an ordinary function call. `min` and `max` were
confirmed with nonconstant arguments, so their rejection is the statement-context rule and not constant
folding; pinned `gc` rejects them although the Go 1.23 spec text does not enumerate them.

Package and local `const`/`type`/`var` accepted; a local variable read by `println`; unused local rejected;
cross-file package declarations independent of file order; two packages sharing a spelling without collision;
duplicate package names rejected; `byte`/`uint8` and `rune`/`int32` interchangeable; `int` assignable to
neither `int32` nor `int64`; an unshadowed `len`, a `var x uintptr` and a recursive `main()` each giving a
boundary with the exact unmet requirement and no diagnostic; every currently accepted program rendering
byte-identically after migration.

## Preserve

`Syntax.Program` as the sole source authority and the AST as the one IR; `Program` as the opaque C4
capability, with `Failure` and `Outside` retaining the exact core; the retained input, work forest, member
index, outcome trace and sealed core; `Machine.T` uninstantiated; direct rendering and the one
`Emit.Mint.issue` authority; `Integer.Kind`, `Float.Kind` and `Complex.Kind` as the only kind carriers;
`Float.TypedConstant` and `Complex.TypedConstant` as the static constant carriers; `Compilable.PackageRef` as
the package-directory key with its proved injectivity; every current public diagnostic constructor, code,
anchor and erasure; certified-module coverage, the whole-theory audit and controls A-E; every
sealed-capability, mint, transport and positive client control; working-tree and staged-index separation;
no-host-Python; `life.md`.

## Stop

An ordinary identifier must exclude a predeclared spelling, or must admit blank; a negative value needs a
second source form; a declaration group must be nonempty; a var or short consumption site must be a generic
statement; the use refinement needs a fallback case; an environment must be pairable with a decision it did
not come from; a site failure or requirement cannot be indexed by its site; a requirement decision cannot run
before a `Program` exists; an accepted capability cannot be a phase projection; a callable fact must be
relabelled by a free proposition; a result occurrence needs an independent atom or fact field; an application,
conversion, `complex` or unary rule cannot reach its argument occurrences; a conversion or `complex` call must
be able to inhabit the statement-eligible branch; a second consumption authority is needed; a current public
diagnostic cannot be migrated without loss; `compiled_retains_core` cannot be stated exactly; a render
predicate cannot be made nontrivial; the pinned toolchain rejects the qualified namespace; a real semantic
cycle appears between the frozen child modules; implementation needs a placeholder, compatibility path,
trusted shortcut, fuel, bound or premature future state.
