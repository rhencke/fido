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
| `Compilable.TypeResolution` | exact type equations, the graph decision, the sealed `TypeReady` environment, object-indexed type meanings, predeclared and defined type identity through `node_rhs` and `Underlying` |
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
| `diagnostic_code`/`diagnostic_primary`/`diagnostic_related`/`erase_diagnostic` | retained; `erase_diagnostic` is a definition over the six-field record, so the projection equations hold definitionally and carry no theorem |

C6 adds, and does not replace: unresolved name, duplicate declaration, argument, operand, not-a-statement,
result count, not-assignable, not-representable, const-initializer-not-constant, no-new-variable, unused
local, type cycle and initialization cycle.

## The published surface

```coq
(* Proposed C6 public surface, in dependency order.  Scratch: untracked, not a build input. *)

From Stdlib Require Import List String Ascii ZArith NArith Sorted.
Import ListNotations.

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
Definition ne_to_list {A} (ne : NonEmpty A) : list A := ne_first A ne :: ne_rest A ne.
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
(* Rendering cannot be pinned against an opaque file: these mirror the repository accessors. *)
Parameter file_decls : SyntaxFile -> list TopLevelDecl.
Parameter path_string : FilePathT -> string.
Parameter module_path : ModuleSpec -> string.
Parameter module_go_version : ModuleSpec -> string.

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
(* §8 The statement's application child is an index refinement of the source, not a free proposition. *)
Parameter statement_application : forall {p}, ExpressionStatementRef p -> option (ApplicationRef p).
Parameter statement_application_is_its_expression : forall {p}
  (s : ExpressionStatementRef p) (a : ApplicationRef p),
  statement_application s = Some a -> statement_expression s = application_expr a.
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
(* The operand is reached through its exact structural use, so a unary fact consumes a result use. *)
Parameter unary_operand_use : forall {p}, UnaryRef p -> DirectExprUseRef p.

(* §6 Inherited-constant provenance is intrinsic: the connecting proofs are fields, not separate claims,
   so no consumer can search backward, index a source list with a free natural, copy source, or reuse the
   predecessor's resolved plan. *)
Parameter SpecInDecl : forall {p}, ConstDeclRef p -> ConstSpecRef p -> Prop.
Parameter NearestPrecedingExplicit :
  forall {p}, ConstDeclRef p -> ConstSpecRef p -> ConstSpecRef p -> Prop.
Parameter NameAtPosition : forall {p}, ConstSpecRef p -> BindingNameRef p -> nat -> Prop.
Parameter ExprAtPosition : forall {p}, ConstSpecRef p -> ExprRef p -> nat -> Prop.
Parameter SpecTypeUse : forall {p}, ConstSpecRef p -> option (TypeUseRef p) -> Prop.
Parameter StructuralIota : forall {p}, ConstSpecRef p -> nat -> Prop.

Record InheritedConstUseRef (p : SyntaxProgram) : Type := MakeInheritedConstUse {
  ic_decl        : ConstDeclRef p;
  ic_current     : ConstSpecRef p;
  ic_predecessor : ConstSpecRef p;
  ic_name        : BindingNameRef p;
  ic_expr        : ExprRef p;
  ic_type        : option (TypeUseRef p);
  ic_position    : nat;
  ic_iota        : nat;
  ic_current_in_decl    : SpecInDecl ic_decl ic_current;
  ic_pred_in_decl       : SpecInDecl ic_decl ic_predecessor;
  ic_pred_is_nearest    : NearestPrecedingExplicit ic_decl ic_current ic_predecessor;
  ic_name_at_position   : NameAtPosition ic_current ic_name ic_position;
  ic_expr_at_position   : ExprAtPosition ic_predecessor ic_expr ic_position;
  ic_type_is_predecessors : SpecTypeUse ic_predecessor ic_type;
  ic_iota_is_structural : StructuralIota ic_current ic_iota
}.

(* One structural expression-use identity.  Semantic refinement is decided, not assumed. *)
Inductive ExprUseRef (p : SyntaxProgram) : Type :=
| DirectUse    : DirectExprUseRef p -> ExprUseRef p
| InheritedUse : InheritedConstUseRef p -> ExprUseRef p.

Definition expression_of_use {p} (u : ExprUseRef p) : ExprRef p :=
  match u with DirectUse _ d => direct_child d | InheritedUse _ i => ic_expr p i end.

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

Inductive NumericBasic : BasicType -> Prop :=
| NBScalar  : forall b, ScalarNumericBasic b -> NumericBasic b
| NBComplex : forall b, ComplexBasicForm b -> NumericBasic b.

(* Float.Kind already owns the two float forms; no second carrier is minted. *)
Definition float_named_basic (f : FloatKind) : PredeclaredBasicType :=
  match f with FKF32 => TFloat32 | FKF64 => TFloat64 end.
Definition complex_named_basic (f : FloatKind) : PredeclaredBasicType :=
  match f with FKF32 => TComplex64 | FKF64 => TComplex128 end.

(* Exact constant arithmetic: every rule computes its result rather than being handed one. *)
Parameter negate_constant : Constant -> option Constant.
Parameter complex_of_constants : Constant -> Constant -> option Constant.

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

(* Sealed: there is no public constructor, so the only `TypeReady` is the one the phase built, and an
   environment cannot exist apart from the exact graph decision that produced it. *)
Parameter TypeReady : forall {p}, ResolvedTypeEquations p -> Type.
Parameter ready_acyclic : forall {p} {eqs : ResolvedTypeEquations p},
  TypeReady eqs -> AcyclicEquations eqs.
(* `TypeReady` IS the environment: sealed, built by the one decision, with no second carrier beside it. *)
Parameter DefinedInEnv : forall {p} {eqs : ResolvedTypeEquations p},
  TypeReady eqs -> BoundDefinedTypeRef p -> Prop.
Parameter defined_key : forall {p}, BoundDefinedTypeRef p -> IndexKey.

Inductive TypeForm {p} {eqs : ResolvedTypeEquations p} (rd : TypeReady eqs) : Type :=
| BasicForm : BasicType -> TypeForm rd.

Inductive SemanticType {p} {eqs : ResolvedTypeEquations p} (rd : TypeReady eqs) : Type :=
| PredeclaredType : PredeclaredBasicType -> SemanticType rd
| DefinedType     : forall d : BoundDefinedTypeRef p, DefinedInEnv rd d -> SemanticType rd.

(* §3.2 One right-hand-side authority: every graph node has exactly one resolved semantic type, and that
   is the only place a declaration's right-hand side is interpreted.  There is no peer alias relation. *)
Parameter node_rhs : forall {p} {eqs : ResolvedTypeEquations p} (rd : TypeReady eqs),
  TypeNode p -> SemanticType rd.

Definition type_view {p} {eqs : ResolvedTypeEquations p} {rd : TypeReady eqs}
  (t : SemanticType rd) : TypeView :=
  match t with
  | PredeclaredType _ b => PredeclaredView b
  | DefinedType _ d _ => DefinedView (defined_key d)
  end.

(* §3.1 vs §3.2: a definition has its own identity, and its underlying form is its resolved RHS's form. *)
Inductive Underlying {p} {eqs : ResolvedTypeEquations p} (rd : TypeReady eqs)
  : SemanticType rd -> TypeForm rd -> Prop :=
| UnderlyingPredeclared : forall t,
    Underlying rd (PredeclaredType rd t) (BasicForm rd (predeclared_basic_form t))
| UnderlyingDefined : forall d h f,
    Underlying rd (node_rhs rd (DefinedNode p d)) f -> Underlying rd (DefinedType rd d h) f.

(* Identity is generated: name for predeclared, exact declaration reference for defined. *)
Inductive Identical {p} {eqs : ResolvedTypeEquations p} (rd : TypeReady eqs)
  : SemanticType rd -> SemanticType rd -> Prop :=
| IdenticalPredeclared : forall t, Identical rd (PredeclaredType rd t) (PredeclaredType rd t)
| IdenticalDefined : forall d h1 h2,
    Identical rd (DefinedType rd d h1) (DefinedType rd d h2).

(* §Keep: C6 typed assignability is identity. *)
Inductive Assignable {p} {eqs : ResolvedTypeEquations p} (rd : TypeReady eqs)
  : SemanticType rd -> SemanticType rd -> Prop :=
| AssignIdentical : forall s t, Identical rd s t -> Assignable rd s t.

(* The nonconstant conversion authority, strictly narrower than constant conversion. *)
Inductive ValueConvertible {p} {eqs : ResolvedTypeEquations p} (rd : TypeReady eqs)
  : SemanticType rd -> SemanticType rd -> Prop :=
| VConvIdentical : forall s t, Identical rd s t -> ValueConvertible rd s t
| VConvSameUnderlying : forall s t f,
    Underlying rd s f -> Underlying rd t f -> ValueConvertible rd s t
| VConvScalarNumeric : forall s t bs bt,
    Underlying rd s (BasicForm rd bs) -> Underlying rd t (BasicForm rd bt) ->
    ScalarNumericBasic bs -> ScalarNumericBasic bt -> ValueConvertible rd s t
| VConvComplex : forall s t bs bt,
    Underlying rd s (BasicForm rd bs) -> Underlying rd t (BasicForm rd bt) ->
    ComplexBasicForm bs -> ComplexBasicForm bt -> ValueConvertible rd s t.

Inductive Representable {p} {eqs : ResolvedTypeEquations p} (rd : TypeReady eqs)
  : SemanticType rd -> Constant -> Prop :=
| RepresentableAt : forall s b c,
    Underlying rd s (BasicForm rd b) -> FitsBasic b c -> Representable rd s c.

Inductive ConstantConvertible {p} {eqs : ResolvedTypeEquations p} (rd : TypeReady eqs)
  : SemanticType rd -> Constant -> Constant -> Prop :=
| CConvExact : forall s b c c',
    Underlying rd s (BasicForm rd b) -> convert_constant_to b c = Some c' ->
    ConstantConvertible rd s c c'.

Inductive TypedConstant {p} {eqs : ResolvedTypeEquations p} (rd : TypeReady eqs)
  (s : SemanticType rd) : Type :=
| TypedOf : forall b, Underlying rd s (BasicForm rd b) -> BasicTypedConstant b -> TypedConstant rd s.

Parameter underlyingb : forall {p} {eqs : ResolvedTypeEquations p} (rd : TypeReady eqs),
  SemanticType rd -> TypeForm rd.
Parameter identicalb assignableb value_convertibleb :
  forall {p} {eqs : ResolvedTypeEquations p} (rd : TypeReady eqs),
    SemanticType rd -> SemanticType rd -> bool.
Parameter representableb : forall {p} {eqs : ResolvedTypeEquations p} (rd : TypeReady eqs),
  SemanticType rd -> Constant -> bool.

Definition default_type {p} {eqs : ResolvedTypeEquations p} (rd : TypeReady eqs)
  (k : UntypedConstantKind) : SemanticType rd :=
  PredeclaredType rd (default_basic k).

Inductive ResolvedTypeTarget {p} {eqs : ResolvedTypeEquations p} (rd : TypeReady eqs)
  : RawTypeTarget p -> SemanticType rd -> Prop :=
| ResolvedPredeclaredType : forall n t, AdmittedPredeclaredType n t ->
    ResolvedTypeTarget rd (RawPredeclared p n) (PredeclaredType rd t)
| ResolvedPredeclaredAlias : forall n t, AliasPredeclared n t ->
    ResolvedTypeTarget rd (RawPredeclared p n) (PredeclaredType rd t)
| ResolvedSourceAlias : forall a,
    ResolvedTypeTarget rd (RawAlias p a) (node_rhs rd (AliasNode p a))
| ResolvedDefinedType : forall d h,
    ResolvedTypeTarget rd (RawDefined p d) (DefinedType rd d h).

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

(* The exact C6 capability each predeclared name carries; every other name has an exact missing rule. *)
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
| SVariable    : VariableSiteRef p -> Site p
| SDeclaration : BindingSiteRef p -> Site p
| SDependency  : PackageRef p -> Site p.

(* §10 Dependency causality is closed: a blocked site names exactly why it is blocked. *)
Inductive SiteDependency (p : SyntaxProgram) : Site p -> Site p -> Prop :=
| DepUseOfExpression : forall u : ExprUseRef p,
    SiteDependency p (SExpression p (expression_of_use u)) (SUse p u)
| DepApplicationHead : forall a : ApplicationRef p,
    SiteDependency p (SExpression p (application_head a)) (SApplication p a)
| DepApplicationArgument : forall (a : ApplicationRef p) (u : DirectExprUseRef p),
    In u (application_argument_uses a) ->
    SiteDependency p (SUse p (DirectUse p u)) (SApplication p a)
| DepStatementApplication : forall (s : ExpressionStatementRef p) (a : ApplicationRef p),
    statement_application s = Some a ->
    SiteDependency p (SApplication p a) (SStatement p s)
| DepUnaryOperand : forall n : UnaryRef p,
    SiteDependency p (SUse p (DirectUse p (unary_operand_use n))) (SUnary p n)
| DepVariableDeclaration : forall v : VariableSiteRef p,
    SiteDependency p (SDeclaration p (variable_site_binding_site v)) (SVariable p v).

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

Inductive ContextReason : Type :=
| IotaOutsideConstSpec : ContextReason
| NilWithNoTarget      : ContextReason
| PackageInitNotAFunc  : ContextReason.

(* ── §13 Anchors and stable codes ──────────────────────────────────────────── *)
Inductive DiagnosticAnchor (p : SyntaxProgram) : Type :=
| AtNode    : NodeRef p -> DiagnosticAnchor p
| AtFile    : FileRef p -> DiagnosticAnchor p
| AtPackage : PackageRef p -> DiagnosticAnchor p
| AtProgram : DiagnosticAnchor p.

Inductive DiagnosticCode : Type :=
| CodeUnresolvedName | CodeDuplicateDeclaration | CodeUnusedLocal
| CodeArgument | CodeOperand | CodeNotAStatement | CodeResultCount
| CodeNotAssignable | CodeNotRepresentable | CodeConstInitializerNotConstant
| CodeNoNewVariable | CodeTypeCycle | CodeInitializationCycle | CodeContext
| CodeInvalidConversion | CodeDefaultNotRepresentable
| CodeMainRedeclared | CodeMissingMainEntry | CodeBuildOutputIsDirectory.

(* ── §2.1 The C6 scope forest ──────────────────────────────────────────────── *)
(* Exactly three scope kinds at C6: the predeclared outer scope, one scope per package, and the current
   `main` function block.  There is no nested block scope before C8.
   File-order independence needs no theorem here: no scope constructor mentions a file, and
   `declaring_scope` below takes only a package and a declaration context, so a permuted file list cannot
   produce a different scope forest. *)
Inductive ScopeId (p : SyntaxProgram) : Type :=
| PredeclaredScope : ScopeId p
| PackageScope     : PackageRef p -> ScopeId p
| MainBlockScope   : PackageRef p -> ScopeId p.

Definition scope_parent {p} (s : ScopeId p) : option (ScopeId p) :=
  match s with
  | PredeclaredScope _ => None
  | PackageScope _ k   => Some (PredeclaredScope p)
  | MainBlockScope _ k => Some (PackageScope p k)
  end.

(* ── §2.3 The exact Go scope-start table ───────────────────────────────────── *)
Inductive ScopeStart : Type :=
| StartWholePackage    (* package-level names: forward references are legal *)
| StartAfterSpec       (* a local const or var name: after its own specification *)
| StartAtOwnIdentifier (* a local type name: at its own identifier, so self-reference is a cycle *)
| StartAfterStatement  (* a short-declaration new name: after the whole statement *)
| StartOutermost.      (* a predeclared name: the outer scope, shadowable everywhere *)

Inductive DeclContext : Type :=
| PackageConstDecl | PackageVarDecl | PackageTypeDecl
| LocalConstDecl | LocalVarDecl | LocalTypeDecl
| ShortDecl | PredeclaredDecl.

Definition scope_start (c : DeclContext) : ScopeStart :=
  match c with
  | PackageConstDecl | PackageVarDecl | PackageTypeDecl => StartWholePackage
  | LocalConstDecl | LocalVarDecl => StartAfterSpec
  | LocalTypeDecl => StartAtOwnIdentifier
  | ShortDecl => StartAfterStatement
  | PredeclaredDecl => StartOutermost
  end.

Definition declaring_scope {p} (k : PackageRef p) (c : DeclContext) : ScopeId p :=
  match c with
  | PackageConstDecl | PackageVarDecl | PackageTypeDecl => PackageScope p k
  | LocalConstDecl | LocalVarDecl | LocalTypeDecl | ShortDecl => MainBlockScope p k
  | PredeclaredDecl => PredeclaredScope p
  end.

(* ── §2.2 Binder creation ──────────────────────────────────────────────────── *)
(* Blank creates no object.  Only a short-declaration left side may reuse, and a reuse retains the exact
   existing variable object rather than minting a second one. *)
Inductive BinderClass {p} {i : Input p} (ph : Phase i) : Type :=
| BinderBlank    : BlankRef p -> BinderClass ph
| BinderNew      : BindingSiteRef p -> ObjectRef ph -> BinderClass ph
| BinderReuse    : BindingSiteRef p -> ObjectRef ph -> BinderClass ph.

Parameter binder_class : forall {p} {i : Input p} (ph : Phase i),
  BindingNameRef p -> BinderClass ph.

Definition binder_object {p} {i : Input p} {ph : Phase i} (b : BinderClass ph)
  : option (ObjectRef ph) :=
  match b with
  | BinderBlank _ _ => None
  | BinderNew _ _ o => Some o
  | BinderReuse _ _ o => Some o
  end.

(* A binding site's context and spelling: without these the reservation rule below could never be applied
   to anything, which is exactly how it went unstated. *)
Parameter binding_site_context : forall {p}, BindingSiteRef p -> DeclContext.
Parameter binding_site_name : forall {p}, BindingSiteRef p -> string.

(* The special package-level name `init` is reserved for functions; pinned `gc` rejects a package-level
   const, var or type named `init`, and accepts it as an ordinary local name. *)
Definition PackageInitReserved (c : DeclContext) (n : string) : Prop :=
  (c = PackageConstDecl \/ c = PackageVarDecl \/ c = PackageTypeDecl) /\ n = "init"%string.

(* ── §2.4 Binding: one declarative relation and one reflected decision ──────── *)
Parameter ScopeLookup : forall {p} {i : Input p} (ph : Phase i),
  ScopeId p -> NameUseRef p -> ObjectRef ph -> Prop.
Parameter scope_lookup : forall {p} {i : Input p} (ph : Phase i)
  (s : ScopeId p) (u : NameUseRef p), option (ObjectRef ph).

(* A binding fact is indexed by its exact use and its exact resolved object: the object is not a separate
   projection that could be swapped for another. *)
Parameter BindingAt : forall {p} {i : Input p} (ph : Phase i),
  NameUseRef p -> ObjectRef ph -> UseRole -> Type.

Parameter InnermostScope : forall {p} {i : Input p} (ph : Phase i),
  NameUseRef p -> ScopeId p -> Prop.

(* ── §4 One object fact, not independent capability families ───────────────── *)
(* Exactly one `ObjectFact` per object, so an object cannot acquire incompatible capabilities.  Capabilities
   are dependent refinements of this fact; none is separately mintable. *)
Inductive ObjectFact {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady (phase_equations ph)) : ObjectRef ph -> Type :=
| OFPredeclaredType : forall n t, AdmittedPredeclaredType n t ->
    ObjectFact ph rd (predeclared_object ph n)
| OFPredeclaredAlias : forall n t, AliasPredeclared n t ->
    ObjectFact ph rd (predeclared_object ph n)
| OFPredeclaredBool : forall n b, predeclared_capability n = CapUntypedBool b ->
    ObjectFact ph rd (predeclared_object ph n)
| OFPredeclaredIota : ObjectFact ph rd (predeclared_object ph PIota)
| OFPredeclaredNil : ObjectFact ph rd (predeclared_object ph PNil)
| OFPredeclaredCallable : forall n, predeclared_capability n = CapCallable ->
    ObjectFact ph rd (predeclared_object ph n)
| OFPredeclaredUnmodelled : forall n, predeclared_capability n = CapMissing ->
    ObjectFact ph rd (predeclared_object ph n)
| OFSourceConstant : forall (s : ObjectSiteRef p) (c : ConstSpecRef p)
    (t : SemanticType rd),
    TypedConstant rd t -> ObjectFact ph rd (source_object ph s)
| OFSourceUntypedConstant : forall (s : ObjectSiteRef p) (c : ConstSpecRef p),
    Constant -> ObjectFact ph rd (source_object ph s)
| OFSourceVariable : forall (s : ObjectSiteRef p) (v : VariableSiteRef p)
    (t : SemanticType rd),
    ObjectFact ph rd (source_object ph s)
| OFSourceAlias : forall (s : ObjectSiteRef p) (a : AliasSpecRef p)
    (t : SemanticType rd),
    ObjectFact ph rd (source_object ph s)
| OFSourceDefined : forall (s : ObjectSiteRef p) (d : BoundDefinedTypeRef p)
    (h : DefinedInEnv rd d),
    ObjectFact ph rd (source_object ph s)
| OFMainFunction : forall s : ObjectSiteRef p, ObjectFact ph rd (source_object ph s).

Parameter object_fact : forall {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady (phase_equations ph)) (o : ObjectRef ph), ObjectFact ph rd o.

Definition object_category {p} {i : Input p} {ph : Phase i} {rd} {o}
  (f : ObjectFact ph rd o) : ObjectKind :=
  match f with
  | OFPredeclaredType _ _ _ _ _ => TypeObject
  | OFPredeclaredAlias _ _ _ _ _ => TypeObject
  | OFSourceAlias _ _ _ _ _ => TypeObject
  | OFSourceDefined _ _ _ _ _ => TypeObject
  | OFPredeclaredBool _ _ _ _ _ => ConstantObject
  | OFPredeclaredIota _ _ => ConstantObject
  | OFSourceConstant _ _ _ _ _ _ => ConstantObject
  | OFSourceUntypedConstant _ _ _ _ _ => ConstantObject
  | OFPredeclaredNil _ _ => NilObject
  | OFPredeclaredCallable _ _ _ _ => BuiltinObject
  | OFPredeclaredUnmodelled _ _ _ _ => BuiltinObject
  | OFSourceVariable _ _ _ _ _ => VariableObject
  | OFMainFunction _ _ _ => FunctionObject
  end.

(* Capability refinements: each is a proposition about the one fact, decided by its constructor. *)
Definition IsTypeCapable {p} {i : Input p} {ph : Phase i} {rd} {o}
  (f : ObjectFact ph rd o) : Prop :=
  match f with
  | OFPredeclaredType _ _ _ _ _ => True
  | OFPredeclaredAlias _ _ _ _ _ => True
  | OFSourceAlias _ _ _ _ _ => True
  | OFSourceDefined _ _ _ _ _ => True
  | _ => False
  end.

Definition IsConstantCapable {p} {i : Input p} {ph : Phase i} {rd} {o}
  (f : ObjectFact ph rd o) : Prop :=
  match f with
  | OFPredeclaredBool _ _ _ _ _ => True
  | OFSourceConstant _ _ _ _ _ _ => True
  | OFSourceUntypedConstant _ _ _ _ _ => True
  | _ => False
  end.

Definition IsVariableCapable {p} {i : Input p} {ph : Phase i} {rd} {o}
  (f : ObjectFact ph rd o) : Prop :=
  match f with OFSourceVariable _ _ _ _ _ => True | _ => False end.

Definition IsCallableCapable {p} {i : Input p} {ph : Phase i} {rd} {o}
  (f : ObjectFact ph rd o) : Prop :=
  match f with OFPredeclaredCallable _ _ _ _ => True | _ => False end.

Definition IsContextualCapable {p} {i : Input p} {ph : Phase i} {rd} {o}
  (f : ObjectFact ph rd o) : Prop :=
  match f with
  | OFPredeclaredIota _ _ => True
  | OFPredeclaredNil _ _ => True
  | _ => False
  end.

Definition IsUnmodelled {p} {i : Input p} {ph : Phase i} {rd} {o}
  (f : ObjectFact ph rd o) : Prop :=
  match f with OFPredeclaredUnmodelled _ _ _ _ => True | _ => False end.

(* The exact semantic type an object-capable fact denotes. *)
Definition object_type {p} {i : Input p} {ph : Phase i} {rd} {o}
  (f : ObjectFact ph rd o) : IsTypeCapable f -> SemanticType rd :=
  match f return IsTypeCapable f -> SemanticType rd with
  | OFPredeclaredType _ _ _ t _ => fun _ => PredeclaredType rd t
  | OFPredeclaredAlias _ _ _ t _ => fun _ => PredeclaredType rd t
  | OFSourceAlias _ _ _ _ t => fun _ => t
  | OFSourceDefined _ _ _ d h => fun _ => DefinedType rd d h
  | _ => fun h => match h return SemanticType rd with end
  end.

(* §4.2 The permanent callable target.  At C6 only a predeclared callable object inhabits it; C9 adds
   function-valued heads by adding a constructor, without replacing the type. *)
Inductive CallableTarget {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady (phase_equations ph)) : Type :=
| ObjectCallable : forall (o : ObjectRef ph) (f : ObjectFact ph rd o),
    IsCallableCapable f -> CallableTarget ph rd.

Definition callable_object {p} {i : Input p} {ph : Phase i} {rd}
  (c : CallableTarget ph rd) : ObjectRef ph :=
  match c with ObjectCallable _ _ o _ _ => o end.

(* ── §2.5 Source order within a scope ──────────────────────────────────────── *)
(* One authority for "declared earlier in the same scope".  Short-declaration reuse and the initialization
   dependency order are both stated over it rather than each carrying its own notion of order. *)
Parameter binding_site_scope : forall {p}, BindingSiteRef p -> ScopeId p.
Parameter DeclaredBefore : forall {p}, BindingSiteRef p -> BindingSiteRef p -> Prop.

(* A short-declaration reuse must name an object minted by an earlier binding in the same scope.  Carried
   by the binder itself: a reuse of an unrelated object is unrepresentable, not merely rejected. *)
Definition SameBlockEarlier {p} {i : Input p} {ph : Phase i}
  (b : BindingSiteRef p) (o : ObjectRef ph) : Prop :=
  exists earlier : BindingSiteRef p,
    object_origin o = SourceSite p (binding_site_object_site earlier) /\
    binding_site_scope earlier = binding_site_scope b /\
    DeclaredBefore earlier b.

(* ── §5 The expression-fact algebra ────────────────────────────────────────── *)
(* One sealed dependent judgment.  A failed, outside or blocked expression has no `ExprFact` at all — it has
   the corresponding exact site outcome.  `referenced_object` and `result_form` are projections of this one
   object, never independently populated. *)

(* Result atoms over the retained phase, so every rule can compute its own vector. *)
Inductive ResultAtomAt {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady (phase_equations ph)) : Type :=
| RAUntyped : Constant -> ResultAtomAt ph rd
| RATyped   : forall t : SemanticType rd, TypedConstant rd t -> ResultAtomAt ph rd
| RAValue   : SemanticType rd -> ResultAtomAt ph rd.

Inductive ResultFormAt {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady (phase_equations ph)) : Type :=
| RFFixed        : list (ResultAtomAt ph rd) -> ResultFormAt ph rd
| RFContextual   : ContextualResult -> ResultFormAt ph rd
| RFNoStandalone : ResultFormAt ph rd.

Inductive ExprFact {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady (phase_equations ph)) : ExprRef p -> Type :=
| EFLiteral : forall (r : ExprRef p) (c : Constant), ExprFact ph rd r
| EFName : forall (r : ExprRef p) (u : NameUseRef p) (o : ObjectRef ph) (role : UseRole),
    BindingAt ph u o role -> ObjectFact ph rd o -> ExprFact ph rd r
| EFUnary : forall (r : ExprRef p) (n : UnaryRef p),
    ResultUseFactAt ph rd (DirectUse p (unary_operand_use n)) ->
    UnaryFact ph rd n -> ExprFact ph rd r
| EFApplication : forall (r : ExprRef p) (a : ApplicationRef p),
    ExprFact ph rd (application_head a) -> AppFact ph rd a -> ExprFact ph rd r

(* A result use retains the exact expression fact of its child and the proof that its source role selects a
   result at all.  A head or statement use cannot inhabit it. *)
with ResultUseFactAt {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady (phase_equations ph)) : ExprUseRef p -> Type :=
| RUFOf : forall u : ExprUseRef p,
    ExprFact ph rd (expression_of_use u) ->
    use_refinement u = ResultRefinement -> ResultUseFactAt ph rd u

(* §7.1 The argument facts are indexed by the EXACT ordered source use list, so there is one fact per source
   argument, in source order, with no duplicate and no omission — by construction, not by theorem. *)
with ArgFacts {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady (phase_equations ph)) : list (DirectExprUseRef p) -> Type :=
| ArgsNil  : ArgFacts ph rd []
| ArgsCons : forall (u : DirectExprUseRef p) (rest : list (DirectExprUseRef p)),
    ResultUseFactAt ph rd (DirectUse p u) -> ArgFacts ph rd rest ->
    ArgFacts ph rd (u :: rest)

with UnaryFact {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady (phase_equations ph)) : UnaryRef p -> Type :=
| UFUntyped : forall (n : UnaryRef p) (c c' : Constant),
    NumericConstantKind (constant_kind c) -> negate_constant c = Some c' -> UnaryFact ph rd n
| UFTypedConstant : forall (n : UnaryRef p) (t : SemanticType rd) (b : BasicType),
    Underlying rd t (BasicForm rd b) -> NumericBasic b ->
    TypedConstant rd t -> TypedConstant rd t -> UnaryFact ph rd n
| UFValue : forall (n : UnaryRef p) (t : SemanticType rd) (b : BasicType),
    Underlying rd t (BasicForm rd b) -> NumericBasic b -> UnaryFact ph rd n

(* Arity is a constructor constraint, not a separate theorem: a conversion demands a one-element source
   argument list and `complex` a two-element one, so a wrong-arity application cannot build a fact. *)
with AppFact {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady (phase_equations ph)) : ApplicationRef p -> Type :=
| AFConversion : forall (a : ApplicationRef p) (dst : SemanticType rd) (u : DirectExprUseRef p),
    application_argument_uses a = [u] ->
    ArgFacts ph rd [u] -> ConvRule ph rd a dst -> AppFact ph rd a
| AFComplex : forall (a : ApplicationRef p) (c : CallableTarget ph rd)
    (u1 u2 : DirectExprUseRef p),
    application_argument_uses a = [u1; u2] ->
    ArgFacts ph rd [u1; u2] -> ComplexRuleF ph rd a -> AppFact ph rd a
| AFPrintln : forall (a : ApplicationRef p) (c : CallableTarget ph rd),
    ArgFacts ph rd (application_argument_uses a) ->
    PrintlnRuleF ph rd a -> AppFact ph rd a

with ConvRule {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady (phase_equations ph)) : ApplicationRef p -> SemanticType rd -> Type :=
| CRConstant : forall (a : ApplicationRef p) (dst : SemanticType rd) (b : BasicType)
    (c c' : Constant),
    Underlying rd dst (BasicForm rd b) -> convert_constant_to b c = Some c' ->
    TypedConstant rd dst -> ConvRule ph rd a dst
| CRValue : forall (a : ApplicationRef p) (dst src : SemanticType rd),
    ValueConvertible rd src dst -> ConvRule ph rd a dst

with ComplexRuleF {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady (phase_equations ph)) : ApplicationRef p -> Type :=
| CxFUntyped : forall (a : ApplicationRef p) (c1 c2 cr : Constant),
    NumericConstantKind (constant_kind c1) -> NumericConstantKind (constant_kind c2) ->
    complex_of_constants c1 c2 = Some cr -> ComplexRuleF ph rd a
| CxFTyped : forall (a : ApplicationRef p) (t : SemanticType rd) (f : FloatKind),
    Underlying rd t (BasicForm rd (predeclared_basic_form (float_named_basic f))) ->
    ComplexRuleF ph rd a

with PrintlnRuleF {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady (phase_equations ph)) : ApplicationRef p -> Type :=
| PrFAccepted : forall a : ApplicationRef p, PrintlnRuleF ph rd a.

(* ── §5 Projections: `result_form` and `referenced_object` are views of the one fact ── *)
Definition unary_result {p} {i : Input p} {ph : Phase i} {rd} {n}
  (f : UnaryFact ph rd n) : list (ResultAtomAt ph rd) :=
  match f with
  | UFUntyped _ _ _ _ c' _ _ => [RAUntyped ph rd c']
  | UFTypedConstant _ _ _ t _ _ _ _ neg => [RATyped ph rd t neg]
  | UFValue _ _ _ t _ _ _ => [RAValue ph rd t]
  end.

Definition conv_result {p} {i : Input p} {ph : Phase i} {rd} {a} {dst}
  (r : ConvRule ph rd a dst) : list (ResultAtomAt ph rd) :=
  match r with
  | CRConstant _ _ _ d _ _ _ _ _ tc => [RATyped ph rd d tc]
  | CRValue _ _ _ d _ _ => [RAValue ph rd d]
  end.

Definition complex_result {p} {i : Input p} {ph : Phase i} {rd} {a}
  (r : ComplexRuleF ph rd a) : list (ResultAtomAt ph rd) :=
  match r with
  | CxFUntyped _ _ _ _ _ cr _ _ _ => [RAUntyped ph rd cr]
  | CxFTyped _ _ _ _ f _ =>
      [RAValue ph rd (PredeclaredType rd (complex_named_basic f))]
  end.

Definition app_result {p} {i : Input p} {ph : Phase i} {rd} {a}
  (f : AppFact ph rd a) : list (ResultAtomAt ph rd) :=
  match f with
  | AFConversion _ _ _ _ _ _ _ r => conv_result r
  | AFComplex _ _ _ _ _ _ _ _ r => complex_result r
  | AFPrintln _ _ _ _ _ _ => []
  end.

(* The result a bound name yields is decided by its one object fact, not supplied beside it. *)
Definition name_result {p} {i : Input p} {ph : Phase i} {rd} {o}
  (f : ObjectFact ph rd o) : ResultFormAt ph rd :=
  match f with
  | OFPredeclaredBool _ _ _ b _ => RFFixed ph rd [RAUntyped ph rd (BoolConstant b)]
  | OFSourceUntypedConstant _ _ _ _ c => RFFixed ph rd [RAUntyped ph rd c]
  | OFSourceConstant _ _ _ _ t tc => RFFixed ph rd [RATyped ph rd t tc]
  | OFSourceVariable _ _ _ _ t => RFFixed ph rd [RAValue ph rd t]
  | OFPredeclaredIota _ _ => RFContextual ph rd IotaResult
  | OFPredeclaredNil _ _ => RFContextual ph rd NilResult
  | _ => RFNoStandalone ph rd
  end.

Definition expr_result {p} {i : Input p} {ph : Phase i} {rd} {r}
  (f : ExprFact ph rd r) : ResultFormAt ph rd :=
  match f with
  | EFLiteral _ _ _ c => RFFixed ph rd [RAUntyped ph rd c]
  | EFName _ _ _ _ _ _ _ of => name_result of
  | EFUnary _ _ _ _ _ uf => RFFixed ph rd (unary_result uf)
  | EFApplication _ _ _ _ _ af => RFFixed ph rd (app_result af)
  end.

Definition expr_referenced_object {p} {i : Input p} {ph : Phase i} {rd} {r}
  (f : ExprFact ph rd r) : option (ObjectRef ph) :=
  match f with
  | EFName _ _ _ _ o _ _ _ => Some o
  | _ => None
  end.

(* ── §8 A statement fact exists only for an eligible statement ─────────────── *)
(* Definite failures, requirements and blocked dependents live solely in the exact statement site outcome;
   they are not branches of this type, which would contradict what an accepted fact means. *)
Definition IsPrintlnApp {p} {i : Input p} {ph : Phase i} {rd} {a}
  (f : AppFact ph rd a) : Prop :=
  match f with AFPrintln _ _ _ _ _ _ => True | _ => False end.

Definition IsConversionApp {p} {i : Input p} {ph : Phase i} {rd} {a}
  (f : AppFact ph rd a) : Prop :=
  match f with AFConversion _ _ _ _ _ _ _ _ => True | _ => False end.

Definition IsComplexApp {p} {i : Input p} {ph : Phase i} {rd} {a}
  (f : AppFact ph rd a) : Prop :=
  match f with AFComplex _ _ _ _ _ _ _ _ _ => True | _ => False end.

Inductive StmtFact {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady (phase_equations ph)) : ExpressionStatementRef p -> Type :=
| SFPrintln : forall (s : ExpressionStatementRef p) (a : ApplicationRef p)
    (f : AppFact ph rd a),
    statement_application s = Some a -> IsPrintlnApp f -> StmtFact ph rd s.

Definition statement_application_of {p} {i : Input p} {ph : Phase i} {rd} {s}
  (f : StmtFact ph rd s) : ApplicationRef p :=
  match f with SFPrintln _ _ _ a _ _ _ => a end.

(* ── §7 One intrinsic result occurrence ────────────────────────────────────── *)
Definition result_atoms_of {p} {i : Input p} {ph : Phase i} {rd} {u}
  (f : ResultUseFactAt ph rd u) : list (ResultAtomAt ph rd) :=
  match f with
  | RUFOf _ _ _ ef _ =>
      match expr_result ef with
      | RFFixed _ _ l => l
      | RFContextual _ _ _ => []
      | RFNoStandalone _ _ => []
      end
  end.

(* The atom is not stored beside the vector: the split equation forces it to BE the element at that
   position, and the position is derived from the split. *)
Record ResultOccurrenceAt {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady (phase_equations ph)) (u : ExprUseRef p) : Type := MakeOccurrence {
  occ_fact   : ResultUseFactAt ph rd u;
  occ_before : list (ResultAtomAt ph rd);
  occ_atom   : ResultAtomAt ph rd;
  occ_after  : list (ResultAtomAt ph rd);
  occ_splits : result_atoms_of occ_fact = occ_before ++ occ_atom :: occ_after
}.

Definition occurrence_position {p} {i : Input p} {ph : Phase i} {rd} {u}
  (o : ResultOccurrenceAt ph rd u) : nat := List.length (occ_before ph rd u o).

(* ── §11 One intrinsic, source-indexed result-consumption plan ─────────────── *)
Inductive ConsumptionTarget (p : SyntaxProgram) : Type :=
| NamedTarget : BindingSiteRef p -> ConsumptionTarget p
| BlankTarget : BlankRef p -> ConsumptionTarget p.

(* The exact source target sequence and right-hand-side use sequence belong to the site itself. *)
Parameter site_targets : forall {p}, ConsumptionSiteRef p -> list (ConsumptionTarget p).
Parameter site_uses : forall {p}, ConsumptionSiteRef p -> list (ExprUseRef p).

Inductive ConstAtomAt {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady (phase_equations ph)) : ResultAtomAt ph rd -> Prop :=
| CAUntyped : forall c, ConstAtomAt ph rd (RAUntyped ph rd c)
| CATyped   : forall t tc, ConstAtomAt ph rd (RATyped ph rd t tc).

(* The exact defaulting / representability / assignability evidence an entry must carry. *)
Inductive AtomFits {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady (phase_equations ph)) : ResultAtomAt ph rd -> SemanticType rd -> Prop :=
| FitUntyped : forall c t, Representable rd t c -> AtomFits ph rd (RAUntyped ph rd c) t
| FitTyped   : forall (s : SemanticType rd) tc t, Assignable rd s t ->
    AtomFits ph rd (RATyped ph rd s tc) t
| FitValue   : forall (s : SemanticType rd) t, Assignable rd s t ->
    AtomFits ph rd (RAValue ph rd s) t.

(* Each plan is indexed by the EXACT remaining source target list, so target coverage, order and
   non-duplication hold by construction rather than by a tautological length equation. *)
Inductive ConstPlan {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady (phase_equations ph)) : list (ConsumptionTarget p) -> Type :=
| CPNil  : ConstPlan ph rd []
| CPCons : forall (t : ConsumptionTarget p) (rest : list (ConsumptionTarget p))
    (u : ExprUseRef p) (o : ResultOccurrenceAt ph rd u),
    ConstAtomAt ph rd (occ_atom ph rd u o) ->
    option (SemanticType rd) -> ConstPlan ph rd rest -> ConstPlan ph rd (t :: rest).

Inductive VarPlan {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady (phase_equations ph)) : list (ConsumptionTarget p) -> Type :=
| VPNil  : VarPlan ph rd []
| VPCons : forall (t : ConsumptionTarget p) (rest : list (ConsumptionTarget p))
    (u : ExprUseRef p) (o : ResultOccurrenceAt ph rd u) (ty : SemanticType rd),
    AtomFits ph rd (occ_atom ph rd u o) ty -> VarPlan ph rd rest ->
    VarPlan ph rd (t :: rest).

(* A new short binder retains its exact object; a same-block reuse retains the exact existing object;
   blank retains neither. *)
Inductive ShortBinder {p} {i : Input p} (ph : Phase i) : Type :=
| SBNew   : BindingSiteRef p -> ObjectRef ph -> ShortBinder ph
| SBReuse : forall (b : BindingSiteRef p) (o : ObjectRef ph),
    SameBlockEarlier b o -> ShortBinder ph.

Inductive ShortPlan {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady (phase_equations ph)) : list (ConsumptionTarget p) -> Type :=
| SPNil   : ShortPlan ph rd []
| SPNamed : forall (b : BindingSiteRef p) (rest : list (ConsumptionTarget p))
    (bind : ShortBinder ph) (u : ExprUseRef p) (o : ResultOccurrenceAt ph rd u)
    (ty : SemanticType rd),
    AtomFits ph rd (occ_atom ph rd u o) ty -> ShortPlan ph rd rest ->
    ShortPlan ph rd (NamedTarget p b :: rest)
| SPBlank : forall (k : BlankRef p) (rest : list (ConsumptionTarget p))
    (u : ExprUseRef p) (o : ResultOccurrenceAt ph rd u),
    ShortPlan ph rd rest -> ShortPlan ph rd (BlankTarget p k :: rest).

(* At least one nonblank short binder must be new; pinned `gc` rejects a short declaration otherwise. *)
Fixpoint ShortHasNewName {p} {i : Input p} {ph : Phase i} {rd} {ts}
  (pl : ShortPlan ph rd ts) : Prop :=
  match pl with
  | SPNil _ _ => False
  | SPNamed _ _ _ _ bind _ _ _ _ rest =>
      match bind with SBNew _ _ _ => True | SBReuse _ _ _ _ => ShortHasNewName rest end
  | SPBlank _ _ _ _ _ _ rest => ShortHasNewName rest
  end.

(* ── §12 Initialization units keep constants out of the runtime projection ──── *)
Inductive InitUnit (p : SyntaxProgram) : Type :=
| ConstEvalUnit  : ConstSpecRef p -> InitUnit p
| VarInitUnit    : BindingSiteRef p -> InitUnit p
| BlankConstUnit : BlankRef p -> InitUnit p
| BlankVarUnit   : BlankRef p -> InitUnit p.

(* A blank CONST is compile-time work; only variable and blank-variable work reaches the C7 store. *)
Definition RuntimeInitUnit {p} (u : InitUnit p) : bool :=
  match u with
  | ConstEvalUnit _ _ => false
  | BlankConstUnit _ _ => false
  | VarInitUnit _ _ => true
  | BlankVarUnit _ _ => true
  end.

(* The consumption fact IS the plan at the site's own targets.  Coverage is therefore structural: a plan
   for another site's targets cannot be offered here, so no separate coverage theorem is needed and none
   could be stated tautologically. *)
Definition ConsumptionFact {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady (phase_equations ph)) (c : ConsumptionSiteRef p) : Type :=
  match c with
  | ConstSite _ _ => ConstPlan ph rd (site_targets c)
  | VarSite _ _   => VarPlan ph rd (site_targets c)
  | ShortSite _ _ => ShortPlan ph rd (site_targets c)
  end.

(* The use sequence a plan actually consumes, in plan order. *)
Fixpoint const_plan_uses {p} {i : Input p} {ph : Phase i} {rd} {ts}
  (pl : ConstPlan ph rd ts) : list (ExprUseRef p) :=
  match pl with
  | CPNil _ _ => []
  | CPCons _ _ _ _ u _ _ _ sub => u :: const_plan_uses sub
  end.

Fixpoint var_plan_uses {p} {i : Input p} {ph : Phase i} {rd} {ts}
  (pl : VarPlan ph rd ts) : list (ExprUseRef p) :=
  match pl with
  | VPNil _ _ => []
  | VPCons _ _ _ _ u _ _ _ sub => u :: var_plan_uses sub
  end.

Fixpoint short_plan_uses {p} {i : Input p} {ph : Phase i} {rd} {ts}
  (pl : ShortPlan ph rd ts) : list (ExprUseRef p) :=
  match pl with
  | SPNil _ _ => []
  | SPNamed _ _ _ _ _ u _ _ _ sub => u :: short_plan_uses sub
  | SPBlank _ _ _ _ u _ sub => u :: short_plan_uses sub
  end.

Definition plan_uses {p} {i : Input p} {ph : Phase i} {rd} (c : ConsumptionSiteRef p)
  : ConsumptionFact ph rd c -> list (ExprUseRef p) :=
  match c as c' return ConsumptionFact ph rd c' -> list (ExprUseRef p) with
  | ConstSite _ _ => fun f => const_plan_uses f
  | VarSite _ _   => fun f => var_plan_uses f
  | ShortSite _ _ => fun f => short_plan_uses f
  end.

(* ── §12 Package initialization order ──────────────────────────────────────── *)
(* The nodes are the package's initialization units; the edges are name uses inside them. *)
Parameter package_init_units : forall {p}, PackageRef p -> list (InitUnit p).
Parameter init_unit_uses : forall {p}, InitUnit p -> list (NameUseRef p).
Parameter init_unit_object : forall {p} {i : Input p} (ph : Phase i),
  InitUnit p -> option (ObjectRef ph).

(* An edge IS a resolved read: it carries the exact use and the exact binding that produced it, so an edge
   cannot be posted beside the bindings it claims to summarise. *)
Inductive InitEdge {p} {i : Input p} (ph : Phase i) (k : PackageRef p)
  : InitUnit p -> InitUnit p -> Prop :=
| InitReads : forall (from to : InitUnit p) (u : NameUseRef p) (o : ObjectRef ph) (role : UseRole),
    List.In from (package_init_units k) ->
    List.In to (package_init_units k) ->
    List.In u (init_unit_uses from) ->
    BindingAt ph u o role ->
    init_unit_object ph to = Some o ->
    InitEdge ph k from to.

(* `y` initializes before `x` whenever `x` reads `y`. *)
Definition PrecedesIn {A : Type} (l : list A) (x y : A) : Prop :=
  exists before mid after, l = before ++ x :: mid ++ y :: after.

(* The ordered outcome carries its own correctness: covering, duplicate-freedom and edge respect are
   fields, not separate theorems that could be stated about a different order. *)
Record InitOrder {p} {i : Input p} (ph : Phase i) (k : PackageRef p) : Type := MakeInitOrder {
  init_sequence  : list (InitUnit p);
  init_covers    : forall u : InitUnit p,
                     List.In u (package_init_units k) <-> List.In u init_sequence;
  init_nodup     : NoDup init_sequence;
  init_respects  : forall from to : InitUnit p,
                     InitEdge ph k from to -> PrecedesIn init_sequence to from
}.

(* Source order is the tie-break, not the rule: it decides only between units with no edge either way. *)
Parameter init_unit_site : forall {p}, InitUnit p -> BindingSiteRef p.
Definition SourceOrderTieBreak {p} {i : Input p} {ph : Phase i} {k : PackageRef p}
  (o : InitOrder ph k) : Prop :=
  forall a b : InitUnit p,
    List.In a (package_init_units k) -> List.In b (package_init_units k) ->
    ~ InitEdge ph k a b -> ~ InitEdge ph k b a ->
    DeclaredBefore (init_unit_site a) (init_unit_site b) ->
    PrecedesIn (init_sequence ph k o) a b.

(* Only variable work reaches the C7 runtime store; constant evaluation is compile-time. *)
Definition runtime_initialization {p} {i : Input p} {ph : Phase i} {k : PackageRef p}
  (o : InitOrder ph k) : list (InitUnit p) :=
  List.filter RuntimeInitUnit (init_sequence ph k o).

(* ── §9 Requirements are exact missing facts ───────────────────────────────── *)
(* Each constructor retains the exact partial facts already established at that site, so a requirement
   cannot pair an arbitrary use with an arbitrary object, and satisfaction never asks whether the outcome
   is already supported. *)
Inductive SiteRequirement {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady (phase_equations ph)) : Site p -> Type :=
| NeedTypeMeaning : forall (u : NameUseRef p) (o : ObjectRef ph) (role : UseRole),
    BindingAt ph u o role -> ObjectFact ph rd o -> SiteRequirement ph rd (SBinding p u)
| NeedValueMeaning : forall (u : NameUseRef p) (o : ObjectRef ph) (role : UseRole),
    BindingAt ph u o role -> ObjectFact ph rd o -> SiteRequirement ph rd (SBinding p u)
| NeedApplication : forall (a : ApplicationRef p),
    ExprFact ph rd (application_head a) ->
    ArgFacts ph rd (application_argument_uses a) ->
    ErasedProfile -> SiteRequirement ph rd (SApplication p a)
| NeedStatement : forall (s : ExpressionStatementRef p) (a : ApplicationRef p),
    statement_application s = Some a ->
    ExprFact ph rd (application_head a) -> SiteRequirement ph rd (SStatement p s)
| NeedUnary : forall n : UnaryRef p,
    ResultUseFactAt ph rd (DirectUse p (unary_operand_use n)) ->
    SiteRequirement ph rd (SUnary p n).

(* Satisfaction is a question about the fact families, not about the site table. *)
Definition RequirementSatisfied {p} {i : Input p} {ph : Phase i} {rd} {s}
  (r : SiteRequirement ph rd s) : Prop :=
  match r with
  | NeedTypeMeaning _ _ _ _ _ _ f => IsTypeCapable f
  | NeedValueMeaning _ _ _ _ _ _ f =>
      IsConstantCapable f \/ IsVariableCapable f \/ IsContextualCapable f
  | NeedApplication _ _ a _ _ _ => inhabited (AppFact ph rd a)
  | NeedStatement _ _ st _ _ _ => inhabited (StmtFact ph rd st)
  | NeedUnary _ _ n _ => inhabited (UnaryFact ph rd n)
  end.

Parameter requirement_dec : forall {p} {i : Input p} {ph : Phase i} {rd} {s}
  (r : SiteRequirement ph rd s),
  { RequirementSatisfied r } + { ~ RequirementSatisfied r }.

(* The exact bound object a name requirement is about is read off its binding fact, never supplied. *)
Definition requirement_object {p} {i : Input p} {ph : Phase i} {rd} {s}
  (r : SiteRequirement ph rd s) : option (ObjectRef ph) :=
  match r with
  | NeedTypeMeaning _ _ _ o _ _ _ => Some o
  | NeedValueMeaning _ _ _ o _ _ _ => Some o
  | _ => None
  end.

Parameter requirement_view : forall {p} {i : Input p} {ph : Phase i} {rd} {s},
  SiteRequirement ph rd s -> RequirementView.

(* ── §10 Site failures retain their exact causes ───────────────────────────── *)
(* A duplicate declaration is a failure at the declaration site, not at some unrelated name use; an argument
   failure retains the exact argument use, not a free index; a consumption failure retains the exact
   occurrence, not a free position. *)
Inductive SiteFailure {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady (phase_equations ph)) : Site p -> Type :=
| FUnresolvedName : forall u : NameUseRef p, SiteFailure ph rd (SBinding p u)
| FDuplicateDeclaration : forall earlier later : BindingSiteRef p,
    SiteFailure ph rd (SDeclaration p later)
| FPackageInitReserved : forall b : BindingSiteRef p, SiteFailure ph rd (SDeclaration p b)
| FArgumentRejected : forall (a : ApplicationRef p) (u : DirectExprUseRef p),
    In u (application_argument_uses a) -> ArgumentReason ->
    SiteFailure ph rd (SApplication p a)
| FInvalidConversion : forall a : ApplicationRef p,
    OperandResultView -> TypeView -> list (ExprRef p) -> SiteFailure ph rd (SApplication p a)
| FOperandRejected : forall n : UnaryRef p, OperandReason -> SiteFailure ph rd (SUnary p n)
| FNotAStatement : forall t : ExpressionStatementRef p, StatementReason ->
    SiteFailure ph rd (SStatement p t)
| FResultCountWrong : forall c : ConsumptionSiteRef p, nat -> nat ->
    SiteFailure ph rd (SConsumption p c)
| FNotAssignableAt : forall (c : ConsumptionSiteRef p) (u : ExprUseRef p),
    ResultOccurrenceAt ph rd u -> SemanticType rd -> SiteFailure ph rd (SConsumption p c)
| FNotRepresentableAt : forall (c : ConsumptionSiteRef p) (u : ExprUseRef p),
    ResultOccurrenceAt ph rd u -> SemanticType rd -> SiteFailure ph rd (SConsumption p c)
| FConstInitNotConstant : forall (c : ConsumptionSiteRef p) (u : ExprUseRef p),
    ResultOccurrenceAt ph rd u -> ConstInitReason -> SiteFailure ph rd (SConsumption p c)
| FNoNewVariable : forall d : ShortDeclRef p,
    SiteFailure ph rd (SConsumption p (ShortSite p d))
| FContext : forall r : ExprRef p, ContextReason -> SiteFailure ph rd (SExpression p r)
| FDefaultNotRepresentable : forall r : ExprRef p,
    UntypedConstantKind -> TypeView -> SiteFailure ph rd (SExpression p r)
| FUnusedLocal : forall v : VariableSiteRef p, SiteFailure ph rd (SVariable p v)
| FInitializationCycle : forall k : PackageRef p, SiteFailure ph rd (SDependency p k).

(* ── The fact a supported site carries ─────────────────────────────────────── *)
Parameter DeclarationFact : forall {p} {i : Input p} (ph : Phase i), BindingSiteRef p -> Type.
(* A supported dependency site is exactly a valid initialization order for that package. *)
Definition DependencyFact {p} {i : Input p} (ph : Phase i) (k : PackageRef p) : Type :=
  InitOrder ph k.
Parameter VariableFact : forall {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady (phase_equations ph)), VariableSiteRef p -> Type.

Definition SiteFact {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady (phase_equations ph)) (s : Site p) : Type :=
  match s with
  | SBinding _ u     => { o : ObjectRef ph & { role : UseRole & BindingAt ph u o role } }
  | SExpression _ r  => ExprFact ph rd r
  | SUse _ u         => match use_refinement u with
                        | ResultRefinement => ResultUseFactAt ph rd u
                        | _ => ExprFact ph rd (expression_of_use u)
                        end
  | SApplication _ a => AppFact ph rd a
  | SStatement _ t   => StmtFact ph rd t
  | SUnary _ n       => UnaryFact ph rd n
  | SConsumption _ c => ConsumptionFact ph rd c
  | SVariable _ v    => VariableFact ph rd v
  | SDeclaration _ b => DeclarationFact ph b
  | SDependency _ k  => DependencyFact ph k
  end.

(* ── §10 One outcome per site; no client constructs these values ────────────── *)
Inductive SiteOutcome {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady (phase_equations ph)) : Site p -> Type :=
| Supported       : forall s, SiteFact ph rd s -> SiteOutcome ph rd s
| DefiniteFailure : forall s, SiteFailure ph rd s -> SiteOutcome ph rd s
| Outside         : forall s, SiteRequirement ph rd s -> SiteOutcome ph rd s
| Blocked         : forall s pred, SiteDependency p pred s ->
                    SiteOutcome ph rd pred -> SiteOutcome ph rd s.

Definition IsSupported {p} {i : Input p} {ph : Phase i} {rd} {s}
  (o : SiteOutcome ph rd s) : Prop :=
  match o with Supported _ _ _ _ => True | _ => False end.

Definition supported_fact {p} {i : Input p} {ph : Phase i} {rd} {s}
  (o : SiteOutcome ph rd s) : IsSupported o -> SiteFact ph rd s :=
  match o in SiteOutcome _ _ s0 return IsSupported o -> SiteFact ph rd s0 with
  | Supported _ _ _ f => fun _ => f
  | DefiniteFailure _ _ _ _ => fun h => match h return SiteFact ph rd _ with end
  | Outside _ _ _ _ => fun h => match h return SiteFact ph rd _ with end
  | Blocked _ _ _ _ _ _ => fun h => match h return SiteFact ph rd _ with end
  end.

Definition IsRootOutside {p} {i : Input p} {ph : Phase i} {rd} {s}
  (o : SiteOutcome ph rd s) : Prop :=
  match o with Outside _ _ _ _ => True | _ => False end.

Definition root_requirement {p} {i : Input p} {ph : Phase i} {rd} {s}
  (o : SiteOutcome ph rd s) : IsRootOutside o -> SiteRequirement ph rd s :=
  match o in SiteOutcome _ _ s0 return IsRootOutside o -> SiteRequirement ph rd s0 with
  | Outside _ _ _ r => fun _ => r
  | Supported _ _ _ _ => fun h => match h return SiteRequirement ph rd _ with end
  | DefiniteFailure _ _ _ _ => fun h => match h return SiteRequirement ph rd _ with end
  | Blocked _ _ _ _ _ _ => fun h => match h return SiteRequirement ph rd _ with end
  end.

Parameter phase_outcome : forall {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady (phase_equations ph)) (s : Site p), SiteOutcome ph rd s.

(* ── §13 The complete diagnostic authority ─────────────────────────────────── *)
(* Site failures enter through one constructor; the package- and program-level reasons keep their own,
   because they have no single site.  Every current public constructor survives. *)
(* Indexed by the phase, not by a ready environment: a cyclic phase has no environment and still needs its
   type-cycle diagnostic.  The site-failure constructor carries the readiness that failure required. *)
Inductive DiagnosticReason {p} {i : Input p} (ph : Phase i) : Type :=
| AtSiteFailure : forall (rd : TypeReady (phase_equations ph)) (s : Site p),
    SiteFailure ph rd s -> DiagnosticReason ph
| TypeCycleFound : TypeCycle (phase_equations ph) -> DiagnosticReason ph
| MainRedeclared : forall later earlier : ObjectSiteRef p, DiagnosticReason ph
| MissingMainEntry : PackageRef p -> DiagnosticReason ph
| BuildOutputIsDirectory : PackageRef p -> string -> DiagnosticReason ph.

Definition site_failure_code {p} {i : Input p} {ph : Phase i} {rd} {s}
  (f : SiteFailure ph rd s) : DiagnosticCode :=
  match f with
  | FUnresolvedName _ _ _ => CodeUnresolvedName
  | FDuplicateDeclaration _ _ _ _ => CodeDuplicateDeclaration
  | FPackageInitReserved _ _ _ => CodeContext
  | FArgumentRejected _ _ _ _ _ _ => CodeArgument
  | FInvalidConversion _ _ _ _ _ _ => CodeInvalidConversion
  | FOperandRejected _ _ _ _ => CodeOperand
  | FNotAStatement _ _ _ _ => CodeNotAStatement
  | FResultCountWrong _ _ _ _ _ => CodeResultCount
  | FNotAssignableAt _ _ _ _ _ _ => CodeNotAssignable
  | FNotRepresentableAt _ _ _ _ _ _ => CodeNotRepresentable
  | FConstInitNotConstant _ _ _ _ _ _ => CodeConstInitializerNotConstant
  | FNoNewVariable _ _ _ => CodeNoNewVariable
  | FContext _ _ _ _ => CodeContext
  | FDefaultNotRepresentable _ _ _ _ _ => CodeDefaultNotRepresentable
  | FUnusedLocal _ _ _ => CodeUnusedLocal
  | FInitializationCycle _ _ _ => CodeInitializationCycle
  end.

Definition diagnostic_code {p} {i : Input p} {ph : Phase i}
  (d : DiagnosticReason ph) : DiagnosticCode :=
  match d with
  | AtSiteFailure _ _ _ f => site_failure_code f
  | TypeCycleFound _ _ => CodeTypeCycle
  | MainRedeclared _ _ _ => CodeMainRedeclared
  | MissingMainEntry _ _ => CodeMissingMainEntry
  | BuildOutputIsDirectory _ _ _ => CodeBuildOutputIsDirectory
  end.

(* The erased payload keeps every observation the current public record retains.  The target and source
   target are what make two otherwise-alike diagnostics compare unequal — `byte` and `uint8` differ by their
   source spelling, and two build-output collisions differ by name — so dropping them would silently
   collapse distinct diagnostics and break canonical `NoDup`. *)
Record ErasedDiagnostic : Type := MakeErasedDiagnostic {
  erased_code   : DiagnosticCode;
  erased_primary : ErasedAnchor;
  erased_related : list ErasedAnchor;
  erased_target  : option TypeView;
  erased_output  : option string;
  erased_source_target : option TypeExpr
}.

Definition diagnostic_target {p} {i : Input p} {ph : Phase i}
  (d : DiagnosticReason ph) : option TypeView :=
  match d with
  | AtSiteFailure _ _ _ f =>
      match f with
      | FInvalidConversion _ _ _ _ t _ => Some t
      | FDefaultNotRepresentable _ _ _ _ t => Some t
      | FNotAssignableAt _ _ _ _ _ t => Some (type_view t)
      | FNotRepresentableAt _ _ _ _ _ t => Some (type_view t)
      | _ => None
      end
  | _ => None
  end.

Definition diagnostic_output {p} {i : Input p} {ph : Phase i}
  (d : DiagnosticReason ph) : option string :=
  match d with BuildOutputIsDirectory _ _ nm => Some nm | _ => None end.

Parameter diagnostic_source_target : forall {p} {i : Input p} {ph : Phase i},
  DiagnosticReason ph -> option TypeExpr.
Parameter diagnostic_primary : forall {p} {i : Input p} {ph : Phase i},
  DiagnosticReason ph -> DiagnosticAnchor p.
Parameter diagnostic_related : forall {p} {i : Input p} {ph : Phase i},
  DiagnosticReason ph -> list (DiagnosticAnchor p).
Parameter erase_anchor : forall {p}, DiagnosticAnchor p -> ErasedAnchor.
Parameter diagnostic_compare : forall {p} {i : Input p} {ph : Phase i},
  DiagnosticReason ph -> DiagnosticReason ph -> comparison.

Definition erase_diagnostic {p} {i : Input p} {ph : Phase i}
  (d : DiagnosticReason ph) : ErasedDiagnostic :=
  MakeErasedDiagnostic (diagnostic_code d) (erase_anchor (diagnostic_primary d))
    (List.map erase_anchor (diagnostic_related d))
    (diagnostic_target d) (diagnostic_output d) (diagnostic_source_target d).

(* ── §14 Boundaries, the report, and the outcome ───────────────────────────── *)
Record PackedBoundary {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady (phase_equations ph)) : Type := MakeBoundary {
  boundary_site : Site p;
  boundary_requirement : SiteRequirement ph rd boundary_site;
  boundary_is_root : IsRootOutside (phase_outcome ph rd boundary_site)
}.

Definition boundary_view {p} {i : Input p} {ph : Phase i} {rd}
  (b : PackedBoundary ph rd) : RequirementView :=
  requirement_view (boundary_requirement ph rd b).

(* The site table is the authority; the report lists are its canonical projections, not peer lists.
   `Core`, `Elaboration` and `phase` are the existing repository names, stubbed once above. *)
Parameter core_diagnostics : forall {p} (c : Core p), list (DiagnosticReason (phase c)).
Parameter core_boundaries : forall {p} (c : Core p),
  list { rd : TypeReady (phase_equations (phase c)) & PackedBoundary (phase c) rd }.

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

(* ── Accepted facts are projections of the one retained phase ──────────────── *)
Definition accepted_phase (cp : Program) : Phase (core_input (core cp)) := phase (core cp).
(* The one readiness authority is the retained phase result; there is no second `core_ready` beside it. *)
Parameter accepted_is_ready : forall cp : Program,
  IsTypeReady (phase_type_result (accepted_phase cp)).
Definition accepted_ready (cp : Program) : TypeReady (phase_equations (accepted_phase cp)) :=
  ready_of (phase_type_result (accepted_phase cp)) (accepted_is_ready cp).
Definition accepted_outcome (cp : Program) (s : Site (source cp))
  : SiteOutcome (accepted_phase cp) (accepted_ready cp) s :=
  phase_outcome (accepted_phase cp) (accepted_ready cp) s.

(* Derived, not postulated: an accepted core has no diagnostic and no boundary, and the report lists are
   exact projections of the root site outcomes, so no site can be failed, outside, or blocked. *)
Lemma accepted_supported : forall (cp : Program) (s : Site (source cp)),
  IsSupported (accepted_outcome cp s).
Proof. Admitted.

Definition accepted_fact (cp : Program) (s : Site (source cp))
  : SiteFact (accepted_phase cp) (accepted_ready cp) s :=
  supported_fact (accepted_outcome cp s) (accepted_supported cp s).

Definition AcceptedType (cp : Program) : Type := SemanticType (accepted_ready cp).
Definition Object (cp : Program) : Type := ObjectRef (accepted_phase cp).
Definition ExpressionFact (cp : Program) (r : ExprRef (source cp)) : Type :=
  ExprFact (accepted_phase cp) (accepted_ready cp) r.
Definition expression_fact (cp : Program) (r : ExprRef (source cp)) : ExpressionFact cp r :=
  accepted_fact cp (SExpression (source cp) r).
Definition ApplicationFact (cp : Program) (a : ApplicationRef (source cp)) : Type :=
  AppFact (accepted_phase cp) (accepted_ready cp) a.
Definition application_fact (cp : Program) (a : ApplicationRef (source cp))
  : ApplicationFact cp a := accepted_fact cp (SApplication (source cp) a).
Definition StatementFact (cp : Program) (t : ExpressionStatementRef (source cp)) : Type :=
  StmtFact (accepted_phase cp) (accepted_ready cp) t.
Definition statement_fact (cp : Program) (t : ExpressionStatementRef (source cp))
  : StatementFact cp t := accepted_fact cp (SStatement (source cp) t).
Definition ConsumptionAt (cp : Program) (c : ConsumptionSiteRef (source cp)) : Type :=
  ConsumptionFact (accepted_phase cp) (accepted_ready cp) c.
Definition consumption_at (cp : Program) (c : ConsumptionSiteRef (source cp))
  : ConsumptionAt cp c := accepted_fact cp (SConsumption (source cp) c).

(* ── §15 Rendering: contexts, exact equations, real whitespace properties ──── *)
Inductive RenderContext : Type :=
| TopContext | UnaryOperandContext | ApplicationHeadContext | ApplicationArgumentContext.

(* Canonical grouping is decided by the spec count: exactly one renders ungrouped, zero or two-or-more
   render grouped.  Pinned `gc` accepts the empty group, so both forms are reachable. *)
Definition renders_grouped {A : Type} (specs : list A) : bool :=
  match specs with [_] => false | _ => true end.

Parameter needs_parens : RenderContext -> Expr -> bool.
Parameter render_in : RenderContext -> Expr -> string.
Parameter render_expr : Expr -> string.
Parameter render_literal : Literal -> string.
Parameter render_type_expr : TypeExpr -> string.
Parameter render_binding_name : BindingName -> string.
Parameter render_declaration : Declaration -> string.
Parameter render_stmt : Stmt -> string.
Parameter render_block : Block -> string.
Parameter render_top_decl : TopLevelDecl -> string.
Parameter render_file : SyntaxFile -> string.
Parameter render_const_spec : ConstSpec -> string.
Parameter render_var_spec : VarSpec -> string.
Parameter render_type_spec : TypeSpec -> string.
Parameter render_program : SyntaxProgram -> list (string * string).
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

(* Exactly two adjacent bytes: a token-boundary property, not a scan of arbitrary contents. *)
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

(* No line ends in a space or a tab, and the final byte is a newline. *)
Definition NoTrailingBlank (s : string) : Prop :=
  ~ HasAdjacent SpaceChar NewlineChar s /\
  ~ HasAdjacent TabChar NewlineChar s /\
  last_char s = Some NewlineChar.
```

## Theorems

Every statement below elaborates over the names above; proof bodies are the implementation's work.

```coq
(* ── §14.1 The three branches are characterized exactly, in both directions ─── *)
(* Each branch is stated as an `iff`, so the theorem claims neither more nor less than the condition the
   directive fixes.  A one-way implication would let a branch be taken for a reason the contract never
   names. *)
Definition IsCompiled {p} (o : Outcome p) : Prop :=
  match o with Compiled _ _ _ => True | _ => False end.
Definition IsRejected {p} (o : Outcome p) : Prop :=
  match o with Rejected _ _ => True | _ => False end.
Definition IsOutsideScope {p} (o : Outcome p) : Prop :=
  match o with OutsideScope _ _ => True | _ => False end.

Definition elaborated (p : SyntaxProgram) : Core p := elaboration_core (elaborate p).

Theorem compiled_iff : forall p : SyntaxProgram,
  IsCompiled (compile p) <->
  core_diagnostics (elaborated p) = [] /\ core_boundaries (elaborated p) = [].
Proof. Admitted.

Theorem rejected_iff : forall p : SyntaxProgram,
  IsRejected (compile p) <-> core_diagnostics (elaborated p) <> [].
Proof. Admitted.

Theorem outside_scope_iff : forall p : SyntaxProgram,
  IsOutsideScope (compile p) <->
  core_diagnostics (elaborated p) = [] /\ core_boundaries (elaborated p) <> [].
Proof. Admitted.

(* ── §14.2 `decision` and `compile` agree on every program ─────────────────── *)
Definition DecidesAccepted {p} {c : Core p} (d : Decision c) : Prop :=
  match d with DecisionAccepted _ _ _ => True | _ => False end.
Definition DecidesRejected {p} {c : Core p} (d : Decision c) : Prop :=
  match d with DecisionRejected _ _ => True | _ => False end.
Definition DecidesOutside {p} {c : Core p} (d : Decision c) : Prop :=
  match d with DecisionOutside _ _ _ => True | _ => False end.

Theorem decision_agrees_compiled : forall p : SyntaxProgram,
  DecidesAccepted (decision (elaborate p)) <-> IsCompiled (compile p).
Proof. Admitted.

Theorem decision_agrees_rejected : forall p : SyntaxProgram,
  DecidesRejected (decision (elaborate p)) <-> IsRejected (compile p).
Proof. Admitted.

Theorem decision_agrees_outside : forall p : SyntaxProgram,
  DecidesOutside (decision (elaborate p)) <-> IsOutsideScope (compile p).
Proof. Admitted.

(* ── §14.3 Every branch retains the exact core it decided on ───────────────── *)
(* Equality to a recomputation is not provenance: each branch carries back the very `Core` the elaboration
   produced.  The `Compiled` branch transports along its own source equation rather than re-elaborating. *)
Theorem compiled_retains_core : forall (p : SyntaxProgram) (cp : Program) (e : source cp = p),
  compile p = Compiled p cp e ->
  eq_rect (source cp) Core (core cp) p e = elaborated p.
Proof. Admitted.

Theorem rejected_retains_core : forall (p : SyntaxProgram) (f : Failure p),
  compile p = Rejected p f -> failure_core f = elaborated p.
Proof. Admitted.

Theorem outside_retains_core : forall (p : SyntaxProgram) (o : Outside_ p),
  compile p = OutsideScope p o -> outside_core o = elaborated p.
Proof. Admitted.

(* ── §15.1 Exact equations for every C6 source constructor ─────────────────── *)
Definition NL : string := String NewlineChar EmptyString.
Definition TAB : string := String TabChar EmptyString.

(* Parenthesization is decided by context and shape only.  A unary operand or an application head that is
   itself a unary keeps its parentheses, which is what makes the `--` token boundary unreachable. *)
Definition IsUnaryExpr (e : Expr) : bool :=
  match e with Unary _ _ => true | _ => false end.

Theorem needs_parens_eq : forall (ctx : RenderContext) (e : Expr),
  needs_parens ctx e =
  match ctx with
  | TopContext | ApplicationArgumentContext => false
  | UnaryOperandContext | ApplicationHeadContext => IsUnaryExpr e
  end.
Proof. Admitted.

Theorem render_expr_is_top : forall e : Expr, render_expr e = render_in TopContext e.
Proof. Admitted.

Theorem render_in_name : forall (ctx : RenderContext) (n : OrdinaryIdentifier),
  render_in ctx (Name n) = spelling (ordinary_identifier n).
Proof. Admitted.

Theorem render_in_literal : forall (ctx : RenderContext) (l : Literal),
  render_in ctx (LiteralExpr l) = render_literal l.
Proof. Admitted.

Theorem render_in_unary : forall (ctx : RenderContext) (e : Expr),
  render_in ctx (Unary UnaryMinus e) =
  (if needs_parens ctx (Unary UnaryMinus e)
   then "(-" ++ render_in UnaryOperandContext e ++ ")"
   else "-" ++ render_in UnaryOperandContext e)%string.
Proof. Admitted.

Theorem render_in_application : forall (ctx : RenderContext) (head : Expr) (args : list Expr),
  render_in ctx (Application head args) =
  (render_in ApplicationHeadContext head ++ "(" ++
   String.concat ", " (List.map (render_in ApplicationArgumentContext) args) ++ ")")%string.
Proof. Admitted.

(* The unary token boundary: no rendered unary ever puts two minus signs together, which would lex as the
   decrement token rather than as two negations. *)
Theorem render_unary_no_double_minus : forall (ctx : RenderContext) (e : Expr),
  ~ HasAdjacent "-"%char "-"%char (render_in ctx (Unary UnaryMinus e)).
Proof. Admitted.

Theorem render_type_expr_named : forall n : OrdinaryIdentifier,
  render_type_expr (NamedType n) = spelling (ordinary_identifier n).
Proof. Admitted.

Theorem render_binding_name_named : forall n : OrdinaryIdentifier,
  render_binding_name (Named n) = spelling (ordinary_identifier n).
Proof. Admitted.

Theorem render_binding_name_blank : render_binding_name Blank = "_"%string.
Proof. Admitted.

(* ── §15.2 Declaration grouping is decided by the spec count, once ─────────── *)
Definition render_group {A : Type} (kw : string) (specs : list A) (r : A -> string) : string :=
  if renders_grouped specs
  then (kw ++ " (" ++ NL ++
        String.concat "" (List.map (fun s => (TAB ++ r s ++ NL)%string) specs) ++ ")")%string
  else (kw ++ " " ++ String.concat "" (List.map r specs))%string.

Theorem render_declaration_const : forall specs : list ConstSpec,
  render_declaration (ConstDecl specs) = render_group "const" specs render_const_spec.
Proof. Admitted.

Theorem render_declaration_var : forall specs : list VarSpec,
  render_declaration (VarDecl specs) = render_group "var" specs render_var_spec.
Proof. Admitted.

Theorem render_declaration_type : forall specs : list TypeSpec,
  render_declaration (TypeDecl specs) = render_group "type" specs render_type_spec.
Proof. Admitted.

(* ── §15.3 Blank, type-only and initializer spec forms ─────────────────────── *)
Definition render_names (names : NonEmpty BindingName) : string :=
  String.concat ", " (List.map render_binding_name (ne_to_list names)).
Definition render_values (values : NonEmpty Expr) : string :=
  String.concat ", " (List.map render_expr (ne_to_list values)).
Definition render_opt_type (ty : option TypeExpr) : string :=
  match ty with Some t => (" " ++ render_type_expr t)%string | None => ""%string end.

Theorem render_const_spec_explicit : forall (names : NonEmpty BindingName)
  (ty : option TypeExpr) (values : NonEmpty Expr),
  render_const_spec (MakeConstSpec names (ExplicitConstInit ty values)) =
  (render_names names ++ render_opt_type ty ++ " = " ++ render_values values)%string.
Proof. Admitted.

Theorem render_const_spec_inherited : forall names : NonEmpty BindingName,
  render_const_spec (MakeConstSpec names InheritedConstInit) = render_names names.
Proof. Admitted.

Theorem render_var_spec_type_only : forall (names : NonEmpty BindingName) (ty : TypeExpr),
  render_var_spec (MakeVarSpec names (VarTypeOnly ty)) =
  (render_names names ++ " " ++ render_type_expr ty)%string.
Proof. Admitted.

Theorem render_var_spec_values : forall (names : NonEmpty BindingName)
  (ty : option TypeExpr) (values : NonEmpty Expr),
  render_var_spec (MakeVarSpec names (VarValues ty values)) =
  (render_names names ++ render_opt_type ty ++ " = " ++ render_values values)%string.
Proof. Admitted.

Theorem render_type_spec_alias : forall (n : BindingName) (t : TypeExpr),
  render_type_spec (AliasSpec n t) = (render_binding_name n ++ " = " ++ render_type_expr t)%string.
Proof. Admitted.

Theorem render_type_spec_def : forall (n : BindingName) (t : TypeExpr),
  render_type_spec (DefSpec n t) = (render_binding_name n ++ " " ++ render_type_expr t)%string.
Proof. Admitted.

(* ── §15.4 Statements and block indentation ────────────────────────────────── *)
Theorem render_stmt_expr : forall e : Expr, render_stmt (ExprStmt e) = render_expr e.
Proof. Admitted.

Theorem render_stmt_declaration : forall d : Declaration,
  render_stmt (DeclarationStmt d) = render_declaration d.
Proof. Admitted.

Theorem render_stmt_short : forall (names : NonEmpty BindingName) (values : NonEmpty Expr),
  render_stmt (ShortVarDecl names values) =
  (render_names names ++ " := " ++ render_values values)%string.
Proof. Admitted.

(* One tab per statement, one statement per line, closing brace unindented. *)
Theorem render_block_eq : forall stmts : list Stmt,
  render_block (MakeBlock stmts) =
  ("{" ++ NL ++
   String.concat "" (List.map (fun s => (TAB ++ render_stmt s ++ NL)%string) stmts) ++ "}")%string.
Proof. Admitted.

Theorem render_top_decl_declaration : forall d : Declaration,
  render_top_decl (TopDeclaration d) = render_declaration d.
Proof. Admitted.

Theorem render_top_decl_main : forall b : Block,
  render_top_decl (Main b) = ("func main() " ++ render_block b)%string.
Proof. Admitted.

(* ── §15.5 File and program traversal ──────────────────────────────────────── *)
(* The package clause is exact and nothing stands between it and the declarations: C6 emits no import
   section, and this equation is where that is stated rather than assumed. *)
Theorem render_file_eq : forall f : SyntaxFile,
  render_file f =
  ("package main" ++ NL ++
   String.concat "" (List.map (fun d => (NL ++ render_top_decl d ++ NL)%string) (file_decls f)))%string.
Proof. Admitted.

Theorem render_gomod_eq : forall m : ModuleSpec,
  render_gomod m =
  ("module " ++ module_path m ++ NL ++ NL ++ "go " ++ module_go_version m ++ NL)%string.
Proof. Admitted.

(* Exact path pairing: `go.mod` first, then each source file at its own path, in program order. *)
Theorem render_program_eq : forall p : SyntaxProgram,
  render_program p =
  ("go.mod"%string, render_gomod (program_module p))
  :: List.map (fun fp => (path_string (fst fp), render_file (snd fp))) (program_files p).
Proof. Admitted.

(* ── §15.6 Whitespace holds for every emitted byte string, not just files ──── *)
Theorem render_program_no_trailing_blank : forall (p : SyntaxProgram) (e : string * string),
  List.In e (render_program p) -> NoTrailingBlank (snd e).
Proof. Admitted.

(* ── §15.7 Valid-side obligations: what an accepted site rules out ─────────── *)
(* A rejection is a report, not a proof of Go-invalidity.  The honest content of a check therefore lives on
   the accepted side: these say what supportedness itself forbids. *)
Theorem supported_declaration_not_init_reserved :
  forall {p} {i : Input p} (ph : Phase i) (rd : TypeReady (phase_equations ph))
    (b : BindingSiteRef p),
  IsSupported (phase_outcome ph rd (SDeclaration p b)) ->
  ~ PackageInitReserved (binding_site_context b) (binding_site_name b).
Proof. Admitted.

(* The three application kinds partition `AppFact`: no application is both a conversion and a call, so a
   statement's println classification cannot silently overlap a conversion. *)
Theorem app_kind_trichotomy :
  forall {p} {i : Input p} {ph : Phase i} {rd} {a : ApplicationRef p} (f : AppFact ph rd a),
  (IsPrintlnApp f /\ ~ IsConversionApp f /\ ~ IsComplexApp f) \/
  (~ IsPrintlnApp f /\ IsConversionApp f /\ ~ IsComplexApp f) \/
  (~ IsPrintlnApp f /\ ~ IsConversionApp f /\ IsComplexApp f).
Proof. Admitted.

(* ── §15.8 The root claims ─────────────────────────────────────────────────── *)
(* Soundness: an accepted program is admissible.  This is the direction the emitter depends on — nothing is
   written unless it was proved. *)
Theorem compile_sound : forall (p : SyntaxProgram) (cp : Program) (e : source cp = p),
  compile p = Compiled p cp e -> Admissible p.
Proof. Admitted.

(* Completeness, restricted to the in-scope domain.  The restriction is the whole honest content of the
   third outcome: outside that domain the kernel declines to judge, so no completeness is claimed and none
   may be read in. *)
Theorem compile_complete_in_scope : forall p : SyntaxProgram,
  Admissible p -> InScope p -> exists (cp : Program) (e : source cp = p), compile p = Compiled p cp e.
Proof. Admitted.

(* The rejection side pins the valid side in both directions over the same domain. *)
Theorem in_scope_inadmissible_rejected : forall p : SyntaxProgram,
  InScope p -> ~ Admissible p -> exists f : Failure p, compile p = Rejected p f.
Proof. Admitted.

Theorem rejected_not_admissible : forall (p : SyntaxProgram) (f : Failure p),
  compile p = Rejected p f -> ~ Admissible p.
Proof. Admitted.

(* ── §15.9 Concrete byte-level render checks ───────────────────────────────── *)
Theorem unary_operand_never_starts_with_minus : forall e : Expr,
  ~ StartsWithMinus (render_in UnaryOperandContext e).
Proof. Admitted.

Theorem parenthesized_exactly_when_needed : forall (ctx : RenderContext) (e : Expr),
  needs_parens ctx e = true -> Parenthesized (render_in ctx e).
Proof. Admitted.

Theorem render_negative_literal :
  render_expr (Unary UnaryMinus (LiteralExpr (IntegerLiteral 1))) = "-1"%string.
Proof. Admitted.

Theorem render_double_negation : forall x : OrdinaryIdentifier,
  render_expr (Unary UnaryMinus (Unary UnaryMinus (Name x)))
    = ("-(-" ++ spelling (ordinary_identifier x) ++ ")")%string.
Proof. Admitted.

Theorem render_call : forall f x : OrdinaryIdentifier,
  render_expr (Application (Name f) [Name x])
    = (spelling (ordinary_identifier f) ++ "(" ++ spelling (ordinary_identifier x) ++ ")")%string.
Proof. Admitted.

Theorem render_call_negated_argument : forall f x : OrdinaryIdentifier,
  render_expr (Application (Name f) [Unary UnaryMinus (Name x)])
    = (spelling (ordinary_identifier f) ++ "(-" ++ spelling (ordinary_identifier x) ++ ")")%string.
Proof. Admitted.

Theorem render_negated_head_call : forall f x : OrdinaryIdentifier,
  render_expr (Application (Unary UnaryMinus (Name f)) [Name x])
    = ("(-" ++ spelling (ordinary_identifier f) ++ ")(" ++
       spelling (ordinary_identifier x) ++ ")")%string.
Proof. Admitted.

Theorem render_file_no_trailing_blank : forall f : SyntaxFile, NoTrailingBlank (render_file f).
Proof. Admitted.

(* ── §16.1 Names: the pinned catalog is complete, exact and injective ──────── *)
Theorem ordinary_excludes_blank_only : forall x : OrdinaryIdentifier,
  spelling (ordinary_identifier x) <> "_"%string.
Proof. Admitted.

Theorem predeclared_spellings_are_source_names : forall n : PredeclaredName,
  predeclared_spelling n <> "_"%string ->
  exists x : OrdinaryIdentifier, spelling (ordinary_identifier x) = predeclared_spelling n.
Proof. Admitted.

Theorem blank_is_not_an_ordinary_name : forall x : OrdinaryIdentifier, Named x <> Blank.
Proof. Admitted.

Theorem all_predeclared_nodup : NoDup all_predeclared.
Proof. Admitted.

Theorem all_predeclared_complete : forall n : PredeclaredName, In n all_predeclared.
Proof. Admitted.

Theorem predeclared_spelling_injective : forall a b : PredeclaredName,
  predeclared_spelling a = predeclared_spelling b -> a = b.
Proof. Admitted.

Theorem classify_spelling_roundtrip : forall n : PredeclaredName,
  classify_spelling (predeclared_spelling n) = Some n.
Proof. Admitted.

Theorem predeclared_eqb_spec : forall a b : PredeclaredName,
  predeclared_eqb a b = true <-> a = b.
Proof. Admitted.

(* ── §16.2 The closed predeclared type bridge ──────────────────────────────── *)
Theorem byte_is_uint8 : AliasPredeclared PByte TUint8.
Proof. Admitted.

Theorem rune_is_int32 : AliasPredeclared PRune TInt32.
Proof. Admitted.

Theorem aliases_mint_no_identity : forall n t,
  AliasPredeclared n t -> ~ AdmittedPredeclaredType n t.
Proof. Admitted.

(* Named for what it proves: every basic type is reachable by some admitted name.  The former name claimed
   a count of sixteen, which the statement never establishes. *)
Theorem every_basic_type_has_a_name : forall t : PredeclaredBasicType,
  exists n, AdmittedPredeclaredType n t.
Proof. Admitted.

Theorem no_type_meaning_names : forall n : PredeclaredName,
  In n [PAny; PComparable; PError; PUintptr] -> predeclared_type_role n = NoTypeMeaning.
Proof. Admitted.

Theorem default_types_exact :
  default_basic UCBool = TBool /\ default_basic UCInteger = TInt /\
  default_basic UCFloat = TFloat64 /\ default_basic UCComplex = TComplex128 /\
  default_basic UCString = TString.
Proof. Admitted.

(* ── §16.3 The use refinement eliminates the child-role witness, with no fallback ── *)
Theorem head_role_is_head_refinement :
  refinement_of_child_role ECApplicationHead = HeadRefinement.
Proof. Admitted.

Theorem statement_role_is_statement_refinement :
  refinement_of_child_role ECStatement = StatementRefinement.
Proof. Admitted.

Theorem argument_role_is_result_refinement :
  refinement_of_child_role ECApplicationArg = ResultRefinement.
Proof. Admitted.

Theorem inherited_use_is_result : forall p (u : InheritedConstUseRef p),
  use_refinement (InheritedUse p u) = ResultRefinement.
Proof. Admitted.

(* A cyclic phase yields no environment at all: readiness is not a flag beside the result. *)
Theorem cyclic_phase_has_no_environment : forall p (eqs : ResolvedTypeEquations p) c,
  ~ IsTypeReady (PhaseCyclic eqs c).
Proof. Admitted.

(* ── §16.4 Occurrences index the atom vector exactly ───────────────────────── *)
(* The split equation is intrinsic to the record; this is the bridge from that form to indexed access, and
   the only thing that gives `occurrence_position` its meaning. *)
Theorem occurrence_atom_is_nth :
  forall {p} {i : Input p} {ph : Phase i} {rd} {u : ExprUseRef p}
    (o : ResultOccurrenceAt ph rd u),
  List.nth_error (result_atoms_of (occ_fact ph rd u o)) (occurrence_position o)
    = Some (occ_atom ph rd u o).
Proof. Admitted.

(* C6 has no multi-valued expression: every result use carries exactly one atom. *)
Theorem c6_result_use_has_one_atom :
  forall {p} {i : Input p} {ph : Phase i} {rd} {u : ExprUseRef p}
    (f : ResultUseFactAt ph rd u),
  List.length (result_atoms_of f) = 1%nat.
Proof. Admitted.

(* ── §16.5 Argument uses hang off the application they belong to ───────────── *)
Theorem argument_use_parent_is_the_application :
  forall {p} (a : ApplicationRef p) (u : DirectExprUseRef p),
  List.In u (application_argument_uses a) ->
  direct_parent u = expr_node (application_expr a).
Proof. Admitted.

(* ── §16.6 The callable capability has exactly two inhabitants ─────────────── *)
Theorem callable_names_are_exactly_two : forall n : PredeclaredName,
  predeclared_capability n = CapCallable -> n = PComplex \/ n = PPrintln.
Proof. Admitted.

(* ── §16.7 The plan consumes exactly the site's own right-hand-side uses ───── *)
(* A list equality, not a length equality: order, identity and non-duplication are all part of the claim.
   The left side comes from the plan and the right side from the site, so this cannot be satisfied by
   comparing a plan against itself. *)
Theorem plan_consumes_every_source :
  forall {p} {i : Input p} {ph : Phase i} {rd} (c : ConsumptionSiteRef p)
    (f : ConsumptionFact ph rd c),
  plan_uses c f = site_uses c.
Proof. Admitted.

(* ── §16.8 The requirement view order is a strict total order ──────────────── *)
(* Without these three, "canonical order" below would name a property nothing establishes. *)
Theorem view_lt_irrefl : forall a : RequirementView, ~ view_lt a a.
Proof. Admitted.

(* Named for what it states.  The former name said "strict", which is irreflexivity, not this. *)
Theorem view_lt_transitive : forall a b c : RequirementView,
  view_lt a b -> view_lt b c -> view_lt a c.
Proof. Admitted.

Theorem view_lt_total : forall a b : RequirementView, view_lt a b \/ a = b \/ view_lt b a.
Proof. Admitted.

(* ── §16.9 The boundary list is canonical, duplicate-free and complete ─────── *)
Definition packed_view {p} (c : Core p)
  (b : { rd : TypeReady (phase_equations (phase c)) & PackedBoundary (phase c) rd })
  : RequirementView := boundary_view (projT2 b).

Fixpoint StrictlyIncreasing (l : list RequirementView) : Prop :=
  match l with
  | [] => True
  | a :: rest =>
      match rest with
      | [] => True
      | b :: _ => view_lt a b /\ StrictlyIncreasing rest
      end
  end.

Theorem boundary_order_canonical : forall {p} (c : Core p),
  StrictlyIncreasing (List.map (packed_view c) (core_boundaries c)).
Proof. Admitted.

Theorem boundary_views_nodup : forall {p} (c : Core p),
  NoDup (List.map (packed_view c) (core_boundaries c)).
Proof. Admitted.

(* Completeness of the list, which no record field can supply: every root-outside site is listed. *)
Theorem root_boundary_complete : forall {p} (c : Core p)
  (rd : TypeReady (phase_equations (phase c))) (s : Site p),
  IsRootOutside (phase_outcome (phase c) rd s) ->
  exists b, List.In b (core_boundaries c) /\
    boundary_site (phase c) (projT1 b) (projT2 b) = s.
Proof. Admitted.

Theorem boundary_requirement_unsatisfied : forall {p} (c : Core p) b,
  List.In b (core_boundaries c) ->
  ~ RequirementSatisfied (boundary_requirement (phase c) (projT1 b) (projT2 b)).
Proof. Admitted.

(* ── §16.10 Objects are identified by their origin ─────────────────────────── *)
Theorem object_origin_injective : forall {p} {i : Input p} {ph : Phase i} (o1 o2 : ObjectRef ph),
  object_origin o1 = object_origin o2 -> o1 = o2.
Proof. Admitted.

(* ── §16.11 Every reflected decision agrees with its relation ──────────────── *)
(* The booleans are separate parameters from the inductives, so without these four the decisions could
   answer anything.  Restated over `TypeReady`: the former `Env` carrier they quantified over is gone. *)
Theorem identicalb_reflect : forall {p} {eqs : ResolvedTypeEquations p} (rd : TypeReady eqs) s t,
  identicalb rd s t = true <-> Identical rd s t.
Proof. Admitted.

Theorem assignableb_reflect : forall {p} {eqs : ResolvedTypeEquations p} (rd : TypeReady eqs) s t,
  assignableb rd s t = true <-> Assignable rd s t.
Proof. Admitted.

Theorem value_convertibleb_reflect : forall {p} {eqs : ResolvedTypeEquations p} (rd : TypeReady eqs) s t,
  value_convertibleb rd s t = true <-> ValueConvertible rd s t.
Proof. Admitted.

Theorem representableb_reflect : forall {p} {eqs : ResolvedTypeEquations p} (rd : TypeReady eqs) s c,
  representableb rd s c = true <-> Representable rd s c.
Proof. Admitted.

(* ── §16.12 The accepted initialization order ──────────────────────────────── *)
(* The order itself is a projection of the accepted dependency site, not a rerun. *)
Definition accepted_init_order (cp : Program) (k : PackageRef (source cp))
  : InitOrder (accepted_phase cp) k :=
  accepted_fact cp (SDependency (source cp) k).

(* Determinism: dependency decides the order, and declaration order decides only where dependency is
   silent.  Without this the accepted order would be merely *some* valid topological order. *)
Theorem accepted_init_order_tiebreak : forall (cp : Program) (k : PackageRef (source cp)),
  SourceOrderTieBreak (accepted_init_order cp k).
Proof. Admitted.
```

## Implementation review boundaries

**Semantic-root review** stops only when the repository is green, the `Compilable.*` modules exist with no
old path beside a new one, and the tree contains: an ordinary identifier that excludes blank and nothing
else, with every predeclared spelling shadowable; blank only as a `BindingName`, admitted by alias and
definition specs; nonnegative literal magnitudes with negation only through `Unary UnaryMinus`; declaration
spec groups as lists; exact `ConstSpecRef`/`VarSpecRef`/`ShortDeclRef` consumption sites; a use refinement
with no fallback; a sealed `TypeReady` no client can construct and which cannot be paired with a
foreign decision; site-indexed failures and requirements with `Blocked` retaining its predecessor;
`requirement_dec` over the phase, decidable before any `Program` exists; every accepted capability a
projection of a phase family, with a callable fact carrying its own identity; result occurrences whose atom
is the exact split projection; conversion, `complex`, `println` and unary rules consuming their exact
argument occurrences and computing their results; a statement judgment only a `println` application can
inhabit; one consumption plan carrying exact fits evidence, indexed by its own site's targets so coverage is
structural; a short-declaration reuse that cannot name an object outside its own scope and earlier;
package initialization edges that carry the exact use and binding that justify them, with an order
retaining its covering, duplicate-freedom and edge respect, and a runtime projection excluding constant
work; the complete diagnostic migration above; exact
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

**Unary rendering.** `-(-x)` and `- -x` both accept, so pinned `gc` does not force the choice; the
contract renders the parenthesized form because it makes the `--` token boundary unreachable by
construction rather than by a scan. `-int(x)` and `println(-x)` accept.

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
be able to inhabit the statement-eligible branch; a second consumption authority is needed; a short-declaration reuse cannot be pinned to a same-scope
earlier binding; an initialization edge cannot carry the binding it summarises, or the accepted order is
merely some topological order rather than the source-order tie-break; a current public
diagnostic cannot be migrated without loss; `compiled_retains_core` cannot be stated exactly; a render
predicate cannot be made nontrivial; the pinned toolchain rejects the qualified namespace; a real semantic
cycle appears between the frozen child modules; implementation needs a placeholder, compatibility path,
trusted shortcut, fuel, bound or premature future state.
