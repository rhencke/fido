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
| `Compilable.Facts` | expression facts, role-indexed use facts, single-result uses, unary/application rules, statement classification, object-indexed meanings, const/var/short consumption plans, binder finalization, exact `StaticVariable`, unused-local facts |
| `Compilable.Report` | site failures, diagnostics, site requirements, reflected satisfaction, boundaries, root/blocked reporting, canonical lists |
| `Compilable.v` | phase composition, whole-program preflight, `Core`, `Elaboration`, `Decision`, `Program`/`Failure`/`Outside`, `Outcome`, `elaborate`, `compile` |
| `Compilable.Evidence` | certified accepted/rejected/outside fixtures and controls; no production module imports it |

`Bindings` precedes `TypeResolution` and `Dependencies`; those three precede `Facts`; `Facts` precedes
`Report`; `Report` precedes `Compilable.v`; `Compilable.v` precedes
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

## Sealing

The declarations below are the specification of what each module must contain, not a public interface. Three
families are module-private and export only their projections: site outcomes, site failures and boundaries
in `Compilable.Report`, and node outcomes in `Compilable.TypeResolution`. Their constructors are freely
applicable, so a client holding them could fabricate an outcome or a boundary; production values come only
from `phase_outcome`, `node_outcome` and `core_boundaries`.

`TypeReady` is sealed differently and does not need its constructor hidden. Building one requires
acyclicity of the whole graph plus support for every node, and that evidence exists only where the phase's
own decision produced it.

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

(* The exact source shape of an expression occurrence.  A fact constructor takes one of these views rather
   than a free `ExprRef` beside a second, unrelated source reference. *)
Parameter LiteralRef : SyntaxProgram -> Type.
Parameter expr_literal : forall {p}, ExprRef p -> option (LiteralRef p).
Parameter expr_name : forall {p}, ExprRef p -> option (NameUseRef p).
Parameter expr_unary : forall {p}, ExprRef p -> option (UnaryRef p).
Parameter expr_application : forall {p}, ExprRef p -> option (ApplicationRef p).
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

(* Where a contextual expression gets its meaning: `iota` from its exact enclosing const spec and index,
   `nil` from its exact legal target.  Both are properties of the use, not of the expression. *)
Parameter iota_context : forall {p}, ExprUseRef p -> option (ConstSpecRef p * nat).

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

(* The equation set is named here so the phase can carry it; the graph over it is the type layer. *)
Parameter ResolvedTypeEquations : SyntaxProgram -> Type.

(* The constant a literal denotes is read off the exact literal, never supplied beside it. *)
Parameter literal_constant : forall {p}, LiteralRef p -> Constant.

(* The value a typed constant carries, so the typed computations below can be pinned to the untyped
   constant authorities rather than being free to return anything. *)
Parameter basic_typed_value : forall b : BasicType, BasicTypedConstant b -> Constant.

(* Negation and the untyped-to-typed step on the exact basic value, so a rule computes its result from its
   operand instead of accepting an unrelated one. *)
Parameter negate_basic_typed : forall b : BasicType,
  BasicTypedConstant b -> option (BasicTypedConstant b).
Parameter basic_typed_of : forall b : BasicType, Constant -> option (BasicTypedConstant b).

(* The one authority for combining two floating values of the same kind into the complex constant of the
   matching kind.  A `complex` rule computes its result through this, never accepting one. *)
Parameter complex_typed_of : forall f : FloatKind,
  BasicTypedConstant (predeclared_basic_form (float_named_basic f)) ->
  BasicTypedConstant (predeclared_basic_form (float_named_basic f)) ->
  option (BasicTypedConstant (predeclared_basic_form (complex_named_basic f))).

(* ── The one retained static phase ─────────────────────────────────────────── *)
Parameter Phase : forall {p}, Input p -> Type.
Parameter phase : forall {p} (core : Core p), Phase (core_input core).
Parameter phase_equations : forall {p} {i : Input p} (ph : Phase i), ResolvedTypeEquations p.

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

(* The predeclared builtins pinned `gc` rejects in statement position.  Confirmed with nonconstant
   arguments, so the rejection is the statement-context rule and not constant folding.  Callability alone is
   not eligibility: `complex` is callable and still cannot stand as a statement. *)
Definition builtin_forbidden_as_statement (n : PredeclaredName) : bool :=
  match n with
  | PAppend | PCap | PComplex | PImag | PLen | PMake | PNew | PReal | PMin | PMax => true
  | _ => false
  end.

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

(* ── §2.1 The scope forest, indexed by exact source occurrences ────────────── *)
(* A lexical scope is identified by the exact source occurrence that establishes it, never by a package key
   plus a tag: rejected source may declare several `main` bodies in one package and each has its own scope.
   At C6 the only scope-establishing occurrence is a `main` body; C8 refines this to nested blocks without
   replacing `ScopeId`. *)
Parameter LexicalScopeRef : SyntaxProgram -> Type.
Parameter lexical_scope_package : forall {p}, LexicalScopeRef p -> PackageRef p.

Inductive ScopeId (p : SyntaxProgram) : Type :=
| PredeclaredScope : ScopeId p
| PackageScope     : PackageRef p -> ScopeId p
| LexicalScope     : LexicalScopeRef p -> ScopeId p.

Definition scope_parent {p} (s : ScopeId p) : option (ScopeId p) :=
  match s with
  | PredeclaredScope _ => None
  | PackageScope _ _   => Some (PredeclaredScope p)
  | LexicalScope _ b   => Some (PackageScope p (lexical_scope_package b))
  end.

Inductive Encloses {p} : ScopeId p -> ScopeId p -> Prop :=
| EnclosesSelf   : forall s, Encloses s s
| EnclosesParent : forall outer inner parent,
    scope_parent inner = Some parent -> Encloses outer parent -> Encloses outer inner.

(* ── §2.2 The exact Go scope-start table ───────────────────────────────────── *)
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

(* ── §2.3 Exact source observations a binding site and a name use carry ────── *)
Parameter binding_site_scope : forall {p}, BindingSiteRef p -> ScopeId p.
Parameter binding_site_spelling : forall {p}, BindingSiteRef p -> string.
Parameter binding_site_context : forall {p}, BindingSiteRef p -> DeclContext.
Parameter binding_site_position : forall {p}, BindingSiteRef p -> nat.
Parameter binding_site_identifier_position : forall {p}, BindingSiteRef p -> nat.
Parameter binding_site_spec_end : forall {p}, BindingSiteRef p -> nat.
Parameter binding_site_statement_end : forall {p}, BindingSiteRef p -> nat.

Parameter name_use_scope : forall {p}, NameUseRef p -> ScopeId p.
Parameter name_use_spelling : forall {p}, NameUseRef p -> string.
Parameter name_use_position : forall {p}, NameUseRef p -> nat.

Definition binding_site_start {p} (b : BindingSiteRef p) : ScopeStart :=
  scope_start (binding_site_context b).

(* The visibility point is derived from the site's own start rule, never supplied beside it. *)
Definition binding_site_visible_from {p} (b : BindingSiteRef p) : nat :=
  match binding_site_start b with
  | StartWholePackage | StartOutermost => 0
  | StartAtOwnIdentifier => binding_site_identifier_position b
  | StartAfterSpec       => binding_site_spec_end b
  | StartAfterStatement  => binding_site_statement_end b
  end.

Definition DeclaredBefore {p} (a b : BindingSiteRef p) : Prop :=
  binding_site_scope a = binding_site_scope b /\
  (binding_site_position a < binding_site_position b)%nat.

Definition VisibleAt {p} (b : BindingSiteRef p) (u : NameUseRef p) : Prop :=
  Encloses (binding_site_scope b) (name_use_scope u) /\
  (binding_site_visible_from b <= name_use_position u)%nat.

(* Nearest wins: a strictly inner scope shadows an outer one.  Two visible bindings of one spelling in one
   scope are a duplicate-declaration failure, not a shadowing question. *)
Definition Closer {p} (inner outer : BindingSiteRef p) : Prop :=
  binding_site_scope inner <> binding_site_scope outer /\
  Encloses (binding_site_scope outer) (binding_site_scope inner).

(* The special package-level name `init` is reserved for functions; pinned `gc` rejects a package-level
   const, var or type named `init`, and accepts it as an ordinary local name. *)
Definition PackageInitReserved (c : DeclContext) (n : string) : Prop :=
  (c = PackageConstDecl \/ c = PackageVarDecl \/ c = PackageTypeDecl) /\ n = "init"%string.

(* ── §2.4 One binding authority: a defined relation and its reflection ─────── *)
(* `Resolves` is not postulated.  It holds exactly when the spelling matches, the binding is visible at this
   exact use, and nothing visible with that spelling is closer.  The predeclared case fires only when no
   source binding of that spelling is visible, which is what makes shadowing exact. *)
Inductive Resolves {p} {i : Input p} (ph : Phase i) : NameUseRef p -> ObjectRef ph -> Prop :=
| ResolvesSource : forall (u : NameUseRef p) (b : BindingSiteRef p),
    binding_site_spelling b = name_use_spelling u ->
    VisibleAt b u ->
    (forall b' : BindingSiteRef p,
       binding_site_spelling b' = name_use_spelling u -> VisibleAt b' u -> ~ Closer b' b) ->
    Resolves ph u (source_object ph (binding_site_object_site b))
| ResolvesPredeclared : forall (u : NameUseRef p) (n : PredeclaredName),
    predeclared_spelling n = name_use_spelling u ->
    (forall b : BindingSiteRef p,
       binding_site_spelling b = name_use_spelling u -> ~ VisibleAt b u) ->
    Resolves ph u (predeclared_object ph n).

Parameter resolve_name : forall {p} {i : Input p} (ph : Phase i),
  NameUseRef p -> option (ObjectRef ph).

(* A binding fact retains the exact object this one decision returned; the role is a projection of the
   exact source use, not an independently supplied field. *)
Record BindingFact {p} {i : Input p} (ph : Phase i) (u : NameUseRef p) : Type := MakeBinding {
  bound_object   : ObjectRef ph;
  bound_resolves : Resolves ph u bound_object
}.

(* ── §2.5 Binder disposition, intrinsic to the exact binding-name occurrence ── *)
(* Each case is indexed by the occurrence it classifies and carries the source view that admits it, so a
   regular const, var, alias or type binder cannot inhabit `Reuse`. *)
Parameter binding_name_blank : forall {p}, BindingNameRef p -> option (BlankRef p).
Parameter binding_name_site : forall {p}, BindingNameRef p -> option (BindingSiteRef p).
Parameter binding_name_short_lhs : forall {p}, BindingNameRef p -> option (ShortDeclRef p).

Inductive BinderDisposition {p} {i : Input p} (ph : Phase i) (n : BindingNameRef p) : Type :=
| BinderBlank : forall k : BlankRef p,
    binding_name_blank n = Some k -> BinderDisposition ph n
| BinderNew : forall b : BindingSiteRef p,
    binding_name_blank n = None -> binding_name_site n = Some b ->
    BinderDisposition ph n
| BinderReuse : forall (d : ShortDeclRef p) (b earlier : BindingSiteRef p),
    binding_name_blank n = None ->
    binding_name_short_lhs n = Some d ->
    binding_name_site n = Some b ->
    binding_site_spelling earlier = binding_site_spelling b ->
    DeclaredBefore earlier b ->
    BinderDisposition ph n.

Parameter binder_disposition : forall {p} {i : Input p} (ph : Phase i) (n : BindingNameRef p),
  BinderDisposition ph n.

(* The object is derived from the exact site, never supplied beside it: a new binder mints the object of
   its own site, and a reuse returns the exact earlier object. *)
Definition binder_object {p} {i : Input p} {ph : Phase i} {n : BindingNameRef p}
  (d : BinderDisposition ph n) : option (ObjectRef ph) :=
  match d with
  | BinderBlank _ _ _ _ => None
  | BinderNew _ _ b _ _ => Some (source_object ph (binding_site_object_site b))
  | BinderReuse _ _ _ _ earlier _ _ _ _ _ =>
      Some (source_object ph (binding_site_object_site earlier))
  end.

(* ── §3.1 The exact type-equation graph ────────────────────────────────────── *)

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

(* ── §3.2 Semantic types need no environment ───────────────────────────────── *)
(* A type is a predeclared basic type or an exact defined-type declaration.  An environment was only ever
   needed to say what a definition's right-hand side is, and that is a per-node outcome below.  An alias has
   no constructor here, which is how it mints no identity. *)
Inductive SemanticType (p : SyntaxProgram) : Type :=
| PredeclaredType : PredeclaredBasicType -> SemanticType p
| DefinedType     : BoundDefinedTypeRef p -> SemanticType p.

Parameter defined_key : forall {p}, BoundDefinedTypeRef p -> IndexKey.

Definition type_view {p} (t : SemanticType p) : TypeView :=
  match t with
  | PredeclaredType _ b => PredeclaredView b
  | DefinedType _ d => DefinedView (defined_key d)
  end.

(* ── §3.3 Every type node has one sealed outcome ───────────────────────────── *)
Inductive TypeNodeFailure (p : SyntaxProgram) : Type :=
| RhsUnresolved  : NameUseRef p -> TypeNodeFailure p
| RhsWrongRole   : NameUseRef p -> TypeNodeFailure p.

(* `Blocked` retains the exact predecessor node, the exact edge, and that predecessor's exact retained
   outcome — never an independently supplied outcome that merely looks equal. *)
Inductive TypeNodeOutcome {p} {i : Input p} (ph : Phase i) : TypeNode p -> Type :=
| NodeSupported : forall (n : TypeNode p), SemanticType p -> TypeNodeOutcome ph n
| NodeFailed    : forall (n : TypeNode p), TypeNodeFailure p -> TypeNodeOutcome ph n
| NodeOutside   : forall (n : TypeNode p) (u : NameUseRef p),
    BindingFact ph u -> TypeNodeOutcome ph n
| NodeBlocked   : forall (n m : TypeNode p),
    TypeEdge (phase_equations ph) n m -> TypeNodeOutcome ph m -> TypeNodeOutcome ph n.

Parameter node_outcome : forall {p} {i : Input p} (ph : Phase i) (n : TypeNode p),
  TypeNodeOutcome ph n.

Definition NodeIsSupported {p} {i : Input p} {ph : Phase i} {n} (o : TypeNodeOutcome ph n) : Prop :=
  match o with NodeSupported _ _ _ => True | _ => False end.

(* A ready environment exists only when the graph is acyclic AND every node is supported.  `type U uintptr;
   type T U` is acyclic, yet `uintptr` has no C6 type meaning, so no environment exists for it.
   The seal is the obligation, not constructor hiding: building one requires evidence about `node_outcome`
   for every node, which only the phase's own decision produces. *)
Record TypeReady {p} {i : Input p} (ph : Phase i) : Type := MakeTypeReady {
  ready_acyclic       : AcyclicEquations (phase_equations ph);
  ready_all_supported : forall n : TypeNode p, NodeIsSupported (node_outcome ph n)
}.

(* Derived from the exact node outcomes, not postulated over arbitrary acyclic graphs. *)
Definition node_rhs {p} {i : Input p} {ph : Phase i} (rd : TypeReady ph)
  (n : TypeNode p) : SemanticType p :=
  match node_outcome ph n as o return NodeIsSupported o -> SemanticType p with
  | NodeSupported _ _ t => fun _ => t
  | NodeFailed _ _ _    => fun h => match h return SemanticType p with end
  | NodeOutside _ _ _ _ => fun h => match h return SemanticType p with end
  | NodeBlocked _ _ _ _ _ => fun h => match h return SemanticType p with end
  end (ready_all_supported ph rd n).

(* ── §3.4 Identity, underlying form and the C6 relations ───────────────────── *)
(* Identity and assignability need no environment at all: a predeclared type is its name, a defined type is
   its exact declaration. *)
Inductive Identical {p} : SemanticType p -> SemanticType p -> Prop :=
| IdenticalPredeclared : forall t, Identical (PredeclaredType p t) (PredeclaredType p t)
| IdenticalDefined     : forall d, Identical (DefinedType p d) (DefinedType p d).

Inductive Assignable {p} : SemanticType p -> SemanticType p -> Prop :=
| AssignIdentical : forall s t, Identical s t -> Assignable s t.

(* The underlying form follows the exact resolved right-hand side, which is why it needs readiness. *)
Inductive Underlying {p} {i : Input p} {ph : Phase i} (rd : TypeReady ph)
  : SemanticType p -> BasicType -> Prop :=
| UnderlyingPredeclared : forall t, Underlying rd (PredeclaredType p t) (predeclared_basic_form t)
| UnderlyingDefined : forall d b,
    Underlying rd (node_rhs rd (DefinedNode p d)) b -> Underlying rd (DefinedType p d) b.

Inductive ValueConvertible {p} {i : Input p} {ph : Phase i} (rd : TypeReady ph)
  : SemanticType p -> SemanticType p -> Prop :=
| VConvIdentical : forall s t, Identical s t -> ValueConvertible rd s t
| VConvSameUnderlying : forall s t b,
    Underlying rd s b -> Underlying rd t b -> ValueConvertible rd s t
| VConvScalarNumeric : forall s t bs bt,
    Underlying rd s bs -> Underlying rd t bt ->
    ScalarNumericBasic bs -> ScalarNumericBasic bt -> ValueConvertible rd s t
| VConvComplex : forall s t bs bt,
    Underlying rd s bs -> Underlying rd t bt ->
    ComplexBasicForm bs -> ComplexBasicForm bt -> ValueConvertible rd s t.

Inductive Representable {p} {i : Input p} {ph : Phase i} (rd : TypeReady ph)
  : SemanticType p -> Constant -> Prop :=
| RepresentableAt : forall s b c, Underlying rd s b -> FitsBasic b c -> Representable rd s c.

Inductive ConstantConvertible {p} {i : Input p} {ph : Phase i} (rd : TypeReady ph)
  : SemanticType p -> Constant -> Constant -> Prop :=
| CConvExact : forall s b c c',
    Underlying rd s b -> convert_constant_to b c = Some c' -> ConstantConvertible rd s c c'.

(* A typed constant retains its exact constant value, so negation and conversion stay causally connected to
   the operand they came from. *)
Record TypedConstant {p} {i : Input p} {ph : Phase i} (rd : TypeReady ph)
  (s : SemanticType p) : Type := MakeTypedConstant {
  typed_form     : BasicType;
  typed_underlying : Underlying rd s typed_form;
  typed_value    : BasicTypedConstant typed_form
}.

Parameter underlyingb : forall {p} {i : Input p} {ph : Phase i} (rd : TypeReady ph),
  SemanticType p -> BasicType.
Parameter identicalb assignableb : forall {p}, SemanticType p -> SemanticType p -> bool.
Parameter value_convertibleb : forall {p} {i : Input p} {ph : Phase i} (rd : TypeReady ph),
  SemanticType p -> SemanticType p -> bool.
Parameter representableb : forall {p} {i : Input p} {ph : Phase i} (rd : TypeReady ph),
  SemanticType p -> Constant -> bool.

Definition default_type {p} (k : UntypedConstantKind) : SemanticType p :=
  PredeclaredType p (default_basic k).

Inductive ResolvedTypeTarget {p} : RawTypeTarget p -> SemanticType p -> Prop :=
| ResolvedPredeclaredType : forall n t, AdmittedPredeclaredType n t ->
    ResolvedTypeTarget (RawPredeclared p n) (PredeclaredType p t)
| ResolvedPredeclaredAlias : forall n t, AliasPredeclared n t ->
    ResolvedTypeTarget (RawPredeclared p n) (PredeclaredType p t)
| ResolvedDefinedType : forall d, ResolvedTypeTarget (RawDefined p d) (DefinedType p d).

(* ── The retained type-phase result ────────────────────────────────────────── *)
(* A cyclic phase has no environment.  There is no builder and no equality to a rerun. *)
Inductive TypePhaseResult {p} {i : Input p} (ph : Phase i) : Type :=
| PhaseReady  : TypeReady ph -> TypePhaseResult ph
| PhaseCyclic : TypeCycle (phase_equations ph) -> TypePhaseResult ph.

Definition IsTypeReady {p} {i : Input p} {ph : Phase i} (res : TypePhaseResult ph) : Prop :=
  match res with PhaseReady _ _ => True | PhaseCyclic _ _ => False end.

Definition ready_of {p} {i : Input p} {ph : Phase i} (res : TypePhaseResult ph)
  : IsTypeReady res -> TypeReady ph :=
  match res return IsTypeReady res -> TypeReady ph with
  | PhaseReady _ r  => fun _ => r
  | PhaseCyclic _ _ => fun h => match h return TypeReady ph with end
  end.

Parameter phase_type_result : forall {p} {i : Input p} (ph : Phase i), TypePhaseResult ph.

(* ── §4.1 Every object has a total descriptor ──────────────────────────────── *)
(* Identity exists before the declaration is known to be semantically valid: a source constant, variable,
   alias or definition is bound even when its right-hand side later fails, is outside scope, or is blocked.
   Every field here is derived from the exact origin, never selected beside it. *)
Inductive SourceCategory : Type :=
| CatConst | CatVar | CatAlias | CatDefined | CatFunc.

Parameter object_site_category : forall {p}, ObjectSiteRef p -> SourceCategory.
Parameter object_site_spelling : forall {p}, ObjectSiteRef p -> string.
Parameter object_site_scope : forall {p}, ObjectSiteRef p -> ScopeId p.
Parameter object_site_alias : forall {p}, ObjectSiteRef p -> option (AliasSpecRef p).
Parameter object_site_defined : forall {p}, ObjectSiteRef p -> option (BoundDefinedTypeRef p).

Definition object_spelling {p} {i : Input p} {ph : Phase i} (o : ObjectRef ph) : string :=
  match object_origin o with
  | Predeclared _ n => predeclared_spelling n
  | SourceSite _ s  => object_site_spelling s
  end.

Definition object_scope {p} {i : Input p} {ph : Phase i} (o : ObjectRef ph) : ScopeId p :=
  match object_origin o with
  | Predeclared _ _ => PredeclaredScope p
  | SourceSite _ s  => object_site_scope s
  end.

Definition object_category {p} {i : Input p} {ph : Phase i} (o : ObjectRef ph)
  : option SourceCategory :=
  match object_origin o with
  | Predeclared _ _ => None
  | SourceSite _ s  => Some (object_site_category s)
  end.

(* ── §4.2 Successful semantic meaning is partial ───────────────────────────── *)
(* A failed, outside or blocked declaration has object identity and no meaning here.  There is no total
   `object_fact`: nothing pretends every source object already denotes something. *)
Inductive TypeMeaning {p} {i : Input p} (ph : Phase i) (rd : TypeReady ph)
  : ObjectRef ph -> Type :=
| TMPredeclared : forall n t, AdmittedPredeclaredType n t ->
    TypeMeaning ph rd (predeclared_object ph n)
| TMPredeclaredAlias : forall n t, AliasPredeclared n t ->
    TypeMeaning ph rd (predeclared_object ph n)
| TMAlias : forall (s : ObjectSiteRef p) (a : AliasSpecRef p),
    object_site_alias s = Some a -> TypeMeaning ph rd (source_object ph s)
| TMDefined : forall (s : ObjectSiteRef p) (d : BoundDefinedTypeRef p),
    object_site_defined s = Some d -> TypeMeaning ph rd (source_object ph s).

(* The denoted type is computed: an alias denotes its exact resolved right-hand side and mints no identity;
   a definition denotes its own exact declaration. *)
Definition type_meaning_type {p} {i : Input p} {ph : Phase i} {rd} {o}
  (m : TypeMeaning ph rd o) : SemanticType p :=
  match m with
  | TMPredeclared _ _ _ t _      => PredeclaredType p t
  | TMPredeclaredAlias _ _ _ t _ => PredeclaredType p t
  | TMAlias _ _ _ a _            => node_rhs rd (AliasNode p a)
  | TMDefined _ _ _ d _          => DefinedType p d
  end.

Inductive ConstantMeaning {p} {i : Input p} (ph : Phase i) (rd : TypeReady ph)
  : ObjectRef ph -> Type :=
| CMPredeclaredBool : forall n b, predeclared_capability n = CapUntypedBool b ->
    ConstantMeaning ph rd (predeclared_object ph n)
| CMUntyped : forall (s : ObjectSiteRef p) (c : ConstSpecRef p),
    Constant -> ConstantMeaning ph rd (source_object ph s)
| CMTyped : forall (s : ObjectSiteRef p) (c : ConstSpecRef p) (t : SemanticType p),
    TypedConstant rd t -> ConstantMeaning ph rd (source_object ph s).

(* The variable retains its exact declaring site; no runtime slot and no numeric identity is minted. *)
Record StaticVariable {p} {i : Input p} (ph : Phase i) (rd : TypeReady ph)
  (o : ObjectRef ph) : Type := MakeStaticVariable {
  static_site : VariableSiteRef p;
  static_type : SemanticType p;
  static_is_its_site :
    object_origin o
      = SourceSite p (binding_site_object_site (variable_site_binding_site static_site))
}.

(* C6 proves the accepted callable inhabitants are exactly `complex` and `println`; C9 adds function-valued
   heads by adding constructors here, without replacing the family. *)
Inductive CallableMeaning {p} {i : Input p} (ph : Phase i) : ObjectRef ph -> Type :=
| CallComplex : CallableMeaning ph (predeclared_object ph PComplex)
| CallPrintln : CallableMeaning ph (predeclared_object ph PPrintln).

Inductive IotaMeaning {p} {i : Input p} (ph : Phase i) : ObjectRef ph -> Type :=
| IotaIs : IotaMeaning ph (predeclared_object ph PIota).

Inductive NilMeaning {p} {i : Input p} (ph : Phase i) : ObjectRef ph -> Type :=
| NilIs : NilMeaning ph (predeclared_object ph PNil).

(* One sum of the successful meanings.  There is deliberately no total function producing it. *)
Inductive ObjectMeaning {p} {i : Input p} (ph : Phase i) (rd : TypeReady ph)
  (o : ObjectRef ph) : Type :=
| MeaningType     : TypeMeaning ph rd o -> ObjectMeaning ph rd o
| MeaningConstant : ConstantMeaning ph rd o -> ObjectMeaning ph rd o
| MeaningVariable : StaticVariable ph rd o -> ObjectMeaning ph rd o
| MeaningCallable : CallableMeaning ph o -> ObjectMeaning ph rd o
| MeaningIota     : IotaMeaning ph o -> ObjectMeaning ph rd o
| MeaningNil      : NilMeaning ph o -> ObjectMeaning ph rd o.

Definition IsTypeCapable {p} {i : Input p} {ph : Phase i} {rd} {o}
  (m : ObjectMeaning ph rd o) : Prop :=
  match m with MeaningType _ _ _ _ => True | _ => False end.

Definition IsConstantCapable {p} {i : Input p} {ph : Phase i} {rd} {o}
  (m : ObjectMeaning ph rd o) : Prop :=
  match m with MeaningConstant _ _ _ _ => True | _ => False end.

Definition IsVariableCapable {p} {i : Input p} {ph : Phase i} {rd} {o}
  (m : ObjectMeaning ph rd o) : Prop :=
  match m with MeaningVariable _ _ _ _ => True | _ => False end.

Definition IsCallableCapable {p} {i : Input p} {ph : Phase i} {rd} {o}
  (m : ObjectMeaning ph rd o) : Prop :=
  match m with MeaningCallable _ _ _ _ => True | _ => False end.

Definition IsContextualCapable {p} {i : Input p} {ph : Phase i} {rd} {o}
  (m : ObjectMeaning ph rd o) : Prop :=
  match m with
  | MeaningIota _ _ _ _ => True
  | MeaningNil _ _ _ _ => True
  | _ => False
  end.

Definition object_type {p} {i : Input p} {ph : Phase i} {rd} {o}
  (m : ObjectMeaning ph rd o) : IsTypeCapable m -> SemanticType p :=
  match m return IsTypeCapable m -> SemanticType p with
  | MeaningType _ _ _ tm => fun _ => type_meaning_type tm
  | _ => fun h => match h return SemanticType p with end
  end.

(* A short-declaration reuse names an object minted by an earlier binding in the same scope. *)
Definition SameBlockEarlier {p} {i : Input p} {ph : Phase i}
  (b : BindingSiteRef p) (o : ObjectRef ph) : Prop :=
  exists earlier : BindingSiteRef p,
    object_origin o = SourceSite p (binding_site_object_site earlier) /\
    DeclaredBefore earlier b.

(* ── §5 The expression-fact algebra ────────────────────────────────────────── *)
(* One sealed dependent judgment.  A failed, outside or blocked expression has no `ExprFact` at all — it has
   the corresponding exact site outcome.  Every family below is indexed by the exact result it computes, so
   the result is never a field a constructor could be handed. *)

(* Result atoms over the retained phase, so every rule can compute its own vector. *)
Inductive ResultAtomAt {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady ph) : Type :=
| RAUntyped : Constant -> ResultAtomAt ph rd
| RATyped   : forall t : SemanticType p, TypedConstant rd t -> ResultAtomAt ph rd
| RAValue   : SemanticType p -> ResultAtomAt ph rd.

Inductive ResultFormAt {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady ph) : Type :=
| RFFixed        : list (ResultAtomAt ph rd) -> ResultFormAt ph rd
| RFContextual   : ContextualResult -> ResultFormAt ph rd
| RFNoStandalone : ResultFormAt ph rd.

(* The result a bound name yields is decided by its one exact meaning, not supplied beside it.  A type or
   callable name has no standalone result; `iota` and `nil` are contextual and resolved at the exact use. *)
Definition name_result {p} {i : Input p} {ph : Phase i} {rd} {o}
  (m : ObjectMeaning ph rd o) : ResultFormAt ph rd :=
  match m with
  | MeaningConstant _ _ _ cm =>
      match cm with
      | CMPredeclaredBool _ _ _ b _ => RFFixed ph rd [RAUntyped ph rd (BoolConstant b)]
      | CMUntyped _ _ _ _ c         => RFFixed ph rd [RAUntyped ph rd c]
      | CMTyped _ _ _ _ t tc        => RFFixed ph rd [RATyped ph rd t tc]
      end
  | MeaningVariable _ _ _ sv => RFFixed ph rd [RAValue ph rd (static_type ph rd o sv)]
  | MeaningIota _ _ _ _ => RFContextual ph rd IotaResult
  | MeaningNil _ _ _ _  => RFContextual ph rd NilResult
  | MeaningType _ _ _ _ => RFNoStandalone ph rd
  | MeaningCallable _ _ _ _ => RFNoStandalone ph rd
  end.

(* Atom builders, so the `complex` cases below read as rules rather than as record plumbing. *)
Definition float_atom_typed {p} {i : Input p} {ph : Phase i} {rd}
  (t : SemanticType p) (f : FloatKind)
  (hu : Underlying rd t (predeclared_basic_form (float_named_basic f)))
  (v : BasicTypedConstant (predeclared_basic_form (float_named_basic f)))
  : ResultAtomAt ph rd :=
  RATyped ph rd t (@MakeTypedConstant p i ph rd t _ hu v).

Definition complex_atom_typed {p} {i : Input p} {ph : Phase i} {rd} (f : FloatKind)
  (vr : BasicTypedConstant (predeclared_basic_form (complex_named_basic f)))
  : ResultAtomAt ph rd :=
  RATyped ph rd (PredeclaredType p (complex_named_basic f))
    (@MakeTypedConstant p i ph rd (PredeclaredType p (complex_named_basic f)) _
      (UnderlyingPredeclared rd (complex_named_basic f)) vr).

Definition complex_atom_value {p} {i : Input p} {ph : Phase i} {rd} (f : FloatKind)
  : ResultAtomAt ph rd :=
  RAValue ph rd (PredeclaredType p (complex_named_basic f)).

(* ── The rule-coverage relations ───────────────────────────────────────────── *)
(* These are the one authority for "C6 has a rule for operands of this exact shape".  The rule families
   below carry a coverage witness rather than restating its premises, and a requirement's satisfaction is
   stated over these — never over whether the successful fact happens to be inhabited. *)
Inductive UnaryRuleCovers {p} {i : Input p} {ph : Phase i} (rd : TypeReady ph)
  : ResultAtomAt ph rd -> Prop :=
| URUntyped : forall c, NumericConstantKind (constant_kind c) ->
    UnaryRuleCovers rd (RAUntyped ph rd c)
| URTyped : forall t tc b, Underlying rd t b -> NumericBasic b ->
    UnaryRuleCovers rd (RATyped ph rd t tc)
| URValue : forall t b, Underlying rd t b -> NumericBasic b ->
    UnaryRuleCovers rd (RAValue ph rd t).

(* `println` admits an argument whose underlying form exists; an untyped constant is defaulted first. *)
Inductive PrintlnArg {p} {i : Input p} {ph : Phase i} (rd : TypeReady ph)
  : ResultAtomAt ph rd -> Prop :=
| PAUntyped : forall c, PrintlnArg rd (RAUntyped ph rd c)
| PATyped   : forall t tc b, Underlying rd t b -> PrintlnArg rd (RATyped ph rd t tc)
| PAValue   : forall t b, Underlying rd t b -> PrintlnArg rd (RAValue ph rd t).

Definition PrintlnRuleCovers {p} {i : Input p} {ph : Phase i} (rd : TypeReady ph)
  (args : list (ResultAtomAt ph rd)) : Prop := List.Forall (PrintlnArg rd) args.

Inductive ConvRuleCovers {p} {i : Input p} {ph : Phase i} (rd : TypeReady ph)
  : SemanticType p -> ResultAtomAt ph rd -> Prop :=
| CCConstant : forall dst b c, Underlying rd dst b ->
    (exists c', convert_constant_to b c = Some c') ->
    ConvRuleCovers rd dst (RAUntyped ph rd c)
| CCValue : forall dst src, ValueConvertible rd src dst ->
    ConvRuleCovers rd dst (RAValue ph rd src).

(* A floating operand of an exact kind, constant or not: what the `complex` combinations quantify over. *)
Inductive FloatOperand {p} {i : Input p} {ph : Phase i} (rd : TypeReady ph)
  : ResultAtomAt ph rd -> FloatKind -> Prop :=
| FOTyped : forall t tc f, Underlying rd t (predeclared_basic_form (float_named_basic f)) ->
    FloatOperand rd (RATyped ph rd t tc) f
| FOValue : forall t f, Underlying rd t (predeclared_basic_form (float_named_basic f)) ->
    FloatOperand rd (RAValue ph rd t) f.

Inductive ComplexRuleCovers {p} {i : Input p} {ph : Phase i} (rd : TypeReady ph)
  : ResultAtomAt ph rd -> ResultAtomAt ph rd -> Prop :=
| CxCBothUntyped : forall c1 c2,
    NumericConstantKind (constant_kind c1) -> NumericConstantKind (constant_kind c2) ->
    ComplexRuleCovers rd (RAUntyped ph rd c1) (RAUntyped ph rd c2)
| CxCUntypedLeft : forall c y f, NumericConstantKind (constant_kind c) -> FloatOperand rd y f ->
    ComplexRuleCovers rd (RAUntyped ph rd c) y
| CxCUntypedRight : forall x c f, FloatOperand rd x f -> NumericConstantKind (constant_kind c) ->
    ComplexRuleCovers rd x (RAUntyped ph rd c)
| CxCBothKinded : forall x y f, FloatOperand rd x f -> FloatOperand rd y f ->
    ComplexRuleCovers rd x y.

Definition ApplicationRuleCovers {p} {i : Input p} {ph : Phase i} (rd : TypeReady ph)
  (args : list (ResultAtomAt ph rd)) : Prop :=
  (exists dst a1, args = [a1] /\ ConvRuleCovers rd dst a1) \/
  (exists a1 a2, args = [a1; a2] /\ ComplexRuleCovers rd a1 a2) \/
  PrintlnRuleCovers rd args.

(* Statement eligibility is `println` and nothing else: `complex` is callable and still cannot stand as a
   statement, which is why callability alone was never the right question. *)
Definition StatementRuleCovers {p} {i : Input p} (ph : Phase i) (a : ApplicationRef p) : Prop :=
  exists (hu : NameUseRef p) (bf : BindingFact ph hu),
    expr_name (application_head a) = Some hu /\
    bound_object ph hu bf = predeclared_object ph PPrintln.

(* A contextual expression is resolved at the exact use.  `iota` takes the index of its own const spec.
   There is deliberately no `nil` constructor: pinned `gc` rejects `nil` in every C6-representable context,
   so a `nil` use produces its exact requirement or diagnostic and never a resolved atom. *)
Inductive ContextResolvesAt {p} {i : Input p} (ph : Phase i) (rd : TypeReady ph)
  : ExprUseRef p -> ContextualResult -> ResultAtomAt ph rd -> Prop :=
| IotaResolves : forall (u : ExprUseRef p) (c : ConstSpecRef p) (k : nat),
    iota_context u = Some (c, k) ->
    ContextResolvesAt ph rd u IotaResult (RAUntyped ph rd (IntegerConstant (Z.of_nat k))).

Inductive ExprFact {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady ph) : ExprRef p -> ResultFormAt ph rd -> Type :=
| EFLiteral : forall (r : ExprRef p) (l : LiteralRef p),
    expr_literal r = Some l ->
    ExprFact ph rd r (RFFixed ph rd [RAUntyped ph rd (literal_constant l)])
| EFName : forall (r : ExprRef p) (u : NameUseRef p),
    expr_name r = Some u ->
    forall (bf : BindingFact ph u) (m : ObjectMeaning ph rd (bound_object ph u bf)),
    ExprFact ph rd r (name_result m)
| EFUnary : forall (r : ExprRef p) (n : UnaryRef p)
    (opa : ResultAtomAt ph rd) (res : list (ResultAtomAt ph rd)),
    expr_unary r = Some n ->
    ResultUseFactAt ph rd (DirectUse p (unary_operand_use n)) opa ->
    UnaryFact ph rd n opa res ->
    ExprFact ph rd r (RFFixed ph rd res)
| EFApplication : forall (r : ExprRef p) (a : ApplicationRef p)
    (hf : ResultFormAt ph rd) (res : list (ResultAtomAt ph rd)),
    expr_application r = Some a ->
    ExprFact ph rd (application_head a) hf -> AppFact ph rd a res ->
    ExprFact ph rd r (RFFixed ph rd res)

(* §10 A result use selects exactly one atom BY CONSTRUCTION.  A head or statement use cannot inhabit it,
   and neither can an expression whose form is contextual-unresolved or no-standalone. *)
with ResultUseFactAt {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady ph) : ExprUseRef p -> ResultAtomAt ph rd -> Type :=
| RUFFixed : forall (u : ExprUseRef p) (a : ResultAtomAt ph rd),
    use_refinement u = ResultRefinement ->
    ExprFact ph rd (expression_of_use u) (RFFixed ph rd [a]) ->
    ResultUseFactAt ph rd u a
| RUFContextual : forall (u : ExprUseRef p) (cr : ContextualResult) (a : ResultAtomAt ph rd),
    use_refinement u = ResultRefinement ->
    ExprFact ph rd (expression_of_use u) (RFContextual ph rd cr) ->
    ContextResolvesAt ph rd u cr a ->
    ResultUseFactAt ph rd u a

(* §7.1 Argument facts are indexed by the EXACT ordered source use list and the exact ordered atoms they
   consume, so there is one fact per source argument, in source order, with no duplicate and no omission. *)
with ArgFacts {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady ph) : list (DirectExprUseRef p) -> list (ResultAtomAt ph rd) -> Type :=
| ArgsNil  : ArgFacts ph rd [] []
| ArgsCons : forall (u : DirectExprUseRef p) (rest : list (DirectExprUseRef p))
    (a : ResultAtomAt ph rd) (arest : list (ResultAtomAt ph rd)),
    ResultUseFactAt ph rd (DirectUse p u) a -> ArgFacts ph rd rest arest ->
    ArgFacts ph rd (u :: rest) (a :: arest)

(* §11 The unary rule is indexed by the exact operand atom and computes its result from it.  There is no
   free input constant and no unrelated output typed constant. *)
with UnaryFact {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady ph) : UnaryRef p -> ResultAtomAt ph rd -> list (ResultAtomAt ph rd) -> Type :=
| UFUntyped : forall (n : UnaryRef p) (c c' : Constant),
    UnaryRuleCovers rd (RAUntyped ph rd c) -> negate_constant c = Some c' ->
    UnaryFact ph rd n (RAUntyped ph rd c) [RAUntyped ph rd c']
| UFTypedConstant : forall (n : UnaryRef p) (t : SemanticType p) (b : BasicType)
    (hu : Underlying rd t b) (v v' : BasicTypedConstant b),
    UnaryRuleCovers rd (RATyped ph rd t (@MakeTypedConstant p i ph rd t b hu v)) ->
    negate_basic_typed b v = Some v' ->
    UnaryFact ph rd n
      (RATyped ph rd t (@MakeTypedConstant p i ph rd t b hu v))
      [RATyped ph rd t (@MakeTypedConstant p i ph rd t b hu v')]
| UFValue : forall (n : UnaryRef p) (t : SemanticType p),
    UnaryRuleCovers rd (RAValue ph rd t) ->
    UnaryFact ph rd n (RAValue ph rd t) [RAValue ph rd t]

(* Arity is a constructor constraint, not a separate theorem: a conversion demands a one-element source
   argument list and `complex` a two-element one, so a wrong-arity application cannot build a fact. *)
with AppFact {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady ph) : ApplicationRef p -> list (ResultAtomAt ph rd) -> Type :=
| AFConversion : forall (a : ApplicationRef p) (dst : SemanticType p) (u : DirectExprUseRef p)
    (arg : ResultAtomAt ph rd) (res : list (ResultAtomAt ph rd)),
    application_argument_uses a = [u] ->
    ArgFacts ph rd [u] [arg] -> ConvRule ph rd a dst arg res -> AppFact ph rd a res
| AFComplex : forall (a : ApplicationRef p) (hu : NameUseRef p) (bf : BindingFact ph hu)
    (u1 u2 : DirectExprUseRef p) (a1 a2 : ResultAtomAt ph rd)
    (res : list (ResultAtomAt ph rd)),
    expr_name (application_head a) = Some hu ->
    CallableMeaning ph (bound_object ph hu bf) ->
    application_argument_uses a = [u1; u2] ->
    ArgFacts ph rd [u1; u2] [a1; a2] -> ComplexRuleF ph rd a a1 a2 res -> AppFact ph rd a res
| AFPrintln : forall (a : ApplicationRef p) (hu : NameUseRef p) (bf : BindingFact ph hu)
    (args : list (ResultAtomAt ph rd)),
    expr_name (application_head a) = Some hu ->
    CallableMeaning ph (bound_object ph hu bf) ->
    ArgFacts ph rd (application_argument_uses a) args ->
    PrintlnRuleF ph rd a args -> AppFact ph rd a []

(* §12.2 The conversion consumes the one exact argument atom and computes the exact result atom. *)
with ConvRule {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady ph)
  : ApplicationRef p -> SemanticType p -> ResultAtomAt ph rd -> list (ResultAtomAt ph rd) -> Type :=
| CRConstant : forall (a : ApplicationRef p) (dst : SemanticType p) (b : BasicType)
    (hu : Underlying rd dst b) (c c' : Constant) (v : BasicTypedConstant b),
    convert_constant_to b c = Some c' -> basic_typed_of b c' = Some v ->
    ConvRule ph rd a dst (RAUntyped ph rd c) [RATyped ph rd dst (@MakeTypedConstant p i ph rd dst b hu v)]
| CRValue : forall (a : ApplicationRef p) (dst src : SemanticType p),
    ValueConvertible rd src dst ->
    ConvRule ph rd a dst (RAValue ph rd src) [RAValue ph rd dst]

(* §12.3 `complex` consumes its two exact argument atoms.  The result's constantness follows the operands'
   and its kind follows the exact floating kind they share. *)
with ComplexRuleF {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady ph)
  : ApplicationRef p -> ResultAtomAt ph rd -> ResultAtomAt ph rd ->
    list (ResultAtomAt ph rd) -> Type :=
(* Two untyped numeric constants give an untyped complex constant. *)
| CxUntypedUntyped : forall (a : ApplicationRef p) (c1 c2 cr : Constant),
    NumericConstantKind (constant_kind c1) -> NumericConstantKind (constant_kind c2) ->
    complex_of_constants c1 c2 = Some cr ->
    ComplexRuleF ph rd a (RAUntyped ph rd c1) (RAUntyped ph rd c2) [RAUntyped ph rd cr]
(* One untyped constant with one typed floating constant: the untyped operand converts to the typed
   operand's exact kind, and the result is a typed complex constant of the matching kind. *)
| CxUntypedTypedL : forall (a : ApplicationRef p) (c : Constant) (t : SemanticType p) (f : FloatKind)
    (hu : Underlying rd t (predeclared_basic_form (float_named_basic f)))
    (v vc : BasicTypedConstant (predeclared_basic_form (float_named_basic f)))
    (vr : BasicTypedConstant (predeclared_basic_form (complex_named_basic f))),
    NumericConstantKind (constant_kind c) ->
    basic_typed_of (predeclared_basic_form (float_named_basic f)) c = Some vc ->
    complex_typed_of f vc v = Some vr ->
    ComplexRuleF ph rd a (RAUntyped ph rd c) (float_atom_typed t f hu v)
      [complex_atom_typed f vr]
| CxUntypedTypedR : forall (a : ApplicationRef p) (c : Constant) (t : SemanticType p) (f : FloatKind)
    (hu : Underlying rd t (predeclared_basic_form (float_named_basic f)))
    (v vc : BasicTypedConstant (predeclared_basic_form (float_named_basic f)))
    (vr : BasicTypedConstant (predeclared_basic_form (complex_named_basic f))),
    NumericConstantKind (constant_kind c) ->
    basic_typed_of (predeclared_basic_form (float_named_basic f)) c = Some vc ->
    complex_typed_of f v vc = Some vr ->
    ComplexRuleF ph rd a (float_atom_typed t f hu v) (RAUntyped ph rd c)
      [complex_atom_typed f vr]
(* One untyped constant with one floating value: the result is a value, not a constant. *)
| CxUntypedValueL : forall (a : ApplicationRef p) (c : Constant) (t : SemanticType p) (f : FloatKind),
    NumericConstantKind (constant_kind c) ->
    Underlying rd t (predeclared_basic_form (float_named_basic f)) ->
    ComplexRuleF ph rd a (RAUntyped ph rd c) (RAValue ph rd t) [complex_atom_value f]
| CxUntypedValueR : forall (a : ApplicationRef p) (c : Constant) (t : SemanticType p) (f : FloatKind),
    NumericConstantKind (constant_kind c) ->
    Underlying rd t (predeclared_basic_form (float_named_basic f)) ->
    ComplexRuleF ph rd a (RAValue ph rd t) (RAUntyped ph rd c) [complex_atom_value f]
(* Two typed floating constants of one identical type give a typed complex constant. *)
| CxTypedTyped : forall (a : ApplicationRef p) (t : SemanticType p) (f : FloatKind)
    (hu : Underlying rd t (predeclared_basic_form (float_named_basic f)))
    (v1 v2 : BasicTypedConstant (predeclared_basic_form (float_named_basic f)))
    (vr : BasicTypedConstant (predeclared_basic_form (complex_named_basic f))),
    complex_typed_of f v1 v2 = Some vr ->
    ComplexRuleF ph rd a (float_atom_typed t f hu v1) (float_atom_typed t f hu v2)
      [complex_atom_typed f vr]
(* A typed floating constant with a floating value of the same type gives a value. *)
| CxTypedValueL : forall (a : ApplicationRef p) (t : SemanticType p) (f : FloatKind)
    (hu : Underlying rd t (predeclared_basic_form (float_named_basic f)))
    (v : BasicTypedConstant (predeclared_basic_form (float_named_basic f))),
    ComplexRuleF ph rd a (float_atom_typed t f hu v) (RAValue ph rd t) [complex_atom_value f]
| CxTypedValueR : forall (a : ApplicationRef p) (t : SemanticType p) (f : FloatKind)
    (hu : Underlying rd t (predeclared_basic_form (float_named_basic f)))
    (v : BasicTypedConstant (predeclared_basic_form (float_named_basic f))),
    ComplexRuleF ph rd a (RAValue ph rd t) (float_atom_typed t f hu v) [complex_atom_value f]
(* Two floating values of one identical type give a value. *)
| CxValues : forall (a : ApplicationRef p) (t : SemanticType p) (f : FloatKind),
    Underlying rd t (predeclared_basic_form (float_named_basic f)) ->
    ComplexRuleF ph rd a (RAValue ph rd t) (RAValue ph rd t) [complex_atom_value f]

with PrintlnRuleF {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady ph) : ApplicationRef p -> list (ResultAtomAt ph rd) -> Type :=
| PrFAdmitted : forall (a : ApplicationRef p) (args : list (ResultAtomAt ph rd)),
    PrintlnRuleCovers rd args -> PrintlnRuleF ph rd a args.

(* ── §5 The one remaining projection ───────────────────────────────────────── *)
(* `result_form` is now the index itself, so there is nothing left to project.  Only the referenced object
   is a genuine view of the fact. *)
Definition expr_referenced_object {p} {i : Input p} {ph : Phase i} {rd} {r} {form}
  (f : ExprFact ph rd r form) : option (ObjectRef ph) :=
  match f with
  | EFName _ _ _ u _ bf _ => Some (bound_object ph u bf)
  | _ => None
  end.

(* ── §8 A statement fact exists only for an eligible statement ─────────────── *)
Definition IsPrintlnApp {p} {i : Input p} {ph : Phase i} {rd} {a} {res}
  (f : AppFact ph rd a res) : Prop :=
  match f with AFPrintln _ _ _ _ _ _ _ _ _ _ => True | _ => False end.

Definition IsConversionApp {p} {i : Input p} {ph : Phase i} {rd} {a} {res}
  (f : AppFact ph rd a res) : Prop :=
  match f with AFConversion _ _ _ _ _ _ _ _ _ _ => True | _ => False end.

Definition IsComplexApp {p} {i : Input p} {ph : Phase i} {rd} {a} {res}
  (f : AppFact ph rd a res) : Prop :=
  match f with AFComplex _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True | _ => False end.

Inductive StmtFact {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady ph) : ExpressionStatementRef p -> Type :=
| SFPrintln : forall (s : ExpressionStatementRef p) (a : ApplicationRef p)
    (res : list (ResultAtomAt ph rd)) (f : AppFact ph rd a res),
    statement_application s = Some a -> IsPrintlnApp f -> StmtFact ph rd s.

Definition statement_application_of {p} {i : Input p} {ph : Phase i} {rd} {s}
  (f : StmtFact ph rd s) : ApplicationRef p :=
  match f with SFPrintln _ _ _ a _ _ _ _ => a end.

(* ── §11 One intrinsic, source-indexed result-consumption plan ─────────────── *)
Inductive ConsumptionTarget (p : SyntaxProgram) : Type :=
| NamedTarget : BindingSiteRef p -> ConsumptionTarget p
| BlankTarget : BlankRef p -> ConsumptionTarget p.

(* The exact source target sequence and right-hand-side use sequence belong to the site itself. *)
Parameter site_targets : forall {p}, ConsumptionSiteRef p -> list (ConsumptionTarget p).
Parameter site_uses : forall {p}, ConsumptionSiteRef p -> list (ExprUseRef p).

Inductive ConstAtomAt {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady ph) : ResultAtomAt ph rd -> Prop :=
| CAUntyped : forall c, ConstAtomAt ph rd (RAUntyped ph rd c)
| CATyped   : forall t tc, ConstAtomAt ph rd (RATyped ph rd t tc).

(* The exact defaulting / representability / assignability evidence an entry must carry. *)
Inductive AtomFits {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady ph) : ResultAtomAt ph rd -> SemanticType p -> Prop :=
| FitUntyped : forall c t, Representable rd t c -> AtomFits ph rd (RAUntyped ph rd c) t
| FitTyped   : forall (s : SemanticType p) tc t, Assignable s t ->
    AtomFits ph rd (RATyped ph rd s tc) t
| FitValue   : forall (s : SemanticType p) t, Assignable s t ->
    AtomFits ph rd (RAValue ph rd s) t.

(* Each plan is indexed by the EXACT remaining source target list AND the EXACT remaining source use list,
   consumed in lockstep.  Target coverage, source consumption, order and non-duplication therefore all hold
   by construction: a plan cannot consume another site's uses, and no separate coverage equation exists that
   could be satisfied by comparing a plan against itself. *)
Inductive ConstPlan {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady ph) : list (ConsumptionTarget p) -> list (ExprUseRef p) -> Type :=
| CPNil  : ConstPlan ph rd [] []
| CPCons : forall (t : ConsumptionTarget p) (rest : list (ConsumptionTarget p))
    (u : ExprUseRef p) (urest : list (ExprUseRef p)) (a : ResultAtomAt ph rd),
    ResultUseFactAt ph rd u a -> ConstAtomAt ph rd a ->
    option (SemanticType p) -> ConstPlan ph rd rest urest ->
    ConstPlan ph rd (t :: rest) (u :: urest).

(* `var x, y int` has targets and no right-hand side at all, so it is a separate form rather than a plan
   with an optional use.  The two forms cannot be interleaved. *)
Inductive VarValuesPlan {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady ph) : list (ConsumptionTarget p) -> list (ExprUseRef p) -> Type :=
| VVNil  : VarValuesPlan ph rd [] []
| VVCons : forall (t : ConsumptionTarget p) (rest : list (ConsumptionTarget p))
    (u : ExprUseRef p) (urest : list (ExprUseRef p)) (a : ResultAtomAt ph rd)
    (ty : SemanticType p),
    ResultUseFactAt ph rd u a -> AtomFits ph rd a ty ->
    VarValuesPlan ph rd rest urest ->
    VarValuesPlan ph rd (t :: rest) (u :: urest).

Inductive VarPlan {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady ph) : list (ConsumptionTarget p) -> list (ExprUseRef p) -> Type :=
| VPTypeOnly : forall (targets : list (ConsumptionTarget p)) (ty : SemanticType p),
    VarPlan ph rd targets []
| VPValues : forall (targets : list (ConsumptionTarget p)) (uses : list (ExprUseRef p)),
    VarValuesPlan ph rd targets uses -> VarPlan ph rd targets uses.

(* A new short binder retains its exact object; a same-block reuse retains the exact existing object;
   blank retains neither. *)
Inductive ShortBinder {p} {i : Input p} (ph : Phase i) : Type :=
| SBNew   : BindingSiteRef p -> ObjectRef ph -> ShortBinder ph
| SBReuse : forall (b : BindingSiteRef p) (o : ObjectRef ph),
    SameBlockEarlier b o -> ShortBinder ph.

Inductive ShortPlan {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady ph) : list (ConsumptionTarget p) -> list (ExprUseRef p) -> Type :=
| SPNil   : ShortPlan ph rd [] []
| SPNamed : forall (b : BindingSiteRef p) (rest : list (ConsumptionTarget p))
    (bind : ShortBinder ph) (u : ExprUseRef p) (urest : list (ExprUseRef p))
    (a : ResultAtomAt ph rd) (ty : SemanticType p),
    ResultUseFactAt ph rd u a -> AtomFits ph rd a ty -> ShortPlan ph rd rest urest ->
    ShortPlan ph rd (NamedTarget p b :: rest) (u :: urest)
| SPBlank : forall (k : BlankRef p) (rest : list (ConsumptionTarget p))
    (u : ExprUseRef p) (urest : list (ExprUseRef p)) (a : ResultAtomAt ph rd),
    ResultUseFactAt ph rd u a -> ShortPlan ph rd rest urest ->
    ShortPlan ph rd (BlankTarget p k :: rest) (u :: urest).

(* At least one nonblank short binder must be new; pinned `gc` rejects a short declaration otherwise. *)
Fixpoint ShortHasNewName {p} {i : Input p} {ph : Phase i} {rd} {ts} {us}
  (pl : ShortPlan ph rd ts us) : Prop :=
  match pl with
  | SPNil _ _ => False
  | SPNamed _ _ _ _ bind _ _ _ _ _ _ rest =>
      match bind with SBNew _ _ _ => True | SBReuse _ _ _ _ => ShortHasNewName rest end
  | SPBlank _ _ _ _ _ _ _ _ rest => ShortHasNewName rest
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
  (rd : TypeReady ph) (c : ConsumptionSiteRef p) : Type :=
  match c with
  | ConstSite _ _ => ConstPlan ph rd (site_targets c) (site_uses c)
  | VarSite _ _   => VarPlan ph rd (site_targets c) (site_uses c)
  | ShortSite _ _ => { pl : ShortPlan ph rd (site_targets c) (site_uses c) & ShortHasNewName pl }
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
| InitReads : forall (from to : InitUnit p) (u : NameUseRef p) (bf : BindingFact ph u),
    List.In from (package_init_units k) ->
    List.In to (package_init_units k) ->
    List.In u (init_unit_uses from) ->
    init_unit_object ph to = Some (bound_object ph u bf) ->
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
(* Every initialization unit has a source position; not every one has a binding site.  A const spec binds
   several names and a blank binds none, so an accessor returning one binding site per unit could only be
   satisfied by inventing one. *)
Parameter init_unit_position : forall {p}, InitUnit p -> nat.
Definition SourceOrderTieBreak {p} {i : Input p} {ph : Phase i} {k : PackageRef p}
  (o : InitOrder ph k) : Prop :=
  forall a b : InitUnit p,
    List.In a (package_init_units k) -> List.In b (package_init_units k) ->
    ~ InitEdge ph k a b -> ~ InitEdge ph k b a ->
    (init_unit_position a < init_unit_position b)%nat ->
    PrecedesIn (init_sequence ph k o) a b.

Inductive InitPath {p} {i : Input p} (ph : Phase i) (k : PackageRef p)
  : InitUnit p -> InitUnit p -> Prop :=
| IPStep : forall a b, InitEdge ph k a b -> InitPath ph k a b
| IPMore : forall a b c, InitEdge ph k a b -> InitPath ph k b c -> InitPath ph k a c.

(* A cycle witness is data: the exact unit that reaches itself, and the exact path by which it does. *)
Record InitCycle {p} {i : Input p} (ph : Phase i) (k : PackageRef p) : Type := MakeInitCycle {
  init_cycle_unit : InitUnit p;
  init_cycle_path : InitPath ph k init_cycle_unit init_cycle_unit
}.

(* One decision, returning the exact witness on either side rather than a boolean to be interpreted. *)
Parameter init_order_dec : forall {p} {i : Input p} (ph : Phase i) (k : PackageRef p),
  InitCycle ph k + InitOrder ph k.

(* Only variable work reaches the C7 runtime store; constant evaluation is compile-time. *)
Definition runtime_initialization {p} {i : Input p} {ph : Phase i} {k : PackageRef p}
  (o : InitOrder ph k) : list (InitUnit p) :=
  List.filter RuntimeInitUnit (init_sequence ph k o).

(* ── §17 The causal dependency relation ────────────────────────────────────── *)
(* Phase-indexed, because several causes are only visible once names are bound: which variable a use reads,
   and which initialization unit a use belongs to.  Type-node causality is not here — `NodeBlocked` already
   retains its exact predecessor node, edge and that predecessor's retained outcome. *)
Inductive SiteDependency {p} {i : Input p} (ph : Phase i) : Site p -> Site p -> Prop :=
| DepUseOfExpression : forall u : ExprUseRef p,
    SiteDependency ph (SExpression p (expression_of_use u)) (SUse p u)
| DepApplicationHead : forall a : ApplicationRef p,
    SiteDependency ph (SExpression p (application_head a)) (SApplication p a)
| DepApplicationArgument : forall (a : ApplicationRef p) (u : DirectExprUseRef p),
    List.In u (application_argument_uses a) ->
    SiteDependency ph (SUse p (DirectUse p u)) (SApplication p a)
| DepStatementApplication : forall (s : ExpressionStatementRef p) (a : ApplicationRef p),
    statement_application s = Some a ->
    SiteDependency ph (SApplication p a) (SStatement p s)
| DepUnaryOperand : forall n : UnaryRef p,
    SiteDependency ph (SUse p (DirectUse p (unary_operand_use n))) (SUnary p n)
| DepVariableDeclaration : forall v : VariableSiteRef p,
    SiteDependency ph (SDeclaration p (variable_site_binding_site v)) (SVariable p v)
(* A name expression depends on the binding that gave its name meaning. *)
| DepNameBinding : forall (r : ExprRef p) (u : NameUseRef p),
    expr_name r = Some u -> SiteDependency ph (SBinding p u) (SExpression p r)
(* A consumption site depends on each of its own right-hand-side uses. *)
| DepConsumptionUse : forall (c : ConsumptionSiteRef p) (u : ExprUseRef p),
    List.In u (site_uses c) -> SiteDependency ph (SUse p u) (SConsumption p c)
(* A package initialization order depends on every binding its units read. *)
| DepDependencyBinding : forall (k : PackageRef p) (unit : InitUnit p) (u : NameUseRef p),
    List.In unit (package_init_units k) -> List.In u (init_unit_uses unit) ->
    SiteDependency ph (SBinding p u) (SDependency p k)
(* A package-level declaration is elaborated after the order that decides when it runs. *)
| DepDeclarationOrder : forall (k : PackageRef p) (b : BindingSiteRef p),
    binding_site_scope b = PackageScope p k ->
    SiteDependency ph (SDependency p k) (SDeclaration p b)
(* A short reuse depends on the earlier same-block variable whose object it retains. *)
| DepShortReuse : forall (d : ShortDeclRef p) (earlier : VariableSiteRef p),
    SiteDependency ph (SVariable p earlier) (SConsumption p (ShortSite p d))
(* The unused-local verdict depends on the exact reads of that variable. *)
| DepLocalRead : forall (v : VariableSiteRef p) (u : NameUseRef p) (bf : BindingFact ph u),
    bound_object ph u bf
      = source_object ph (binding_site_object_site (variable_site_binding_site v)) ->
    SiteDependency ph (SBinding p u) (SVariable p v).

(* ── §9 Requirements are exact missing facts ───────────────────────────────── *)
(* Each constructor retains the exact partial facts already established at that site, so a requirement
   cannot pair an arbitrary use with an arbitrary object, and satisfaction never asks whether the outcome
   is already supported. *)
(* No environment index: a requirement is reportable for an arbitrary core.  Each constructor carries the
   exact readiness the partial facts it retains were established at. *)
Inductive SiteRequirement {p} {i : Input p} (ph : Phase i) : Site p -> Type :=
| NeedTypeMeaning : forall (rd : TypeReady ph) (u : NameUseRef p) (bf : BindingFact ph u),
    ObjectMeaning ph rd (bound_object ph u bf) -> SiteRequirement ph (SBinding p u)
| NeedValueMeaning : forall (rd : TypeReady ph) (u : NameUseRef p) (bf : BindingFact ph u),
    ObjectMeaning ph rd (bound_object ph u bf) -> SiteRequirement ph (SBinding p u)
| NeedApplication : forall (rd : TypeReady ph) (a : ApplicationRef p)
    (hf : ResultFormAt ph rd) (args : list (ResultAtomAt ph rd)),
    ExprFact ph rd (application_head a) hf ->
    ArgFacts ph rd (application_argument_uses a) args ->
    ErasedProfile -> SiteRequirement ph (SApplication p a)
| NeedStatement : forall (rd : TypeReady ph) (s : ExpressionStatementRef p) (a : ApplicationRef p)
    (hf : ResultFormAt ph rd),
    statement_application s = Some a ->
    ExprFact ph rd (application_head a) hf -> SiteRequirement ph (SStatement p s)
| NeedUnary : forall (rd : TypeReady ph) (n : UnaryRef p) (opa : ResultAtomAt ph rd),
    ResultUseFactAt ph rd (DirectUse p (unary_operand_use n)) opa ->
    SiteRequirement ph (SUnary p n).

(* Satisfaction is a question about the fact families, not about the site table. *)
(* Every case is a positive semantic relation over the exact facts the requirement retains.  None asks
   whether the successful site fact happens to be inhabited: that would decide whether a requirement is met
   by checking for the very thing the requirement reports as missing. *)
Definition RequirementSatisfied {p} {i : Input p} {ph : Phase i} {s}
  (r : SiteRequirement ph s) : Prop :=
  match r with
  | NeedTypeMeaning _ _ _ _ f => IsTypeCapable f
  | NeedValueMeaning _ _ _ _ f =>
      IsConstantCapable f \/ IsVariableCapable f \/ IsContextualCapable f
  | NeedApplication _ rd _ _ args _ _ _ => ApplicationRuleCovers rd args
  | NeedStatement _ _ _ a _ _ _ => StatementRuleCovers ph a
  | NeedUnary _ rd _ opa _ => UnaryRuleCovers rd opa
  end.

Parameter requirement_dec : forall {p} {i : Input p} {ph : Phase i} {s}
  (r : SiteRequirement ph s),
  { RequirementSatisfied r } + { ~ RequirementSatisfied r }.

(* The exact bound object a name requirement is about is read off its binding fact, never supplied. *)
Definition requirement_object {p} {i : Input p} {ph : Phase i} {s}
  (r : SiteRequirement ph s) : option (ObjectRef ph) :=
  match r with
  | NeedTypeMeaning _ _ u bf _ => Some (bound_object ph u bf)
  | NeedValueMeaning _ _ u bf _ => Some (bound_object ph u bf)
  | _ => None
  end.

Parameter requirement_view : forall {p} {i : Input p} {ph : Phase i} {s},
  SiteRequirement ph s -> RequirementView.

(* ── §10 Site failures retain their exact causes ───────────────────────────── *)
(* The source witnesses a diagnostic must consume.  These are facts about the source and its bindings, not
   claims that Go rejects the program: two binders sharing a spelling in one scope IS the duplication, and a
   package-level declaration spelled `init` IS the reservation. *)
Definition DuplicateBinders {p} (earlier later : BindingSiteRef p) : Prop :=
  binding_site_spelling earlier = binding_site_spelling later /\
  binding_site_scope earlier = binding_site_scope later /\
  DeclaredBefore earlier later.

Definition ShortHasNoNewName {p} {i : Input p} (ph : Phase i) (d : ShortDeclRef p) : Prop :=
  forall n : BindingNameRef p, binding_name_short_lhs n = Some d ->
    match binder_disposition ph n with
    | BinderNew _ _ _ _ _ => False
    | _ => True
    end.

Definition NoReadOf {p} {i : Input p} (ph : Phase i) (v : VariableSiteRef p) : Prop :=
  forall (u : NameUseRef p) (bf : BindingFact ph u),
    bound_object ph u bf
      <> source_object ph (binding_site_object_site (variable_site_binding_site v)).

(* A duplicate declaration is a failure at the declaration site, not at some unrelated name use; an argument
   failure retains the exact argument use, not a free index; a consumption failure retains the exact
   occurrence, not a free position. *)
(* No environment index: a failed or cyclic core must be able to report why no environment exists.  The
   three cases that genuinely resolved a type carry the exact readiness they used. *)
Inductive SiteFailure {p} {i : Input p} (ph : Phase i) : Site p -> Type :=
| FUnresolvedName : forall u : NameUseRef p, SiteFailure ph (SBinding p u)
| FDuplicateDeclaration : forall earlier later : BindingSiteRef p,
    DuplicateBinders earlier later -> SiteFailure ph (SDeclaration p later)
| FPackageInitReserved : forall b : BindingSiteRef p,
    PackageInitReserved (binding_site_context b) (binding_site_spelling b) ->
    SiteFailure ph (SDeclaration p b)
| FArgumentRejected : forall (a : ApplicationRef p) (u : DirectExprUseRef p),
    In u (application_argument_uses a) -> ArgumentReason ->
    SiteFailure ph (SApplication p a)
| FInvalidConversion : forall a : ApplicationRef p,
    OperandResultView -> TypeView -> list (ExprRef p) -> SiteFailure ph (SApplication p a)
| FOperandRejected : forall n : UnaryRef p, OperandReason -> SiteFailure ph (SUnary p n)
| FNotAStatement : forall t : ExpressionStatementRef p, StatementReason ->
    SiteFailure ph (SStatement p t)
| FResultCountWrong : forall c : ConsumptionSiteRef p, nat -> nat ->
    SiteFailure ph (SConsumption p c)
| FNotAssignableAt : forall (c : ConsumptionSiteRef p) (rd : TypeReady ph) (u : ExprUseRef p)
    (a : ResultAtomAt ph rd),
    ResultUseFactAt ph rd u a -> SemanticType p -> SiteFailure ph (SConsumption p c)
| FNotRepresentableAt : forall (c : ConsumptionSiteRef p) (rd : TypeReady ph) (u : ExprUseRef p)
    (a : ResultAtomAt ph rd),
    ResultUseFactAt ph rd u a -> SemanticType p -> SiteFailure ph (SConsumption p c)
| FConstInitNotConstant : forall (c : ConsumptionSiteRef p) (rd : TypeReady ph) (u : ExprUseRef p)
    (a : ResultAtomAt ph rd),
    ResultUseFactAt ph rd u a -> ConstInitReason -> SiteFailure ph (SConsumption p c)
| FNoNewVariable : forall d : ShortDeclRef p,
    ShortHasNoNewName ph d -> SiteFailure ph (SConsumption p (ShortSite p d))
| FContext : forall r : ExprRef p, ContextReason -> SiteFailure ph (SExpression p r)
| FDefaultNotRepresentable : forall r : ExprRef p,
    UntypedConstantKind -> TypeView -> SiteFailure ph (SExpression p r)
| FUnusedLocal : forall (v : VariableSiteRef p) (rd : TypeReady ph),
    StaticVariable ph rd
      (source_object ph (binding_site_object_site (variable_site_binding_site v))) ->
    NoReadOf ph v -> SiteFailure ph (SVariable p v)
| FInitializationCycle : forall k : PackageRef p, InitCycle ph k -> SiteFailure ph (SDependency p k).

(* ── The fact a supported site carries ─────────────────────────────────────── *)
Parameter DeclarationFact : forall {p} {i : Input p} (ph : Phase i), BindingSiteRef p -> Type.
(* A supported dependency site is exactly a valid initialization order for that package. *)
Definition DependencyFact {p} {i : Input p} (ph : Phase i) (k : PackageRef p) : Type :=
  InitOrder ph k.
(* A supported variable site is exactly the static variable of that site's own object.  There is no total
   variable fact: a failed, outside or blocked declaration has object identity and no static variable. *)
Definition VariableFact {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady ph) (v : VariableSiteRef p) : Type :=
  StaticVariable ph rd (source_object ph (binding_site_object_site (variable_site_binding_site v))).

Definition SiteFact {p} {i : Input p} (ph : Phase i)
  (rd : TypeReady ph) (s : Site p) : Type :=
  match s with
  | SBinding _ u     => BindingFact ph u
  | SExpression _ r  => { form : ResultFormAt ph rd & ExprFact ph rd r form }
  | SUse _ u         => match use_refinement u with
                        | ResultRefinement => { a : ResultAtomAt ph rd & ResultUseFactAt ph rd u a }
                        | _ => { form : ResultFormAt ph rd &
                                 ExprFact ph rd (expression_of_use u) form }
                        end
  | SApplication _ a => { res : list (ResultAtomAt ph rd) & AppFact ph rd a res }
  | SStatement _ t   => StmtFact ph rd t
  | SUnary _ n       => { opa : ResultAtomAt ph rd &
                        { res : list (ResultAtomAt ph rd) & UnaryFact ph rd n opa res } }
  | SConsumption _ c => ConsumptionFact ph rd c
  | SVariable _ v    => VariableFact ph rd v
  | SDeclaration _ b => DeclarationFact ph b
  | SDependency _ k  => DependencyFact ph k
  end.

(* ── §10 One outcome per site ──────────────────────────────────────────────── *)
(* The topology below is the specification of a module-private type.  `Compilable.Report` exports
   `phase_outcome` and the projections; it does not export these constructors, because they are freely
   applicable and a client holding them could fabricate an outcome claiming a site failed. *)
Inductive SiteOutcome {p} {i : Input p} (ph : Phase i) : Site p -> Type :=
| Supported       : forall (s : Site p) (rd : TypeReady ph), SiteFact ph rd s -> SiteOutcome ph s
| DefiniteFailure : forall s, SiteFailure ph s -> SiteOutcome ph s
| Outside         : forall s, SiteRequirement ph s -> SiteOutcome ph s
(* Blocked retains the exact predecessor site and the exact dependency edge, and nothing more: the
   predecessor's outcome is `phase_outcome ph pred`, which is unique, so no equal-looking substitute can be
   supplied alongside it. *)
| Blocked         : forall s pred, SiteDependency ph pred s -> SiteOutcome ph s.

Definition IsSupported {p} {i : Input p} {ph : Phase i} {s}
  (o : SiteOutcome ph s) : Prop :=
  match o with Supported _ _ _ _ => True | _ => False end.

(* Indexed by the exact environment, so extracting the fact never needs two environments to be equal. *)
Inductive SupportedAt {p} {i : Input p} {ph : Phase i} (rd : TypeReady ph)
  : forall s : Site p, SiteOutcome ph s -> Type :=
| IsSupportedAt : forall (s : Site p) (f : SiteFact ph rd s),
    SupportedAt rd s (Supported ph s rd f).

Definition supported_fact {p} {i : Input p} {ph : Phase i} {rd} {s} {o : SiteOutcome ph s}
  (h : SupportedAt rd s o) : SiteFact ph rd s :=
  match h in SupportedAt _ s0 _ return SiteFact ph rd s0 with
  | IsSupportedAt _ _ f => f
  end.

Definition IsDefiniteFailure {p} {i : Input p} {ph : Phase i} {s}
  (o : SiteOutcome ph s) : Prop :=
  match o with DefiniteFailure _ _ _ => True | _ => False end.

Definition IsRootOutside {p} {i : Input p} {ph : Phase i} {s}
  (o : SiteOutcome ph s) : Prop :=
  match o with Outside _ _ _ => True | _ => False end.

Definition root_requirement {p} {i : Input p} {ph : Phase i} {s}
  (o : SiteOutcome ph s) : IsRootOutside o -> SiteRequirement ph s :=
  match o in SiteOutcome _ s0 return IsRootOutside o -> SiteRequirement ph s0 with
  | Outside _ _ r => fun _ => r
  | Supported _ _ _ _ => fun h => match h return SiteRequirement ph _ with end
  | DefiniteFailure _ _ _ => fun h => match h return SiteRequirement ph _ with end
  | Blocked _ _ _ _ => fun h => match h return SiteRequirement ph _ with end
  end.

(* Every site has an outcome for an arbitrary core, with no global environment in sight. *)
Parameter phase_outcome : forall {p} {i : Input p} (ph : Phase i) (s : Site p), SiteOutcome ph s.

(* ── §13 The complete diagnostic authority ─────────────────────────────────── *)
(* Site failures enter through one constructor; the package- and program-level reasons keep their own,
   because they have no single site.  Every current public constructor survives. *)
(* Indexed by the phase, not by a ready environment: a cyclic phase has no environment and still needs its
   type-cycle diagnostic.  The site-failure constructor carries the readiness that failure required. *)
Inductive DiagnosticReason {p} {i : Input p} (ph : Phase i) : Type :=
| AtSiteFailure : forall s : Site p, SiteFailure ph s -> DiagnosticReason ph
| TypeCycleFound : TypeCycle (phase_equations ph) -> DiagnosticReason ph
| MainRedeclared : forall later earlier : ObjectSiteRef p, DiagnosticReason ph
| MissingMainEntry : PackageRef p -> DiagnosticReason ph
| BuildOutputIsDirectory : PackageRef p -> string -> DiagnosticReason ph.

Definition site_failure_code {p} {i : Input p} {ph : Phase i} {s}
  (f : SiteFailure ph s) : DiagnosticCode :=
  match f with
  | FUnresolvedName _ _ => CodeUnresolvedName
  | FDuplicateDeclaration _ _ _ _ => CodeDuplicateDeclaration
  | FPackageInitReserved _ _ _ => CodeContext
  | FArgumentRejected _ _ _ _ _ => CodeArgument
  | FInvalidConversion _ _ _ _ _ => CodeInvalidConversion
  | FOperandRejected _ _ _ => CodeOperand
  | FNotAStatement _ _ _ => CodeNotAStatement
  | FResultCountWrong _ _ _ _ => CodeResultCount
  | FNotAssignableAt _ _ _ _ _ _ _ => CodeNotAssignable
  | FNotRepresentableAt _ _ _ _ _ _ _ => CodeNotRepresentable
  | FConstInitNotConstant _ _ _ _ _ _ _ => CodeConstInitializerNotConstant
  | FNoNewVariable _ _ _ => CodeNoNewVariable
  | FContext _ _ _ => CodeContext
  | FDefaultNotRepresentable _ _ _ _ => CodeDefaultNotRepresentable
  | FUnusedLocal _ _ _ _ _ => CodeUnusedLocal
  | FInitializationCycle _ _ _ => CodeInitializationCycle
  end.

Definition diagnostic_code {p} {i : Input p} {ph : Phase i}
  (d : DiagnosticReason ph) : DiagnosticCode :=
  match d with
  | AtSiteFailure _ _ f => site_failure_code f
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
  | AtSiteFailure _ _ f =>
      match f with
      | FInvalidConversion _ _ _ t _ => Some t
      | FDefaultNotRepresentable _ _ _ t => Some t
      | FNotAssignableAt _ _ _ _ _ _ t => Some (type_view t)
      | FNotRepresentableAt _ _ _ _ _ _ t => Some (type_view t)
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
(* No environment index: an outside-scope core is precisely one with no ready environment, so a boundary
   that needed one could never be reported. *)
Record PackedBoundary {p} {i : Input p} (ph : Phase i) : Type := MakeBoundary {
  boundary_site : Site p;
  boundary_requirement : SiteRequirement ph boundary_site;
  boundary_is_root : IsRootOutside (phase_outcome ph boundary_site)
}.

Definition boundary_view {p} {i : Input p} {ph : Phase i}
  (b : PackedBoundary ph) : RequirementView :=
  requirement_view (boundary_requirement ph b).

(* The site table is the authority; the report lists are its canonical projections, not peer lists.
   `Core`, `Elaboration` and `phase` are the existing repository names, stubbed once above. *)
Parameter core_diagnostics : forall {p} (c : Core p), list (DiagnosticReason (phase c)).
Parameter core_boundaries : forall {p} (c : Core p), list (PackedBoundary (phase c)).

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
Definition accepted_ready (cp : Program) : TypeReady (accepted_phase cp) :=
  ready_of (phase_type_result (accepted_phase cp)) (accepted_is_ready cp).
Definition accepted_outcome (cp : Program) (s : Site (source cp))
  : SiteOutcome (accepted_phase cp) s :=
  phase_outcome (accepted_phase cp) s.

(* Derived, not postulated: an accepted core has no diagnostic and no boundary, and the report lists are
   exact projections of the root site outcomes, so no site can be failed, outside, or blocked. *)
(* Only the accepted capability projects one common exact ready environment: every site is supported at
   that same environment, which is what makes the accepted facts total. *)
Parameter accepted_supported : forall (cp : Program) (s : Site (source cp)),
  SupportedAt (accepted_ready cp) s (accepted_outcome cp s).

Definition accepted_fact (cp : Program) (s : Site (source cp))
  : SiteFact (accepted_phase cp) (accepted_ready cp) s :=
  supported_fact (accepted_supported cp s).

Definition AcceptedType (cp : Program) : Type := SemanticType (source cp).
Definition Object (cp : Program) : Type := ObjectRef (accepted_phase cp).
Definition ExpressionFact (cp : Program) (r : ExprRef (source cp)) : Type :=
  { form : ResultFormAt (accepted_phase cp) (accepted_ready cp) &
    ExprFact (accepted_phase cp) (accepted_ready cp) r form }.
Definition expression_fact (cp : Program) (r : ExprRef (source cp)) : ExpressionFact cp r :=
  accepted_fact cp (SExpression (source cp) r).
Definition ApplicationFact (cp : Program) (a : ApplicationRef (source cp)) : Type :=
  { res : list (ResultAtomAt (accepted_phase cp) (accepted_ready cp)) &
    AppFact (accepted_phase cp) (accepted_ready cp) a res }.
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
(* The three literal emission authorities: canonical decimal for magnitudes, canonical Go escaping for
   strings.  Nothing else may spell a literal. *)
Parameter decimal_of_magnitude : N -> string.
Parameter decimal_of_float : NonNegativeDecimal -> string.
Parameter escape_go_string : string -> string.
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
Definition DQUOTE : string := String (ascii_of_nat 34) EmptyString.

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

(* ── §15.10 Exact literal bytes ────────────────────────────────────────────── *)
Theorem render_literal_integer : forall n : N,
  render_literal (IntegerLiteral n) = decimal_of_magnitude n.
Proof. Admitted.

Theorem render_literal_float : forall d : NonNegativeDecimal,
  render_literal (FloatLiteral d) = decimal_of_float d.
Proof. Admitted.

(* The canonical Go spelling: double-quoted with the escaping authority applied to the exact contents. *)
Theorem render_literal_string : forall s : string,
  render_literal (StringLiteral s) = (DQUOTE ++ escape_go_string s ++ DQUOTE)%string.
Proof. Admitted.

(* ── §15.11 The empty declaration group's exact bytes ──────────────────────── *)
(* `renders_grouped` sends the empty group to the parenthesized form, so the chosen bytes are frozen here
   rather than left implicit.  Pinned `gc` accepts both this and `const ()`. *)
Theorem render_empty_const_group :
  render_declaration (ConstDecl []) = ("const (" ++ NL ++ ")")%string.
Proof. Admitted.

Theorem render_empty_var_group :
  render_declaration (VarDecl []) = ("var (" ++ NL ++ ")")%string.
Proof. Admitted.

Theorem render_empty_type_group :
  render_declaration (TypeDecl []) = ("type (" ++ NL ++ ")")%string.
Proof. Admitted.

(* ── §15.7 Valid-side obligations: what an accepted site rules out ─────────── *)
(* A rejection is a report, not a proof of Go-invalidity.  The honest content of a check therefore lives on
   the accepted side: these say what supportedness itself forbids. *)
Theorem supported_declaration_not_init_reserved :
  forall {p} {i : Input p} (ph : Phase i) (b : BindingSiteRef p),
  IsSupported (phase_outcome ph (SDeclaration p b)) ->
  ~ PackageInitReserved (binding_site_context b) (binding_site_spelling b).
Proof. Admitted.

(* The three application kinds partition `AppFact`: no application is both a conversion and a call, so a
   statement's println classification cannot silently overlap a conversion. *)
Theorem app_kind_trichotomy :
  forall {p} {i : Input p} {ph : Phase i} {rd} {a : ApplicationRef p}
    {res : list (ResultAtomAt ph rd)} (f : AppFact ph rd a res),
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
(* The token boundary lives at the junction between the operator and its operand.  A rendered unary may
   legitimately contain `--` inside a string literal, so the property is about the operand's first byte. *)
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
Theorem cyclic_phase_has_no_environment :
  forall p (i : Input p) (ph : Phase i) (c : TypeCycle (phase_equations ph)),
  ~ IsTypeReady (PhaseCyclic ph c).
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

(* ── §16.13 Statement classification is exact, not a boundary of convenience ── *)
(* Go has already decided that these builtins cannot stand as statements, so the outcome is a definite
   failure carrying its exact reason.  Reporting them as `OutsideScope` would launder a known rejection into
   "unmodelled", which is precisely what the three-way decision exists to prevent. *)
Theorem forbidden_builtin_is_definite_failure :
  forall {p} {i : Input p} (ph : Phase i) (s : ExpressionStatementRef p)
    (a : ApplicationRef p) (hu : NameUseRef p) (bf : BindingFact ph hu) (n : PredeclaredName),
  statement_application s = Some a ->
  expr_name (application_head a) = Some hu ->
  object_origin (bound_object ph hu bf) = Predeclared p n ->
  builtin_forbidden_as_statement n = true ->
  phase_outcome ph (SStatement p s)
    = DefiniteFailure ph (SStatement p s) (FNotAStatement ph s (BuiltinNotAStatement n)).
Proof. Admitted.

(* A bare conversion is a definite failure for the same reason, and retains the exact target type view. *)
Theorem conversion_is_not_a_statement :
  forall {p} {i : Input p} (ph : Phase i) (rd : TypeReady ph)
    (s : ExpressionStatementRef p) (a : ApplicationRef p)
    (res : list (ResultAtomAt ph rd)) (f : AppFact ph rd a res),
  statement_application s = Some a -> IsConversionApp f ->
  exists tv : TypeView,
    phase_outcome ph (SStatement p s)
      = DefiniteFailure ph (SStatement p s) (FNotAStatement ph s (ConversionNotAStatement tv)).
Proof. Admitted.

(* An expression statement that is not an application at all is a definite failure retaining its exact
   result form, never a missing-rule boundary. *)
Theorem non_application_is_not_a_statement :
  forall {p} {i : Input p} (ph : Phase i) (s : ExpressionStatementRef p),
  statement_application s = None ->
  exists rf : ErasedResultForm,
    phase_outcome ph (SStatement p s)
      = DefiniteFailure ph (SStatement p s) (FNotAStatement ph s (NotAnApplication rf)).
Proof. Admitted.

(* ── §16.14 Coverage and the rules agree ───────────────────────────────────── *)
(* The coverage relations are the definition of satisfaction and the rule families are the construction;
   §18 requires them stated separately, since defining satisfaction as "the rule is inhabited" would decide
   a requirement by checking for the very thing it reports as missing.  These theorems are the bridge, so
   the separation is a proved agreement rather than an unchecked restatement. *)
Theorem unary_coverage_iff_rule :
  forall {p} {i : Input p} {ph : Phase i} (rd : TypeReady ph) (n : UnaryRef p)
    (opa : ResultAtomAt ph rd),
  UnaryRuleCovers rd opa <-> exists res, inhabited (UnaryFact ph rd n opa res).
Proof. Admitted.

Theorem conversion_coverage_iff_rule :
  forall {p} {i : Input p} {ph : Phase i} (rd : TypeReady ph) (a : ApplicationRef p)
    (dst : SemanticType p) (arg : ResultAtomAt ph rd),
  ConvRuleCovers rd dst arg <-> exists res, inhabited (ConvRule ph rd a dst arg res).
Proof. Admitted.

Theorem complex_coverage_iff_rule :
  forall {p} {i : Input p} {ph : Phase i} (rd : TypeReady ph) (a : ApplicationRef p)
    (a1 a2 : ResultAtomAt ph rd),
  ComplexRuleCovers rd a1 a2 <-> exists res, inhabited (ComplexRuleF ph rd a a1 a2 res).
Proof. Admitted.

Theorem println_coverage_iff_rule :
  forall {p} {i : Input p} {ph : Phase i} (rd : TypeReady ph) (a : ApplicationRef p)
    (args : list (ResultAtomAt ph rd)),
  PrintlnRuleCovers rd args <-> inhabited (PrintlnRuleF ph rd a args).
Proof. Admitted.

(* A blocked site's predecessor is genuinely unresolved: blocking is never reported for a site whose cause
   in fact succeeded. *)
Theorem blocked_predecessor_is_not_supported :
  forall {p} {i : Input p} (ph : Phase i) (s pred : Site p) (e : SiteDependency ph pred s),
  phase_outcome ph s = Blocked ph s pred e ->
  ~ IsSupported (phase_outcome ph pred).
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
Definition packed_view {p} (c : Core p) (b : PackedBoundary (phase c)) : RequirementView :=
  boundary_view b.

Fixpoint StrictlyIncreasingBy {A : Type} (lt : A -> A -> Prop) (l : list A) : Prop :=
  match l with
  | [] => True
  | a :: rest =>
      match rest with
      | [] => True
      | b :: _ => lt a b /\ StrictlyIncreasingBy lt rest
      end
  end.

Definition StrictlyIncreasing (l : list RequirementView) : Prop :=
  StrictlyIncreasingBy view_lt l.

Theorem boundary_order_canonical : forall {p} (c : Core p),
  StrictlyIncreasing (List.map (packed_view c) (core_boundaries c)).
Proof. Admitted.

Theorem boundary_views_nodup : forall {p} (c : Core p),
  NoDup (List.map (packed_view c) (core_boundaries c)).
Proof. Admitted.

(* Completeness of the list, which no record field can supply: every root-outside site is listed. *)
Theorem root_boundary_complete : forall {p} (c : Core p) (s : Site p),
  IsRootOutside (phase_outcome (phase c) s) ->
  exists b, List.In b (core_boundaries c) /\
    boundary_site (phase c) b = s.
Proof. Admitted.

Theorem boundary_requirement_unsatisfied : forall {p} (c : Core p) b,
  List.In b (core_boundaries c) ->
  ~ RequirementSatisfied (boundary_requirement (phase c) b).
Proof. Admitted.

(* ── §16.10 Objects are identified by their origin ─────────────────────────── *)
Theorem object_origin_injective : forall {p} {i : Input p} {ph : Phase i} (o1 o2 : ObjectRef ph),
  object_origin o1 = object_origin o2 -> o1 = o2.
Proof. Admitted.

(* ── §16.11 Every reflected decision agrees with its relation ──────────────── *)
(* The booleans are separate parameters from the inductives, so without these four the decisions could
   answer anything.  Identity and assignability decide with no environment at all; convertibility and
   representability need the exact readiness their underlying form depends on. *)
Theorem identicalb_reflect : forall {p} (s t : SemanticType p),
  identicalb s t = true <-> Identical s t.
Proof. Admitted.

Theorem assignableb_reflect : forall {p} (s t : SemanticType p),
  assignableb s t = true <-> Assignable s t.
Proof. Admitted.

Theorem value_convertibleb_reflect :
  forall {p} {i : Input p} {ph : Phase i} (rd : TypeReady ph) (s t : SemanticType p),
  value_convertibleb rd s t = true <-> ValueConvertible rd s t.
Proof. Admitted.

Theorem representableb_reflect :
  forall {p} {i : Input p} {ph : Phase i} (rd : TypeReady ph) (s : SemanticType p) (c : Constant),
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

(* ── §17 Binding: what no constructor can enforce ──────────────────────────── *)
(* `Resolves` is a relation and `resolve_name` is a function; without this they could disagree. *)
Theorem resolve_name_reflects :
  forall {p} {i : Input p} (ph : Phase i) (u : NameUseRef p) (o : ObjectRef ph),
  resolve_name ph u = Some o <-> Resolves ph u o.
Proof. Admitted.

(* A resolved object always carries the spelling that was written at the use. *)
Theorem resolution_is_same_spelling :
  forall {p} {i : Input p} (ph : Phase i) (u : NameUseRef p) (o : ObjectRef ph),
  Resolves ph u o -> object_spelling o = name_use_spelling u.
Proof. Admitted.

(* Nearest-visible is unique: no use resolves to two different objects. *)
Theorem resolution_is_unique :
  forall {p} {i : Input p} (ph : Phase i) (u : NameUseRef p) (o1 o2 : ObjectRef ph),
  Resolves ph u o1 -> Resolves ph u o2 -> o1 = o2.
Proof. Admitted.

(* Exact shadowing: a visible source binding of that spelling displaces the predeclared object. *)
Theorem source_binding_shadows_predeclared :
  forall {p} {i : Input p} (ph : Phase i) (u : NameUseRef p) (b : BindingSiteRef p)
    (n : PredeclaredName),
  binding_site_spelling b = name_use_spelling u -> VisibleAt b u ->
  ~ Resolves ph u (predeclared_object ph n).
Proof. Admitted.

(* Package collection is file-order independent: a package-level binding's scope is fixed by its package
   alone, so no permutation of the file list can move it. *)
Theorem package_scope_independent_of_file :
  forall {p} (b : BindingSiteRef p) (k : PackageRef p),
  binding_site_scope b = PackageScope p k ->
  scope_parent (binding_site_scope b) = Some (PredeclaredScope p).
Proof. Admitted.

(* The scope-start rules, stated as what they exclude rather than as definitional unfolds. *)
Theorem local_const_not_visible_in_its_own_spec :
  forall {p} (b : BindingSiteRef p) (u : NameUseRef p),
  binding_site_context b = LocalConstDecl ->
  (name_use_position u < binding_site_spec_end b)%nat -> ~ VisibleAt b u.
Proof. Admitted.

Theorem short_name_not_visible_in_its_own_statement :
  forall {p} (b : BindingSiteRef p) (u : NameUseRef p),
  binding_site_context b = ShortDecl ->
  (name_use_position u < binding_site_statement_end b)%nat -> ~ VisibleAt b u.
Proof. Admitted.

(* A local type name IS visible at its own identifier, which is exactly why self-reference is a cycle and
   not an unresolved name. *)
Theorem local_type_visible_at_its_own_identifier :
  forall {p} (b : BindingSiteRef p) (u : NameUseRef p),
  binding_site_context b = LocalTypeDecl ->
  Encloses (binding_site_scope b) (name_use_scope u) ->
  (binding_site_identifier_position b <= name_use_position u)%nat -> VisibleAt b u.
Proof. Admitted.

(* Characterizations: a duplicate is exactly two visible binders of one spelling in one scope, and an
   unresolved name is exactly one with nothing visible and no predeclared spelling. *)
Theorem duplicate_declaration_characterization :
  forall {p} {i : Input p} (ph : Phase i) (earlier later : BindingSiteRef p),
  DuplicateBinders earlier later ->
  exists w, phase_outcome ph (SDeclaration p later)
    = DefiniteFailure ph (SDeclaration p later) (FDuplicateDeclaration ph earlier later w).
Proof. Admitted.

Theorem unresolved_name_characterization :
  forall {p} {i : Input p} (ph : Phase i) (u : NameUseRef p),
  (forall b : BindingSiteRef p,
     binding_site_spelling b = name_use_spelling u -> ~ VisibleAt b u) ->
  (forall n : PredeclaredName, predeclared_spelling n <> name_use_spelling u) ->
  phase_outcome ph (SBinding p u)
    = DefiniteFailure ph (SBinding p u) (FUnresolvedName ph u).
Proof. Admitted.

(* ── §18 Type resolution ───────────────────────────────────────────────────── *)
(* A supported node denotes exactly the type its outcome carries. *)
Theorem node_outcome_sound :
  forall {p} {i : Input p} {ph : Phase i} (rd : TypeReady ph) (n : TypeNode p) (t : SemanticType p),
  node_outcome ph n = NodeSupported ph n t -> node_rhs rd n = t.
Proof. Admitted.

(* ── §19 Objects ───────────────────────────────────────────────────────────── *)
Theorem source_object_origin_is_its_site :
  forall {p} {i : Input p} (ph : Phase i) (s : ObjectSiteRef p),
  object_origin (source_object ph s) = SourceSite p s.
Proof. Admitted.

(* ── §20 Dependencies and reports ──────────────────────────────────────────── *)
Theorem init_units_nodup : forall {p} (k : PackageRef p), NoDup (package_init_units k).
Proof. Admitted.

(* The runtime projection carries only runtime work, and carries it in the accepted order. *)
Theorem runtime_projection_excludes_constants :
  forall {p} {i : Input p} {ph : Phase i} {k : PackageRef p} (o : InitOrder ph k),
  List.Forall (fun u => RuntimeInitUnit u = true) (runtime_initialization o).
Proof. Admitted.

Theorem runtime_projection_preserves_order :
  forall {p} {i : Input p} {ph : Phase i} {k : PackageRef p} (o : InitOrder ph k) (a b : InitUnit p),
  PrecedesIn (runtime_initialization o) a b -> PrecedesIn (init_sequence ph k o) a b.
Proof. Admitted.

(* A blocked site is never reported: only root causes reach the diagnostic and boundary lists. *)
Theorem blocked_sites_are_not_reported :
  forall {p} (c : Core p) (s pred : Site p) (e : SiteDependency (phase c) pred s),
  phase_outcome (phase c) s = Blocked (phase c) s pred e ->
  ~ List.In s (List.map (boundary_site (phase c)) (core_boundaries c)).
Proof. Admitted.

(* The accepted environment is the phase's own retained result, not a rebuild equal to it. *)
Theorem accepted_environment_is_retained : forall cp : Program,
  phase_type_result (accepted_phase cp) = PhaseReady (accepted_phase cp) (accepted_ready cp).
Proof. Admitted.

(* ── §21 The diagnostic list is canonical, duplicate-free and complete ─────── *)
Definition diagnostic_lt {p} {i : Input p} {ph : Phase i}
  (a b : DiagnosticReason ph) : Prop := diagnostic_compare a b = Lt.

Theorem diagnostic_order_canonical : forall {p} (c : Core p),
  StrictlyIncreasingBy diagnostic_lt (core_diagnostics c).
Proof. Admitted.

(* Distinct diagnostics stay distinct after erasure, which is what makes the erased report faithful. *)
Theorem erased_diagnostics_nodup : forall {p} (c : Core p),
  NoDup (List.map erase_diagnostic (core_diagnostics c)).
Proof. Admitted.

(* Completeness: every root definite failure is reported.  No constructor can supply this. *)
Theorem root_failure_complete : forall {p} (c : Core p) (s : Site p),
  IsDefiniteFailure (phase_outcome (phase c) s) ->
  exists d : DiagnosticReason (phase c), List.In d (core_diagnostics c).
Proof. Admitted.

(* ── §22 The typed computations are pinned to the untyped authorities ──────── *)
(* Without these, `negate_basic_typed`, `basic_typed_of` and `complex_typed_of` could return any value of
   the right type and the rules that call them would still typecheck — the typed result would be causally
   unrelated to the operand it claims to come from. *)
Theorem negate_basic_typed_negates : forall (b : BasicType) (v v' : BasicTypedConstant b),
  negate_basic_typed b v = Some v' ->
  negate_constant (basic_typed_value b v) = Some (basic_typed_value b v').
Proof. Admitted.

Theorem basic_typed_of_keeps_its_value : forall (b : BasicType) (c : Constant)
  (v : BasicTypedConstant b),
  basic_typed_of b c = Some v -> basic_typed_value b v = c.
Proof. Admitted.

Theorem complex_typed_of_combines : forall (f : FloatKind)
  (v1 v2 : BasicTypedConstant (predeclared_basic_form (float_named_basic f)))
  (vr : BasicTypedConstant (predeclared_basic_form (complex_named_basic f))),
  complex_typed_of f v1 v2 = Some vr ->
  complex_of_constants
    (basic_typed_value (predeclared_basic_form (float_named_basic f)) v1)
    (basic_typed_value (predeclared_basic_form (float_named_basic f)) v2)
  = Some (basic_typed_value (predeclared_basic_form (complex_named_basic f)) vr).
Proof. Admitted.

(* `underlyingb` is the only reflected decision returning a form rather than a boolean. *)
Theorem underlyingb_reflects :
  forall {p} {i : Input p} {ph : Phase i} (rd : TypeReady ph) (t : SemanticType p) (b : BasicType),
  underlyingb rd t = b <-> Underlying rd t b.
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

**Type chains, `complex` profiles and cycles.** `type U uintptr; type T U` accepts, so a predeclared name
with no C6 type meaning is a boundary and never a rejection. All six `complex` operand combinations accept
with the kind the contract assigns — two untyped giving `complex128`, and any `float32` operand giving
`complex64`; mixed `float32`/`float64` rejects, so both operands share one kind. A package-level forward
reference accepts while `var a = b; var b = a` and the same pair as constants both reject, so dependency
decides initialization order and cycles are definite failures.

**Short declarations.** `x := 1; x, y := 2, 3` accepts and `x := 1; x := 2` rejects, so at least one nonblank
left-hand name must be new. `x := 1; x, y := "s", 3` rejects, so a reuse carries exact type compatibility.

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
