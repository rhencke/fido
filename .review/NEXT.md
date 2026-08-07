# C6 — the static semantic foundation

Review: contract

Goal: ordinary source names acquire meaning only through binding. C6 lands the pinned predeclared identity
catalog, a closed type algebra with **named** predeclared types, exact constants, expression/use/application
facts, one result-consumption authority, compiler-owned static variable identity, the package dependency
outcome, and a three-way decision that never calls unmodelled Go a rejection.

**C6 is entirely static.** No `Runtime`, value, place, store, environment or `Machine.T`; C7 introduces them
as one vertical. `ARCHITECTURE.md` owns the ownership law, `ROADMAP.md` the milestone sequence.

The declarations below are the published surface **verbatim**: `make contract-surface` elaborates exactly
this text under the pinned Rocq. Names are written unqualified, as they elaborate; each block states the
module that owns it. The first block is the existing repository surface this contract reuses unchanged — it
declares nothing new.

Its typed rules were checked against pinned Go 1.23 with `make go-probe` before being written down; the
alarms and their outcomes are in §Done.

## Module order

```text
Decimal Integer Float Complex FilePath ModulePath Version Collections Names Syntax Index Typing
Compilable Machine Safe Render Emit
```

## The published surface

```coq
(* ── (a) existing repository public names, faithfully stubbed ──────────────── *)
Parameter SyntaxProgram SyntaxFile ModuleSpec FilePathT : Type.
Parameter Identifier : Type.
Parameter spelling : Identifier -> string.
Parameter IntegerKind FloatKind ComplexKind : Type.
Parameter IntegerRepresentable : IntegerKind -> Z -> Prop.
Parameter FloatValue : FloatKind -> Type.
Parameter ComplexValue : ComplexKind -> Type.
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

Record NonEmpty (A : Type) : Type := MakeNonEmpty { ne_first : A; ne_rest : list A }.
Record NonNegativeDecimal : Type := MakeNonNegDecimal {
  nnd_decimal : Decimal;
  nnd_nonneg  : (0 <= coefficient nnd_decimal)%Z }.

(* ── Syntax ────────────────────────────────────────────────────────────────── *)
Inductive BindingName : Type := Named (n : OrdinaryIdentifier) | Blank.
Inductive UnaryOp : Type := UnaryMinus.

Inductive Literal : Type :=
| IntegerLiteral : nat -> Literal
| FloatLiteral   : NonNegativeDecimal -> Literal
| StringLiteral  : string -> Literal.

Inductive TypeExpr : Type := NamedType (n : OrdinaryIdentifier).

Inductive Expr : Type :=
| Name        : OrdinaryIdentifier -> Expr
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

Parameter program_files : SyntaxProgram -> list (FilePathT * SyntaxFile).
Parameter program_module : SyntaxProgram -> ModuleSpec.

(* ── Index ─────────────────────────────────────────────────────────────────── *)
Inductive Role : Type :=
| RFilePackage | RFileTopLevel | RMainBlock | RBlockStatement | RStatementDeclaration
| RDeclarationSpec | RBindingNameOccurrence | RConstSpecType | RConstInitializerExpression
| RVarSpecType | RVarInitializerExpression | RTypeSpecTarget | RTypeNameUse
| RShortRightExpression | RStatementExpression | RUnaryOperand
| RApplicationHead | RApplicationArgument.

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
Parameter ObjectSiteRef ConsumptionSiteRef StatementRef FileRef : SyntaxProgram -> Type.
Parameter AliasSpecRef BoundDefinedTypeRef : SyntaxProgram -> Type.

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

Inductive ExprUseRef (p : SyntaxProgram) : Type :=
| DirectUse    : DirectExprUseRef p -> ExprUseRef p
| InheritedUse : InheritedConstUseRef p -> ExprUseRef p.

Definition expression_of_use {p} (u : ExprUseRef p) : ExprRef p :=
  match u with DirectUse _ d => direct_child d | InheritedUse _ i => ic_expr i end.

(* ── Typing: named predeclared identities over a form algebra ──────────────── *)
Inductive BasicType : Type :=
| BoolBasic | IntegerBasic (k : IntegerKind) | FloatBasic (k : FloatKind)
| ComplexBasic (k : ComplexKind) | StringBasic.

Parameter KInt KInt8 KInt16 KInt32 KInt64 KUint KUint8 KUint16 KUint32 KUint64 : IntegerKind.
Parameter KFloat32 KFloat64 : FloatKind.
Parameter KComplex64 KComplex128 : ComplexKind.

Inductive PredeclaredBasicType : Type :=
| TBool
| TInt | TInt8 | TInt16 | TInt32 | TInt64
| TUint | TUint8 | TUint16 | TUint32 | TUint64
| TFloat32 | TFloat64 | TComplex64 | TComplex128 | TString.

Definition predeclared_basic_form (t : PredeclaredBasicType) : BasicType :=
  match t with
  | TBool => BoolBasic
  | TInt => IntegerBasic KInt | TInt8 => IntegerBasic KInt8 | TInt16 => IntegerBasic KInt16
  | TInt32 => IntegerBasic KInt32 | TInt64 => IntegerBasic KInt64
  | TUint => IntegerBasic KUint | TUint8 => IntegerBasic KUint8 | TUint16 => IntegerBasic KUint16
  | TUint32 => IntegerBasic KUint32 | TUint64 => IntegerBasic KUint64
  | TFloat32 => FloatBasic KFloat32 | TFloat64 => FloatBasic KFloat64
  | TComplex64 => ComplexBasic KComplex64 | TComplex128 => ComplexBasic KComplex128
  | TString => StringBasic
  end.

Inductive ScalarNumericBasic : BasicType -> Prop :=
| SNInteger : forall k, ScalarNumericBasic (IntegerBasic k)
| SNFloat   : forall k, ScalarNumericBasic (FloatBasic k).
Inductive ComplexBasicForm : BasicType -> Prop :=
| CBComplex : forall k, ComplexBasicForm (ComplexBasic k).

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

(* the existing one constant-conversion authority, restated over the basic form it targets *)
Parameter convert_constant_to : BasicType -> Constant -> option Constant.
Definition FitsBasic (b : BasicType) (c : Constant) : Prop :=
  exists c', convert_constant_to b c = Some c'.

Inductive BasicTypedConstant : BasicType -> Type :=
| TCBool    : bool -> BasicTypedConstant BoolBasic
| TCInteger : forall k z, IntegerRepresentable k z -> BasicTypedConstant (IntegerBasic k)
| TCFloat   : forall k, FloatValue k -> BasicTypedConstant (FloatBasic k)
| TCComplex : forall k, ComplexValue k -> BasicTypedConstant (ComplexBasic k)
| TCString  : string -> BasicTypedConstant StringBasic.

Inductive TypeView : Type :=
| PredeclaredTypeView : PredeclaredBasicType -> TypeView
| DefinedTypeView     : IndexKey -> TypeView.

Inductive RawTypeTarget (p : SyntaxProgram) : Type :=
| PredeclaredRaw : PredeclaredName -> RawTypeTarget p
| AliasRaw       : AliasSpecRef p -> RawTypeTarget p
| DefinedRaw     : BoundDefinedTypeRef p -> RawTypeTarget p.

Parameter ResolvedTypeEquations : SyntaxProgram -> Type.
Parameter TypeGraphEvidence : forall {p}, ResolvedTypeEquations p -> Type.
Parameter TypeCycle : forall {p}, ResolvedTypeEquations p -> Type.
Parameter AcyclicEquations : forall {p}, ResolvedTypeEquations p -> Prop.
Parameter acyclic_dec : forall {p} (eqs : ResolvedTypeEquations p),
  { AcyclicEquations eqs } + { ~ AcyclicEquations eqs }.

Parameter Env : forall {p} (eqs : ResolvedTypeEquations p), TypeGraphEvidence eqs -> Type.
Parameter build_env : forall {p} (eqs : ResolvedTypeEquations p) (ev : TypeGraphEvidence eqs), Env eqs ev.
Parameter DefinedInEnv : forall {p} {eqs : ResolvedTypeEquations p} {ev},
  Env eqs ev -> BoundDefinedTypeRef p -> Prop.
Parameter defined_key : forall {p}, BoundDefinedTypeRef p -> IndexKey.

Inductive TypeForm {p} {eqs : ResolvedTypeEquations p} {ev} (env : Env eqs ev) : Type :=
| BasicForm : BasicType -> TypeForm env.

Inductive SemanticType {p} {eqs : ResolvedTypeEquations p} {ev} (env : Env eqs ev) : Type :=
| PredeclaredType : PredeclaredBasicType -> SemanticType env
| DefinedType     : forall d : BoundDefinedTypeRef p, DefinedInEnv env d -> SemanticType env.

Parameter defined_underlying : forall {p} {eqs : ResolvedTypeEquations p} {ev}
  (env : Env eqs ev) (d : BoundDefinedTypeRef p), DefinedInEnv env d -> BasicType.

Definition type_view {p} {eqs : ResolvedTypeEquations p} {ev} {env : Env eqs ev}
  (s : SemanticType env) : TypeView :=
  match s with
  | PredeclaredType _ t => PredeclaredTypeView t
  | DefinedType _ d _   => DefinedTypeView (defined_key d)
  end.

Inductive Underlying {p} {eqs : ResolvedTypeEquations p} {ev} (env : Env eqs ev)
  : SemanticType env -> TypeForm env -> Prop :=
| UnderlyingPredeclared : forall t,
    Underlying env (PredeclaredType env t) (BasicForm env (predeclared_basic_form t))
| UnderlyingDefined : forall d h,
    Underlying env (DefinedType env d h) (BasicForm env (defined_underlying env d h)).

Inductive Identical {p} {eqs : ResolvedTypeEquations p} {ev} (env : Env eqs ev)
  : SemanticType env -> SemanticType env -> Prop :=
| IdenticalPredeclared : forall t, Identical env (PredeclaredType env t) (PredeclaredType env t)
| IdenticalDefined : forall d h1 h2, Identical env (DefinedType env d h1) (DefinedType env d h2).

Inductive Assignable {p} {eqs : ResolvedTypeEquations p} {ev} (env : Env eqs ev)
  : SemanticType env -> SemanticType env -> Prop :=
| AssignIdentical : forall s t, Identical env s t -> Assignable env s t.

Inductive ValueConvertible {p} {eqs : ResolvedTypeEquations p} {ev} (env : Env eqs ev)
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

Inductive Representable {p} {eqs : ResolvedTypeEquations p} {ev} (env : Env eqs ev)
  : SemanticType env -> Constant -> Prop :=
| RepresentableAt : forall s b c,
    Underlying env s (BasicForm env b) -> FitsBasic b c -> Representable env s c.

Inductive ConstantConvertible {p} {eqs : ResolvedTypeEquations p} {ev} (env : Env eqs ev)
  : Constant -> option (SemanticType env) -> SemanticType env -> Prop :=
| CConvExact : forall c src tgt, Representable env tgt c -> ConstantConvertible env c src tgt.

Inductive TypedConstant {p} {eqs : ResolvedTypeEquations p} {ev} (env : Env eqs ev)
  (s : SemanticType env) : Type :=
| TypedOf : forall b, Underlying env s (BasicForm env b) -> BasicTypedConstant b -> TypedConstant env s.

Parameter underlyingb : forall {p} {eqs : ResolvedTypeEquations p} {ev} (env : Env eqs ev),
  SemanticType env -> TypeForm env.
Parameter identicalb assignableb value_convertibleb :
  forall {p} {eqs : ResolvedTypeEquations p} {ev} (env : Env eqs ev),
  SemanticType env -> SemanticType env -> bool.
Parameter representableb : forall {p} {eqs : ResolvedTypeEquations p} {ev} (env : Env eqs ev),
  SemanticType env -> Constant -> bool.
Parameter default_type : forall {p} {eqs : ResolvedTypeEquations p} {ev} (env : Env eqs ev),
  Constant -> SemanticType env.

Parameter AliasResolvesTo : forall {p} {eqs : ResolvedTypeEquations p} {ev},
  Env eqs ev -> AliasSpecRef p -> RawTypeTarget p -> Prop.
Parameter AdmittedPredeclaredType AliasPredeclared : PredeclaredName -> PredeclaredBasicType -> Prop.

Inductive ResolvedTypeTarget {p} {eqs : ResolvedTypeEquations p} {ev} (env : Env eqs ev)
  : RawTypeTarget p -> SemanticType env -> Prop :=
| ResolvedPredeclaredType : forall n t, AdmittedPredeclaredType n t ->
    ResolvedTypeTarget env (PredeclaredRaw p n) (PredeclaredType env t)
| ResolvedPredeclaredAlias : forall n t, AliasPredeclared n t ->
    ResolvedTypeTarget env (PredeclaredRaw p n) (PredeclaredType env t)
| ResolvedSourceAlias : forall a rt s, AliasResolvesTo env a rt ->
    ResolvedTypeTarget env rt s -> ResolvedTypeTarget env (AliasRaw p a) s
| ResolvedDefinedType : forall d (h : DefinedInEnv env d),
    ResolvedTypeTarget env (DefinedRaw p d) (DefinedType env d h).

(* ── The retained static phase ─────────────────────────────────────────────── *)
Inductive TypePhaseResult {p} (eqs : ResolvedTypeEquations p) : Type :=
| TypeReady  : forall g : TypeGraphEvidence eqs, Env eqs g -> TypePhaseResult eqs
| TypeCyclic : TypeCycle eqs -> TypePhaseResult eqs.

Definition IsTypeReady {p} {eqs : ResolvedTypeEquations p} (r : TypePhaseResult eqs) : Prop :=
  match r with TypeReady _ _ _ => True | TypeCyclic _ _ => False end.

Definition ready_graph {p} {eqs : ResolvedTypeEquations p} (r : TypePhaseResult eqs)
  : IsTypeReady r -> TypeGraphEvidence eqs :=
  match r return IsTypeReady r -> TypeGraphEvidence eqs with
  | TypeReady _ g _ => fun _ => g
  | TypeCyclic _ _  => fun h => match h return TypeGraphEvidence eqs with end
  end.

Definition ready_env {p} {eqs : ResolvedTypeEquations p} (r : TypePhaseResult eqs)
  : forall h : IsTypeReady r, Env eqs (ready_graph r h) :=
  match r return forall h : IsTypeReady r, Env eqs (ready_graph r h) with
  | TypeReady _ g e => fun _ => e
  | TypeCyclic _ _  => fun h => match h return Env eqs (ready_graph (TypeCyclic eqs _) h) with end
  end.

Parameter Phase : forall {p}, Input p -> Type.
Parameter phase : forall {p} (core : Core p), Phase (core_input core).
Parameter phase_equations : forall {p} {i : Input p} (ph : Phase i), ResolvedTypeEquations p.
Parameter phase_type_result : forall {p} {i : Input p} (ph : Phase i),
  TypePhaseResult (phase_equations ph).

Inductive ObjectKind : Type :=
| TypeObject | ConstantObject | VariableObject | FunctionObject | BuiltinObject | NilObject.

Inductive ObjectOrigin (p : SyntaxProgram) : Type :=
| Predeclared  : PredeclaredName -> ObjectOrigin p
| SourceObject : ObjectSiteRef p -> ObjectOrigin p.

Inductive ObjectKey : Type :=
| PredeclaredObjectKey : PredeclaredName -> ObjectKey
| SourceObjectKey      : IndexKey -> ObjectKey.

Definition origin_key {p} (o : ObjectOrigin p) : ObjectKey :=
  match o with
  | Predeclared _ n  => PredeclaredObjectKey n
  | SourceObject _ s => SourceObjectKey (object_site_key s)
  end.

Parameter ObjectRef : forall {p} {i : Input p}, Phase i -> Type.
Parameter object_origin : forall {p} {i : Input p} {ph : Phase i}, ObjectRef ph -> ObjectOrigin p.
Parameter object_kind : forall {p} {i : Input p} {ph : Phase i}, ObjectRef ph -> ObjectKind.
Definition object_key {p} {i : Input p} {ph : Phase i} (o : ObjectRef ph) : ObjectKey :=
  origin_key (object_origin o).
Parameter object_eqb : forall {p} {i : Input p} {ph : Phase i}, ObjectRef ph -> ObjectRef ph -> bool.
Parameter predeclared_object : forall {p} {i : Input p} (ph : Phase i), PredeclaredName -> ObjectRef ph.
Parameter source_object : forall {p} {i : Input p} (ph : Phase i), ObjectSiteRef p -> ObjectRef ph.

Definition predeclared_kind (n : PredeclaredName) : ObjectKind :=
  match n with
  | PAny | PBool | PByte | PComparable | PComplex64 | PComplex128 | PError | PFloat32 | PFloat64
  | PInt | PInt8 | PInt16 | PInt32 | PInt64 | PRune | PString | PUint | PUint8 | PUint16
  | PUint32 | PUint64 | PUintptr => TypeObject
  | PTrue | PFalse | PIota => ConstantObject
  | PNil => NilObject
  | _ => BuiltinObject
  end.

(* ── Erased views ──────────────────────────────────────────────────────────── *)
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
| ETCallable      : ObjectKey -> ErasedTarget
| ETNotApplicable : ObjectKind -> ErasedTarget.

Inductive RequirementView : Type :=
| RVTypeMeaning  : IndexKey -> ObjectKey -> RequirementView
| RVValueMeaning : IndexKey -> ObjectKey -> RequirementView
| RVApplication  : IndexKey -> ErasedTarget -> ErasedProfile -> RequirementView
| RVStatement    : IndexKey -> ErasedResultForm -> RequirementView
| RVUnary        : IndexKey -> UnaryOp -> ErasedResultForm -> RequirementView.

Parameter requirement_view_eqb : RequirementView -> RequirementView -> bool.
Parameter requirement_view_compare : RequirementView -> RequirementView -> comparison.
Definition view_lt (a b : RequirementView) : Prop := requirement_view_compare a b = Lt.

(* ── Package identity and the dependency object ────────────────────────────── *)
Parameter PackageRef : SyntaxProgram -> Type.

Inductive InitUnit (p : SyntaxProgram) : Type :=
| ConstUnit : ConstSpecRef p -> InitUnit p
| VarUnit   : BindingSiteRef p -> InitUnit p
| BlankUnit : BlankRef p -> InitUnit p.

Parameter DependencyGraph : forall {p} {i : Input p}, Phase i -> PackageRef p -> Type.
Parameter DependencyCycle : forall {p} {i : Input p} {ph : Phase i} {k}, DependencyGraph ph k -> Type.
Parameter AcyclicOrder : forall {p} {i : Input p} {ph : Phase i} {k}
  (g : DependencyGraph ph k), list (InitUnit p) -> Prop.
Parameter EdgesFromBindings : forall {p} {i : Input p} {ph : Phase i} {k},
  DependencyGraph ph k -> Prop.

Inductive DependencyOutcome {p} {i : Input p} {ph : Phase i} {k} (g : DependencyGraph ph k) : Type :=
| DependencyAcyclic : forall order : list (InitUnit p), AcyclicOrder g order -> DependencyOutcome g
| DependencyCyclic  : DependencyCycle g -> DependencyOutcome g.

Parameter phase_dependency_graph : forall {p} {i : Input p} (ph : Phase i) (k : PackageRef p),
  DependencyGraph ph k.
Parameter phase_dependency_outcome : forall {p} {i : Input p} (ph : Phase i) (k : PackageRef p),
  DependencyOutcome (phase_dependency_graph ph k).

(* ── Phase fact families and requirements ──────────────────────────────────── *)
Parameter PhaseBindingFact : forall {p} {i : Input p} (ph : Phase i), NameUseRef p -> Type.
Parameter bound_object : forall {p} {i : Input p} {ph : Phase i} {u},
  PhaseBindingFact ph u -> ObjectRef ph.
Parameter binding_use_role : forall {p} {i : Input p} {ph : Phase i} {u},
  PhaseBindingFact ph u -> UseRole.
Parameter binding_package : forall {p} {i : Input p} {ph : Phase i} {u},
  PhaseBindingFact ph u -> PackageRef p.
Parameter PhaseExpressionFact : forall {p} {i : Input p} (ph : Phase i), ExprRef p -> Type.
Parameter PhaseUseFact : forall {p} {i : Input p} (ph : Phase i), ExprUseRef p -> Type.
Parameter PhaseApplicationSite : forall {p} {i : Input p} (ph : Phase i), ApplicationRef p -> Type.
Parameter PhaseStatementSite : forall {p} {i : Input p} (ph : Phase i),
  ExpressionStatementRef p -> Type.
Parameter PhaseUnarySite : forall {p} {i : Input p} (ph : Phase i), UnaryRef p -> Type.
Parameter PhaseConsumption : forall {p} {i : Input p} (ph : Phase i), ConsumptionSiteRef p -> Type.
Parameter PhaseStaticVariable : forall {p} {i : Input p} (ph : Phase i), ObjectRef ph -> Type.

Inductive SemanticRequirement {p} {i : Input p} (ph : Phase i) : Type :=
| TypeMeaningReq  : forall u, PhaseBindingFact ph u -> SemanticRequirement ph
| ValueMeaningReq : forall u, PhaseBindingFact ph u -> SemanticRequirement ph
| ApplicationReq  : forall a, PhaseApplicationSite ph a -> SemanticRequirement ph
| StatementReq    : forall s, PhaseStatementSite ph s -> SemanticRequirement ph
| UnaryReq        : forall n, PhaseUnarySite ph n -> SemanticRequirement ph.

Parameter requirement_view : forall {p} {i : Input p} {ph : Phase i},
  SemanticRequirement ph -> RequirementView.
Parameter TypeMeaningHolds ValueMeaningHolds :
  forall {p} {i : Input p} {ph : Phase i} {u}, PhaseBindingFact ph u -> Prop.
Parameter ApplicationHolds : forall {p} {i : Input p} {ph : Phase i} {a},
  PhaseApplicationSite ph a -> Prop.
Parameter StatementHolds : forall {p} {i : Input p} {ph : Phase i} {s},
  PhaseStatementSite ph s -> Prop.
Parameter UnaryHolds : forall {p} {i : Input p} {ph : Phase i} {n},
  PhaseUnarySite ph n -> Prop.

Definition RequirementSatisfied {p} {i : Input p} {ph : Phase i}
  (r : SemanticRequirement ph) : Prop :=
  match r with
  | TypeMeaningReq _ _ b  => TypeMeaningHolds b
  | ValueMeaningReq _ _ b => ValueMeaningHolds b
  | ApplicationReq _ _ st => ApplicationHolds st
  | StatementReq _ _ st   => StatementHolds st
  | UnaryReq _ _ st       => UnaryHolds st
  end.

Parameter requirement_dec : forall {p} {i : Input p} {ph : Phase i} (r : SemanticRequirement ph),
  { RequirementSatisfied r } + { ~ RequirementSatisfied r }.
Parameter ScopeBoundary : forall {p} {i : Input p} (ph : Phase i), SemanticRequirement ph -> Type.
Parameter boundary_missing : forall {p} {i : Input p} {ph : Phase i} {r : SemanticRequirement ph},
  ScopeBoundary ph r -> ~ RequirementSatisfied r.
Parameter PackedBoundary : forall {p} {i : Input p}, Phase i -> Type.
Parameter boundary_requirement : forall {p} {i : Input p} {ph : Phase i},
  PackedBoundary ph -> SemanticRequirement ph.
Parameter boundary_evidence : forall {p} {i : Input p} {ph : Phase i} (b : PackedBoundary ph),
  ScopeBoundary ph (boundary_requirement b).
Definition boundary_view {p} {i : Input p} {ph : Phase i} (b : PackedBoundary ph)
  : RequirementView := requirement_view (boundary_requirement b).

(* ── Diagnostics ───────────────────────────────────────────────────────────── *)
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

Inductive AssignmentTargetAnchor (p : SyntaxProgram) : Type :=
| ExplicitTypeTarget : TypeUseRef p -> AssignmentTargetAnchor p
| InferredTarget     : BindingSiteRef p -> AssignmentTargetAnchor p.

Inductive ArgumentReason : Type :=
| ArgWrongCount       : nat -> nat -> ArgumentReason
| ArgNotAssignable    : TypeView -> TypeView -> ArgumentReason
| ArgNotRepresentable : TypeView -> ArgumentReason
| ArgProfileRejected  : ErasedResultForm -> ArgumentReason.

Inductive OperandReason : Type :=
| OperandNotNumeric : TypeView -> OperandReason
| OperandNoResult   : OperandReason.

Inductive IneligibleReason : Type :=
| NotAnApplication     : IneligibleReason
| NotCallableStatement : ErasedTarget -> IneligibleReason.

Inductive DiagnosticCode : Type :=
| CodeInvalidConversion | CodeDefaultNotRepresentable | CodeMainRedeclared | CodeMissingMainEntry
| CodeBuildOutputIsDirectory | CodeDuplicateBinding | CodeInitMisuse | CodeUnresolvedName
| CodeWrongRole | CodeNotApplicable | CodeTypeCycle | CodeDependencyCycle
| CodeFirstSpecInherited | CodeResultMismatch | CodeShortDeclNoNew | CodeShortRedeclType
| CodeNilNoTarget | CodeIotaNoContext | CodeNotAssignable | CodeUnusedLocal
| CodeBadArgument | CodeBadOperand | CodeNotStatement.

Inductive DiagnosticReason {p} {i : Input p} (ph : Phase i) : Type :=
| InvalidConversion : ApplicationRef p -> ExprRef p -> ExprRef p -> list (ApplicationRef p) ->
    TypeView -> OperandResultView -> DiagnosticReason ph
| DefaultNotRepresentable : ExprRef p -> Constant -> TypeView -> DiagnosticReason ph
| MainRedeclared : ObjectSiteRef p -> ObjectSiteRef p -> DiagnosticReason ph
| MissingMainEntry : PackageRef p -> DiagnosticReason ph
| BuildOutputIsDirectory : PackageRef p -> string -> DiagnosticReason ph
| DuplicateBinding : BindingSiteRef p -> BindingSiteRef p -> DiagnosticReason ph
| InitMisuse : BindingSiteRef p -> DiagnosticReason ph
| UnresolvedName : NameUseRef p -> string -> DiagnosticReason ph
| WrongRole : NameUseRef p -> UseRole -> ObjectKind -> DiagnosticReason ph
| NotApplicable : ApplicationRef p -> HeadView -> DiagnosticReason ph
| TypeCycleDiag : TypeCycle (phase_equations ph) -> DiagnosticReason ph
| DependencyCycleDiag : forall k, DependencyCycle (phase_dependency_graph ph k) -> DiagnosticReason ph
| FirstSpecInherited : ConstSpecRef p -> DiagnosticReason ph
| ResultMismatch : ConsumptionSiteRef p -> nat -> ErasedProfile -> DiagnosticReason ph
| ShortDeclNoNew : StatementRef p -> DiagnosticReason ph
| ShortRedeclType : BindingSiteRef p -> TypeView -> TypeView -> DiagnosticReason ph
| NilNoTarget : ExprRef p -> DiagnosticReason ph
| IotaNoContext : ExprRef p -> DiagnosticReason ph
| NotAssignable : ExprUseRef p -> AssignmentTargetAnchor p -> TypeView -> TypeView ->
    DiagnosticReason ph
| UnusedLocal : VariableSiteRef p -> DiagnosticReason ph
| BadArgument : DirectExprUseRef p -> ArgumentReason -> DiagnosticReason ph
| BadOperand : DirectExprUseRef p -> OperandReason -> DiagnosticReason ph
| NotStatement : ExpressionStatementRef p -> IneligibleReason -> DiagnosticReason ph.

Definition diagnostic_code {p} {i : Input p} {ph : Phase i} (d : DiagnosticReason ph)
  : DiagnosticCode :=
  match d with
  | InvalidConversion _ _ _ _ _ _ _ => CodeInvalidConversion
  | DefaultNotRepresentable _ _ _ _ => CodeDefaultNotRepresentable
  | MainRedeclared _ _ _            => CodeMainRedeclared
  | MissingMainEntry _ _            => CodeMissingMainEntry
  | BuildOutputIsDirectory _ _ _    => CodeBuildOutputIsDirectory
  | DuplicateBinding _ _ _          => CodeDuplicateBinding
  | InitMisuse _ _                  => CodeInitMisuse
  | UnresolvedName _ _ _            => CodeUnresolvedName
  | WrongRole _ _ _ _               => CodeWrongRole
  | NotApplicable _ _ _             => CodeNotApplicable
  | TypeCycleDiag _ _               => CodeTypeCycle
  | DependencyCycleDiag _ _ _       => CodeDependencyCycle
  | FirstSpecInherited _ _          => CodeFirstSpecInherited
  | ResultMismatch _ _ _ _          => CodeResultMismatch
  | ShortDeclNoNew _ _              => CodeShortDeclNoNew
  | ShortRedeclType _ _ _ _         => CodeShortRedeclType
  | NilNoTarget _ _                 => CodeNilNoTarget
  | IotaNoContext _ _               => CodeIotaNoContext
  | NotAssignable _ _ _ _ _         => CodeNotAssignable
  | UnusedLocal _ _                 => CodeUnusedLocal
  | BadArgument _ _ _               => CodeBadArgument
  | BadOperand _ _ _                => CodeBadOperand
  | NotStatement _ _ _              => CodeNotStatement
  end.

Parameter diagnostic_primary : forall {p} {i : Input p} {ph : Phase i},
  DiagnosticReason ph -> DiagnosticAnchor p.
Parameter diagnostic_related : forall {p} {i : Input p} {ph : Phase i},
  DiagnosticReason ph -> list (DiagnosticAnchor p).

(* ── Private site outcomes: no total fact over a blocked site ──────────────── *)
Inductive SiteOutcome {p} {i : Input p} (ph : Phase i) (F : Type) : Type :=
| Supported       : F -> SiteOutcome ph F
| DefiniteFailure : DiagnosticReason ph -> SiteOutcome ph F
| OutsideSite     : PackedBoundary ph -> SiteOutcome ph F
| Blocked         : NodeRef p -> SiteOutcome ph F.

Definition IsSupported {p} {i : Input p} {ph : Phase i} {F} (o : SiteOutcome ph F) : Prop :=
  match o with Supported _ _ _ => True | _ => False end.

Definition supported_fact {p} {i : Input p} {ph : Phase i} {F} (o : SiteOutcome ph F)
  : IsSupported o -> F :=
  match o return IsSupported o -> F with
  | Supported _ _ f       => fun _ => f
  | DefiniteFailure _ _ _ => fun h => match h return F with end
  | OutsideSite _ _ _     => fun h => match h return F with end
  | Blocked _ _ _         => fun h => match h return F with end
  end.

Parameter phase_binding_outcome : forall {p} {i : Input p} (ph : Phase i) (u : NameUseRef p),
  SiteOutcome ph (PhaseBindingFact ph u).
Parameter phase_expression_outcome : forall {p} {i : Input p} (ph : Phase i) (r : ExprRef p),
  SiteOutcome ph (PhaseExpressionFact ph r).
Parameter phase_use_outcome : forall {p} {i : Input p} (ph : Phase i) (u : ExprUseRef p),
  SiteOutcome ph (PhaseUseFact ph u).
Parameter phase_consumption_outcome : forall {p} {i : Input p} (ph : Phase i)
  (s : ConsumptionSiteRef p), SiteOutcome ph (PhaseConsumption ph s).
Parameter phase_variable_outcome : forall {p} {i : Input p} (ph : Phase i) (s : VariableSiteRef p),
  SiteOutcome ph { o : ObjectRef ph & PhaseStaticVariable ph o }.

Parameter core_diagnostics : forall {p} (core : Core p), list (DiagnosticReason (phase core)).
Parameter core_boundaries : forall {p} (core : Core p), list (PackedBoundary (phase core)).
Parameter RootRequirement : forall {p} {i : Input p} (ph : Phase i),
  SemanticRequirement ph -> Prop.

(* ── Outcome ───────────────────────────────────────────────────────────────── *)
Inductive Decision {p} (core : Core p) : Type :=
| AcceptedDecision : core_diagnostics core = [] -> core_boundaries core = [] -> Decision core
| RejectedDecision : core_diagnostics core <> [] -> Decision core
| OutsideDecision  : core_diagnostics core = [] -> core_boundaries core <> [] -> Decision core.

Parameter decision : forall {p} (a : Elaboration p), Decision (elaboration_core a).

Parameter Program : Type.
Parameter source : Program -> SyntaxProgram.
Parameter core : forall cp : Program, Core (source cp).
Parameter accepted : forall cp : Program, core_diagnostics (core cp) = [].
Parameter in_scope : forall cp : Program, core_boundaries (core cp) = [].

Parameter Failure : SyntaxProgram -> Type.
Parameter failure_core : forall {p}, Failure p -> Core p.
Parameter rejected : forall {p} (f : Failure p), core_diagnostics (failure_core f) <> [].
Parameter Outside : SyntaxProgram -> Type.
Parameter outside_core : forall {p}, Outside p -> Core p.
Parameter outside_clean : forall {p} (o : Outside p), core_diagnostics (outside_core o) = [].
Parameter outside_blocked : forall {p} (o : Outside p), core_boundaries (outside_core o) <> [].

Inductive Outcome (p : SyntaxProgram) : Type :=
| Compiled     : forall cp : Program, source cp = p -> Outcome p
| Rejected     : Failure p -> Outcome p
| OutsideScope : Outside p -> Outcome p.

Parameter compile : forall p : SyntaxProgram, Outcome p.
Definition InScope (p : SyntaxProgram) : Prop :=
  core_boundaries (elaboration_core (elaborate p)) = [].

(* ── Accepted facts by dependent elimination of the retained phase ─────────── *)
Definition accepted_phase (cp : Program) : Phase (core_input (core cp)) := phase (core cp).
Definition accepted_equations (cp : Program) : ResolvedTypeEquations (source cp) :=
  phase_equations (accepted_phase cp).

Parameter accepted_ready : forall cp : Program, IsTypeReady (phase_type_result (accepted_phase cp)).
Definition accepted_graph (cp : Program) : TypeGraphEvidence (accepted_equations cp) :=
  ready_graph (phase_type_result (accepted_phase cp)) (accepted_ready cp).
Definition accepted_environment (cp : Program) : Env (accepted_equations cp) (accepted_graph cp) :=
  ready_env (phase_type_result (accepted_phase cp)) (accepted_ready cp).

Definition Object (cp : Program) : Type := ObjectRef (accepted_phase cp).
Definition AcceptedType (cp : Program) : Type := SemanticType (accepted_environment cp).
Definition AcceptedTypedConstant (cp : Program) (t : AcceptedType cp) : Type :=
  TypedConstant (accepted_environment cp) t.
Definition AcceptedIdentical (cp : Program) (s t : AcceptedType cp) : Prop :=
  Identical (accepted_environment cp) s t.
Definition AcceptedAssignable (cp : Program) (s t : AcceptedType cp) : Prop :=
  Assignable (accepted_environment cp) s t.
Definition accepted_type_view (cp : Program) (t : AcceptedType cp) : TypeView := type_view t.
Definition object_kind_of {cp : Program} (o : Object cp) : ObjectKind := object_kind o.
Definition object_origin_of {cp : Program} (o : Object cp) : ObjectOrigin (source cp) :=
  object_origin o.
Definition object_key_of {cp : Program} (o : Object cp) : ObjectKey := object_key o.

Parameter accepted_binding_supported : forall (cp : Program) u,
  IsSupported (phase_binding_outcome (accepted_phase cp) u).
Parameter accepted_expression_supported : forall (cp : Program) r,
  IsSupported (phase_expression_outcome (accepted_phase cp) r).
Parameter accepted_use_supported : forall (cp : Program) u,
  IsSupported (phase_use_outcome (accepted_phase cp) u).
Parameter accepted_consumption_supported : forall (cp : Program) s,
  IsSupported (phase_consumption_outcome (accepted_phase cp) s).
Parameter accepted_variable_supported : forall (cp : Program) s,
  IsSupported (phase_variable_outcome (accepted_phase cp) s).

Definition BindingFact (cp : Program) (u : NameUseRef (source cp)) : Type :=
  PhaseBindingFact (accepted_phase cp) u.
Definition binding_fact (cp : Program) (u : NameUseRef (source cp)) : BindingFact cp u :=
  supported_fact _ (accepted_binding_supported cp u).
Definition ExpressionFact (cp : Program) (r : ExprRef (source cp)) : Type :=
  PhaseExpressionFact (accepted_phase cp) r.
Definition expression_fact (cp : Program) (r : ExprRef (source cp)) : ExpressionFact cp r :=
  supported_fact _ (accepted_expression_supported cp r).
Definition UseFact (cp : Program) (u : ExprUseRef (source cp)) : Type :=
  PhaseUseFact (accepted_phase cp) u.
Definition use_fact (cp : Program) (u : ExprUseRef (source cp)) : UseFact cp u :=
  supported_fact _ (accepted_use_supported cp u).
Definition Consumption (cp : Program) (s : ConsumptionSiteRef (source cp)) : Type :=
  PhaseConsumption (accepted_phase cp) s.
Definition consumption (cp : Program) (s : ConsumptionSiteRef (source cp)) : Consumption cp s :=
  supported_fact _ (accepted_consumption_supported cp s).
Definition StaticVariable (cp : Program) (o : Object cp) : Type :=
  PhaseStaticVariable (accepted_phase cp) o.
Definition static_variable_at (cp : Program) (s : VariableSiteRef (source cp))
  : { o : Object cp & StaticVariable cp o } :=
  supported_fact _ (accepted_variable_supported cp s).

Definition bound_object_at (cp : Program) (u : NameUseRef (source cp)) : Object cp :=
  bound_object (binding_fact cp u).
Definition use_role_at (cp : Program) (u : NameUseRef (source cp)) : UseRole :=
  binding_use_role (binding_fact cp u).

(* ── Object capabilities, each indexed by the exact object ─────────────────── *)
Parameter TypeMeaning ConstantMeaning ValueMeaning IotaMeaning NilMeaning :
  forall (cp : Program), Object cp -> Type.
Parameter type_meaning_type : forall {cp} {o}, TypeMeaning cp o -> AcceptedType cp.
Parameter value_meaning_type : forall {cp} {o}, ValueMeaning cp o -> AcceptedType cp.
Parameter constant_meaning_untyped : forall {cp} {o}, ConstantMeaning cp o -> option Constant.
Parameter constant_meaning_typed : forall {cp} {o}, ConstantMeaning cp o ->
  option { t : AcceptedType cp & AcceptedTypedConstant cp t }.
Parameter static_variable_type : forall {cp} {o}, StaticVariable cp o -> AcceptedType cp.

Inductive BinderDisposition (cp : Program) : Type :=
| DispBlank    : BinderDisposition cp
| DispDeclares : Object cp -> BinderDisposition cp
| DispReuses   : forall o : Object cp, StaticVariable cp o -> BinderDisposition cp.
Parameter binder_disposition : forall (cp : Program) (s : BindingSiteRef (source cp)),
  BinderDisposition cp.

Inductive ResultAtom (cp : Program) : Type :=
| UntypedConstant   : Constant -> ResultAtom cp
| TypedConstantAtom : forall t : AcceptedType cp, AcceptedTypedConstant cp t -> ResultAtom cp
| ValueResult       : AcceptedType cp -> ResultAtom cp.

Inductive ResultForm (cp : Program) : Type :=
| FixedResults       : list (ResultAtom cp) -> ResultForm cp
| ContextualForm     : ContextualResult -> ResultForm cp
| NoStandaloneResult : ResultForm cp.

Definition erase_atom {cp : Program} (a : ResultAtom cp) : ErasedAtom :=
  match a with
  | UntypedConstant _ c     => EAUntyped (constant_kind c)
  | TypedConstantAtom _ t _ => EATyped (accepted_type_view cp t)
  | ValueResult _ t         => EAValue (accepted_type_view cp t)
  end.
Definition erase_result_form {cp : Program} (rf : ResultForm cp) : ErasedResultForm :=
  match rf with
  | FixedResults _ atoms => ERFixed (map erase_atom atoms)
  | ContextualForm _ c   => ERContextual c
  | NoStandaloneResult _ => ERNoStandalone
  end.

Parameter referenced_object : forall {cp} {r}, ExpressionFact cp r -> option (Object cp).
Parameter result_form : forall {cp} {r}, ExpressionFact cp r -> ResultForm cp.
Parameter use_expression_fact : forall {cp} {u} (f : UseFact cp u),
  ExpressionFact cp (expression_of_use u).
Parameter use_target_type : forall {cp} {u}, UseFact cp u -> option (AcceptedType cp).
Parameter use_selected : forall {cp} {u}, UseFact cp u -> ResultAtom cp.

(* ── Application: canonical child facts, closed judgment ───────────────────── *)
Parameter HeadCallable : forall {cp} {r}, ExpressionFact cp r -> Type.
Parameter HeadDenotesType : forall {cp} {r}, ExpressionFact cp r -> AcceptedType cp -> Prop.
Parameter CallableIs : forall {cp} {r} {f : ExpressionFact cp r},
  HeadCallable f -> PredeclaredName -> Prop.

Inductive AppTarget {cp} {r} (f : ExpressionFact cp r) : Type :=
| ConversionTarget : forall t : AcceptedType cp, HeadDenotesType f t -> AppTarget f
| CallableTarget   : HeadCallable f -> AppTarget f.

Definition app_head_fact (cp : Program) (a : ApplicationRef (source cp))
  : ExpressionFact cp (application_head a) := expression_fact cp (application_head a).
Definition app_parent_fact (cp : Program) (a : ApplicationRef (source cp))
  : ExpressionFact cp (application_expr a) := expression_fact cp (application_expr a).
Definition app_argument_uses (cp : Program) (a : ApplicationRef (source cp))
  : list (ExprUseRef (source cp)) :=
  map (fun d => DirectUse (source cp) d) (application_argument_uses a).
Definition app_argument_atoms (cp : Program) (a : ApplicationRef (source cp))
  : list (ResultAtom cp) := map (fun u => use_selected (use_fact cp u)) (app_argument_uses cp a).
Definition app_profile (cp : Program) (a : ApplicationRef (source cp)) : ErasedProfile :=
  map (fun u => erase_result_form (result_form (use_expression_fact (use_fact cp u))))
      (app_argument_uses cp a).

Parameter app_target : forall (cp : Program) (a : ApplicationRef (source cp)),
  AppTarget (app_head_fact cp a).

Inductive ComplexArgumentsOk (cp : Program) (a : ApplicationRef (source cp)) : Prop :=
| ComplexUntypedPair : forall c1 c2,
    app_argument_atoms cp a = [UntypedConstant cp c1; UntypedConstant cp c2] ->
    ComplexArgumentsOk cp a
| ComplexTypedPair : forall t1 k1 t2 k2,
    app_argument_atoms cp a = [TypedConstantAtom cp t1 k1; TypedConstantAtom cp t2 k2] ->
    AcceptedIdentical cp t1 t2 -> ComplexArgumentsOk cp a
| ComplexValuePair : forall s1 s2,
    app_argument_atoms cp a = [ValueResult cp s1; ValueResult cp s2] ->
    AcceptedIdentical cp s1 s2 -> ComplexArgumentsOk cp a.

Parameter PrintlnArgumentOk : forall (cp : Program), ResultAtom cp -> Prop.
Definition PrintlnArgumentsOk (cp : Program) (a : ApplicationRef (source cp)) : Prop :=
  Forall (PrintlnArgumentOk cp) (app_argument_atoms cp a).

Inductive ApplicationAccepts (cp : Program) (a : ApplicationRef (source cp))
  : list (ResultAtom cp) -> Prop :=
| AcceptConversionConstant : forall t Ht c res,
    app_target cp a = ConversionTarget (app_head_fact cp a) t Ht ->
    app_argument_atoms cp a = [UntypedConstant cp c] ->
    ConstantConvertible (accepted_environment cp) c None t ->
    ApplicationAccepts cp a [res]
| AcceptConversionValue : forall t Ht s,
    app_target cp a = ConversionTarget (app_head_fact cp a) t Ht ->
    app_argument_atoms cp a = [ValueResult cp s] ->
    ValueConvertible (accepted_environment cp) s t ->
    ApplicationAccepts cp a [ValueResult cp t]
| AcceptComplex : forall c res,
    app_target cp a = CallableTarget (app_head_fact cp a) c ->
    CallableIs c PComplex -> ComplexArgumentsOk cp a ->
    ApplicationAccepts cp a [res]
| AcceptPrintln : forall c,
    app_target cp a = CallableTarget (app_head_fact cp a) c ->
    CallableIs c PPrintln -> PrintlnArgumentsOk cp a ->
    ApplicationAccepts cp a [].

(* ── Statement eligibility: its own closed rule ────────────────────────────── *)
Parameter StatementApplication : forall (cp : Program),
  ExpressionStatementRef (source cp) -> ApplicationRef (source cp) -> Prop.

Inductive StatementEligible (cp : Program) (s : ExpressionStatementRef (source cp)) : Prop :=
| EligiblePrintln : forall a c,
    StatementApplication cp s a ->
    app_target cp a = CallableTarget (app_head_fact cp a) c ->
    CallableIs c PPrintln -> StatementEligible cp s.

Parameter statement_eligible_dec : forall cp s,
  { StatementEligible cp s } + { ~ StatementEligible cp s }.

(* ── One result-consumption authority ──────────────────────────────────────── *)
Inductive ConsumptionTarget (p : SyntaxProgram) : Type :=
| NamedTarget : BindingSiteRef p -> ConsumptionTarget p
| BlankTarget : BlankRef p -> ConsumptionTarget p.

Record ConsumptionEntry (cp : Program) : Type := MakeConsumptionEntry {
  ce_target      : ConsumptionTarget (source cp);
  ce_use         : ExprUseRef (source cp);
  ce_fact        : UseFact cp ce_use;
  ce_atom        : ResultAtom cp;
  ce_selected    : use_selected ce_fact = ce_atom;
  ce_target_type : option (AcceptedType cp);
  ce_binder      : option (BinderDisposition cp) }.

Parameter consumption_entries : forall {cp} {s}, Consumption cp s -> list (ConsumptionEntry cp).
Parameter consumption_sources : forall {cp} {s}, Consumption cp s -> list (ExprUseRef (source cp)).
Parameter SiteTargets : forall (cp : Program), ConsumptionSiteRef (source cp) ->
  list (ConsumptionTarget (source cp)) -> Prop.

(* ── Render ────────────────────────────────────────────────────────────────── *)
Inductive Prec : Type := PrimaryPrec | UnaryPrec.
Definition prec (e : Expr) : Prec :=
  match e with Unary _ _ => UnaryPrec | _ => PrimaryPrec end.
Definition PrecLooser (child required : Prec) : Prop :=
  match child, required with UnaryPrec, PrimaryPrec => True | _, _ => False end.

Parameter render_at : Prec -> Expr -> string.
Parameter render_expr : Expr -> string.
Parameter render_file : SyntaxFile -> string.
Parameter render_program : SyntaxProgram -> list (FilePathT * string).
Parameter render_gomod : ModuleSpec -> string.

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

(* ── Remaining relations named by the theorems ─────────────────────────────── *)
Parameter InnermostDeclaring : forall (cp : Program),
  NameUseRef (source cp) -> BindingSiteRef (source cp) -> Prop.
Parameter ShortDeclSite : forall (cp : Program), ConsumptionSiteRef (source cp) -> Prop.
Parameter short_left_sites : forall (cp : Program), ConsumptionSiteRef (source cp) ->
  list (BindingSiteRef (source cp)).
Parameter SameBlockEarlier : forall (cp : Program), BindingSiteRef (source cp) -> Object cp -> Prop.
Parameter ReadsVariableAtPhase : forall {p} {i : Input p} (ph : Phase i), VariableSiteRef p -> Prop.
Parameter ScopesFileOrderIndependent : forall {p} {i : Input p}, Phase i -> Prop.

```

## Theorems

Every statement below elaborates over the names above; proof bodies are the implementation's work.

```coq
(* ── Theorems ──────────────────────────────────────────────────────────────── *)

Theorem all_predeclared_nodup : NoDup all_predeclared.
Theorem all_predeclared_complete : forall n, In n all_predeclared.
Theorem predeclared_spelling_injective : forall a b,
  predeclared_spelling a = predeclared_spelling b -> a = b.
Theorem classify_spelling_roundtrip : forall n, classify_spelling (predeclared_spelling n) = Some n.
Theorem classify_spelling_sound : forall s n,
  classify_spelling s = Some n -> s = predeclared_spelling n.
Theorem predeclared_eqb_spec : forall a b, predeclared_eqb a b = true <-> a = b.

Theorem byte_is_uint8 : AliasPredeclared PByte TUint8.
Theorem rune_is_int32 : AliasPredeclared PRune TInt32.
Theorem unsupported_predeclared_types_have_no_meaning : forall n t,
  In n [PAny; PComparable; PError; PUintptr] -> ~ AdmittedPredeclaredType n t.

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

Theorem decision_accepted_iff : forall p (a : Elaboration p),
  (exists Hd Hb, decision a = AcceptedDecision (elaboration_core a) Hd Hb)
  <-> core_diagnostics (elaboration_core a) = [] /\ core_boundaries (elaboration_core a) = [].
Theorem decision_rejected_iff : forall p (a : Elaboration p),
  (exists Hd, decision a = RejectedDecision (elaboration_core a) Hd)
  <-> core_diagnostics (elaboration_core a) <> [].
Theorem decision_outside_iff : forall p (a : Elaboration p),
  (exists Hd Hb, decision a = OutsideDecision (elaboration_core a) Hd Hb)
  <-> core_diagnostics (elaboration_core a) = [] /\ core_boundaries (elaboration_core a) <> [].
Theorem compiled_retains_core : forall p cp (Hcp : source cp = p),
  compile p = Compiled p cp Hcp ->
  eq_rect (source cp) Core (core cp) p Hcp = elaboration_core (elaborate p).
Theorem rejected_retains_core : forall p (f : Failure p),
  compile p = Rejected p f -> failure_core f = elaboration_core (elaborate p).
Theorem outside_retains_core : forall p (o : Outside p),
  compile p = OutsideScope p o -> outside_core o = elaboration_core (elaborate p).
Theorem in_scope_accepted_iff : forall p, InScope p ->
  (core_diagnostics (elaboration_core (elaborate p)) = [] <-> Admissible p).
Theorem in_scope_inadmissible_rejected : forall p, InScope p -> ~ Admissible p ->
  exists f, compile p = Rejected p f.
Theorem in_scope_admissible_compiled : forall p, Admissible p -> InScope p ->
  exists cp Hcp, compile p = Compiled p cp Hcp.
Theorem rejected_not_admissible : forall p (f : Failure p),
  compile p = Rejected p f -> ~ Admissible p.

Theorem type_ready_iff_acyclic : forall p (i : Input p) (ph : Phase i),
  IsTypeReady (phase_type_result ph) <-> AcyclicEquations (phase_equations ph).
Theorem type_ready_env_is_built : forall p (i : Input p) (ph : Phase i) g e,
  phase_type_result ph = TypeReady (phase_equations ph) g e -> e = build_env (phase_equations ph) g.
Theorem acyclic_dec_reflects : forall p (eqs : ResolvedTypeEquations p),
  (exists h, acyclic_dec eqs = left h) <-> AcyclicEquations eqs.

Theorem assignable_is_identity : forall p eqs ev (env : @Env p eqs ev) s t,
  Assignable env s t <-> Identical env s t.
Theorem defined_not_assignable_to_predeclared : forall p eqs ev (env : @Env p eqs ev) d h t,
  ~ Assignable env (DefinedType env d h) (PredeclaredType env t).
Theorem predeclared_not_assignable_to_defined : forall p eqs ev (env : @Env p eqs ev) t d h,
  ~ Assignable env (PredeclaredType env t) (DefinedType env d h).
Theorem no_value_scalar_to_complex : forall p eqs ev (env : @Env p eqs ev) s t bs bt,
  Underlying env s (BasicForm env bs) -> Underlying env t (BasicForm env bt) ->
  ScalarNumericBasic bs -> ComplexBasicForm bt -> ~ ValueConvertible env s t.
Theorem no_value_complex_to_scalar : forall p eqs ev (env : @Env p eqs ev) s t bs bt,
  Underlying env s (BasicForm env bs) -> Underlying env t (BasicForm env bt) ->
  ComplexBasicForm bs -> ScalarNumericBasic bt -> ~ ValueConvertible env s t.
Theorem defined_same_underlying_convertible : forall p eqs ev (env : @Env p eqs ev) d1 h1 d2 h2,
  defined_underlying env d1 h1 = defined_underlying env d2 h2 ->
  ValueConvertible env (DefinedType env d1 h1) (DefinedType env d2 h2).
Theorem underlyingb_reflect : forall p eqs ev (env : @Env p eqs ev) s f,
  underlyingb env s = f <-> Underlying env s f.
Theorem identicalb_reflect : forall p eqs ev (env : @Env p eqs ev) s t,
  identicalb env s t = true <-> Identical env s t.
Theorem assignableb_reflect : forall p eqs ev (env : @Env p eqs ev) s t,
  assignableb env s t = true <-> Assignable env s t.
Theorem value_convertibleb_reflect : forall p eqs ev (env : @Env p eqs ev) s t,
  value_convertibleb env s t = true <-> ValueConvertible env s t.
Theorem representableb_reflect : forall p eqs ev (env : @Env p eqs ev) s c,
  representableb env s c = true <-> Representable env s c.

Theorem scopes_file_order_independent : forall p (i : Input p) (ph : Phase i),
  ScopesFileOrderIndependent ph.
Theorem predeclared_shadowed : forall cp u s o,
  binder_disposition cp s = DispDeclares cp o -> InnermostDeclaring cp u s ->
  bound_object_at cp u = o.

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

Theorem direct_use_provenance : forall p (u : DirectExprUseRef p),
  OccupiesRole (direct_parent u) (expr_node (direct_child u)) (direct_role u)
  /\ ExprChildRole (direct_role u).
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

Theorem iota_object_is_contextual : forall cp r (f : ExpressionFact cp r) o,
  referenced_object f = Some o -> object_origin_of o = Predeclared (source cp) PIota ->
  result_form f = ContextualForm cp IotaResult.
Theorem nil_object_is_contextual : forall cp r (f : ExpressionFact cp r) o,
  referenced_object f = Some o -> object_origin_of o = Predeclared (source cp) PNil ->
  result_form f = ContextualForm cp NilResult.
Theorem ordinary_constant_is_fixed : forall cp r (f : ExpressionFact cp r) o,
  referenced_object f = Some o -> object_kind_of o = ConstantObject ->
  object_origin_of o <> Predeclared (source cp) PIota ->
  exists atom, result_form f = FixedResults cp [atom].
Theorem variable_name_one_value : forall cp r (f : ExpressionFact cp r) o,
  referenced_object f = Some o -> object_kind_of o = VariableObject ->
  exists t, result_form f = FixedResults cp [ValueResult cp t].
Theorem type_name_no_result : forall cp r (f : ExpressionFact cp r) o,
  referenced_object f = Some o -> object_kind_of o = TypeObject ->
  result_form f = NoStandaloneResult cp.
Theorem builtin_name_no_result : forall cp r (f : ExpressionFact cp r) o,
  referenced_object f = Some o -> object_kind_of o = BuiltinObject ->
  result_form f = NoStandaloneResult cp.

Theorem app_results_are_parent_results : forall cp a res,
  ApplicationAccepts cp a res -> result_form (app_parent_fact cp a) = FixedResults cp res.
Theorem complex_needs_identical_types : forall cp a t1 k1 t2 k2,
  app_argument_atoms cp a = [TypedConstantAtom cp t1 k1; TypedConstantAtom cp t2 k2] ->
  ComplexArgumentsOk cp a -> AcceptedIdentical cp t1 t2.
Theorem statement_eligible_reflect : forall cp s,
  (exists h, statement_eligible_dec cp s = left h) <-> StatementEligible cp s.
Theorem conversion_is_not_statement : forall cp s a t Ht,
  StatementApplication cp s a ->
  app_target cp a = ConversionTarget (app_head_fact cp a) t Ht ->
  ~ StatementEligible cp s.
Theorem complex_is_not_statement : forall cp s a c,
  StatementApplication cp s a ->
  app_target cp a = CallableTarget (app_head_fact cp a) c -> CallableIs c PComplex ->
  ~ StatementEligible cp s.

Theorem consumption_covers_targets : forall cp s targets,
  SiteTargets cp s targets ->
  map (ce_target cp) (consumption_entries (consumption cp s)) = targets.
Theorem consumption_one_result_per_source : forall cp s,
  List.length (consumption_sources (consumption cp s))
  = List.length (consumption_entries (consumption cp s)).

Theorem short_decl_has_new_name : forall cp s,
  ShortDeclSite cp s ->
  exists b, In b (short_left_sites cp s)
         /\ exists o, binder_disposition cp b = DispDeclares cp o.
Theorem short_reuse_is_same_block : forall cp b o v,
  binder_disposition cp b = DispReuses cp o v -> SameBlockEarlier cp b o.
Theorem static_variable_origin : forall cp s,
  object_origin_of (projT1 (static_variable_at cp s))
  = SourceObject (source cp) (binding_site_object_site (variable_site_binding_site s)).

Theorem dependency_edges_from_bindings : forall p (i : Input p) (ph : Phase i) k,
  EdgesFromBindings (phase_dependency_graph ph k).
Theorem accepted_dependency_acyclic : forall cp k,
  exists order h, phase_dependency_outcome (accepted_phase cp) k
                = DependencyAcyclic (phase_dependency_graph (accepted_phase cp) k) order h.

Theorem unused_local_only_when_analyzed : forall p (c : Core p) s,
  In (UnusedLocal (phase c) s) (core_diagnostics c) ->
  IsSupported (phase_variable_outcome (phase c) s).
Theorem unused_local_iff : forall p (c : Core p) s,
  IsSupported (phase_variable_outcome (phase c) s) ->
  (In (UnusedLocal (phase c) s) (core_diagnostics c) <-> ~ ReadsVariableAtPhase (phase c) s).
Theorem diagnostic_anchors_exist : forall p (i : Input p) (ph : Phase i) (d : DiagnosticReason ph),
  exists a : DiagnosticAnchor p, diagnostic_primary d = a.

Theorem unary_never_merges : forall e, NoAdjacentMinus (render_expr (Unary UnaryMinus e)).
Theorem parens_exactly_when_needed : forall r e,
  Parenthesized (render_at r e) <-> PrecLooser (prec e) r.
Theorem render_ascii : forall e, AsciiOnly (render_expr e).
Theorem render_file_no_trailing_blank : forall f, NoTrailingBlank (render_file f).

```

## Migration of accepted guarantees

| declaration | disposition |
|---|---|
| `Safe.Property`, `Safe.Program`, `compiled`, `certify`, `certify_retains`, `Safe.source`, `Safe.core`, `certify_source`, `certify_retains_capability`, `certify_retains_core` | retained unchanged |
| `Safe.Value`, `value_type`, `ValueWellFormed`, `value_well_formedb`, `typed_constant_to_value`, `resolved_constant_value` | moved to C7 `Runtime` |
| `value_well_formedb_iff`, `typed_constant_to_value_type`, `typed_constant_to_value_well_formed`, `typed_constant_to_value_float`, `typed_constant_to_value_complex`, `typed_constant_to_value_denotes`, `resolved_constant_value_float`, `resolved_constant_value_complex` | moved to C7 `Runtime` |
| `ValueDenotesConstant`, `value_denotes_constant_runtime`, `value_denotes_complex_runtime`, `float_nonconstant_no_denotes`, `complex_nonconstant_no_denotes` | moved to C7 `Runtime` |
| `Safe.eval_expr` and every evaluation lemma and corollary | moved to C7 `Machine`; `SPEC-X034` owns them |
| `Safe.eval_stmt`, `eval_decl`, `eval_file` | deleted; subsumed by the C7 run relation |
| `Typing.resolve_constant_info`, `ConstantRepresentable` | restated as `Representable` over the environment |
| `Typing.convert_constant` | restated as `convert_constant_to`, the one constant-conversion authority over a basic form |
| `Render.const_info_denotes` | restated with the `Application` carrier; retained at C6 |
| `Render.const_info_denotes_functional` | retained unchanged |
| `Render.resolved_expr_denotes` | split: constant/spelling half retained at C6; the value half moves to C7 |
| `Render.resolved_string_denotes`, `boundary_max`, `boundary_min` | moved to C7 with the value half |
| `Render` type-expression spelling and injectivity | restated over `TypeExpr` |
| `Render` expression, argument, statement and declaration rendering | restated over the new source roots |
| `Render` ASCII and newline-safety; integer, string, float and complex decoding | retained; the complex decoder reads an `Application` |
| `Compilable.predeclared_type`, `predeclared_type_of_name` | deleted; subsumed by the phase binding relation |
| `Names.TypeName`, `SupportedType`, `classify`, `supported_of`, `all_type_names` | deleted; subsumed by `PredeclaredName` |
| `compile_complete` | restated: `Admissible p -> InScope p -> exists cp Hcp, compile p = Compiled cp Hcp` |
| `compile_rejected_of_inadmissible`, `elaboration_accepted_iff_admissible`, `elaboration_rejected_iff_inadmissible` | restated with the `InScope` premise |
| `compile_ok_valid`, `compile_rejected_not_admissible` | retained unchanged |
| `compile_program_typed`, `compile_ok_of_source_spec_valid_b` | restated over the phase judgment with `InScope` |
| `program_of_admissible`, `capability_of_admissible`, `capability_source`, `capability_is_compile_outcome` | restated with the `InScope` premise |

Proof-only helpers become `Local`. No compatibility alias and no public legacy renderer survives; prior-byte
preservation is migration evidence discharged by the exact goldens and the generated-artifact byte-compare.

## Review boundaries

**Semantic-root review** stops only when the repository is green and contains: the corrected source and index
roots, with `Role` unindexed, `OccupiesRole` over two node references, and package identity in `Compilable`;
named predeclared types with `byte`/`rune` as aliases and no admitted meaning for `any`, `comparable`, `error`
or `uintptr`; identity-only assignability; separate value and constant conversion; intrinsic
`BasicTypedConstant`; the retained phase with `TypePhaseResult` and `accepted_environment` by dependent
elimination; private `SiteOutcome` with no total fact over a blocked site; requirement satisfaction defined
from the retained authorities; one `RequirementView`; the dependency outcome over `InitUnit`; canonical child
facts for applications and the closed `ApplicationAccepts`; the separate statement rule; one
`ConsumptionEntry` mapping; the `DiagnosticAnchor` topology; the old fixed resolver, old expression phase,
`Safe.Value` and `Safe.eval_expr` deleted; no `Runtime` module or machine; prior generated bytes unchanged.

**Final C6 review** then completes declaration and shadowing behaviour, diagnostics and boundaries, direct
rendering, C6 fixtures, `LAT-077`, generated-artifact evidence, and current document and ledger truth.

C7 is forbidden until Rob accepts C6.

## Done

The typed rules were checked against pinned Go 1.23 with `make go-probe`. Every alarm agreed:

| probe | pinned `gc` | C6 rule |
|---|---|---|
| `type MyInt int; var x int; var y MyInt; x = y` | REJECT | not `Identical`, so not `Assignable` |
| `type MyInt int; var x int; var y MyInt; y = x` | REJECT | same |
| `type A int; type B int; B(a)` | ACCEPT | `VConvSameUnderlying` |
| `type A bool; type B bool; B(a)` | ACCEPT | `VConvSameUnderlying` |
| `type A string; type B string; B(a)` | ACCEPT | `VConvSameUnderlying` |
| `var i int; complex128(i)` | REJECT | no `ValueConvertible` scalar→complex |
| `var c complex128; float64(c)` | REJECT | no `ValueConvertible` complex→scalar |
| typed complex constant `3` converted to `int` | ACCEPT | `ConstantConvertible` through `convert_constant_to` |
| `var b byte; var u uint8; b = u; u = b` | ACCEPT | `AliasPredeclared PByte TUint8` |
| `var r rune; var i int32; r = i; i = r` | ACCEPT | `AliasPredeclared PRune TInt32` |
| `var i int; float64(i)` | ACCEPT | `VConvScalarNumeric` |
| `type S string; string(s)` | ACCEPT | `VConvSameUnderlying` |
| `println(1)` as a statement | ACCEPT | `EligiblePrintln` |
| `complex(1.0, 2.0)` as a statement | REJECT | no eligibility constructor |
| `len("x")` as a statement | REJECT | no eligibility constructor, and `len` is outside scope |
| `uint8(3)` as a statement | REJECT | no eligibility constructor |
| `var x int32; var y int; x = y` | REJECT | `int` and `int32` are distinct named identities |
| `var x int64; var y int; x = y` | REJECT | same, so a shared width is not a shared type |
| `type F float64; var a, b F; complex(a, b)` | ACCEPT `complex128` | identical operand types; result form from the shared underlying |
| `type F float32; var a, b F; complex(a, b)` | ACCEPT `complex64` | same rule at the narrower form |
| `type F float64; type G float64; complex(a, b)` | REJECT | operand types not `Identical` |
| `var a float32; var b float64; complex(a, b)` | REJECT | same |
| `var a float32; complex(a, 1)` | ACCEPT `complex64` | untyped operand converts to the typed operand's exact type |

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
unmet requirement and no diagnostic; a type use of `any`, `comparable`, `error` or `uintptr` gives a
type-meaning boundary; `type U uintptr; type T U; var x T` gives exactly one root boundary, two blocked sites,
and **no** unused-local diagnostic for `x`. `_, y := 1, 2` places the blank entry in its own source position.
Short declaration with no new nonblank name rejected; short redeclaration returning the exact existing object;
blank declarations creating no object; `true` and `false` as exact untyped boolean constants; an ordinary
declared constant **not** acquiring `iota`'s contextual result; alias preserving identity; a local type spec
naming itself rejected as a cycle; package constant and variable cycles rejected, including a cycle through a
blank package initializer; a package expression depending on a forward constant accepted; a first const spec
with an inherited initializer rejected; an inherited spec taking the predecessor expression under its own
`iota`; unshadowed `nil` and out-of-context `iota` rejected; a `println` argument of a defined type whose
underlying form is `string` accepted; unary minus on a constant and a variable accepted and on a string
rejected; `-(-x)` rendering with its parentheses; every currently accepted program rendering byte-identically
after migration; generated C6 programs passing the pinned Go build with their exact expected observation.

The multi-result `_, y := f()` case belongs to C9, which introduces functions and multi-results.

## Preserve

`Syntax.Program` as the sole source authority and the AST as the one IR; `Program` as the opaque C4
capability, with `Failure` and `Outside` retaining the exact core; the retained input, work forest, member
index, outcome trace and sealed core; `Machine.T` uninstantiated; direct rendering and the one
`Emit.Mint.issue` authority; certified-module coverage, the whole-theory audit and controls A-E; every
sealed-capability, mint, transport and positive client control; working-tree and staged-index separation;
no-host-Python; `life.md`.

## Stop

A predeclared basic type cannot keep a named identity over the form algebra; `byte` or `rune` mints an
identity; assignability needs a constructor beyond identity; value conversion cannot be separated from
constant conversion; `BasicTypedConstant` cannot be made intrinsic; `TypePhaseResult` cannot be tied to the
graph decision; `accepted_environment` cannot be reached by dependent elimination; a total fact query is
needed over a blocked site; an accepted family cannot be defined over a phase family; `ObjectKey` cannot
avoid forging an `Index.Key` for a predeclared object; a direct use cannot carry an `ExprChildRole`;
`RequirementSatisfied` cannot be defined from the retained authorities; the dependency node cannot cover
blank initialization work; a diagnostic payload type cannot be defined or anchored; `render_file` cannot
consume `Syntax.File`; a theorem cannot be stated over the names above; `LAT-077` needs a diagnostic the
phase cannot produce; a run relation, value, store, environment or machine is needed for a C6 row;
implementation needs a placeholder, compatibility path, trusted shortcut, fuel, bound or premature future
state.
