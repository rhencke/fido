
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

Parameter literal_constant : forall {p}, LiteralRef p -> Constant.

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
