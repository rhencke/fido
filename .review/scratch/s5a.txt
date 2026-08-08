
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
