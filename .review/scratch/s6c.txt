
(* ── §6 Total object descriptor ────────────────────────────────────────────── *)
Inductive SourceCategory : Type :=
| CatConst | CatVar | CatAlias | CatDefined | CatFunc.

Definition object_site_category {p} (s : ObjectSiteRef p) : SourceCategory :=
  match object_site_view s with
  | OSConst _   => CatConst
  | OSVar _     => CatVar
  | OSAlias _   => CatAlias
  | OSDefined _ => CatDefined
  | OSMain _    => CatFunc
  end.

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

(* ObjectKind is derived from origin/category. *)
Definition object_kind_of {p} {i : Input p} {ph : Phase i} (o : ObjectRef ph) : ObjectKind :=
  match object_origin o with
  | Predeclared _ n => predeclared_kind n
  | SourceSite _ s  => match object_site_category s with
    | CatConst => ConstantObject | CatVar => VariableObject
    | CatAlias | CatDefined => TypeObject | CatFunc => FunctionObject
    end
  end.

(* ── §6 Successful semantic meaning is partial ────────────────────────────── *)
Inductive TypeMeaning {p} {i : Input p} (ph : Phase i)
  : ObjectRef ph -> Type :=
| TMPredeclared : forall n t, AdmittedPredeclaredType n t ->
    TypeMeaning ph (predeclared_object ph n)
| TMPredeclaredAlias : forall n t, AliasPredeclared n t ->
    TypeMeaning ph (predeclared_object ph n)
| TMAlias : forall (a : AliasSpecRef p) (rhs : SemanticType p),
    TypeMeaning ph (source_object ph (alias_object_site a))
| TMDefined : forall (d : BoundDefinedTypeRef p),
    TypeMeaning ph (source_object ph (defined_object_site d)).

Definition type_meaning_type {p} {i : Input p} {ph : Phase i} {o}
  (m : TypeMeaning ph o) : SemanticType p :=
  match m with
  | TMPredeclared _ _ t _      => PredeclaredType p t
  | TMPredeclaredAlias _ _ t _ => PredeclaredType p t
  | TMAlias _ _ rhs            => rhs
  | TMDefined _ d              => DefinedType p d
  end.

Inductive DeclaredConstant {p} {i : Input p} (ph : Phase i)  : Type :=
| DeclaredUntyped : Constant -> DeclaredConstant ph
| DeclaredTyped   : forall t : SemanticType p, TypedConstant ph t -> DeclaredConstant ph.

Parameter ConstantDeclarationFact : forall {p} {i : Input p} (ph : Phase i),
  ObjectEstablisher p -> Type.
Parameter constant_declared : forall {p} {i : Input p} {ph : Phase i} {s},
  ConstantDeclarationFact ph s -> DeclaredConstant ph.

Parameter VariableDeclarationFact : forall {p} {i : Input p} (ph : Phase i),
  ObjectEstablisher p -> Type.
Parameter variable_declared_type : forall {p} {i : Input p} {ph : Phase i} {s},
  VariableDeclarationFact ph s -> SemanticType p.

Inductive ConstantMeaning {p} {i : Input p} (ph : Phase i)
  : ObjectRef ph -> Type :=
| CMPredeclaredBool : forall n b, predeclared_capability n = CapUntypedBool b ->
    ConstantMeaning ph (predeclared_object ph n)
| CMDeclared : forall (c : ConstSpecRef p)
    (est : ObjectEstablisher p) (df : ConstantDeclarationFact ph est),
    ConstantMeaning ph (source_object ph (const_object_site c)).

Record StaticVariable {p} {i : Input p} (ph : Phase i)
  (o : ObjectRef ph) : Type := MakeStaticVariable {
  static_var_site    : VariableSiteRef p;
  static_est         : ObjectEstablisher p;
  static_decl        : VariableDeclarationFact ph static_est;
  static_is_its_site : object_origin o = SourceSite p (establisher_site static_est)
}.

Definition static_type {p} {i : Input p} {ph : Phase i} {o}
  (sv : StaticVariable ph o) : SemanticType p :=
  variable_declared_type (static_decl ph o sv).

Definition static_object_site {p} {i : Input p} {ph : Phase i} {o}
  (sv : StaticVariable ph o) : ObjectSiteRef p :=
  var_object_site (static_var_site ph o sv).

Inductive CallableMeaning {p} {i : Input p} (ph : Phase i) : ObjectRef ph -> Type :=
| CallComplex : CallableMeaning ph (predeclared_object ph PComplex)
| CallPrintln : CallableMeaning ph (predeclared_object ph PPrintln).

Inductive IotaMeaning {p} {i : Input p} (ph : Phase i) : ObjectRef ph -> Type :=
| IotaIs : IotaMeaning ph (predeclared_object ph PIota).

Inductive NilMeaning {p} {i : Input p} (ph : Phase i) : ObjectRef ph -> Type :=
| NilIs : NilMeaning ph (predeclared_object ph PNil).

Inductive ObjectMeaning {p} {i : Input p} (ph : Phase i)
  (o : ObjectRef ph) : Type :=
| MeaningType     : TypeMeaning ph o -> ObjectMeaning ph o
| MeaningConstant : ConstantMeaning ph o -> ObjectMeaning ph o
| MeaningVariable : StaticVariable ph o -> ObjectMeaning ph o
| MeaningCallable : CallableMeaning ph o -> ObjectMeaning ph o
| MeaningIota     : IotaMeaning ph o -> ObjectMeaning ph o
| MeaningNil      : NilMeaning ph o -> ObjectMeaning ph o.

(* §7 Exact role decisions over the object descriptor and the use role.  Wrong role is a definite error,
   not a capability bucket.  A type used as a value is wrong-role, not "value capable".  A callable alone
   has no standalone value.  `iota` and `nil` are contextual, not ordinary values. *)
Inductive TypeRoleResult {p} {i : Input p} (ph : Phase i) : ObjectRef ph -> Type :=
| TypeRoleAdmitted : forall o, TypeRoleResult ph o
| TypeRoleMissing  : forall o, TypeRoleResult ph o
| TypeRoleWrong    : forall o, TypeRoleResult ph o.

Inductive ValueRoleResult {p} {i : Input p} (ph : Phase i) : ObjectRef ph -> Type :=
| ValueRoleConstant    : forall o, ValueRoleResult ph o
| ValueRoleVariable    : forall o, ValueRoleResult ph o
| ValueRoleContextual  : forall o, ValueRoleResult ph o
| ValueRoleMissing     : forall o, ValueRoleResult ph o
| ValueRoleWrong       : forall o, ValueRoleResult ph o.

Inductive HeadRoleResult {p} {i : Input p} (ph : Phase i) : ObjectRef ph -> Type :=
| HeadRoleType     : forall o, HeadRoleResult ph o
| HeadRoleCallable : forall o, HeadRoleResult ph o
| HeadRoleMissing  : forall o, HeadRoleResult ph o
| HeadRoleWrong    : forall o, HeadRoleResult ph o.

Parameter type_role_decision : forall {p} {i : Input p} (ph : Phase i) (o : ObjectRef ph),
  TypeRoleResult ph o.
Parameter value_role_decision : forall {p} {i : Input p} (ph : Phase i) (o : ObjectRef ph),
  ValueRoleResult ph o.
Parameter head_role_decision : forall {p} {i : Input p} (ph : Phase i) (o : ObjectRef ph),
  HeadRoleResult ph o.

(* Backward compatibility: the requirements still reference these until §13 rewrites them. *)
Definition HasTypeCapability {p} {i : Input p} {ph : Phase i} (o : ObjectRef ph) : Prop :=
  match type_role_decision ph o with TypeRoleAdmitted _ _ => True | _ => False end.

Definition HasValueCapability {p} {i : Input p} {ph : Phase i} (o : ObjectRef ph) : Prop :=
  match value_role_decision ph o with
  | ValueRoleConstant _ _ | ValueRoleVariable _ _ | ValueRoleContextual _ _ => True
  | _ => False
  end.
