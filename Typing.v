(* The one type authority: evidence over the raw syntax, never a second typed tree beside it. *)
From Stdlib Require Import NArith ZArith List Bool String Ascii Lia.
From Stdlib Require Import SetoidList Permutation.
From Fido Require Import Integer Float Complex Syntax.
Import ListNotations.
Open Scope Z_scope.

(* The type universe: bool, the integer, float and complex families, and string as an exact byte sequence. *)
Inductive SemanticType : Type :=
| BoolType
| IntegerType : Integer.Kind -> SemanticType
| FloatType   : Float.Kind -> SemanticType
| ComplexType : Complex.Kind -> SemanticType
| StringType.

Definition type_equalb (a b : SemanticType) : bool :=
  match a, b with
  | BoolType, BoolType => true
  | IntegerType it1, IntegerType it2 => Integer.equalb it1 it2
  | FloatType ft1, FloatType ft2 => Float.kind_equalb ft1 ft2
  | ComplexType ct1, ComplexType ct2 => Complex.kind_equalb ct1 ct2
  | StringType, StringType => true
  | _, _ => false
  end.

Lemma type_equalb_spec : forall a b, type_equalb a b = true <-> a = b.
Proof.
  intros [| it1 | ft1 | ct1 |] [| it2 | ft2 | ct2 |]; simpl; split; intro H;
    try reflexivity; try discriminate.
  - apply Integer.equalb_spec in H; subst; reflexivity.
  - injection H as Heq; subst; apply Integer.equalb_spec; reflexivity.
  - apply Float.kind_equalb_spec in H; subst; reflexivity.
  - injection H as Heq; subst; apply Float.kind_equalb_spec; reflexivity.
  - apply Complex.kind_equalb_spec in H; subst; reflexivity.
  - injection H as Heq; subst; apply Complex.kind_equalb_spec; reflexivity.
Qed.

(* The exact untyped constant values of the current raw literals. *)
Inductive Constant : Type :=
| BoolConstant    : bool -> Constant
| IntegerConstant     : Z -> Constant
| FloatConstant   : Float.Constant -> Constant
| ComplexConstant : Complex.Constant -> Constant
| StringConstant  : string -> Constant.

(* The exact integer a floating constant denotes, when it denotes one; the sole float-to-integer bridge. *)
Definition constant_to_int (q : Float.Constant) : option Z :=
  if Z.eqb (Z.rem (Float.numerator q) (Zpos (Float.denominator q))) 0
  then Some (Float.numerator q / Zpos (Float.denominator q)) else None.

(* Decidable float-format equality; it reduces to [left eq_refl], so a same-format conversion is the identity. *)
Definition float_kind_eq_dec (a b : Float.Kind) : {a = b} + {a <> b}.
Proof. decide equality. Defined.

(* Decidable complex-format equality, the analogue of [float_kind_eq_dec]. *)
Definition complex_kind_eq_dec (a b : Complex.Kind) : {a = b} + {a <> b}.
Proof. decide equality. Defined.

(* A typed constant cannot exist without the evidence its type requires, so an out-of-range one has no value. *)
Inductive TypedConstant : SemanticType -> Type :=
| TypedBool    : bool -> TypedConstant BoolType
| TypedInteger : forall (it : Integer.Kind) (z : Z), Integer.representableb it z = true -> TypedConstant (IntegerType it)
| TypedFloat   : forall (ft : Float.Kind), Float.TypedConstant ft -> TypedConstant (FloatType ft)
| TypedComplex : forall (ct : Complex.Kind), Complex.TypedConstant ct -> TypedConstant (ComplexType ct)
| TypedString  : string -> TypedConstant StringType.

(* Forget the type, keep the exact constant; this reads stored data and never re-rounds a float. *)
Definition typed_exact {t : SemanticType} (tc : TypedConstant t) : Constant :=
  match tc with
  | TypedBool b        => BoolConstant b
  | TypedInteger _ z _ => IntegerConstant z
  | TypedFloat _ tfc   => FloatConstant (Float.exact tfc)
  | TypedComplex _ tcc => ComplexConstant (Complex.typed_exact tcc)
  | TypedString s      => StringConstant s
  end.

(* An index-annotated match extracts the intrinsic component, so no dependent destruction is needed. *)
Definition typed_float {ft : Float.Kind} (tc : TypedConstant (FloatType ft)) : Float.TypedConstant ft :=
  match tc in TypedConstant t return match t with FloatType f => Float.TypedConstant f | _ => unit end with
  | TypedFloat _ tfc => tfc
  | TypedBool _ => tt | TypedInteger _ _ _ => tt | TypedComplex _ _ => tt | TypedString _ => tt
  end.

Definition typed_complex {ct : Complex.Kind} (tc : TypedConstant (ComplexType ct)) : Complex.TypedConstant ct :=
  match tc in TypedConstant t return match t with ComplexType c => Complex.TypedConstant c | _ => unit end with
  | TypedComplex _ tcc => tcc
  | TypedBool _ => tt | TypedInteger _ _ _ => tt | TypedFloat _ _ => tt | TypedString _ => tt
  end.

(* A decidable guard carrying its own proof, so [typed_integer_of_Z] needs no dependent convoy. *)
Definition bool_true_dec (b : bool) : {b = true} + {b = false} :=
  match b with true => left eq_refl | false => right eq_refl end.

(* Construct a typed integer constant exactly when the value is representable, carrying the range proof. *)
Definition typed_integer_of_Z (it : Integer.Kind) (z : Z) : option (TypedConstant (IntegerType it)) :=
  match bool_true_dec (Integer.representableb it z) with
  | left H  => Some (TypedInteger it z H)
  | right _ => None
  end.

(* Construct a typed float constant by the one rounding authority. *)
Definition typed_float_of_constant (ft : Float.Kind) (q : Float.Constant) : option (TypedConstant (FloatType ft)) :=
  option_map (TypedFloat ft) (round_typed_float ft q).

(* Construct a typed complex constant by the one authority; either component's overflow rejects the whole. *)
Definition typed_complex_of_constant (ct : Complex.Kind) (c : Complex.Constant) : option (TypedConstant (ComplexType ct)) :=
  option_map (TypedComplex ct) (Complex.round_typed ct c).

(* The exact numeric embedding into the complex plane, with no rounding of its own. *)
Definition numeric_constant_to_complex (c : Constant) : option Complex.Constant :=
  match c with
  | IntegerConstant z     => Some (Complex.of_real (Float.constant_of_Z z))
  | FloatConstant q   => Some (Complex.of_real q)
  | ComplexConstant c => Some c
  | _          => None
  end.

(* One constant-status analysis over the raw AST: a literal is untyped, an explicit conversion is typed. *)
Inductive ConstantInfo : Type :=
| UntypedInfo : Constant -> ConstantInfo
| TypedInfo   : forall (t : SemanticType), TypedConstant t -> ConstantInfo.

(* An untyped constant is its own exact value; a typed one projects its intrinsic exact value. *)
Definition constant_info_exact (ci : ConstantInfo) : Constant :=
  match ci with UntypedInfo c => c | TypedInfo _ tc => typed_exact tc end.

(* The packed result of resolving one expression: existential evidence, not a typed tree. *)
Inductive ResolvedConstant : Type :=
| PackResolved : forall (t : SemanticType), TypedConstant t -> ResolvedConstant.

Definition resolved_constant_type (rc : ResolvedConstant) : SemanticType :=
  match rc with PackResolved t _ => t end.
Definition resolved_constant_exact (rc : ResolvedConstant) : Constant :=
  match rc with PackResolved _ tc => typed_exact tc end.

(* Converting a typed float to its own format returns the existing constant unchanged, with no reround. *)
Definition same_float_kind_identity (ft : Float.Kind) (ci : ConstantInfo) : option (TypedConstant (FloatType ft)) :=
  match ci with
  | TypedInfo (FloatType ft') tc =>
      match float_kind_eq_dec ft' ft with
      | left Heq => Some (eq_rect (FloatType ft') (fun T => TypedConstant T) tc (FloatType ft) (f_equal FloatType Heq))
      | right _  => None
      end
  | _ => None
  end.

(* Converting a typed complex to its own format returns the existing constant unchanged. *)
Definition same_complex_kind_identity (ct : Complex.Kind) (ci : ConstantInfo) : option (TypedConstant (ComplexType ct)) :=
  match ci with
  | TypedInfo (ComplexType ct') tc =>
      match complex_kind_eq_dec ct' ct with
      | left Heq => Some (eq_rect (ComplexType ct') (fun T => TypedConstant T) tc (ComplexType ct) (f_equal ComplexType Heq))
      | right _  => None
      end
  | _ => None
  end.

(* A typed float at the complex component format becomes the real component directly, with no reround. *)
Definition reuse_float_as_complex (ct : Complex.Kind) (ci : ConstantInfo) : option (TypedConstant (ComplexType ct)) :=
  match ci with
  | TypedInfo (FloatType ft') tc =>
      match float_kind_eq_dec ft' (Complex.component_kind ct) with
      | left Heq =>
          option_map
            (fun imz => TypedComplex ct
               (Complex.MakeTypedConstant (eq_rect ft' (fun f => Float.TypedConstant f) (typed_float tc)
                              (Complex.component_kind ct) Heq) imz))
            (round_typed_float (Complex.component_kind ct) Float.constant_zero)
      | right _ => None
      end
  | _ => None
  end.

(* A matching-format typed complex with exact zero imaginary projects its existing real component. *)
Definition reuse_complex_as_float (ft : Float.Kind) (ci : ConstantInfo) : option (TypedConstant (FloatType ft)) :=
  match ci with
  | TypedInfo (ComplexType ct') tc =>
      match float_kind_eq_dec (Complex.component_kind ct') ft with
      | left Heq =>
          if Complex.constant_imaginary_is_zero (Complex.typed_exact (typed_complex tc))
          then Some (eq_rect (Complex.component_kind ct') (fun f => TypedConstant (FloatType f))
                             (TypedFloat (Complex.component_kind ct') (Complex.typed_real (typed_complex tc)))
                             ft Heq)
          else None
      | right _ => None
      end
  | _ => None
  end.

(* Float-target conversion: reuse where the format already matches, otherwise round the exact value once. *)
Definition convert_to_float (ft : Float.Kind) (ci : ConstantInfo) : option (TypedConstant (FloatType ft)) :=
  match same_float_kind_identity ft ci with
  | Some tc => Some tc
  | None =>
  match reuse_complex_as_float ft ci with
  | Some tc => Some tc
  | None =>
      match constant_info_exact ci with
      | IntegerConstant z    => typed_float_of_constant ft (Float.constant_of_Z z)
      | FloatConstant q  => typed_float_of_constant ft q
      | ComplexConstant c => match Complex.real_if_imaginary_zero c with
                      | Some q => typed_float_of_constant ft q
                      | None   => None end
      | _         => None
      end
  end end.

(* Complex-target conversion: reuse where the format matches, otherwise round each component once. *)
Definition convert_to_complex (ct : Complex.Kind) (ci : ConstantInfo) : option (TypedConstant (ComplexType ct)) :=
  match same_complex_kind_identity ct ci with
  | Some tc => Some tc
  | None =>
  match reuse_float_as_complex ct ci with
  | Some tc => Some tc
  | None =>
      match numeric_constant_to_complex (constant_info_exact ci) with
      | Some c => typed_complex_of_constant ct c
      | None   => None
      end
  end end.

(* The one target-directed conversion authority, consuming a source status and producing a typed constant. *)
Definition convert_constant (target : SemanticType) (ci : ConstantInfo) : option (TypedConstant target) :=
  match target with
  | BoolType    => None
  | StringType  => None
  | IntegerType it =>
      match constant_info_exact ci with
      | IntegerConstant z   => typed_integer_of_Z it z
      | FloatConstant q => match constant_to_int q with
                    | Some z => typed_integer_of_Z it z
                    | None => None end
      | ComplexConstant c => match Complex.real_if_imaginary_zero c with
                      | Some q => match constant_to_int q with
                                  | Some z => typed_integer_of_Z it z
                                  | None => None end
                      | None => None end
      | _ => None
      end
  | FloatType ft => convert_to_float ft ci
  | ComplexType ct => convert_to_complex ct ci
  end.

(* Typing an untyped constant at a numeric target routes through the same conversion authority. *)
Definition type_untyped_constant_at (t : SemanticType) (c : Constant) : option (TypedConstant t) :=
  match t with
  | BoolType       => match c with BoolConstant b   => Some (TypedBool b)  | _ => None end
  | StringType     => match c with StringConstant s => Some (TypedString s) | _ => None end
  | IntegerType it => convert_constant (IntegerType it) (UntypedInfo c)
  | FloatType ft   => convert_constant (FloatType ft) (UntypedInfo c)
  | ComplexType ct => convert_constant (ComplexType ct) (UntypedInfo c)
  end.

(* Representability is successful typing at the requested type, so it cannot disagree with conversion. *)
Definition ConstantRepresentable (t : SemanticType) (c : Constant) : Prop :=
  exists tc : TypedConstant t, type_untyped_constant_at t c = Some tc.

Definition constant_representableb (t : SemanticType) (c : Constant) : bool :=
  match type_untyped_constant_at t c with Some _ => true | None => false end.

Lemma constant_representableb_iff : forall t c, constant_representableb t c = true <-> ConstantRepresentable t c.
Proof.
  intros t c; unfold constant_representableb, ConstantRepresentable.
  destruct (type_untyped_constant_at t c) as [tc|] eqn:E; split.
  - intros _; exists tc; reflexivity.
  - intros _; reflexivity.
  - discriminate.
  - intros [tc' H]; discriminate.
Qed.

(* Untyped representability at a numeric target is definitionally the conversion of that untyped status. *)
Lemma type_untyped_int_convert : forall it c,
  type_untyped_constant_at (IntegerType it) c = convert_constant (IntegerType it) (UntypedInfo c).
Proof. reflexivity. Qed.
Lemma type_untyped_float_convert : forall ft c,
  type_untyped_constant_at (FloatType ft) c = convert_constant (FloatType ft) (UntypedInfo c).
Proof. reflexivity. Qed.
Lemma type_untyped_complex_convert : forall ct c,
  type_untyped_constant_at (ComplexType ct) c = convert_constant (ComplexType ct) (UntypedInfo c).
Proof. reflexivity. Qed.

(* The typing spec takes a source-name resolver as a parameter; the compiler owns the resolver itself. *)
Section TypingResolver.
Variable rt : Syntax.TypeExpr -> SemanticType.

Fixpoint constant_info (e : Syntax.Expr) : option ConstantInfo :=
  match e with
  | Syntax.BoolLiteral b   => Some (UntypedInfo (BoolConstant b))
  | Syntax.IntegerLiteral n    => Some (UntypedInfo (IntegerConstant (Z.of_N n)))
  | Syntax.NegatedIntegerLiteral n    => Some (UntypedInfo (IntegerConstant (- Z.of_N n)))
  | Syntax.StringLiteral s => Some (UntypedInfo (StringConstant s))
  | Syntax.FloatLiteral d  => Some (UntypedInfo (FloatConstant (Float.decimal_value d)))
  | Syntax.ComplexLiteral dc => Some (UntypedInfo (ComplexConstant (Complex.decimal_value dc)))
  | Syntax.Convert ts x =>
      match constant_info x with
      | Some ci => option_map (TypedInfo (rt ts)) (convert_constant (rt ts) ci)
      | None => None
      end
  end.

(* One node's constant status, given its child's already-computed status, so nothing recomputes a subtree. *)
Definition constant_info_step (e : Syntax.Expr) (child : option ConstantInfo) : option ConstantInfo :=
  match e with
  | Syntax.BoolLiteral b     => Some (UntypedInfo (BoolConstant b))
  | Syntax.IntegerLiteral n      => Some (UntypedInfo (IntegerConstant (Z.of_N n)))
  | Syntax.NegatedIntegerLiteral n      => Some (UntypedInfo (IntegerConstant (- Z.of_N n)))
  | Syntax.StringLiteral s   => Some (UntypedInfo (StringConstant s))
  | Syntax.FloatLiteral d    => Some (UntypedInfo (FloatConstant (Float.decimal_value d)))
  | Syntax.ComplexLiteral dc => Some (UntypedInfo (ComplexConstant (Complex.decimal_value dc)))
  | Syntax.Convert ts _ =>
      match child with Some ci => option_map (TypedInfo (rt ts)) (convert_constant (rt ts) ci) | None => None end
  end.

(* A node's one current expression child, which is the conversion operand. *)
Definition expression_child (e : Syntax.Expr) : option Syntax.Expr :=
  match e with
  | Syntax.Convert _ e' => Some e'
  | _ => None
  end.

(* The recursive authority is exactly the one-node step applied to the child's status. *)
Lemma constant_info_step_reflect : forall e,
  constant_info e = constant_info_step e (match expression_child e with Some c => constant_info c | None => None end).
Proof. intro e; destruct e; reflexivity. Qed.

(* Defaulting turns an untyped constant into a typed one; an overflowing bare float has no default. *)
Definition default_constant (c : Constant) : option ResolvedConstant :=
  match c with
  | BoolConstant b    => Some (PackResolved BoolType (TypedBool b))
  | IntegerConstant z     => option_map (PackResolved (IntegerType Integer.Int)) (typed_integer_of_Z Integer.Int z)
  | FloatConstant q   => option_map (PackResolved (FloatType F64)) (typed_float_of_constant F64 q)
  | ComplexConstant c => option_map (PackResolved (ComplexType C128)) (typed_complex_of_constant C128 c)
  | StringConstant s  => Some (PackResolved StringType (TypedString s))
  end.

(* An untyped status defaults and a typed one packs unchanged, its validity already intrinsic. *)
Definition resolve_constant_info (ci : ConstantInfo) : option ResolvedConstant :=
  match ci with
  | UntypedInfo c  => default_constant c
  | TypedInfo t tc => Some (PackResolved t tc)
  end.

(* A successful constant-status resolution is a function of the syntax. *)
Lemma constant_info_deterministic : forall e ci1 ci2,
  constant_info e = Some ci1 -> constant_info e = Some ci2 -> ci1 = ci2.
Proof. intros e ci1 ci2 H1 H2; rewrite H1 in H2; injection H2 as <-; reflexivity. Qed.

(* A literal zero and a negated literal zero denote the same untyped constant. *)
Lemma constant_info_zero_sign : constant_info (Syntax.IntegerLiteral 0) = constant_info (Syntax.NegatedIntegerLiteral 0).
Proof. reflexivity. Qed.

(* A nested same-format float conversion is an identity, so evaluation never rounds a typed float twice. *)
Lemma convert_constant_same_float : forall ft (tc : TypedConstant (FloatType ft)),
  convert_constant (FloatType ft) (TypedInfo (FloatType ft) tc) = Some tc.
Proof. intros ft tc; destruct ft; reflexivity. Qed.

(* A nested same-format complex conversion is an identity, keeping the same stored component objects. *)
Lemma convert_constant_same_complex : forall ct (tc : TypedConstant (ComplexType ct)),
  convert_constant (ComplexType ct) (TypedInfo (ComplexType ct) tc) = Some tc.
Proof. intros ct tc; destruct ct; reflexivity. Qed.

(* A matching-format typed float becomes the real component as the same object, with no reround. *)
Lemma convert_complex_reuses_float_component : forall ct (tc : TypedConstant (FloatType (Complex.component_kind ct))),
  exists tcc, convert_constant (ComplexType ct) (TypedInfo (FloatType (Complex.component_kind ct)) tc)
                = Some (TypedComplex ct tcc)
           /\ Complex.typed_real tcc = typed_float tc.
Proof.
  intros ct tc; destruct ct.
  - destruct (round_typed_float F32 Float.constant_zero) as [imz|] eqn:Hz; [ | vm_compute in Hz; discriminate ].
    exists (Complex.MakeTypedConstant (typed_float tc) imz); split; [ | reflexivity ].
    unfold convert_constant, convert_to_complex, same_complex_kind_identity, reuse_float_as_complex;
      cbn [Complex.component_kind float_kind_eq_dec eq_rect option_map]; rewrite Hz; reflexivity.
  - destruct (round_typed_float F64 Float.constant_zero) as [imz|] eqn:Hz; [ | vm_compute in Hz; discriminate ].
    exists (Complex.MakeTypedConstant (typed_float tc) imz); split; [ | reflexivity ].
    unfold convert_constant, convert_to_complex, same_complex_kind_identity, reuse_float_as_complex;
      cbn [Complex.component_kind float_kind_eq_dec eq_rect option_map]; rewrite Hz; reflexivity.
Qed.

(* A zero-imaginary typed complex projects its existing real component as the same object. *)
Lemma convert_float_reuses_complex_component : forall ct (tc : TypedConstant (ComplexType ct)),
  Complex.constant_imaginary_is_zero (Complex.typed_exact (typed_complex tc)) = true ->
  convert_constant (FloatType (Complex.component_kind ct)) (TypedInfo (ComplexType ct) tc)
    = Some (TypedFloat (Complex.component_kind ct) (Complex.typed_real (typed_complex tc))).
Proof.
  intros ct tc Hz; destruct ct;
    unfold convert_constant, convert_to_float, same_float_kind_identity, reuse_complex_as_float;
    cbn [Complex.component_kind float_kind_eq_dec eq_rect]; rewrite Hz; reflexivity.
Qed.

(* An integer-typed constant's exact value is in range, extracted by an index-annotated match. *)
Lemma typed_int_value : forall it (tc : TypedConstant (IntegerType it)),
  exists z, typed_exact tc = IntegerConstant z /\ Integer.representableb it z = true.
Proof.
  intros it tc.
  refine (match tc as tc0 in TypedConstant t
          return (match t with
                  | IntegerType it' => exists z, typed_exact tc0 = IntegerConstant z /\ Integer.representableb it' z = true
                  | _ => True end)
          with
          | TypedInteger it0 z0 Hpf => _
          | _ => I
          end).
  exists z0; split; [ reflexivity | exact Hpf ].
Qed.

(* Converting a typed integer to its own type preserves the exact value and the type. *)
Lemma convert_constant_same_int : forall it (tc : TypedConstant (IntegerType it)),
  exists tc', convert_constant (IntegerType it) (TypedInfo (IntegerType it) tc) = Some tc'
           /\ typed_exact tc' = typed_exact tc.
Proof.
  intros it tc.
  destruct (typed_int_value it tc) as [ z [ Hexact Hz ] ].
  cbn [convert_constant constant_info_exact]; rewrite Hexact.
  unfold typed_integer_of_Z; destruct (bool_true_dec (Integer.representableb it z)) as [H'|H'].
  - exists (TypedInteger it z H'); split; reflexivity.
  - congruence.
Qed.

(* An invalid inner conversion propagates and no outer conversion revives it. *)
Lemma constant_info_conv_none : forall ts e,
  constant_info e = None -> constant_info (Syntax.Convert ts e) = None.
Proof. intros ts e H; simpl; rewrite H; reflexivity. Qed.

(* Use-context resolution: one expression-use context and its per-type policy. *)
Inductive Use : Type :=
| PrintlnArgument.

(* The exhaustive per-type use policy; a `println` argument accepts every current type. *)
Inductive Allows : Use -> SemanticType -> Prop :=
| AllowsPrintlnBool    : Allows PrintlnArgument BoolType
| AllowsPrintlnInteger     : forall it, Allows PrintlnArgument (IntegerType it)
| AllowsPrintlnFloat   : forall ft, Allows PrintlnArgument (FloatType ft)
| AllowsPrintlnComplex : forall ct, Allows PrintlnArgument (ComplexType ct)
| AllowsPrintlnString  : Allows PrintlnArgument StringType.

Definition use_allowsb (u : Use) (t : SemanticType) : bool :=
  match u, t with
  | PrintlnArgument, BoolType       => true
  | PrintlnArgument, IntegerType _  => true
  | PrintlnArgument, FloatType _    => true
  | PrintlnArgument, ComplexType _  => true
  | PrintlnArgument, StringType     => true
  end.

Lemma use_allowsb_iff : forall u t, use_allowsb u t = true <-> Allows u t.
Proof.
  intros [] [| it | ft | ct |]; simpl; split; intro H; try constructor; try reflexivity; inversion H.
Qed.

(* One expression's resolved typing: it analyzes, resolves, and its intrinsic type must be allowed here. *)
Inductive Resolve : Use -> Syntax.Expr -> SemanticType -> Prop :=
| Resolved : forall u e ci rc,
    constant_info e = Some ci ->
    resolve_constant_info ci = Some rc ->
    Allows u (resolved_constant_type rc) ->
    Resolve u e (resolved_constant_type rc).

(* The resolution that exposes the [ResolvedConstant] witness. *)
Definition resolve_constant (u : Use) (e : Syntax.Expr) : option ResolvedConstant :=
  match constant_info e with
  | None => None
  | Some ci =>
      match resolve_constant_info ci with
      | None => None
      | Some rc => if use_allowsb u (resolved_constant_type rc) then Some rc else None
      end
  end.

Definition resolve (u : Use) (e : Syntax.Expr) : option SemanticType :=
  option_map resolved_constant_type (resolve_constant u e).

Lemma resolve_constant_sound : forall u e rc,
  resolve_constant u e = Some rc ->
  exists ci, constant_info e = Some ci /\ resolve_constant_info ci = Some rc
             /\ Allows u (resolved_constant_type rc).
Proof.
  intros u e rc H; unfold resolve_constant in H.
  destruct (constant_info e) as [ci|] eqn:Hci; [| discriminate].
  destruct (resolve_constant_info ci) as [rc'|] eqn:Hrc; [| discriminate].
  destruct (use_allowsb u (resolved_constant_type rc')) eqn:Hua; [| discriminate].
  injection H as ->. exists ci; split; [ reflexivity | split; [ exact Hrc | apply use_allowsb_iff; exact Hua ] ].
Qed.

Lemma resolve_sound : forall u e t, resolve u e = Some t -> Resolve u e t.
Proof.
  intros u e t H. unfold resolve in H.
  destruct (resolve_constant u e) as [rc|] eqn:Hrc; cbn [option_map] in H; [| discriminate].
  injection H as <-. destruct (resolve_constant_sound u e rc Hrc) as [ci [Hci [Hri Hua]]].
  eapply Resolved; [ exact Hci | exact Hri | exact Hua ].
Qed.

Lemma resolve_complete : forall u e t, Resolve u e t -> resolve u e = Some t.
Proof.
  intros u e t H; destruct H as [ u0 e0 ci rc Hci Hrc Hua ].
  apply use_allowsb_iff in Hua.
  unfold resolve, resolve_constant; rewrite Hci, Hrc, Hua; reflexivity.
Qed.

Lemma resolve_deterministic : forall u e t1 t2, Resolve u e t1 -> Resolve u e t2 -> t1 = t2.
Proof.
  intros u e t1 t2 H1 H2.
  apply resolve_complete in H1; apply resolve_complete in H2.
  rewrite H1 in H2; injection H2 as <-; reflexivity.
Qed.

(* An expression is typed in a use context exactly when it resolves to some type there. *)
Definition expression_typedb (u : Use) (e : Syntax.Expr) : bool :=
  match resolve u e with Some _ => true | None => false end.

Lemma expression_typedb_iff : forall u e, expression_typedb u e = true <-> exists t, Resolve u e t.
Proof.
  intros u e; unfold expression_typedb; destruct (resolve u e) as [ t | ] eqn:Hr; split.
  - intros _; exists t; apply resolve_sound; exact Hr.
  - intros _; reflexivity.
  - intro H; discriminate H.
  - intros [t' Ht]; apply resolve_complete in Ht; rewrite Ht in Hr; discriminate.
Qed.

Inductive Stmt : Syntax.Stmt -> Prop :=
| TypedPrintln : forall args,
    Forall (fun e => exists t, Resolve PrintlnArgument e t) args -> Stmt (Syntax.Println args).

Inductive Decl : Syntax.Decl -> Prop :=
| TypedMain : forall body, Forall Stmt body -> Decl (Syntax.Main body).

Definition File (decls : list Syntax.Decl) : Prop := Forall Decl decls.
Definition SourceFile (sf : Syntax.File) : Prop := File (Syntax.declarations sf).

(* Whole-program typing quantifies over the map's [MapsTo], never over a construction-order list. *)
Definition Program (p : Syntax.Program) : Prop :=
  forall path sf, Syntax.maps_to_file path sf (Syntax.files p) -> SourceFile sf.

Definition stmt_typedb (s : Syntax.Stmt) : bool :=
  match s with Syntax.Println args => forallb (expression_typedb PrintlnArgument) args end.
Definition decl_typedb (d : Syntax.Decl) : bool :=
  match d with Syntax.Main body => forallb stmt_typedb body end.
Definition file_typedb (decls : list Syntax.Decl) : bool := forallb decl_typedb decls.
Definition source_file_typedb (sf : Syntax.File) : bool := file_typedb (Syntax.declarations sf).
(* The executable checker traverses the map's canonical derived enumeration. *)
Definition program_typedb (p : Syntax.Program) : bool :=
  forallb (fun b => source_file_typedb (snd b)) (Syntax.file_bindings (Syntax.files p)).

Lemma forallb_iff_forall {X} : forall (f : X -> bool) (P : X -> Prop) (l : list X),
  (forall x, f x = true <-> P x) -> (forallb f l = true <-> Forall P l).
Proof.
  intros f P l Hpt; induction l as [ | x l' IH ]; simpl.
  - split; [ constructor | reflexivity ].
  - rewrite Bool.andb_true_iff, Hpt, IH.
    split; [ intros [Hx Hl]; constructor; assumption
           | intro H; inversion H; subst; split; assumption ].
Qed.

Lemma stmt_typedb_iff : forall s, stmt_typedb s = true <-> Stmt s.
Proof.
  intros [args]; simpl.
  rewrite (forallb_iff_forall (expression_typedb PrintlnArgument) (fun e => exists t, Resolve PrintlnArgument e t)
             args (fun e => expression_typedb_iff PrintlnArgument e)).
  split; [ intro H; constructor; exact H | intro H; inversion H; subst; assumption ].
Qed.

Lemma decl_typedb_iff : forall d, decl_typedb d = true <-> Decl d.
Proof.
  intros [body]; simpl. rewrite (forallb_iff_forall stmt_typedb Stmt body stmt_typedb_iff).
  split; [ intro H; constructor; exact H | intro H; inversion H; subst; assumption ].
Qed.

Lemma file_typedb_iff : forall f, file_typedb f = true <-> File f.
Proof. intro f; unfold file_typedb, File; apply forallb_iff_forall; exact decl_typedb_iff. Qed.

Lemma source_file_typedb_iff : forall sf, source_file_typedb sf = true <-> SourceFile sf.
Proof. intro sf; apply file_typedb_iff. Qed.

(* The map-based judgment and the executable checker are the same, bridged by the standard map. *)
Lemma program_typedb_iff : forall p, program_typedb p = true <-> Program p.
Proof.
  intro p. unfold program_typedb, Program.
  rewrite (forallb_iff_forall (fun b => source_file_typedb (snd b)) (fun b => SourceFile (snd b))
             (Syntax.file_bindings (Syntax.files p)) (fun b => source_file_typedb_iff (snd b))).
  unfold Syntax.maps_to_file, Syntax.file_bindings. split.
  - intros H path sf Hmt.
    apply Syntax.FileFacts.elements_mapsto_iff, InA_alt in Hmt.
    destruct Hmt as [[k' e'] [Heq Hin]]. destruct Heq as [_ He]. cbn in *.
    rewrite Forall_forall in H. specialize (H (k', e') Hin). cbn in H. rewrite He. exact H.
  - intros H. apply Forall_forall. intros [k e] Hin. cbn.
    apply (H k e), Syntax.FileFacts.elements_mapsto_iff, InA_alt.
    exists (k, e). split; [ split; reflexivity | exact Hin ].
Qed.

(* Whole-program typing respects semantic map equality, so equal maps type identically. *)
Lemma program_equal : forall p1 p2,
  Syntax.FilesEqual (Syntax.files p1) (Syntax.files p2) -> Program p1 -> Program p2.
Proof.
  intros p1 p2 Heq Ht path sf Hmt. apply (Ht path sf). unfold Syntax.maps_to_file in *.
  apply Syntax.FileFacts.find_mapsto_iff. rewrite (Heq path). apply Syntax.FileFacts.find_mapsto_iff. exact Hmt.
Qed.

(* The reflected checker agrees on semantically equal maps, whatever the backing tree's order. *)
Lemma program_typedb_equal : forall p1 p2,
  Syntax.FilesEqual (Syntax.files p1) (Syntax.files p2) -> program_typedb p1 = program_typedb p2.
Proof.
  intros p1 p2 Heq.
  destruct (program_typedb p1) eqn:E1; destruct (program_typedb p2) eqn:E2; try reflexivity.
  - exfalso. apply program_typedb_iff in E1.
    assert (program_typedb p2 = true)
      by (apply program_typedb_iff; exact (program_equal p1 p2 Heq E1)).
    rewrite E2 in H; discriminate.
  - exfalso. apply program_typedb_iff in E2.
    assert (program_typedb p1 = true)
      by (apply program_typedb_iff;
          exact (program_equal p2 p1 (Syntax.files_equal_sym _ _ Heq) E2)).
    rewrite E1 in H; discriminate.
Qed.

(* A permuted node list builds a semantically equal map, so it types identically. *)
Theorem program_typedb_build_permutation : forall ms nodes1 nodes2 p1 p2,
  Permutation nodes1 nodes2 ->
  build_program ms nodes1 = Some p1 -> build_program ms nodes2 = Some p2 ->
  program_typedb p1 = program_typedb p2.
Proof.
  intros ms nodes1 nodes2 p1 p2 Hperm Hb1 Hb2. apply program_typedb_equal.
  unfold build_program in *.
  destruct (Syntax.files_of_nodes nodes1) as [fm1|] eqn:F1; [ | discriminate ].
  destruct (Syntax.files_of_nodes nodes2) as [fm2|] eqn:F2; [ | discriminate ].
  injection Hb1 as <-. injection Hb2 as <-. cbn [Syntax.files].
  exact (Syntax.files_of_nodes_permutation nodes1 nodes2 fm1 fm2 Hperm F1 F2).
Qed.

(* The empty file types vacuously, and so does the empty program. *)
Lemma empty_file_typed : File [].
Proof. constructor. Qed.

End TypingResolver.

(* Shared constant fixtures that carry no source type name, so they need no resolver. *)
Definition integer_literal (z : Z) : Syntax.Expr :=
  if Z.leb 0 z then Syntax.IntegerLiteral (Z.to_N z) else Syntax.NegatedIntegerLiteral (Z.to_N (- z)).

(* The decimal and decimal-complex constant fixtures. *)
Definition decimal_15em1 : Float.Decimal := Float.MakeDecimal 15 (-1) eq_refl.   (* 1.5 *)
Definition decimal_3    : Float.Decimal := Float.MakeDecimal 3 0 eq_refl.        (* 3.0 *)
Definition decimal_35em1 : Float.Decimal := Float.MakeDecimal 35 (-1) eq_refl.   (* 3.5 *)
Definition decimal_128  : Float.Decimal := Float.MakeDecimal 128 0 eq_refl.      (* 128.0 *)
Definition decimal_m1   : Float.Decimal := Float.MakeDecimal (-1) 0 eq_refl.     (* -1.0 *)
Definition decimal_single_rounding : Float.Decimal := Float.MakeDecimal 2305843146652647425 0 eq_refl.
Definition decimal_m25em1 : Float.Decimal := Float.MakeDecimal (-25) (-1) eq_refl.  (* -2.5 *)
Definition decimal_127_0  : Float.Decimal := Float.MakeDecimal 127 0 eq_refl.
Definition decimal_1_0    : Float.Decimal := Float.MakeDecimal 1 0 eq_refl.
Definition decimal_m1_0   : Float.Decimal := Float.MakeDecimal (-1) 0 eq_refl.
Definition decimal_0_0    : Float.Decimal := Float.MakeDecimal 0 0 eq_refl.
Definition decimal_complex_1p5_m2p5 : Complex.Decimal := Complex.MakeDecimal decimal_15em1 decimal_m25em1.
(* 1e-50: nonzero, and it underflows binary32 to +0 *)
Definition decimal_tiny_imaginary : Float.Decimal := Float.MakeDecimal 1 (-50) eq_refl.

(* A mismatched or out-of-range typed constant cannot be constructed at all. *)
Fail Definition mismatch_string_carrying_int : TypedConstant StringType := TypedInteger Integer.Int 3 eq_refl.
Fail Definition mismatch_int_out_of_range : TypedConstant (IntegerType Integer.Int8) := TypedInteger Integer.Int8 128 eq_refl.
Fail Definition mismatch_float_carrying_bool : TypedConstant (FloatType F64) := TypedBool true.

(* Every string literal is representable, for an arbitrary finite byte sequence. *)
Lemma string_representable : forall s, ConstantRepresentable StringType (StringConstant s).
Proof. intro s; exists (TypedString s); reflexivity. Qed.
Lemma string_representableb : forall s, constant_representableb StringType (StringConstant s) = true.
Proof. reflexivity. Qed.

(* index-free [forallb] plumbing for the whole-program typing folds *)

Lemma forallb_ext_in {A} (f g : A -> bool) (l : list A) :
  (forall x, In x l -> f x = g x) -> forallb f l = forallb g l.
Proof.
  induction l as [|a l IH]; simpl; intros H; [reflexivity|].
  rewrite (H a (or_introl eq_refl)), IH; [reflexivity | intros x Hx; apply H; right; exact Hx].
Qed.

Lemma forallb_map_snd {A B} (f : B -> bool) (l : list (A * B)) :
  forallb (fun x => f (snd x)) l = forallb f (map snd l).
Proof. induction l as [|a l IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.
