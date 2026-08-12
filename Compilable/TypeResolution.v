From Stdlib Require Import NArith ZArith List Bool String Ascii Lia.
From Stdlib Require Import SetoidList Permutation.
From Fido Require Import Integer Float Complex Syntax.
Import ListNotations.
Open Scope Z_scope.

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

Definition typed_integer_of_Z (it : Integer.Kind) (z : Z) : option (TypedConstant (IntegerType it)) :=
  match bool_true_dec (Integer.representableb it z) with
  | left H  => Some (TypedInteger it z H)
  | right _ => None
  end.

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

Lemma type_untyped_int_convert : forall it c,
  type_untyped_constant_at (IntegerType it) c = convert_constant (IntegerType it) (UntypedInfo c).
Proof. reflexivity. Qed.
Lemma type_untyped_float_convert : forall ft c,
  type_untyped_constant_at (FloatType ft) c = convert_constant (FloatType ft) (UntypedInfo c).
Proof. reflexivity. Qed.
Lemma type_untyped_complex_convert : forall ct c,
  type_untyped_constant_at (ComplexType ct) c = convert_constant (ComplexType ct) (UntypedInfo c).
Proof. reflexivity. Qed.

(* Exact negation of a folded constant; a source magnitude gains its sign from a unary minus. *)
Lemma float_constant_neg_canonical : forall q : Float.Constant,
  (Z.gcd (- Float.numerator q) (Zpos (Float.denominator q)) =? 1) = true.
Proof. intro q. rewrite Z.gcd_opp_l. exact (Float.canonical q). Qed.
Definition float_constant_neg (q : Float.Constant) : Float.Constant :=
  Float.MakeConstant (- Float.numerator q) (Float.denominator q) (float_constant_neg_canonical q).
Definition constant_neg (c : Constant) : option Constant :=
  match c with
  | IntegerConstant z => Some (IntegerConstant (- z))
  | FloatConstant q   => Some (FloatConstant (float_constant_neg q))
  | ComplexConstant cc => Some (ComplexConstant (Complex.MakeConstant
      (float_constant_neg (Complex.exact_real cc)) (float_constant_neg (Complex.exact_imaginary cc))))
  | _ => None
  end.

(* The exact numeric embedding of a folded constant as a floating component, with no rounding. *)
Definition constant_to_float (c : Constant) : option Float.Constant :=
  match c with
  | IntegerConstant z => Some (Float.constant_of_Z z)
  | FloatConstant q   => Some q
  | _ => None
  end.
Definition complex_of_constants (re im : Constant) : option Constant :=
  match constant_to_float re, constant_to_float im with
  | Some r, Some i => Some (ComplexConstant (Complex.MakeConstant r i))
  | _, _ => None
  end.

(* A source name's resolved meaning; the compiler's binding supplies it, never a spelling scan. *)
Inductive NameMeaning : Type :=
| NMValueConstant  : Constant -> NameMeaning
| NMConversionType : SemanticType -> NameMeaning
| NMComplexBuiltin : NameMeaning
| NMPrintlnBuiltin : NameMeaning.

(* A complex builtin's components must be floating or untyped numeric; the exact rule classifies a pair. *)
Inductive ComplexClass : Type := CxOk | CxDefer | CxError.
Definition complex_comp (ci : ConstantInfo) : option (option Float.Kind) :=
  match ci with
  | UntypedInfo (IntegerConstant _) | UntypedInfo (FloatConstant _) => Some None
  | TypedInfo (FloatType ft) _ => Some (Some ft)
  | _ => None
  end.
Definition complex_class (cre cim : ConstantInfo) : ComplexClass :=
  match complex_comp cre, complex_comp cim with
  | None, _ | _, None => CxError
  | Some None, Some None => CxOk
  | Some (Some a), Some (Some b) => if Float.kind_equalb a b then CxDefer else CxError
  | _, _ => CxDefer
  end.

(* The typing spec takes a source-name resolver; None is the compiler-owned unresolved/unmodelled binding result. *)
Section TypingResolver.
Variable resolve_name : Names.OrdinaryIdentifier -> option NameMeaning.

Fixpoint constant_info (e : Syntax.Expr) : option ConstantInfo :=
  match e with
  | Syntax.Name n =>
      match resolve_name n with Some (NMValueConstant c) => Some (UntypedInfo c) | _ => None end
  | Syntax.LiteralExpr (Syntax.IntegerLiteral k) => Some (UntypedInfo (IntegerConstant (Z.of_N k)))
  | Syntax.LiteralExpr (Syntax.FloatLiteral d)   => Some (UntypedInfo (FloatConstant (Float.nnd_value d)))
  | Syntax.LiteralExpr (Syntax.StringLiteral s)  => Some (UntypedInfo (StringConstant s))
  | Syntax.Unary Syntax.UnaryMinus e' =>
      match constant_info e' with
      | Some (UntypedInfo c)  => option_map UntypedInfo (constant_neg c)
      | Some (TypedInfo t tc) =>
          match constant_neg (constant_info_exact (TypedInfo t tc)) with
          | Some c => option_map (TypedInfo t) (convert_constant t (UntypedInfo c))
          | None   => None
          end
      | None => None
      end
  | Syntax.Application head args =>
      match head, args with
      | Syntax.Name n, x :: nil =>
          match resolve_name n with
          | Some (NMConversionType t) =>
              match constant_info x with
              | Some ci => option_map (TypedInfo t) (convert_constant t ci)
              | None => None
              end
          | _ => None
          end
      | Syntax.Name n, re :: im :: nil =>
          match resolve_name n with
          | Some NMComplexBuiltin =>
              match constant_info re, constant_info im with
              | Some cre, Some cim =>
                  match complex_class cre cim with
                  | CxOk => option_map UntypedInfo
                              (complex_of_constants (constant_info_exact cre) (constant_info_exact cim))
                  | _ => None
                  end
              | _, _ => None
              end
          | _ => None
          end
      | _, _ => None
      end
  end.

(* Defaulting turns an untyped constant into a typed one; an overflowing bare float has no default. *)
Definition default_constant (c : Constant) : option ResolvedConstant :=
  match c with
  | BoolConstant b    => Some (PackResolved BoolType (TypedBool b))
  | IntegerConstant z     => option_map (PackResolved (IntegerType Integer.Int)) (typed_integer_of_Z Integer.Int z)
  | FloatConstant q   => option_map (PackResolved (FloatType F64)) (typed_float_of_constant F64 q)
  | ComplexConstant c => option_map (PackResolved (ComplexType C128)) (typed_complex_of_constant C128 c)
  | StringConstant s  => Some (PackResolved StringType (TypedString s))
  end.

Definition resolve_constant_info (ci : ConstantInfo) : option ResolvedConstant :=
  match ci with
  | UntypedInfo c  => default_constant c
  | TypedInfo t tc => Some (PackResolved t tc)
  end.

Lemma constant_info_deterministic : forall e ci1 ci2,
  constant_info e = Some ci1 -> constant_info e = Some ci2 -> ci1 = ci2.
Proof. intros e ci1 ci2 H1 H2; rewrite H1 in H2; injection H2 as <-; reflexivity. Qed.

Lemma constant_info_zero_sign :
  constant_info (Syntax.LiteralExpr (Syntax.IntegerLiteral 0))
  = constant_info (Syntax.Unary Syntax.UnaryMinus (Syntax.LiteralExpr (Syntax.IntegerLiteral 0))).
Proof. reflexivity. Qed.

(* A nested same-format float conversion returns the same carrier, so a typed float is never rerounded. *)
Lemma convert_constant_same_float : forall ft (tc : TypedConstant (FloatType ft)),
  convert_constant (FloatType ft) (TypedInfo (FloatType ft) tc) = Some tc.
Proof. intros ft tc; destruct ft; reflexivity. Qed.

Lemma convert_constant_same_complex : forall ct (tc : TypedConstant (ComplexType ct)),
  convert_constant (ComplexType ct) (TypedInfo (ComplexType ct) tc) = Some tc.
Proof. intros ct tc; destruct ct; reflexivity. Qed.

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

Lemma convert_float_reuses_complex_component : forall ct (tc : TypedConstant (ComplexType ct)),
  Complex.constant_imaginary_is_zero (Complex.typed_exact (typed_complex tc)) = true ->
  convert_constant (FloatType (Complex.component_kind ct)) (TypedInfo (ComplexType ct) tc)
    = Some (TypedFloat (Complex.component_kind ct) (Complex.typed_real (typed_complex tc))).
Proof.
  intros ct tc Hz; destruct ct;
    unfold convert_constant, convert_to_float, same_float_kind_identity, reuse_complex_as_float;
    cbn [Complex.component_kind float_kind_eq_dec eq_rect]; rewrite Hz; reflexivity.
Qed.

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
Lemma constant_info_conv_none : forall n x,
  constant_info x = None -> constant_info (Syntax.Application (Syntax.Name n) [x]) = None.
Proof. intros n x H; cbn [constant_info]; destruct (resolve_name n) as [[c|t| |]|]; rewrite ?H; reflexivity. Qed.

End TypingResolver.

(* A mismatched or out-of-range typed constant cannot be constructed at all. *)
Fail Definition mismatch_string_carrying_int : TypedConstant StringType := TypedInteger Integer.Int 3 eq_refl.
Fail Definition mismatch_int_out_of_range : TypedConstant (IntegerType Integer.Int8) := TypedInteger Integer.Int8 128 eq_refl.
Fail Definition mismatch_float_carrying_bool : TypedConstant (FloatType F64) := TypedBool true.

