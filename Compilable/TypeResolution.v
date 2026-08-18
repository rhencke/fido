From Stdlib Require Import NArith ZArith List Bool String Lia.
From Fido Require Import Integer Float Complex Names.
Import ListNotations.
Open Scope Z_scope.

(* Pure structural form only: TypeForm is the shape a constant may take, never a nominal type identity. *)

Inductive TypeForm : Type :=
| BoolForm
| IntegerForm : Integer.Kind -> TypeForm
| FloatForm   : Float.Kind -> TypeForm
| ComplexForm : Complex.Kind -> TypeForm
| StringForm.

Definition form_equalb (a b : TypeForm) : bool :=
  match a, b with
  | BoolForm, BoolForm => true
  | IntegerForm k1, IntegerForm k2 => Integer.equalb k1 k2
  | FloatForm k1, FloatForm k2 => Float.kind_equalb k1 k2
  | ComplexForm k1, ComplexForm k2 => Complex.kind_equalb k1 k2
  | StringForm, StringForm => true
  | _, _ => false
  end.

Lemma form_equalb_spec : forall a b, form_equalb a b = true <-> a = b.
Proof.
  intros [| k1 | k1 | k1 |] [| k2 | k2 | k2 |]; cbn; split; intro H;
    try reflexivity; try discriminate.
  - apply Integer.equalb_spec in H; subst; reflexivity.
  - injection H as ->; apply Integer.equalb_spec; reflexivity.
  - apply Float.kind_equalb_spec in H; subst; reflexivity.
  - injection H as ->; apply Float.kind_equalb_spec; reflexivity.
  - apply Complex.kind_equalb_spec in H; subst; reflexivity.
  - injection H as ->; apply Complex.kind_equalb_spec; reflexivity.
Qed.

(* Distinct forms are separated by the decision procedure: form carries no identity that would merge them. *)
Lemma form_identity_separation : forall a b, a <> b <-> form_equalb a b = false.
Proof.
  intros a b; split.
  - intro Hne. destruct (form_equalb a b) eqn:E; [ apply form_equalb_spec in E; contradiction | reflexivity ].
  - intros E Heq; subst b. assert (form_equalb a a = true) by (apply form_equalb_spec; reflexivity); congruence.
Qed.

(* An exact folded constant value; never a nominal type. *)
Inductive Constant : Type :=
| CInt     : Z -> Constant
| CFloat   : Float.Constant -> Constant
| CComplex : Complex.Constant -> Constant
| CString  : string -> Constant
| CBool    : bool -> Constant.

(* A typed constant cannot exist without the evidence its form requires, so an out-of-range one has no value. *)
Inductive TypedConstant : TypeForm -> Type :=
| TCBool    : bool -> TypedConstant BoolForm
| TCInt     : forall (k : Integer.Kind) (z : Z), Integer.representableb k z = true -> TypedConstant (IntegerForm k)
| TCFloat   : forall (k : Float.Kind), Float.TypedConstant k -> TypedConstant (FloatForm k)
| TCComplex : forall (k : Complex.Kind), Complex.TypedConstant k -> TypedConstant (ComplexForm k)
| TCString  : string -> TypedConstant StringForm.

(* Forget the form, keep the exact constant; reads stored data and never re-rounds. *)
Definition typed_exact {t : TypeForm} (tc : TypedConstant t) : Constant :=
  match tc with
  | TCBool b       => CBool b
  | TCInt _ z _    => CInt z
  | TCFloat _ v    => CFloat (Float.exact v)
  | TCComplex _ v  => CComplex (Complex.typed_exact v)
  | TCString s     => CString s
  end.

(* A typed constant's exact value has exactly the shape its form dictates; integers carry their range proof. *)
Lemma typed_constant_intrinsic : forall t (tc : TypedConstant t),
  match t as t0 return TypedConstant t0 -> Prop with
  | BoolForm      => fun c => exists b, typed_exact c = CBool b
  | IntegerForm k => fun c => exists z, typed_exact c = CInt z /\ Integer.representableb k z = true
  | FloatForm _   => fun c => exists q, typed_exact c = CFloat q
  | ComplexForm _ => fun c => exists cc, typed_exact c = CComplex cc
  | StringForm    => fun c => exists s, typed_exact c = CString s
  end tc.
Proof.
  intros t tc; destruct tc; cbn.
  - eexists; reflexivity.
  - eexists; split; [ reflexivity | eassumption ].
  - eexists; reflexivity.
  - eexists; reflexivity.
  - eexists; reflexivity.
Qed.

Inductive TypedFlag : Type :=
| Untyped
| ExplicitlyTyped : TypeForm -> TypedFlag.

Record ConstantInfo := mk_cinfo {
  ci_const : Constant;
  ci_typed : TypedFlag
}.

Record ResolvedConstant := mk_rc {
  rc_form  : TypeForm;
  rc_value : TypedConstant rc_form
}.

Definition resolved_constant_form (rc : ResolvedConstant) : TypeForm := rc_form rc.
Definition resolved_constant_exact (rc : ResolvedConstant) : Constant := typed_exact (rc_value rc).

(* Conversion is total with three exact outcomes: a target-form value, an out-of-range value, or not the target form. *)
Inductive ConversionResult (target : TypeForm) : Type :=
| Converted : TypedConstant target -> ConversionResult target
| Overflows : Constant -> ConversionResult target
| NotForm   : Constant -> ConversionResult target.
Arguments Converted {target} _.
Arguments Overflows {target} _.
Arguments NotForm {target} _.

(* The exact integer a constant denotes, when it denotes one; the sole float/complex-to-integer bridge. *)
Definition constant_to_int (q : Float.Constant) : option Z :=
  if Z.eqb (Z.rem (Float.numerator q) (Zpos (Float.denominator q))) 0
  then Some (Float.numerator q / Zpos (Float.denominator q)) else None.

Definition int_value (c : Constant) : option Z :=
  match c with
  | CInt z     => Some z
  | CFloat q   => constant_to_int q
  | CComplex cc => match Complex.real_if_imaginary_zero cc with Some q => constant_to_int q | None => None end
  | _          => None
  end.
Definition float_value (c : Constant) : option Float.Constant :=
  match c with
  | CInt z     => Some (Float.constant_of_Z z)
  | CFloat q   => Some q
  | CComplex cc => Complex.real_if_imaginary_zero cc
  | _          => None
  end.
Definition complex_value (c : Constant) : option Complex.Constant :=
  match c with
  | CInt z     => Some (Complex.of_real (Float.constant_of_Z z))
  | CFloat q   => Some (Complex.of_real q)
  | CComplex cc => Some cc
  | _          => None
  end.

(* A decidable guard carrying its own proof, so the integer branch needs no dependent convoy. *)
Definition bool_true_dec (b : bool) : {b = true} + {b = false} :=
  match b with true => left eq_refl | false => right eq_refl end.

Definition convert_constant (target : TypeForm) (ci : ConstantInfo) : ConversionResult target :=
  let c := ci_const ci in
  match target with
  | BoolForm     => match c with CBool b   => Converted (TCBool b)   | _ => NotForm c end
  | StringForm   => match c with CString s => Converted (TCString s) | _ => NotForm c end
  | IntegerForm k =>
      match int_value c with
      | Some z => match bool_true_dec (Integer.representableb k z) with
                  | left H  => Converted (TCInt k z H)
                  | right _ => Overflows c
                  end
      | None => NotForm c
      end
  | FloatForm k =>
      match float_value c with
      | Some q => match round_typed_float k q with
                  | Some v => Converted (TCFloat k v)
                  | None   => Overflows c
                  end
      | None => NotForm c
      end
  | ComplexForm k =>
      match complex_value c with
      | Some cc => match Complex.round_typed k cc with
                   | Some v => Converted (TCComplex k v)
                   | None   => Overflows c
                   end
      | None => NotForm c
      end
  end.

(* A failed conversion carries the exact offending constant, so overflow diagnostics name the real value. *)
Lemma convert_total_exact : forall target ci,
  (forall c, convert_constant target ci = Overflows c -> c = ci_const ci)
  /\ (forall c, convert_constant target ci = NotForm c -> c = ci_const ci).
Proof.
  intros target ci; split; intros c H; unfold convert_constant in H; destruct target;
    repeat (match goal with
            | [ H : context[match ?x with _ => _ end] |- _ ] => destruct x eqn:?
            end); try discriminate; injection H as <-; reflexivity.
Qed.

Definition constant_representableb (target : TypeForm) (c : Constant) : bool :=
  match convert_constant target (mk_cinfo c Untyped) with Converted _ => true | _ => false end.

Definition ConstantRepresentable (target : TypeForm) (c : Constant) : Prop :=
  constant_representableb target c = true.

Lemma representable_iff_converted : forall target c,
  ConstantRepresentable target c <-> exists tc, convert_constant target (mk_cinfo c Untyped) = Converted tc.
Proof.
  intros target c; unfold ConstantRepresentable, constant_representableb.
  destruct (convert_constant target (mk_cinfo c Untyped)) as [tc| |] eqn:E; split.
  - intros _; exists tc; reflexivity.
  - intros _; reflexivity.
  - discriminate.
  - intros [tc H]; discriminate.
  - discriminate.
  - intros [tc H]; discriminate.
Qed.

(* Exact negation of a folded constant; a source magnitude gains its sign from a unary minus. *)
Lemma float_constant_neg_canonical : forall q : Float.Constant,
  (Z.gcd (- Float.numerator q) (Zpos (Float.denominator q)) =? 1) = true.
Proof. intro q. rewrite Z.gcd_opp_l. exact (Float.canonical q). Qed.
Definition float_constant_neg (q : Float.Constant) : Float.Constant :=
  Float.MakeConstant (- Float.numerator q) (Float.denominator q) (float_constant_neg_canonical q).
Definition constant_neg (c : Constant) : option Constant :=
  match c with
  | CInt z     => Some (CInt (- z))
  | CFloat q   => Some (CFloat (float_constant_neg q))
  | CComplex cc => Some (CComplex (Complex.MakeConstant
      (float_constant_neg (Complex.exact_real cc)) (float_constant_neg (Complex.exact_imaginary cc))))
  | _ => None
  end.

(* The exact numeric embedding of a folded constant as a floating component, with no rounding. *)
Definition constant_to_float (c : Constant) : option Float.Constant :=
  match c with
  | CInt z   => Some (Float.constant_of_Z z)
  | CFloat q => Some q
  | _ => None
  end.
Definition complex_of_constants (re im : Constant) : option Constant :=
  match constant_to_float re, constant_to_float im with
  | Some r, Some i => Some (CComplex (Complex.MakeConstant r i))
  | _, _ => None
  end.

(* Defaulting turns an untyped constant into a typed one; an overflowing bare numeric constant has no default. *)
Definition default_constant (c : Constant) : option ResolvedConstant :=
  match c with
  | CBool b    => Some (mk_rc BoolForm (TCBool b))
  | CString s  => Some (mk_rc StringForm (TCString s))
  | CInt z     => match bool_true_dec (Integer.representableb Integer.Int z) with
                  | left H  => Some (mk_rc (IntegerForm Integer.Int) (TCInt Integer.Int z H))
                  | right _ => None
                  end
  | CFloat q   => match round_typed_float Float.F64 q with
                  | Some v => Some (mk_rc (FloatForm Float.F64) (TCFloat Float.F64 v))
                  | None   => None
                  end
  | CComplex cc => match Complex.round_typed Complex.C128 cc with
                   | Some v => Some (mk_rc (ComplexForm Complex.C128) (TCComplex Complex.C128 v))
                   | None   => None
                   end
  end.

(* A source name's resolved FORM meaning; contextual policy (complex/println/iota/nil) lives in Facts, not here. *)
Inductive NameMeaning : Type :=
| NMConversionForm : TypeForm -> NameMeaning
| NMValueConstant  : Constant -> NameMeaning
| NMNoFormMeaning.

Definition predeclared_meaning (n : Names.PredeclaredName) : NameMeaning :=
  match n with
  | Names.PBool       => NMConversionForm BoolForm
  | Names.PString     => NMConversionForm StringForm
  | Names.PInt        => NMConversionForm (IntegerForm Integer.Int)
  | Names.PInt8       => NMConversionForm (IntegerForm Integer.Int8)
  | Names.PInt16      => NMConversionForm (IntegerForm Integer.Int16)
  | Names.PInt32      => NMConversionForm (IntegerForm Integer.Int32)
  | Names.PInt64      => NMConversionForm (IntegerForm Integer.Int64)
  | Names.PUint       => NMConversionForm (IntegerForm Integer.Uint)
  | Names.PUint8      => NMConversionForm (IntegerForm Integer.Uint8)
  | Names.PUint16     => NMConversionForm (IntegerForm Integer.Uint16)
  | Names.PUint32     => NMConversionForm (IntegerForm Integer.Uint32)
  | Names.PUint64     => NMConversionForm (IntegerForm Integer.Uint64)
  | Names.PByte       => NMConversionForm (IntegerForm Integer.Uint8)
  | Names.PRune       => NMConversionForm (IntegerForm Integer.Int32)
  | Names.PFloat32    => NMConversionForm (FloatForm Float.F32)
  | Names.PFloat64    => NMConversionForm (FloatForm Float.F64)
  | Names.PComplex64  => NMConversionForm (ComplexForm Complex.C64)
  | Names.PComplex128 => NMConversionForm (ComplexForm Complex.C128)
  | Names.PTrue       => NMValueConstant (CBool true)
  | Names.PFalse      => NMValueConstant (CBool false)
  | _                 => NMNoFormMeaning
  end.

(* A mismatched or out-of-range typed constant cannot be constructed at all. *)
Fail Definition mismatch_string_carrying_int : TypedConstant StringForm := TCInt Integer.Int 3 eq_refl.
Fail Definition mismatch_int_out_of_range : TypedConstant (IntegerForm Integer.Int8) := TCInt Integer.Int8 128 eq_refl.
Fail Definition mismatch_float_carrying_bool : TypedConstant (FloatForm Float.F64) := TCBool true.
