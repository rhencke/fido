From Stdlib Require Import NArith ZArith List Bool String Ascii Lia Eqdep_dec.
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

(* Conversion is total with five constructor-disjoint outcomes; every failure retains the exact source ConstantInfo. *)
Inductive ConversionResult (target : TypeForm) : Type :=
| Converted        : TypedConstant target -> ConversionResult target
| Overflows        : ConstantInfo -> ConversionResult target
| NotRepresentable : ConstantInfo -> ConversionResult target
| InvalidForm      : ConstantInfo -> ConversionResult target
| Unmet            : ConstantInfo -> ConversionResult target.
Arguments Converted {target} _.
Arguments Overflows {target} _.
Arguments NotRepresentable {target} _.
Arguments InvalidForm {target} _.
Arguments Unmet {target} _.

(* Overflows is a range failure, NotRepresentable a value outside the target domain, InvalidForm a wrong source form *)
Definition numeric_source (c : Constant) : bool :=
  match c with CInt _ | CFloat _ | CComplex _ => true | _ => false end.

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

(* Integer-to-string conversion: the UTF-8 bytes of code point z when z is a Unicode scalar value, else U+FFFD. *)
Definition unicode_scalarb (z : Z) : bool :=
  (0 <=? z) && (z <=? 0x10FFFF) && negb ((0xD800 <=? z) && (z <=? 0xDFFF)).
Definition UnicodeScalar (z : Z) : Prop := unicode_scalarb z = true.

Lemma unicode_scalar_iff : forall z, UnicodeScalar z <-> (0 <= z <= 0x10FFFF /\ ~ (0xD800 <= z <= 0xDFFF)).
Proof.
  intro z; unfold UnicodeScalar, unicode_scalarb; split.
  - intro H. apply andb_true_iff in H; destruct H as [H H3]. apply andb_true_iff in H; destruct H as [H1 H2].
    apply Z.leb_le in H1; apply Z.leb_le in H2. apply negb_true_iff, andb_false_iff in H3.
    split; [ split; assumption | intros [H4 H5] ].
    destruct H3 as [H3 | H3]; apply Z.leb_gt in H3; lia.
  - intros [[H1 H2] H3]. apply andb_true_iff; split; [ apply andb_true_iff; split; apply Z.leb_le; assumption | ].
    apply negb_true_iff, andb_false_iff.
    destruct (Z_lt_le_dec z 0xD800) as [H4 | H4]; [ left; apply Z.leb_gt; exact H4 | right; apply Z.leb_gt ].
    destruct (Z_lt_le_dec 0xDFFF z) as [H5 | H5]; [ exact H5 | exfalso; apply H3; split; assumption ].
Qed.

Definition utf8_replacement : list Z := [0xEF; 0xBF; 0xBD].

Definition utf8_bytes_scalar (z : Z) : list Z :=
  if z <=? 0x7F then [z]
  else if z <=? 0x7FF then [0xC0 + z / 64; 0x80 + z mod 64]
  else if z <=? 0xFFFF then [0xE0 + z / 4096; 0x80 + (z / 64) mod 64; 0x80 + z mod 64]
  else [0xF0 + z / 262144; 0x80 + (z / 4096) mod 64; 0x80 + (z / 64) mod 64; 0x80 + z mod 64].

Definition utf8_bytes (z : Z) : list Z := if unicode_scalarb z then utf8_bytes_scalar z else utf8_replacement.

Definition string_of_bytes (bs : list Z) : string :=
  fold_right (fun b s => String (Ascii.ascii_of_N (Z.to_N b)) s) EmptyString bs.

Definition utf8_string_of_Z (z : Z) : string := string_of_bytes (utf8_bytes z).

(* The UTF-8 specification read from the byte side: a well-formed sequence fixes its code point arithmetically. *)
Inductive Utf8Encoding : Z -> list Z -> Prop :=
| Utf8One : forall cp, 0 <= cp <= 0x7F -> Utf8Encoding cp [cp]
| Utf8Two : forall cp b0 b1,
    0xC0 <= b0 <= 0xDF -> 0x80 <= b1 <= 0xBF ->
    cp = (b0 - 0xC0) * 64 + (b1 - 0x80) -> 0x80 <= cp <= 0x7FF ->
    Utf8Encoding cp [b0; b1]
| Utf8Three : forall cp b0 b1 b2,
    0xE0 <= b0 <= 0xEF -> 0x80 <= b1 <= 0xBF -> 0x80 <= b2 <= 0xBF ->
    cp = (b0 - 0xE0) * 4096 + (b1 - 0x80) * 64 + (b2 - 0x80) ->
    0x800 <= cp <= 0xFFFF -> ~ (0xD800 <= cp <= 0xDFFF) ->
    Utf8Encoding cp [b0; b1; b2]
| Utf8Four : forall cp b0 b1 b2 b3,
    0xF0 <= b0 <= 0xF7 -> 0x80 <= b1 <= 0xBF -> 0x80 <= b2 <= 0xBF -> 0x80 <= b3 <= 0xBF ->
    cp = (b0 - 0xF0) * 262144 + (b1 - 0x80) * 4096 + (b2 - 0x80) * 64 + (b3 - 0x80) ->
    0x10000 <= cp <= 0x10FFFF ->
    Utf8Encoding cp [b0; b1; b2; b3].

Definition utf8_continuationb (b : Z) : bool := (0x80 <=? b) && (b <=? 0xBF).

(* A decoded value survives only as a Unicode scalar value at or above its shortest form's lower bound. *)
Definition utf8_scalar_from (lo cp : Z) : option Z :=
  if (lo <=? cp) && unicode_scalarb cp then Some cp else None.

(* Exactly one complete well-formed sequence decodes; any other shape, length or continuation byte is None. *)
Definition utf8_decode (bs : list Z) : option Z :=
  match bs with
  | [b0] => if (0 <=? b0) && (b0 <=? 0x7F) then Some b0 else None
  | [b0; b1] =>
      if (0xC2 <=? b0) && (b0 <=? 0xDF) && utf8_continuationb b1
      then Some ((b0 - 0xC0) * 64 + (b1 - 0x80)) else None
  | [b0; b1; b2] =>
      if (0xE0 <=? b0) && (b0 <=? 0xEF) && utf8_continuationb b1 && utf8_continuationb b2
      then utf8_scalar_from 0x800 ((b0 - 0xE0) * 4096 + (b1 - 0x80) * 64 + (b2 - 0x80)) else None
  | [b0; b1; b2; b3] =>
      if (0xF0 <=? b0) && (b0 <=? 0xF4) && utf8_continuationb b1 && utf8_continuationb b2
         && utf8_continuationb b3
      then utf8_scalar_from 0x10000
             ((b0 - 0xF0) * 262144 + (b1 - 0x80) * 4096 + (b2 - 0x80) * 64 + (b3 - 0x80))
      else None
  | _ => None
  end.

Ltac utf8_bools :=
  repeat match goal with
  | [ H : (_ && _) = true |- _ ] => apply andb_true_iff in H; destruct H
  | [ H : (_ <=? _) = true |- _ ] => apply Z.leb_le in H
  end.
Ltac utf8_branch H E :=
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:E end;
  [ try rewrite E in H; cbv iota in H | try rewrite E in H; discriminate ].
Ltac utf8_leb := match goal with |- context [?a <=? ?b] => destruct (Z.leb_spec a b); [ | lia ] end.

Lemma utf8_scalar_from_some : forall lo cp v,
  utf8_scalar_from lo cp = Some v -> v = cp /\ lo <= cp /\ UnicodeScalar cp.
Proof.
  intros lo cp v H; unfold utf8_scalar_from in H; utf8_branch H E.
  injection H as H; subst v. apply andb_true_iff in E; destruct E as [E1 E2]; apply Z.leb_le in E1.
  split; [ reflexivity | split; [ exact E1 | exact E2 ] ].
Qed.

Lemma utf8_scalar_from_scalar : forall lo cp, lo <= cp -> UnicodeScalar cp -> utf8_scalar_from lo cp = Some cp.
Proof.
  intros lo cp Hlo Hsc; unfold utf8_scalar_from, UnicodeScalar in *.
  rewrite Hsc, (proj2 (Z.leb_le lo cp) Hlo). reflexivity.
Qed.

Lemma utf8_div_64_64 : forall z, z / 64 / 64 = z / 4096.
Proof. intro z; rewrite Z.div_div by lia; reflexivity. Qed.
Lemma utf8_div_4096_64 : forall z, z / 4096 / 64 = z / 262144.
Proof. intro z; rewrite Z.div_div by lia; reflexivity. Qed.

Lemma utf8_digits : forall z,
  z = 64 * (z / 64) + z mod 64
  /\ z / 64 = 64 * (z / 4096) + (z / 64) mod 64
  /\ z / 4096 = 64 * (z / 262144) + (z / 4096) mod 64
  /\ 0 <= z mod 64 < 64 /\ 0 <= (z / 64) mod 64 < 64 /\ 0 <= (z / 4096) mod 64 < 64.
Proof.
  intro z.
  pose proof (Z.div_mod z 64 ltac:(lia)) as H1.
  pose proof (Z.div_mod (z / 64) 64 ltac:(lia)) as H2.
  pose proof (Z.div_mod (z / 4096) 64 ltac:(lia)) as H3.
  rewrite utf8_div_64_64 in H2. rewrite utf8_div_4096_64 in H3.
  pose proof (Z.mod_pos_bound z 64 ltac:(lia)) as [B1 B1'].
  pose proof (Z.mod_pos_bound (z / 64) 64 ltac:(lia)) as [B2 B2'].
  pose proof (Z.mod_pos_bound (z / 4096) 64 ltac:(lia)) as [B3 B3'].
  repeat split; lia.
Qed.

Lemma utf8_bytes_one : forall z, z <= 0x7F -> utf8_bytes_scalar z = [z].
Proof. intros z H; unfold utf8_bytes_scalar; rewrite (proj2 (Z.leb_le z 0x7F) H); reflexivity. Qed.

Lemma utf8_bytes_two : forall z, 0x7F < z -> z <= 0x7FF -> utf8_bytes_scalar z = [0xC0 + z / 64; 0x80 + z mod 64].
Proof.
  intros z H1 H2; unfold utf8_bytes_scalar.
  rewrite (proj2 (Z.leb_gt z 0x7F) H1), (proj2 (Z.leb_le z 0x7FF) H2); reflexivity.
Qed.

Lemma utf8_bytes_three : forall z, 0x7FF < z -> z <= 0xFFFF ->
  utf8_bytes_scalar z = [0xE0 + z / 4096; 0x80 + (z / 64) mod 64; 0x80 + z mod 64].
Proof.
  intros z H1 H2; unfold utf8_bytes_scalar.
  rewrite (proj2 (Z.leb_gt z 0x7F) ltac:(lia)), (proj2 (Z.leb_gt z 0x7FF) H1), (proj2 (Z.leb_le z 0xFFFF) H2).
  reflexivity.
Qed.

Lemma utf8_bytes_four : forall z, 0xFFFF < z ->
  utf8_bytes_scalar z = [0xF0 + z / 262144; 0x80 + (z / 4096) mod 64; 0x80 + (z / 64) mod 64; 0x80 + z mod 64].
Proof.
  intros z H; unfold utf8_bytes_scalar.
  rewrite (proj2 (Z.leb_gt z 0x7F) ltac:(lia)), (proj2 (Z.leb_gt z 0x7FF) ltac:(lia)), (proj2 (Z.leb_gt z 0xFFFF) H).
  reflexivity.
Qed.

Lemma utf8_bytes_non_scalar : forall z, ~ UnicodeScalar z -> utf8_bytes z = utf8_replacement.
Proof.
  intros z H; unfold utf8_bytes; destruct (unicode_scalarb z) eqn:E; [ exfalso; apply H; exact E | reflexivity ].
Qed.

Lemma utf8_bytes_scalar_spec : forall z, UnicodeScalar z -> Utf8Encoding z (utf8_bytes z).
Proof.
  intros z Hz; pose proof Hz as Hb; unfold UnicodeScalar in Hb.
  apply unicode_scalar_iff in Hz; destruct Hz as [[Hlo Hhi] Hsur].
  unfold utf8_bytes; rewrite Hb.
  pose proof (utf8_digits z) as (D1 & D2 & D3 & [B1 B1'] & [B2 B2'] & [B3 B3']).
  destruct (Z_lt_le_dec 0x7F z) as [H1 | H1]; [ | rewrite utf8_bytes_one by lia; apply Utf8One; split; lia ].
  destruct (Z_lt_le_dec 0x7FF z) as [H2 | H2]; [ | rewrite utf8_bytes_two by lia; apply Utf8Two; repeat split; lia ].
  destruct (Z_lt_le_dec 0xFFFF z) as [H3 | H3].
  - rewrite utf8_bytes_four by lia; apply Utf8Four; repeat split; lia.
  - rewrite utf8_bytes_three by lia; apply Utf8Three; try exact Hsur; repeat split; lia.
Qed.

Lemma utf8_decode_sound : forall bs cp, utf8_decode bs = Some cp -> Utf8Encoding cp bs.
Proof.
  intros bs cp H.
  destruct bs as [| b0 [| b1 [| b2 [| b3 [| b4 r]]]]]; unfold utf8_decode, utf8_continuationb in H;
    try discriminate; utf8_branch H E.
  - injection H as H; subst cp. utf8_bools. apply Utf8One; split; lia.
  - injection H as H; subst cp. utf8_bools. apply Utf8Two; repeat split; lia.
  - apply utf8_scalar_from_some in H; destruct H as [-> [Hlo Hsc]].
    apply unicode_scalar_iff in Hsc; destruct Hsc as [[_ Hhi] Hsur].
    utf8_bools. apply Utf8Three; try exact Hsur; repeat split; lia.
  - apply utf8_scalar_from_some in H; destruct H as [-> [Hlo Hsc]].
    apply unicode_scalar_iff in Hsc; destruct Hsc as [[_ Hhi] Hsur].
    utf8_bools. apply Utf8Four; repeat split; lia.
Qed.

Lemma utf8_decode_complete : forall cp bs, Utf8Encoding cp bs -> utf8_decode bs = Some cp.
Proof.
  intros cp bs Henc.
  destruct Henc as [ c [Hl Hh] | c b0 b1 [H0l H0h] [H1l H1h] Heq [Hl Hh]
                   | c b0 b1 b2 [H0l H0h] [H1l H1h] [H2l H2h] Heq [Hl Hh] Hsur
                   | c b0 b1 b2 b3 [H0l H0h] [H1l H1h] [H2l H2h] [H3l H3h] Heq [Hl Hh] ];
    subst; unfold utf8_decode, utf8_continuationb.
  - repeat utf8_leb; reflexivity.
  - repeat utf8_leb; reflexivity.
  - rewrite utf8_scalar_from_scalar by first [ lia | apply unicode_scalar_iff; split; [ split; lia | exact Hsur ] ].
    repeat utf8_leb; reflexivity.
  - rewrite utf8_scalar_from_scalar
      by first [ lia | apply unicode_scalar_iff; split; [ split; lia | intros [Hc1 Hc2]; lia ] ].
    repeat utf8_leb; reflexivity.
Qed.

Lemma utf8_decode_encode : forall z, UnicodeScalar z -> utf8_decode (utf8_bytes z) = Some z.
Proof. intros z Hz; apply utf8_decode_complete, utf8_bytes_scalar_spec, Hz. Qed.

Lemma utf8_encoding_scalar : forall cp bs, Utf8Encoding cp bs -> UnicodeScalar cp.
Proof.
  intros cp bs Henc; apply unicode_scalar_iff.
  destruct Henc as [ c [Hl Hh] | c b0 b1 _ _ _ [Hl Hh] | c b0 b1 b2 _ _ _ _ [Hl Hh] Hsur
                   | c b0 b1 b2 b3 _ _ _ _ _ [Hl Hh] ].
  - split; [ split; lia | intros [Hc1 Hc2]; lia ].
  - split; [ split; lia | intros [Hc1 Hc2]; lia ].
  - split; [ split; lia | exact Hsur ].
  - split; [ split; lia | intros [Hc1 Hc2]; lia ].
Qed.

Lemma utf8_bytes_length : forall z, UnicodeScalar z ->
  List.length (utf8_bytes z)
  = (if (z <=? 0x7F)%Z then 1 else if (z <=? 0x7FF)%Z then 2 else if (z <=? 0xFFFF)%Z then 3 else 4)%nat.
Proof.
  intros z Hz; unfold UnicodeScalar in Hz; unfold utf8_bytes, utf8_bytes_scalar; rewrite Hz.
  destruct (z <=? 0x7F); [ reflexivity | ].
  destruct (z <=? 0x7FF); [ reflexivity | ].
  destruct (z <=? 0xFFFF); reflexivity.
Qed.

Lemma utf8_bytes_range : forall z, Forall (fun b => 0 <= b <= 255) (utf8_bytes z).
Proof.
  intro z; unfold utf8_bytes, utf8_replacement; destruct (unicode_scalarb z) eqn:E; [ | repeat constructor; lia ].
  assert (Hs : UnicodeScalar z) by exact E.
  apply unicode_scalar_iff in Hs; destruct Hs as [[Hlo Hhi] _].
  pose proof (utf8_digits z) as (D1 & D2 & D3 & [B1 B1'] & [B2 B2'] & [B3 B3']).
  destruct (Z_lt_le_dec 0x7F z) as [H1 | H1]; [ | rewrite utf8_bytes_one by lia; repeat constructor; lia ].
  destruct (Z_lt_le_dec 0x7FF z) as [H2 | H2]; [ | rewrite utf8_bytes_two by lia; repeat constructor; lia ].
  destruct (Z_lt_le_dec 0xFFFF z) as [H3 | H3];
    [ rewrite utf8_bytes_four by lia | rewrite utf8_bytes_three by lia ]; repeat constructor; lia.
Qed.

Lemma utf8_replacement_decodes : utf8_decode utf8_replacement = Some 0xFFFD.
Proof. vm_compute; reflexivity. Qed.

Lemma utf8_bytes_injective : forall a b, UnicodeScalar a -> UnicodeScalar b -> utf8_bytes a = utf8_bytes b -> a = b.
Proof.
  intros a b Ha Hb Heq.
  pose proof (utf8_decode_encode a Ha) as Da; pose proof (utf8_decode_encode b Hb) as Db.
  rewrite Heq, Db in Da. injection Da as Da. symmetry; exact Da.
Qed.

Example utf8_ex_0000 : utf8_bytes 0 = [0]. Proof. vm_compute; reflexivity. Qed.
Example utf8_ex_007F : utf8_bytes 0x7F = [0x7F]. Proof. vm_compute; reflexivity. Qed.
Example utf8_ex_0080 : utf8_bytes 0x80 = [0xC2; 0x80]. Proof. vm_compute; reflexivity. Qed.
Example utf8_ex_07FF : utf8_bytes 0x7FF = [0xDF; 0xBF]. Proof. vm_compute; reflexivity. Qed.
Example utf8_ex_0800 : utf8_bytes 0x800 = [0xE0; 0xA0; 0x80]. Proof. vm_compute; reflexivity. Qed.
Example utf8_ex_D7FF : utf8_bytes 0xD7FF = [0xED; 0x9F; 0xBF]. Proof. vm_compute; reflexivity. Qed.
Example utf8_ex_E000 : utf8_bytes 0xE000 = [0xEE; 0x80; 0x80]. Proof. vm_compute; reflexivity. Qed.
Example utf8_ex_FFFF : utf8_bytes 0xFFFF = [0xEF; 0xBF; 0xBF]. Proof. vm_compute; reflexivity. Qed.
Example utf8_ex_10000 : utf8_bytes 0x10000 = [0xF0; 0x90; 0x80; 0x80]. Proof. vm_compute; reflexivity. Qed.
Example utf8_ex_10FFFF : utf8_bytes 0x10FFFF = [0xF4; 0x8F; 0xBF; 0xBF]. Proof. vm_compute; reflexivity. Qed.
Example utf8_ex_neg1 : utf8_bytes (-1) = [0xEF; 0xBF; 0xBD]. Proof. vm_compute; reflexivity. Qed.
Example utf8_ex_D800 : utf8_bytes 0xD800 = [0xEF; 0xBF; 0xBD]. Proof. vm_compute; reflexivity. Qed.
Example utf8_ex_DFFF : utf8_bytes 0xDFFF = [0xEF; 0xBF; 0xBD]. Proof. vm_compute; reflexivity. Qed.
Example utf8_ex_110000 : utf8_bytes 0x110000 = [0xEF; 0xBF; 0xBD]. Proof. vm_compute; reflexivity. Qed.

Definition convert_constant (target : TypeForm) (ci : ConstantInfo) : ConversionResult target :=
  let c := ci_const ci in
  let no_value := fun t : TypeForm => if numeric_source c then @NotRepresentable t ci else @InvalidForm t ci in
  match target with
  | BoolForm     => match c with CBool b   => Converted (TCBool b)   | _ => InvalidForm ci end
  | StringForm   => match c with
                    | CString s => Converted (TCString s)
                    | CInt z    => Converted (TCString (utf8_string_of_Z z))
                    | _         => InvalidForm ci
                    end
  | IntegerForm k =>
      match int_value c with
      | Some z => match bool_true_dec (Integer.representableb k z) with
                  | left H  => Converted (TCInt k z H)
                  | right _ => Overflows ci
                  end
      | None => no_value _
      end
  | FloatForm k =>
      match float_value c with
      | Some q => match round_typed_float k q with
                  | Some v => Converted (TCFloat k v)
                  | None   => Overflows ci
                  end
      | None => no_value _
      end
  | ComplexForm k =>
      match complex_value c with
      | Some cc => match Complex.round_typed k cc with
                   | Some v => Converted (TCComplex k v)
                   | None   => Overflows ci
                   end
      | None => no_value _
      end
  end.

(* A failed conversion carries the exact offending ConstantInfo, so every failure names the real value and its flag. *)
Lemma convert_total_exact : forall target ci,
  (forall ci', convert_constant target ci = Overflows ci' -> ci' = ci)
  /\ (forall ci', convert_constant target ci = NotRepresentable ci' -> ci' = ci)
  /\ (forall ci', convert_constant target ci = InvalidForm ci' -> ci' = ci)
  /\ (forall ci', convert_constant target ci = Unmet ci' -> ci' = ci).
Proof.
  intros target ci; repeat split; intros ci' H; unfold convert_constant in H; destruct target;
    repeat (match goal with
            | [ H : context[match ?x with _ => _ end] |- _ ] => destruct x eqn:?
            end); try discriminate; injection H as <-; reflexivity.
Qed.

(* No represented source form is a valid conversion whose rule is absent: the Unmet boundary has no producer today. *)
Lemma convert_never_unmet : forall target ci ci', convert_constant target ci <> Unmet ci'.
Proof.
  intros target ci ci' H; unfold convert_constant in H; destruct target;
    repeat (match goal with
            | [ H : context[match ?x with _ => _ end] |- _ ] => destruct x eqn:?
            end); discriminate.
Qed.

(* The three failure cases are constructor-disjoint: the NotRepresentable/InvalidForm split follows the source form. *)
Lemma convert_no_value_form : forall target ci ci',
  (convert_constant target ci = NotRepresentable ci' -> numeric_source (ci_const ci) = true)
  /\ (convert_constant target ci = InvalidForm ci' -> numeric_source (ci_const ci) = false \/ target = BoolForm \/ target = StringForm).
Proof.
  intros target ci ci'; split; intro H; unfold convert_constant in H; destruct target;
    repeat (match goal with
            | [ H : context[match ?x with _ => _ end] |- _ ] => destruct x eqn:?
            end); try discriminate; auto.
Qed.

Lemma convert_int_to_string : forall ci z,
  ci_const ci = CInt z -> convert_constant StringForm ci = Converted (TCString (utf8_string_of_Z z)).
Proof. intros ci z H; unfold convert_constant; rewrite H; reflexivity. Qed.

Lemma convert_string_identity : forall ci s,
  ci_const ci = CString s -> convert_constant StringForm ci = Converted (TCString s).
Proof. intros ci s H; unfold convert_constant; rewrite H; reflexivity. Qed.

Definition constant_representableb (target : TypeForm) (c : Constant) : bool :=
  match convert_constant target (mk_cinfo c Untyped) with Converted _ => true | _ => false end.

Definition ConstantRepresentable (target : TypeForm) (c : Constant) : Prop :=
  constant_representableb target c = true.

Lemma representable_iff_converted : forall target c,
  ConstantRepresentable target c <-> exists tc, convert_constant target (mk_cinfo c Untyped) = Converted tc.
Proof.
  intros target c; unfold ConstantRepresentable, constant_representableb.
  destruct (convert_constant target (mk_cinfo c Untyped)) as [tc| | | |] eqn:E; split.
  - intros _; exists tc; reflexivity.
  - intros _; reflexivity.
  - discriminate.
  - intros [tc H]; discriminate.
  - discriminate.
  - intros [tc H]; discriminate.
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

(* Negation is an involution: the exact negated constant negates back to the exact source on every numeric form. *)
Lemma float_constant_neg_involutive : forall q, float_constant_neg (float_constant_neg q) = q.
Proof.
  intro q. destruct q as [n d Hc]. unfold float_constant_neg. cbn [Float.numerator Float.denominator].
  generalize (float_constant_neg_canonical (Float.MakeConstant (- n) d (float_constant_neg_canonical (Float.MakeConstant n d Hc)))).
  cbn [Float.numerator Float.denominator]. rewrite Z.opp_involutive. intro H'. f_equal. apply (UIP_dec Bool.bool_dec).
Qed.
Lemma constant_neg_involutive : forall c c', constant_neg c = Some c' -> constant_neg c' = Some c.
Proof.
  intros c c' H. destruct c; cbn in H; try discriminate H; injection H as H; subst c'; cbn.
  - rewrite Z.opp_involutive. reflexivity.
  - rewrite float_constant_neg_involutive. reflexivity.
  - match goal with cc : Complex.Constant |- _ => destruct cc as [re im] end.
    cbn [Complex.exact_real Complex.exact_imaginary]. rewrite !float_constant_neg_involutive. reflexivity.
Qed.

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
