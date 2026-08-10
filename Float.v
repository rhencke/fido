From Stdlib Require Import ZArith String.
From Stdlib Require Import Lia Znumtheory Eqdep_dec.
From Stdlib Require Import Floats.SpecFloat.
Open Scope Z_scope.

Inductive Kind := F32 | F64.

Definition kind_equalb (a b : Kind) : bool :=
  match a, b with F32, F32 => true | F64, F64 => true | _, _ => false end.

Lemma kind_equalb_spec : forall a b, kind_equalb a b = true <-> a = b.
Proof. intros [] []; simpl; split; congruence. Qed.

(* binary32 is (prec 24, emax 128) and binary64 is (prec 53, emax 1024), the two pairs SpecFloat takes. *)
Definition precision (ft : Kind) : Z := match ft with F32 => 24 | F64 => 53 end.
Definition maximum_exponent (ft : Kind) : Z := match ft with F32 => 128 | F64 => 1024 end.

Lemma precision_f32 : precision F32 = 24.   Proof. reflexivity. Qed.
Lemma precision_f64 : precision F64 = 53.   Proof. reflexivity. Qed.
Lemma maximum_exponent_f32 : maximum_exponent F32 = 128.  Proof. reflexivity. Qed.
Lemma maximum_exponent_f64 : maximum_exponent F64 = 1024. Proof. reflexivity. Qed.

(* An exact rational in lowest terms by construction, so a non-reduced fraction such as 2/4 has no value. *)
Record Constant := MakeConstant {
  numerator : Z ;
  denominator : positive ;
  canonical  : (Z.gcd numerator (Zpos denominator) =? 1) = true
}.

Lemma gcd_z_1 : forall z, (Z.gcd z 1 =? 1) = true.
Proof. intro z; apply Z.eqb_eq; apply Z.gcd_1_r. Qed.

Definition constant_of_Z (z : Z) : Constant := MakeConstant z 1 (gcd_z_1 z).

Definition constant_zero : Constant := constant_of_Z 0.

(* An exact integer embedded as a mantissa fed only to [SFdiv], which normalizes it. *)
Definition ieee_of_Z (z : Z) : spec_float :=
  match z with
  | Z0     => S754_zero false
  | Zpos p => S754_finite false p 0
  | Zneg p => S754_finite true  p 0
  end.

Definition round_ieee (ft : Kind) (a : Constant) : spec_float :=
  SFdiv (precision ft) (maximum_exponent ft) (ieee_of_Z (numerator a)) (ieee_of_Z (Zpos (denominator a))).

Definition cond_Zopp (s : bool) (m : Z) : Z := if s then Z.opp m else m.

Definition ieee_to_Z (v : spec_float) : option Z :=
  match v with
  | S754_zero _ => Some 0
  | S754_finite s m e =>
      let n := cond_Zopp s (Zpos m) in
      if Z.leb 0 e then Some (n * 2 ^ e)               (* integer by construction *)
      else let d := 2 ^ (- e) in                       (* dyadic n*2^e; integer iff 2^(-e) | n *)
           if Z.eqb (n mod d) 0 then Some (n / d) else None
  | _ => None
  end.

(* A double-rounding witness: direct binary32 rounds up where binary64-then-binary32 rounds to even, down. *)
Definition single_rounding_x : Constant := constant_of_Z 2305843146652647425.

Example single_rounding_direct_f32 :
  ieee_to_Z (round_ieee F32 single_rounding_x) = Some 2305843284091600896.
Proof. reflexivity. Qed.

Example single_rounding_double_f32_via_f64 :
  ieee_to_Z (SFdiv 24 128 (round_ieee F64 single_rounding_x) (ieee_of_Z 1)) = Some 2305843009213693952.
Proof. reflexivity. Qed.

Example single_rounding_direct_differs_double :
  round_ieee F32 single_rounding_x <> SFdiv 24 128 (round_ieee F64 single_rounding_x) (ieee_of_Z 1).
Proof. discriminate. Qed.

Example round_f32_2p24_plus1 :
  ieee_to_Z (round_ieee F32 (constant_of_Z 16777217)) = Some 16777216.
Proof. reflexivity. Qed.

Example round_f64_2p53_plus1 :
  ieee_to_Z (round_ieee F64 (constant_of_Z 9007199254740993)) = Some 9007199254740992.
Proof. reflexivity. Qed.

Example round_f32_exact_small : ieee_to_Z (round_ieee F32 (constant_of_Z 3)) = Some 3. Proof. reflexivity. Qed.
Example round_f64_exact_small : ieee_to_Z (round_ieee F64 (constant_of_Z 42)) = Some 42. Proof. reflexivity. Qed.


Definition constant_canonical (a : Constant) : Prop :=
  Z.gcd (numerator a) (Zpos (denominator a)) = 1.

Definition constant_eq (a b : Constant) : Prop :=
  numerator a * Zpos (denominator b) = numerator b * Zpos (denominator a).

Definition constant_equalb (a b : Constant) : bool :=
  Z.eqb (numerator a * Zpos (denominator b)) (numerator b * Zpos (denominator a)).

Lemma constant_equalb_spec : forall a b, constant_equalb a b = true <-> constant_eq a b.
Proof. intros a b; unfold constant_equalb, constant_eq; apply Z.eqb_eq. Qed.

Lemma constant_of_Z_canonical : forall z, constant_canonical (constant_of_Z z).
Proof. intro z; unfold constant_canonical, constant_of_Z; cbn [numerator denominator]; apply Z.gcd_1_r. Qed.

Lemma constant_zero_canonical : constant_canonical constant_zero.
Proof. apply constant_of_Z_canonical. Qed.

Lemma constant_canonical_intrinsic : forall a, constant_canonical a.
Proof. intro a; unfold constant_canonical; apply Z.eqb_eq; exact (canonical a). Qed.

Lemma numerator_denominator_eq : forall a b, numerator a = numerator b -> denominator a = denominator b -> a = b.
Proof.
  intros [na da wa] [nb db wb] Hn Hd; cbn in Hn, Hd; subst nb db.
  f_equal. apply (UIP_dec Bool.bool_dec).
Qed.

Lemma gcd_den_pos : forall (n : Z) (d : positive), 0 < Z.gcd n (Zpos d).
Proof.
  intros n d.
  assert (H0 : Z.gcd n (Zpos d) <> 0).
  { intro H. apply Z.gcd_eq_0 in H. destruct H as [_ H]. discriminate. }
  pose proof (Z.gcd_nonneg n (Zpos d)). lia.
Qed.

Lemma reduce_den_pos : forall (n : Z) (d : positive), 0 < Zpos d / Z.gcd n (Zpos d).
Proof.
  intros n d. pose proof (gcd_den_pos n d) as Hg.
  pose proof (Z.gcd_divide_r n (Zpos d)) as Hdiv.
  pose proof (Zdivide_Zdiv_eq _ _ Hg Hdiv) as Heq.
  assert (0 < Zpos d) by (apply Pos2Z.is_pos). nia.
Qed.

Lemma reduce_zpos : forall (n : Z) (d : positive),
  Zpos (Z.to_pos (Zpos d / Z.gcd n (Zpos d))) = Zpos d / Z.gcd n (Zpos d).
Proof. intros; apply Z2Pos.id; apply reduce_den_pos. Qed.

Lemma reduce_well_formed : forall n d,
  (Z.gcd (n / Z.gcd n (Zpos d)) (Zpos (Z.to_pos (Zpos d / Z.gcd n (Zpos d)))) =? 1) = true.
Proof.
  intros n d; apply Z.eqb_eq. rewrite reduce_zpos.
  apply Z.gcd_div_gcd; [ pose proof (gcd_den_pos n d); lia | reflexivity ].
Qed.

Definition reduce_constant (n : Z) (d : positive) : Constant :=
  MakeConstant (n / Z.gcd n (Zpos d)) (Z.to_pos (Zpos d / Z.gcd n (Zpos d))) (reduce_well_formed n d).

Lemma reduce_constant_canonical : forall n d, constant_canonical (reduce_constant n d).
Proof. intros; apply constant_canonical_intrinsic. Qed.

Lemma reduce_constant_eq : forall n d,
  numerator (reduce_constant n d) * Zpos d = n * Zpos (denominator (reduce_constant n d)).
Proof.
  intros n d. cbn [numerator denominator reduce_constant].
  rewrite reduce_zpos.
  remember (Z.gcd n (Zpos d)) as g eqn:Hgdef.
  assert (Hgpos : 0 < g) by (rewrite Hgdef; apply gcd_den_pos).
  assert (Hn : n = g * (n / g))
    by (apply Zdivide_Zdiv_eq; [ exact Hgpos | rewrite Hgdef; apply Z.gcd_divide_l ]).
  assert (Hd : Zpos d = g * (Zpos d / g))
    by (apply Zdivide_Zdiv_eq; [ exact Hgpos | rewrite Hgdef; apply Z.gcd_divide_r ]).
  rewrite Hn at 2. rewrite Hd at 1. ring.
Qed.

(* Every constant is in lowest terms, so rational equality is Leibniz equality. *)
Lemma constant_canonical_unique : forall a b, constant_eq a b -> a = b.
Proof.
  intros [na da wa] [nb db wb] Heq.
  assert (Ha : Z.gcd na (Zpos da) = 1) by (apply Z.eqb_eq; exact wa).
  assert (Hb : Z.gcd nb (Zpos db) = 1) by (apply Z.eqb_eq; exact wb).
  unfold constant_eq in Heq; cbn [numerator denominator] in Heq.
  (* [constant_canonical] IS [Z.coprime]; a coprime divisor of a product divides the other factor (Gauss). *)
  assert (Hcpa : Z.coprime (Zpos da) na) by (apply Z.Symmetric_coprime; exact Ha).
  assert (Hcpb : Z.coprime (Zpos db) nb) by (apply Z.Symmetric_coprime; exact Hb).
  assert (Hda_dvd : (Zpos da | Zpos db)).
  { apply Z.gauss with (m := na); [ rewrite Heq; exists nb; ring | exact Hcpa ]. }
  assert (Hdb_dvd : (Zpos db | Zpos da)).
  { apply Z.gauss with (m := nb); [ rewrite <- Heq; exists na; ring | exact Hcpb ]. }
  assert (Hle1 : Zpos da <= Zpos db) by (apply Z.divide_pos_le; [ apply Pos2Z.is_pos | exact Hda_dvd ]).
  assert (Hle2 : Zpos db <= Zpos da) by (apply Z.divide_pos_le; [ apply Pos2Z.is_pos | exact Hdb_dvd ]).
  assert (Hdeq : da = db) by (apply Pos2Z.inj; lia).
  subst db.
  assert (na = nb) by (pose proof (Pos2Z.is_pos da); nia).
  subst nb. f_equal. apply (UIP_dec Bool.bool_dec).
Qed.

Lemma constant_equalb_eq : forall a b, constant_equalb a b = true <-> a = b.
Proof.
  intros a b; split.
  - intro H; apply constant_canonical_unique, constant_equalb_spec; exact H.
  - intro H; subst b; unfold constant_equalb; apply Z.eqb_eq; reflexivity.
Qed.

(* A rounded [spec_float] back to an exact constant; an infinity or a NaN has no exact constant. *)
Definition ieee_to_constant (v : spec_float) : option Constant :=
  match v with
  | S754_zero _ => Some constant_zero
  | S754_finite s m e =>
      let n := cond_Zopp s (Zpos m) in
      if Z.leb 0 e then Some (constant_of_Z (n * 2 ^ e))
      else Some (reduce_constant n (Z.to_pos (2 ^ (- e))))
  | _ => None
  end.

Definition decimal_max_coeff : Z := 10 ^ 40.   (* |coeff| < 10^40  (<= 40 significant digits) *)
Definition decimal_max_exp   : Z := 4096.

(* Canonical: zero is exactly (0,0), and a nonzero coefficient has no removable factor of ten. *)
Definition decimal_canonicalb (c e : Z) : bool :=
  if Z.eqb c 0 then Z.eqb e 0 else negb (Z.eqb (Z.rem c 10) 0).

Definition decimal_wfb (c e : Z) : bool :=
  decimal_canonicalb c e
  && (Z.abs c <? decimal_max_coeff)
  && (- decimal_max_exp <=? e) && (e <=? decimal_max_exp).

Record Decimal := MakeDecimal {
  coefficient : Z ;
  exponent : Z ;
  canonical_decimal    : decimal_wfb coefficient exponent = true
}.

Definition decimal_equalb (a b : Decimal) : bool :=
  Z.eqb (coefficient a) (coefficient b) && Z.eqb (exponent a) (exponent b).

Lemma decimal_equalb_spec : forall a b, decimal_equalb a b = true <-> a = b.
Proof.
  intros a b; unfold decimal_equalb; split.
  - intro H. apply Bool.andb_true_iff in H as [H1 H2].
    apply Z.eqb_eq in H1; apply Z.eqb_eq in H2.
    destruct a as [ca ea pa], b as [cb eb pb]; cbn in H1, H2; subst.
    f_equal. apply (UIP_dec Bool.bool_dec).
  - intro H; subst b. rewrite !Z.eqb_refl; reflexivity.
Qed.

(* The exact rational value of the literal, with no rounding: raw interpretation is exact. *)
Definition decimal_to_constant (coeff exp : Z) : Constant :=
  if 0 <=? exp then constant_of_Z (coeff * 10 ^ exp)
  else reduce_constant coeff (Z.to_pos (10 ^ (- exp))).

Definition decimal_value (d : Decimal) : Constant :=
  decimal_to_constant (coefficient d) (exponent d).

Lemma decimal_value_canonical : forall d, constant_canonical (decimal_value d).
Proof.
  intro d; unfold decimal_value, decimal_to_constant.
  destruct (0 <=? exponent d); [ apply constant_of_Z_canonical | apply reduce_constant_canonical ].
Qed.

(* The one zero literal; its value is unsigned, so there is no negative-zero decimal literal. *)
Definition decimal_zero : Decimal := MakeDecimal 0 0 eq_refl.

Lemma decimal_value_zero : decimal_value decimal_zero = constant_zero.
Proof. reflexivity. Qed.

Lemma decimal_zero_unique : forall d, coefficient d = 0 -> d = decimal_zero.
Proof.
  intro d. pose proof (canonical_decimal d) as Hwf. unfold decimal_wfb, decimal_canonicalb in Hwf.
  intro Hc. rewrite Hc in Hwf. cbn in Hwf.
  apply Bool.andb_true_iff in Hwf as [Hwf _]. apply Bool.andb_true_iff in Hwf as [Hwf _].
  apply Bool.andb_true_iff in Hwf as [Hcan _]. apply Z.eqb_eq in Hcan.
  apply decimal_equalb_spec. unfold decimal_equalb, decimal_zero; cbn. rewrite Hc, Hcan; reflexivity.
Qed.

Example decimal_wfb_max_ok :
  decimal_wfb (decimal_max_coeff - 1) decimal_max_exp = true.
Proof. reflexivity. Qed.
Example decimal_wfb_coeff_over :
  decimal_wfb decimal_max_coeff 0 = false.
Proof. reflexivity. Qed.
Example decimal_wfb_exp_over :
  decimal_wfb 1 (decimal_max_exp + 1) = false.
Proof. reflexivity. Qed.
Example decimal_wfb_trailing_zero_noncanon :
  decimal_wfb 250 0 = false.               (* 250 has a removable factor of ten -> not canonical *)
Proof. reflexivity. Qed.
Example decimal_value_1p5 :                                        (* 15 * 10^-1 = 3/2 *)
  numerator (decimal_value (MakeDecimal 15 (-1) eq_refl)) = 3
  /\ denominator (decimal_value (MakeDecimal 15 (-1) eq_refl)) = 2%positive.
Proof. split; reflexivity. Qed.
Example decimal_value_1e6 :
  decimal_value (MakeDecimal 1 6 eq_refl) = constant_of_Z 1000000.
Proof. reflexivity. Qed.
Example decimal_value_neg :                                       (* -15 * 10^-1 = -3/2 *)
  numerator (decimal_value (MakeDecimal (-15) (-1) eq_refl)) = -3
  /\ denominator (decimal_value (MakeDecimal (-15) (-1) eq_refl)) = 2%positive.
Proof. split; reflexivity. Qed.
Example decimal_value_tenth :                                     (* 1 * 10^-1 = 1/10 (the example) *)
  numerator (decimal_value (MakeDecimal 1 (-1) eq_refl)) = 1
  /\ denominator (decimal_value (MakeDecimal 1 (-1) eq_refl)) = 10%positive.
Proof. split; reflexivity. Qed.

(* Zero-sign normalization: a constant has no signed zero, so a zero result normalizes to positive zero. *)
Definition strip_neg_zero (v : spec_float) : spec_float :=
  match v with S754_zero _ => S754_zero false | x => x end.

(* A [sumor] decides the read-back once and carries its proof, so nothing downstream re-abstracts a motive. *)
Definition ieee_repr_dec (v : spec_float) :
  {r : Constant | ieee_to_constant v = Some r} + {ieee_to_constant v = None} :=
  match ieee_to_constant v as o
    return (ieee_to_constant v = o ->
            {r : Constant | ieee_to_constant v = Some r} + {ieee_to_constant v = None})
  with
  | Some r => fun H => inleft (exist _ r H)
  | None   => fun H => inright H
  end eq_refl.

(* A float typed constant is a purely static carrier of one rounding's exact rational and rounded representation. *)
Record TypedConstant (ft : Kind) : Type := MakeTypedConstant {
  exact    : Constant ;
  rounded  : spec_float ;
  formed   : exists q : Constant, rounded = strip_neg_zero (round_ieee ft q) ;
  coherent : ieee_to_constant rounded = Some exact
}.
Arguments MakeTypedConstant {ft} _ _ _ _.
Arguments exact {ft} _.
Arguments rounded {ft} _.
Arguments formed {ft} _.
Arguments coherent {ft} _.

(* The sole rounding-from-exact typed-float formation authority: round once at [ft], normalize zero, derive both. *)
Definition round_typed_float (ft : Kind) (q : Constant) : option (TypedConstant ft) :=
  let r0 := strip_neg_zero (round_ieee ft q) in
  match ieee_repr_dec r0 with
  | inleft (exist _ r Hr) => Some (MakeTypedConstant r r0 (ex_intro _ q eq_refl) Hr)
  | inright _             => None
  end.

(* A successful rounding retains exactly the destination-format rounded value as its representation. *)
Lemma round_typed_float_rounded : forall ft q tc,
  round_typed_float ft q = Some tc -> rounded tc = strip_neg_zero (round_ieee ft q).
Proof.
  intros ft q tc H. unfold round_typed_float in H.
  destruct (ieee_repr_dec (strip_neg_zero (round_ieee ft q))) as [[r Hr]|Hn];
    [ injection H as <-; reflexivity | discriminate ].
Qed.

(* The exact-rational rounding is the [exact] projection of the typed result, not a second rounding call. *)
Definition round_constant (ft : Kind) (a : Constant) : option Constant :=
  option_map exact (round_typed_float ft a).

Lemma round_constant_typed : forall ft q,
  round_constant ft q = option_map exact (round_typed_float ft q).
Proof. reflexivity. Qed.

Definition Representable (ft : Kind) (a : Constant) : Prop :=
  exists r, round_constant ft a = Some r.

Definition representableb (ft : Kind) (a : Constant) : bool :=
  match round_constant ft a with Some _ => true | None => false end.

Lemma representableb_spec :
  forall ft a, representableb ft a = true <-> Representable ft a.
Proof.
  intros ft a. unfold representableb, Representable.
  destruct (round_constant ft a) as [r|] eqn:E; split.
  - intros _; exists r; reflexivity.
  - intros _; reflexivity.
  - discriminate.
  - intros [r H]; discriminate.
Qed.

Lemma round_typed_float_representable : forall ft q,
  representableb ft q = true <-> exists tc, round_typed_float ft q = Some tc.
Proof.
  intros ft q. unfold representableb, round_constant.
  destruct (round_typed_float ft q) as [tc|] eqn:E; cbn [option_map]; split.
  - intros _; exists tc; reflexivity.
  - intros _; reflexivity.
  - discriminate.
  - intros [tc' HH]; discriminate.
Qed.

(* The rounded representation is in the image of [round_ieee ft], so the format index [ft] is load-bearing. *)
Lemma typed_format_image : forall ft (tc : TypedConstant ft),
  exists q, rounded tc = strip_neg_zero (round_ieee ft q).
Proof. intros ft tc; exact (formed tc). Qed.

(* Read-back coherence: reading the retained representation yields the retained exact rational. *)
Lemma typed_readback : forall ft (tc : TypedConstant ft),
  ieee_to_constant (rounded tc) = Some (exact tc).
Proof. intros ft tc; exact (coherent tc). Qed.

(* Positive-zero-or-finite shape: negative zero, infinity and NaN are unconstructible as typed constants. *)
Lemma typed_not_neg_zero : forall ft (tc : TypedConstant ft), rounded tc <> S754_zero true.
Proof.
  intros ft tc H. destruct (formed tc) as [q Hq]. rewrite H in Hq.
  destruct (round_ieee ft q); cbn in Hq; discriminate.
Qed.
Lemma typed_not_nan : forall ft (tc : TypedConstant ft), rounded tc <> S754_nan.
Proof. intros ft tc H; pose proof (coherent tc) as Hc; rewrite H in Hc; discriminate. Qed.
Lemma typed_not_inf : forall ft (tc : TypedConstant ft) s, rounded tc <> S754_infinity s.
Proof. intros ft tc s H; pose proof (coherent tc) as Hc; rewrite H in Hc; discriminate. Qed.

Example round_const_single_rounding_direct_f32 :
  round_constant F32 single_rounding_x = Some (constant_of_Z 2305843284091600896).
Proof. vm_compute. reflexivity. Qed.
Example round_const_single_rounding_double_f32 :
  ieee_to_constant (SFdiv 24 128 (round_ieee F64 single_rounding_x) (ieee_of_Z 1))
    = Some (constant_of_Z 2305843009213693952).
Proof. reflexivity. Qed.
Example round_const_overflow_f32 :
  round_constant F32 (constant_of_Z (10 ^ 40)) = None.
Proof. vm_compute. reflexivity. Qed.
Example round_const_underflow_f64 :
  round_constant F64 (reduce_constant 1 (10 ^ 330)%positive) = Some constant_zero.
Proof. vm_compute. reflexivity. Qed.
Example round_const_source_zero_f64 :
  round_constant F64 constant_zero = Some constant_zero.   (* the canonical zero rounds to +0 *)
Proof. vm_compute. reflexivity. Qed.
Example representableb_single_rounding_f32 : representableb F32 single_rounding_x = true.
Proof. vm_compute. reflexivity. Qed.
Example representableb_overflow_f32 : representableb F32 (constant_of_Z (10 ^ 40)) = false.
Proof. vm_compute. reflexivity. Qed.

(* The honest carrier is constructible, and a negative-zero or NaN representation is refused by the fields. *)
Example tfc_five_f64_ok :
  match round_typed_float F64 (constant_of_Z 5) with Some _ => True | None => False end.
Proof. vm_compute; exact I. Qed.
Fail Definition tfc_neg_zero_unconstructible : TypedConstant F64 :=
  MakeTypedConstant constant_zero (S754_zero true) (ex_intro _ constant_zero eq_refl) eq_refl.
Fail Definition tfc_nan_unconstructible : TypedConstant F64 :=
  MakeTypedConstant constant_zero S754_nan (ex_intro _ constant_zero eq_refl) eq_refl.

Example round_typed_neg_underflow_f64 :
  match round_typed_float F64 (reduce_constant (-1) (10 ^ 330)%positive) with
  | Some tc => exact tc = constant_zero /\ rounded tc = S754_zero false
  | None => False
  end.
Proof. vm_compute. split; reflexivity. Qed.
