(** Float — the ONE float-family descriptor + exact-constant authority.  Two live Go float types, F32 =
    binary32 and F64 = binary64; precision and exponent bound are SINGLE-SOURCED from the one [Kind]
    descriptor.  The exact untyped floating constant is an exact RATIONAL [Constant] (numerator [Z] over a
    [positive] denominator — never a [float], a [spec_float], a decimal source string, or a rounded value).
    Target-directed rounding is a SINGLE direct round of that exact rational at the destination format, over
    [SpecFloat.spec_float] and computable [Z] arithmetic — F32 rounds DIRECTLY at binary32, never through F64
    (the historical double-rounding scar).  Everything here is axiom-free: no [PrimFloat]/[Prim2SF]/[SF2Prim],
    no primitive integers.  No float ARITHMETIC (deferred). *)
From Stdlib Require Import ZArith String.
From Stdlib Require Import Lia Znumtheory Eqdep_dec.
From Stdlib Require Import Floats.SpecFloat.
Open Scope Z_scope.

(** ---- the one float-type descriptor ---- *)
Inductive Kind := F32 | F64.

Definition kind_equalb (a b : Kind) : bool :=
  match a, b with F32, F32 => true | F64, F64 => true | _, _ => false end.

Lemma kind_equalb_spec : forall a b, kind_equalb a b = true <-> a = b.
Proof. intros [] []; simpl; split; congruence. Qed.

(** binary32 = (prec 24, emax 128); binary64 = (prec 53, emax 1024).  SpecFloat is precision-parameterized,
    so faithful binary32 is the SAME functions with these two magic pairs. *)
Definition precision (ft : Kind) : Z := match ft with F32 => 24 | F64 => 53 end.
Definition maximum_exponent (ft : Kind) : Z := match ft with F32 => 128 | F64 => 1024 end.

Lemma precision_f32 : precision F32 = 24.   Proof. reflexivity. Qed.
Lemma precision_f64 : precision F64 = 53.   Proof. reflexivity. Qed.
Lemma maximum_exponent_f32 : maximum_exponent F32 = 128.  Proof. reflexivity. Qed.
Lemma maximum_exponent_f64 : maximum_exponent F64 = 1024. Proof. reflexivity. Qed.

(** ---- the exact untyped floating constant: an exact rational, INTRINSICALLY canonical ----
    A [Constant] is a numerator over a POSITIVE denominator that are COPRIME by construction ([canonical] — a
    proof-irrelevant [bool] equality, axiom-free), so every value is already in lowest terms: a non-reduced
    fraction like 2/4 has NO [Constant] value.  Canonical zero is [constant_of_Z 0 = 0/1].  Equality by canonical
    representation is therefore Leibniz equality ([constant_equalb_eq]). *)
Record Constant := MakeConstant {
  numerator : Z ;
  denominator : positive ;
  canonical  : (Z.gcd numerator (Zpos denominator) =? 1) = true
}.

Lemma gcd_z_1 : forall z, (Z.gcd z 1 =? 1) = true.
Proof. intro z; apply Z.eqb_eq; apply Z.gcd_1_r. Qed.

(** the exact integer [z] as the canonical rational [z/1]. *)
Definition constant_of_Z (z : Z) : Constant := MakeConstant z 1 (gcd_z_1 z).

Definition constant_zero : Constant := constant_of_Z 0.

(** ---- exact rational -> spec_float, then a single direct round at the destination format ----
    [ieee_of_Z] embeds an exact integer as a (deliberately non-canonical) [spec_float] mantissa fed only to
    [SFdiv], which normalizes.  [round_ieee] performs ONE correctly-rounded division of numerator by
    denominator at the destination precision — so F32 rounds directly at binary32, never through binary64. *)
Definition ieee_of_Z (z : Z) : spec_float :=
  match z with
  | Z0     => S754_zero false
  | Zpos p => S754_finite false p 0
  | Zneg p => S754_finite true  p 0
  end.

Definition round_ieee (ft : Kind) (a : Constant) : spec_float :=
  SFdiv (precision ft) (maximum_exponent ft) (ieee_of_Z (numerator a)) (ieee_of_Z (Zpos (denominator a))).

Definition cond_Zopp (s : bool) (m : Z) : Z := if s then Z.opp m else m.

(** the exact integer value of an integer-valued finite/zero [spec_float] (nonnegative binary exponent), if
    it denotes an integer — the map back a float->integer constant conversion and the e2e witness use. *)
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

(** ---- ★double-rounding scar: direct binary32 rounding differs from binary64-then-binary32 ----
    input x = 2305843146652647425 = 2^61 + 2^37 + 1.  Direct binary32 rounds UP (strictly above the midpoint)
    to 2^61 + 2^38 = 2305843284091600896; rounding to binary64 first drops the +1 to the exact midpoint
    2^61 + 2^37, which binary32 then rounds to even DOWN to 2^61 = 2305843009213693952.  Both pinned. *)
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

(** ---- precision boundaries: 2^24+1 rounds to 2^24 at binary32; 2^53+1 rounds to 2^53 at binary64 ---- *)
Example round_f32_2p24_plus1 :
  ieee_to_Z (round_ieee F32 (constant_of_Z 16777217)) = Some 16777216.
Proof. reflexivity. Qed.

Example round_f64_2p53_plus1 :
  ieee_to_Z (round_ieee F64 (constant_of_Z 9007199254740993)) = Some 9007199254740992.
Proof. reflexivity. Qed.

(** small exact values are unchanged. *)
Example round_f32_exact_small : ieee_to_Z (round_ieee F32 (constant_of_Z 3)) = Some 3. Proof. reflexivity. Qed.
Example round_f64_exact_small : ieee_to_Z (round_ieee F64 (constant_of_Z 42)) = Some 42. Proof. reflexivity. Qed.

(** Canonical exact-rational equality + reduction, and the ONE target-directed constant-conversion /
    representability authority.  A [Constant] value is CANONICAL when its stored numerator and (positive)
    denominator are coprime; [constant_equalb] decides RATIONAL equality by cross-multiplication (independent of the
    stored form); [reduce_constant] normalizes any (num, den) to its coprime canonical form preserving the exact
    value; and on canonical values rational equality coincides with Leibniz equality
    ([constant_canonical_unique]).  Canonical zero is [constant_zero = MakeConstant 0 1]. *)

Definition constant_canonical (a : Constant) : Prop :=
  Z.gcd (numerator a) (Zpos (denominator a)) = 1.

(** rational-value equality (the meaning [constant_equalb] decides) — cross-multiplication over [Z]. *)
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

(** every [Constant] is canonical BY CONSTRUCTION — the coprimality [canonical] is a stored proof. *)
Lemma constant_canonical_intrinsic : forall a, constant_canonical a.
Proof. intro a; unfold constant_canonical; apply Z.eqb_eq; exact (canonical a). Qed.

(** two [Constant]s with the same numerator + denominator ARE equal — the coprimality witness is
    proof-irrelevant (UIP over decidable [bool] equality, axiom-free). *)
Lemma numerator_denominator_eq : forall a b, numerator a = numerator b -> denominator a = denominator b -> a = b.
Proof.
  intros [na da wa] [nb db wb] Hn Hd; cbn in Hn, Hd; subst nb db.
  f_equal. apply (UIP_dec Bool.bool_dec).
Qed.

(** the gcd of a numerator and a POSITIVE denominator is itself positive (never 0). *)
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

(** the reduced form is coprime — the intrinsic [canonical] obligation. *)
Lemma reduce_well_formed : forall n d,
  (Z.gcd (n / Z.gcd n (Zpos d)) (Zpos (Z.to_pos (Zpos d / Z.gcd n (Zpos d)))) =? 1) = true.
Proof.
  intros n d; apply Z.eqb_eq. rewrite reduce_zpos.
  apply Z.gcd_div_gcd; [ pose proof (gcd_den_pos n d); lia | reflexivity ].
Qed.

(** normalize (num, den) to coprime canonical form. *)
Definition reduce_constant (n : Z) (d : positive) : Constant :=
  MakeConstant (n / Z.gcd n (Zpos d)) (Z.to_pos (Zpos d / Z.gcd n (Zpos d))) (reduce_well_formed n d).

Lemma reduce_constant_canonical : forall n d, constant_canonical (reduce_constant n d).
Proof. intros; apply constant_canonical_intrinsic. Qed.

(** reduction preserves the exact rational value: [reduce_constant n d] cross-multiplies equal to [n/d]. *)
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

(** EQUALITY BY CANONICAL REPRESENTATION: since every [Constant] is in lowest terms, rational equality is
    Leibniz equality (uniqueness of the reduced fraction). *)
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

(** [constant_equalb] decides Leibniz equality (via the canonical uniqueness above). *)
Lemma constant_equalb_eq : forall a b, constant_equalb a b = true <-> a = b.
Proof.
  intros a b; split.
  - intro H; apply constant_canonical_unique, constant_equalb_spec; exact H.
  - intro H; subst b; unfold constant_equalb; apply Z.eqb_eq; reflexivity.
Qed.

(** ---- rounded spec_float back to an exact canonical constant ----
    [S754_zero] -> canonical +0; a finite dyadic n*2^e -> exact rational (integer when e>=0, else n/2^(-e)
    reduced); infinity (overflow) and NaN are NOT representable as an exact constant. *)
Definition ieee_to_constant (v : spec_float) : option Constant :=
  match v with
  | S754_zero _ => Some constant_zero
  | S754_finite s m e =>
      let n := cond_Zopp s (Zpos m) in
      if Z.leb 0 e then Some (constant_of_Z (n * 2 ^ e))
      else Some (reduce_constant n (Z.to_pos (2 ^ (- e))))
  | _ => None
  end.

(** [round_constant] (the exact-rational rounding), [Representable]/[representableb], the
    constant-conversion scar/overflow/underflow fixtures, and the representable-finite/no-nan/no-inf lemmas are
    defined BELOW as PROJECTIONS of the ONE [round_typed_float] authority — so [round_ieee] has a single
    construction call site (the typed-float authority is structurally single-rooted). *)

(** The intrinsic finite-decimal raw literal domain — [Decimal], the exact SEMANTIC value a raw float
    source token carries (never source spelling: no underscores / hex / capitalization / leading zeros /
    negative-zero spelling).  Its value is [coefficient * 10 ^ exponent].  It is INTRINSICALLY CANONICAL and
    INTRINSICALLY BOUNDED: a value is representable ONLY in one normal form (zero is exactly (0,0); a nonzero
    coefficient has no removable factor of ten) and ONLY within a deliberately bounded coefficient/exponent
    box chosen to lie FAR inside what pinned Go 1.23 accepts as a source literal (probed: gc parses 1000-digit
    coefficients and 10^6 exponents; we cap at 40 significant digits and |exp10| <= 4096, covering every F32/
    F64 overflow (~e39/e309) and underflow (~e-330) fixture with margin).  Out-of-box / non-canonical pairs
    are UNREPRESENTABLE (no [Decimal] value), not rejected — so every [Decimal] renders to a literal
    the pinned toolchain accepts.  The internal [Constant] mathematics is deliberately WIDER than this raw
    literal box. *)

Definition decimal_max_coeff : Z := 10 ^ 40.   (* |coeff| < 10^40  (<= 40 significant digits) *)
Definition decimal_max_exp   : Z := 4096.      (* -4096 <= exp10 <= 4096 *)

(** canonical: zero is exactly (0,0); a nonzero coefficient is not divisible by ten (no removable factor). *)
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

(** equality by canonical representation: a [Decimal] is fixed by its (coeff, exp10) pair — the
    well-formedness witness is proof-irrelevant (UIP over the decidable [bool] equality, axiom-free). *)
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

(** the exact rational value of the literal, as a canonical [Constant] (NO rounding — raw interpretation is
    exact).  Nonnegative exponent -> the exact integer coeff*10^e; negative exponent -> the reduced dyadic-
    free rational coeff / 10^(-e). *)
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

(** the ONE zero literal (canonicality forces (0,0)); its exact value is unsigned zero — there is no
    negative-zero decimal literal (a zero coefficient is the same value regardless of any sign spelling). *)
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

(** ---- boundary + value fixtures (kernel-checked) ---- *)
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
(* the exact rational value, compared by numerator/denominator (the coprimality witness is proof-irrelevant,
   so record equality is by num/den). *)
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

(** The runtime float value — a FORMAT-CANONICAL [spec_float] tied to one [Kind], with a PROOF-CARRYING
    canonical invariant.  A value is canonical for [ft] when it is in the IMAGE of the format normalizer
    [round_ieee ft] (finite / +/-inf on overflow / +/-0 on underflow — the only source today), OR is NaN
    or an infinity (future runtime ops).  This is future-compatible with every IEEE case (finite, +/-0, inf,
    NaN) and is NOT a "values-from-constants-only" invariant.  Construction from a constant is [eq_refl]. *)

Definition ieee_is_finite_or_zero (v : spec_float) : bool :=
  match v with S754_finite _ _ _ | S754_zero _ => true | _ => false end.

Definition FloatCanonical (ft : Kind) (v : spec_float) : Prop :=
  (exists q, v = round_ieee ft q) \/ v = S754_nan \/ (exists s, v = S754_infinity s).

Record Value (ft : Kind) : Type := MakeValue {
  ieee : spec_float ;
  canonical_value : FloatCanonical ft ieee
}.
Arguments MakeValue {ft} _ _.
Arguments ieee {ft} _.

(** rounding an unsigned-zero constant yields +0 (never -0) — the constant zero has no sign. *)
Lemma round_ieee_zero : forall ft, round_ieee ft constant_zero = S754_zero false.
Proof. intro ft; destruct ft; reflexivity. Qed.

(** normalize a ZERO result to +0 (a negative underflow rounds to -0, but a CONSTANT has no signed zero — see
   ; the Value TYPE still admits -0 for future runtime ops). *)
Definition strip_neg_zero (v : spec_float) : spec_float :=
  match v with S754_zero _ => S754_zero false | x => x end.

(** the canonicality of a constant's runtime spec_float — the single-rounding [round_ieee] result with a
    zero normalized to +0.  There is NO public [Constant -> Value] constructor: the runtime is built
    ONLY inside [round_typed_float] (the one authority) and reached ONLY as [runtime]. *)
Lemma const_runtime_canonical : forall ft q,
  FloatCanonical ft (strip_neg_zero (round_ieee ft q)).
Proof.
  intros ft q; unfold FloatCanonical, strip_neg_zero.
  destruct (round_ieee ft q) as [sb|sb| |sb m e] eqn:E.
  - left; exists constant_zero; rewrite round_ieee_zero; reflexivity.
  - right; right; exists sb; reflexivity.
  - right; left; reflexivity.
  - left; exists q; rewrite E; reflexivity.
Qed.

(** INTRINSIC TYPED FLOAT CONSTANTS — one package that carries BOTH the exact
    rounded rational AND its canonical runtime IEEE value, plus a proof they denote
    the same value.  Constructed by the ONE authority [round_typed_float], which
    rounds ONCE at the destination format (F32 directly at binary32); the exact and
    runtime representations come from that single rounding event, so evaluation never
    rounds a typed float constant again. *)

(** the constant-origin runtime shape (contract): a typed float constant's runtime is exactly +0 or a
    finite value — never -0, infinity, or NaN.  (Those inhabit the general [Value] domain, but are not
    constants.) *)
Definition constant_runtimeb (v : spec_float) : bool :=
  match v with
  | S754_zero false   => true
  | S754_finite _ _ _ => true
  | _                 => false
  end.

Record TypedConstant (ft : Kind) : Type := MakeTypedConstant {
  exact   : Constant ;                                            (* A: exact rounded rational *)
  runtime : Value ft ;                                         (* B: canonical runtime IEEE value *)
  coherent     : ieee_to_constant (ieee runtime) = Some exact ; (* C: exact/runtime coherence *)
  shape   : constant_runtimeb (ieee runtime) = true      (* D: +0 or finite only *)
}.
Arguments MakeTypedConstant {ft} _ _ _ _.
Arguments exact {ft} _.
Arguments runtime {ft} _.
Arguments coherent {ft} _.
Arguments shape {ft} _.

(** [ieee_to_constant] ignores a zero's sign, so stripping it does not change the read-back constant. *)
Lemma ieee_to_constant_strip : forall w, ieee_to_constant (strip_neg_zero w) = ieee_to_constant w.
Proof. intro w; destruct w; reflexivity. Qed.

(** the constant runtime is never -0, so once it reads back as an exact constant it is necessarily +0 or
    finite — establishing shape field D from coherence field C. *)
Lemma const_runtime_shape : forall ft q r,
  ieee_to_constant (strip_neg_zero (round_ieee ft q)) = Some r ->
  constant_runtimeb (strip_neg_zero (round_ieee ft q)) = true.
Proof.
  intros ft q r H.
  destruct (round_ieee ft q) as [sb|sb| |sb m e]; cbn [strip_neg_zero] in *;
    cbn [ieee_to_constant constant_runtimeb] in *; try reflexivity; discriminate.
Qed.

(** decide an ALREADY-BOUND [spec_float]'s constant read-back once, CARRYING the proof — a [sumor] value
    (not a dependent [option] match, and NOT a re-rounding: it consumes the bound value [v]), so downstream
    reasoning destructs a plain value and never re-abstracts a convoy motive. *)
Definition ieee_repr_dec (v : spec_float) :
  {r : Constant | ieee_to_constant v = Some r} + {ieee_to_constant v = None} :=
  match ieee_to_constant v as o
    return (ieee_to_constant v = o ->
            {r : Constant | ieee_to_constant v = Some r} + {ieee_to_constant v = None})
  with
  | Some r => fun H => inleft (exist _ r H)
  | None   => fun H => inright H
  end eq_refl.

(** package a typed float constant from ONE already-rounded canonical [spec_float] [v]: field A (the exact
    rounded rational) is [v]'s constant read-back and field B (the runtime value) is [v] itself — BOTH
    representations derive from the single bound [v], never a second rounding.  [round_ieee] is NOT called
    here; this is the sole [Value]-from-a-constant construction. *)
Definition typed_from_canonical (ft : Kind) (v : spec_float)
    (Hc : FloatCanonical ft v)
    (Hshape : forall r, ieee_to_constant v = Some r -> constant_runtimeb v = true)
    : option (TypedConstant ft) :=
  match ieee_repr_dec v with
  | inleft (exist _ r Hr) => Some (MakeTypedConstant r (MakeValue v Hc) Hr (Hshape r Hr))
  | inright _             => None
  end.

(** the ONE typed-float-constant construction authority (contract): round the exact rational ONCE at [ft]
    (the SINGLE [round_ieee] call, sign-normalized to +0), bind that result, and derive BOTH the exact
    rounded rational and the canonical runtime value from that one bound value via [typed_from_canonical] —
    overflow (infinity) and NaN read back as [None] and are rejected. *)
Definition round_typed_float (ft : Kind) (q : Constant) : option (TypedConstant ft) :=
  typed_from_canonical ft (strip_neg_zero (round_ieee ft q))
                     (const_runtime_canonical ft q) (const_runtime_shape ft q).

(** the runtime spec_float of a typed float constant is exactly the single-rounding sign-normalized result. *)
Lemma round_typed_float_runtime_sf : forall ft q tc,
  round_typed_float ft q = Some tc -> ieee (runtime tc) = strip_neg_zero (round_ieee ft q).
Proof.
  intros ft q tc H. unfold round_typed_float, typed_from_canonical in H.
  destruct (ieee_repr_dec (strip_neg_zero (round_ieee ft q))) as [[r Hr]|Hn];
    [ injection H as <-; reflexivity | discriminate ].
Qed.

(** [round_typed_float] is the ONE structural root of float-constant construction: it evaluates
    [round_ieee] at exactly ONE site, BINDS that result, and derives both the exact rational and the
    runtime value from it (via [typed_from_canonical]); the exact-rational rounding, the representability
    authority, and the constant-conversion fixtures below are all PROJECTIONS of it. *)

(** the exact-rational rounding is the [exact] projection of the typed result — NOT a second
    [round_ieee] caller. *)
Definition round_constant (ft : Kind) (a : Constant) : option Constant :=
  option_map exact (round_typed_float ft a).

Lemma round_constant_typed : forall ft q,
  round_constant ft q = option_map exact (round_typed_float ft q).
Proof. reflexivity. Qed.

(** the ONE float representability authority + its reflected decision, over the projected [round_constant]. *)
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

(** representability is EXACTLY existence of a typed result (reflected through [round_typed_float]). *)
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

(** ---- constant-conversion fixtures (contract), over the projected [round_constant] ----
    the direct-F32 double-round scar as an EXACT integer-valued constant; overflow rejects; underflow rounds
    to canonical +0; a source zero rounds to canonical +0 (no negative-zero constant). *)
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

(** the runtime of a typed float constant is +0 or finite — NEVER negative zero, infinity, or NaN
    (those inhabit the general [Value] domain but are not constants).  Directly from the [shape]
    field, which no forged runtime can satisfy. *)
Lemma typed_runtime_not_neg_zero : forall ft (tc : TypedConstant ft),
  ieee (runtime tc) <> S754_zero true.
Proof. intros ft tc H; pose proof (shape tc) as Hs; rewrite H in Hs; discriminate. Qed.
Lemma typed_runtime_not_nan : forall ft (tc : TypedConstant ft),
  ieee (runtime tc) <> S754_nan.
Proof. intros ft tc H; pose proof (shape tc) as Hs; rewrite H in Hs; discriminate. Qed.
Lemma typed_runtime_not_inf : forall ft (tc : TypedConstant ft) s,
  ieee (runtime tc) <> S754_infinity s.
Proof. intros ft tc s H; pose proof (shape tc) as Hs; rewrite H in Hs; discriminate. Qed.

(** canonical general-domain runtime values that are NOT constants: NaN, infinity, and negative zero
    inhabit [Value] (the domain future runtime ops need) but no [TypedConstant] runtime equals them. *)
Definition value_nan (ft : Kind) : Value ft :=
  MakeValue S754_nan (or_intror (or_introl eq_refl)).
Definition value_inf (ft : Kind) (s : bool) : Value ft :=
  MakeValue (S754_infinity s) (or_intror (or_intror (ex_intro _ s eq_refl))).
(* the negative-zero image of a negative underflow (proved once via vm_compute so the Definition needs no
   heavy kernel conversion). *)
Lemma neg_zero_f64_canonical : FloatCanonical F64 (S754_zero true).
Proof. left; exists (reduce_constant (-1) (10 ^ 330)%positive); vm_compute; reflexivity. Qed.
Definition value_neg_zero_F64 : Value F64 := MakeValue (S754_zero true) neg_zero_f64_canonical.

(** a typed float constant whose runtime is NaN / negative zero is UNREPRESENTABLE — the [coherent] and
    [shape] fields cannot be satisfied (NaN reads back as [None], -0 fails the +0-or-finite shape).  [Fail]
    confirms the term does not typecheck (no tracked axiom, nothing added to the environment). *)
Fail Definition tfc_nan_unrepresentable : TypedConstant F64 := MakeTypedConstant constant_zero (value_nan F64) eq_refl eq_refl.
Fail Definition tfc_neg_zero_unrepresentable : TypedConstant F64 := MakeTypedConstant constant_zero value_neg_zero_F64 eq_refl eq_refl.

(** a negative tiny constant underflows to canonical +0: [round_typed_float] SUCCEEDS, the exact value is
    [constant_zero], and the stored runtime is +0 (never -0) — evaluation returns that +0 with no second round. *)
Example round_typed_neg_underflow_f64 :
  match round_typed_float F64 (reduce_constant (-1) (10 ^ 330)%positive) with
  | Some tc => exact tc = constant_zero /\ ieee (runtime tc) = S754_zero false
  | None => False
  end.
Proof. vm_compute. split; reflexivity. Qed.
