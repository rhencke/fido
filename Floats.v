(** ============================================================================
    Floats — the ONE float-family descriptor + exact-constant authority.  Two live Go float types, F32 =
    binary32 and F64 = binary64; precision and exponent bound are SINGLE-SOURCED from the one [FloatType]
    descriptor.  The exact untyped floating constant is an exact RATIONAL [FloatConst] (numerator [Z] over a
    [positive] denominator — never a [float], a [spec_float], a decimal source string, or a rounded value).
    Target-directed rounding is a SINGLE direct round of that exact rational at the destination format, over
    [SpecFloat.spec_float] and computable [Z] arithmetic — F32 rounds DIRECTLY at binary32, never through F64
    (the historical double-rounding scar).  Everything here is axiom-free: no [PrimFloat]/[Prim2SF]/[SF2Prim],
    no primitive integers.  No float ARITHMETIC (deferred).
    ============================================================================ *)
From Stdlib Require Import ZArith String.
From Stdlib Require Import Lia Znumtheory Eqdep_dec.
From Stdlib Require Import Floats.SpecFloat.
Open Scope Z_scope.

(** ---- the one float-type descriptor ---- *)
Inductive FloatType := F32 | F64.

Definition float_type_eqb (a b : FloatType) : bool :=
  match a, b with F32, F32 => true | F64, F64 => true | _, _ => false end.

Lemma float_type_eqb_eq : forall a b, float_type_eqb a b = true <-> a = b.
Proof. intros [] []; simpl; split; congruence. Qed.

Definition float_keyword (ft : FloatType) : string :=
  match ft with F32 => "float32" | F64 => "float64" end%string.

(** binary32 = (prec 24, emax 128); binary64 = (prec 53, emax 1024).  SpecFloat is precision-parameterized,
    so faithful binary32 is the SAME functions with these two magic pairs. *)
Definition float_prec (ft : FloatType) : Z := match ft with F32 => 24 | F64 => 53 end.
Definition float_emax (ft : FloatType) : Z := match ft with F32 => 128 | F64 => 1024 end.

Lemma float_keyword_F32 : float_keyword F32 = "float32"%string. Proof. reflexivity. Qed.
Lemma float_keyword_F64 : float_keyword F64 = "float64"%string. Proof. reflexivity. Qed.
Lemma float_prec_F32 : float_prec F32 = 24.   Proof. reflexivity. Qed.
Lemma float_prec_F64 : float_prec F64 = 53.   Proof. reflexivity. Qed.
Lemma float_emax_F32 : float_emax F32 = 128.  Proof. reflexivity. Qed.
Lemma float_emax_F64 : float_emax F64 = 1024. Proof. reflexivity. Qed.

(** ---- the exact untyped floating constant: an exact rational, INTRINSICALLY canonical ----
    A [FloatConst] is a numerator over a POSITIVE denominator that are COPRIME by construction ([fc_wf] — a
    proof-irrelevant [bool] equality, axiom-free), so every value is already in lowest terms: a non-reduced
    fraction like 2/4 has NO [FloatConst] value.  Canonical zero is [fc_of_Z 0 = 0/1].  Equality by canonical
    representation is therefore Leibniz equality ([fc_eqb_eq]). *)
Record FloatConst := mkFC {
  fc_num : Z ;
  fc_den : positive ;
  fc_wf  : (Z.gcd fc_num (Zpos fc_den) =? 1) = true
}.

Lemma gcd_z_1 : forall z, (Z.gcd z 1 =? 1) = true.
Proof. intro z; apply Z.eqb_eq; apply Z.gcd_1_r. Qed.

(** the exact integer [z] as the canonical rational [z/1]. *)
Definition fc_of_Z (z : Z) : FloatConst := mkFC z 1 (gcd_z_1 z).

Definition fc_zero : FloatConst := fc_of_Z 0.

(** ---- exact rational -> spec_float, then a single direct round at the destination format ----
    [sf_of_Z] embeds an exact integer as a (deliberately non-canonical) [spec_float] mantissa fed only to
    [SFdiv], which normalizes.  [round_float_sf] performs ONE correctly-rounded division of numerator by
    denominator at the destination precision — so F32 rounds directly at binary32, never through binary64. *)
Definition sf_of_Z (z : Z) : spec_float :=
  match z with
  | Z0     => S754_zero false
  | Zpos p => S754_finite false p 0
  | Zneg p => S754_finite true  p 0
  end.

Definition round_float_sf (ft : FloatType) (a : FloatConst) : spec_float :=
  SFdiv (float_prec ft) (float_emax ft) (sf_of_Z (fc_num a)) (sf_of_Z (Zpos (fc_den a))).

Definition cond_Zopp (s : bool) (m : Z) : Z := if s then Z.opp m else m.

(** the exact integer value of an integer-valued finite/zero [spec_float] (nonnegative binary exponent), if
    it denotes an integer — the map back a float->integer constant conversion and the e2e witness use. *)
Definition sf_to_Z (v : spec_float) : option Z :=
  match v with
  | S754_zero _ => Some 0
  | S754_finite s m e =>
      let n := cond_Zopp s (Zpos m) in
      if Z.leb 0 e then Some (n * 2 ^ e)               (* integer by construction *)
      else let d := 2 ^ (- e) in                       (* dyadic n*2^e; integer iff 2^(-e) | n *)
           if Z.eqb (n mod d) 0 then Some (n / d) else None
  | _ => None
  end.

(** ---- ★§30 double-rounding scar: direct binary32 rounding differs from binary64-then-binary32 ----
    input x = 2305843146652647425 = 2^61 + 2^37 + 1.  Direct binary32 rounds UP (strictly above the midpoint)
    to 2^61 + 2^38 = 2305843284091600896; rounding to binary64 first drops the +1 to the exact midpoint
    2^61 + 2^37, which binary32 then rounds to even DOWN to 2^61 = 2305843009213693952.  Both pinned. *)
Definition scar_x : FloatConst := fc_of_Z 2305843146652647425.

Example scar_direct_f32 :
  sf_to_Z (round_float_sf F32 scar_x) = Some 2305843284091600896.
Proof. reflexivity. Qed.

Example scar_double_f32_via_f64 :
  sf_to_Z (SFdiv 24 128 (round_float_sf F64 scar_x) (sf_of_Z 1)) = Some 2305843009213693952.
Proof. reflexivity. Qed.

Example scar_direct_differs_double :
  round_float_sf F32 scar_x <> SFdiv 24 128 (round_float_sf F64 scar_x) (sf_of_Z 1).
Proof. discriminate. Qed.

(** ---- §31 precision boundaries: 2^24+1 rounds to 2^24 at binary32; 2^53+1 rounds to 2^53 at binary64 ---- *)
Example round_f32_2p24_plus1 :
  sf_to_Z (round_float_sf F32 (fc_of_Z 16777217)) = Some 16777216.
Proof. reflexivity. Qed.

Example round_f64_2p53_plus1 :
  sf_to_Z (round_float_sf F64 (fc_of_Z 9007199254740993)) = Some 9007199254740992.
Proof. reflexivity. Qed.

(** small exact values are unchanged. *)
Example round_f32_exact_small : sf_to_Z (round_float_sf F32 (fc_of_Z 3)) = Some 3. Proof. reflexivity. Qed.
Example round_f64_exact_small : sf_to_Z (round_float_sf F64 (fc_of_Z 42)) = Some 42. Proof. reflexivity. Qed.

(** ============================================================================
    Canonical exact-rational equality + reduction, and the ONE target-directed constant-conversion /
    representability authority.  A [FloatConst] value is CANONICAL when its stored numerator and (positive)
    denominator are coprime; [fc_eqb] decides RATIONAL equality by cross-multiplication (independent of the
    stored form); [reduce_fc] normalizes any (num, den) to its coprime canonical form preserving the exact
    value; and on canonical values rational equality coincides with Leibniz equality
    ([fc_canonical_unique]).  Canonical zero is [fc_zero = mkFC 0 1].
    ============================================================================ *)

Definition fc_canonical (a : FloatConst) : Prop :=
  Z.gcd (fc_num a) (Zpos (fc_den a)) = 1.

(** rational-value equality (the meaning [fc_eqb] decides) — cross-multiplication over [Z]. *)
Definition fc_eq (a b : FloatConst) : Prop :=
  fc_num a * Zpos (fc_den b) = fc_num b * Zpos (fc_den a).

Definition fc_eqb (a b : FloatConst) : bool :=
  Z.eqb (fc_num a * Zpos (fc_den b)) (fc_num b * Zpos (fc_den a)).

Lemma fc_eqb_spec : forall a b, fc_eqb a b = true <-> fc_eq a b.
Proof. intros a b; unfold fc_eqb, fc_eq; apply Z.eqb_eq. Qed.

Lemma fc_of_Z_canonical : forall z, fc_canonical (fc_of_Z z).
Proof. intro z; unfold fc_canonical, fc_of_Z; cbn [fc_num fc_den]; apply Z.gcd_1_r. Qed.

Lemma fc_zero_canonical : fc_canonical fc_zero.
Proof. apply fc_of_Z_canonical. Qed.

(** every [FloatConst] is canonical BY CONSTRUCTION — the coprimality [fc_wf] is a stored proof. *)
Lemma fc_canonical_intrinsic : forall a, fc_canonical a.
Proof. intro a; unfold fc_canonical; apply Z.eqb_eq; exact (fc_wf a). Qed.

(** two [FloatConst]s with the same numerator + denominator ARE equal — the coprimality witness is
    proof-irrelevant (UIP over decidable [bool] equality, axiom-free). *)
Lemma fc_num_den_eq : forall a b, fc_num a = fc_num b -> fc_den a = fc_den b -> a = b.
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

(** the reduced form is coprime — the intrinsic [fc_wf] obligation. *)
Lemma reduce_fc_wf : forall n d,
  (Z.gcd (n / Z.gcd n (Zpos d)) (Zpos (Z.to_pos (Zpos d / Z.gcd n (Zpos d)))) =? 1) = true.
Proof.
  intros n d; apply Z.eqb_eq. rewrite reduce_zpos.
  apply Z.gcd_div_gcd; [ pose proof (gcd_den_pos n d); lia | reflexivity ].
Qed.

(** normalize (num, den) to coprime canonical form. *)
Definition reduce_fc (n : Z) (d : positive) : FloatConst :=
  mkFC (n / Z.gcd n (Zpos d)) (Z.to_pos (Zpos d / Z.gcd n (Zpos d))) (reduce_fc_wf n d).

Lemma reduce_fc_canonical : forall n d, fc_canonical (reduce_fc n d).
Proof. intros; apply fc_canonical_intrinsic. Qed.

(** reduction preserves the exact rational value: [reduce_fc n d] cross-multiplies equal to [n/d]. *)
Lemma reduce_fc_eq : forall n d,
  fc_num (reduce_fc n d) * Zpos d = n * Zpos (fc_den (reduce_fc n d)).
Proof.
  intros n d. cbn [fc_num fc_den reduce_fc].
  rewrite reduce_zpos.
  remember (Z.gcd n (Zpos d)) as g eqn:Hgdef.
  assert (Hgpos : 0 < g) by (rewrite Hgdef; apply gcd_den_pos).
  assert (Hn : n = g * (n / g))
    by (apply Zdivide_Zdiv_eq; [ exact Hgpos | rewrite Hgdef; apply Z.gcd_divide_l ]).
  assert (Hd : Zpos d = g * (Zpos d / g))
    by (apply Zdivide_Zdiv_eq; [ exact Hgpos | rewrite Hgdef; apply Z.gcd_divide_r ]).
  rewrite Hn at 2. rewrite Hd at 1. ring.
Qed.

(** EQUALITY BY CANONICAL REPRESENTATION: since every [FloatConst] is in lowest terms, rational equality is
    Leibniz equality (uniqueness of the reduced fraction). *)
Lemma fc_canonical_unique : forall a b, fc_eq a b -> a = b.
Proof.
  intros [na da wa] [nb db wb] Heq.
  assert (Ha : Z.gcd na (Zpos da) = 1) by (apply Z.eqb_eq; exact wa).
  assert (Hb : Z.gcd nb (Zpos db) = 1) by (apply Z.eqb_eq; exact wb).
  unfold fc_eq in Heq; cbn [fc_num fc_den] in Heq.
  (* [fc_canonical] IS [Z.coprime]; a coprime divisor of a product divides the other factor (Gauss). *)
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

(** [fc_eqb] decides Leibniz equality (via the canonical uniqueness above). *)
Lemma fc_eqb_eq : forall a b, fc_eqb a b = true <-> a = b.
Proof.
  intros a b; split.
  - intro H; apply fc_canonical_unique, fc_eqb_spec; exact H.
  - intro H; subst b; unfold fc_eqb; apply Z.eqb_eq; reflexivity.
Qed.

(** ---- rounded spec_float back to an exact canonical constant ----
    [S754_zero] -> canonical +0; a finite dyadic n*2^e -> exact rational (integer when e>=0, else n/2^(-e)
    reduced); infinity (overflow) and NaN are NOT representable as an exact constant. *)
Definition sf_to_FloatConst (v : spec_float) : option FloatConst :=
  match v with
  | S754_zero _ => Some fc_zero
  | S754_finite s m e =>
      let n := cond_Zopp s (Zpos m) in
      if Z.leb 0 e then Some (fc_of_Z (n * 2 ^ e))
      else Some (reduce_fc n (Z.to_pos (2 ^ (- e))))
  | _ => None
  end.

(** the ONE target-directed exact float-constant rounding authority: round the exact source rational ONCE at
    the destination format, then read it back as an exact canonical constant.  Overflow (infinity) rejects;
    underflow rounds to canonical +0; NaN never arises for a valid (nonzero-denominator) rational. *)
Definition round_float_const (ft : FloatType) (a : FloatConst) : option FloatConst :=
  sf_to_FloatConst (round_float_sf ft a).

(** the ONE float representability authority + its reflected decision. *)
Definition FloatConstRepresentable (ft : FloatType) (a : FloatConst) : Prop :=
  exists r, round_float_const ft a = Some r.

Definition float_representableb (ft : FloatType) (a : FloatConst) : bool :=
  match round_float_const ft a with Some _ => true | None => false end.

Lemma float_representableb_spec :
  forall ft a, float_representableb ft a = true <-> FloatConstRepresentable ft a.
Proof.
  intros ft a. unfold float_representableb, FloatConstRepresentable.
  destruct (round_float_const ft a) as [r|] eqn:E; split.
  - intros _; exists r; reflexivity.
  - intros _; reflexivity.
  - discriminate.
  - intros [r H]; discriminate.
Qed.

(** ---- constant-conversion fixtures (contract §30/§32/§33) ----
    the direct-F32 double-round scar as an EXACT integer-valued constant; overflow rejects; underflow rounds
    to canonical +0; a source zero (any denominator) rounds to canonical +0 (no negative-zero constant). *)
Example round_const_scar_direct_f32 :
  round_float_const F32 scar_x = Some (fc_of_Z 2305843284091600896).
Proof. reflexivity. Qed.

Example round_const_scar_double_f32 :
  sf_to_FloatConst (SFdiv 24 128 (round_float_sf F64 scar_x) (sf_of_Z 1))
    = Some (fc_of_Z 2305843009213693952).
Proof. reflexivity. Qed.

Example round_const_overflow_f32 :
  round_float_const F32 (fc_of_Z (10 ^ 40)) = None.
Proof. vm_compute. reflexivity. Qed.

Example round_const_underflow_f64 :
  round_float_const F64 (reduce_fc 1 (10 ^ 330)%positive) = Some fc_zero.
Proof. vm_compute. reflexivity. Qed.

Example round_const_source_zero_f64 :
  round_float_const F64 fc_zero = Some fc_zero.   (* the canonical zero rounds to +0 *)
Proof. reflexivity. Qed.

Example float_representableb_scar_f32 : float_representableb F32 scar_x = true.
Proof. reflexivity. Qed.

Example float_representableb_overflow_f32 : float_representableb F32 (fc_of_Z (10 ^ 40)) = false.
Proof. vm_compute. reflexivity. Qed.

(** ============================================================================
    The intrinsic finite-decimal raw literal domain — [DecimalFloat], the exact SEMANTIC value a raw float
    source token carries (never source spelling: no underscores / hex / capitalization / leading zeros /
    negative-zero spelling).  Its value is [dm_coeff * 10 ^ dm_exp10].  It is INTRINSICALLY CANONICAL and
    INTRINSICALLY BOUNDED: a value is representable ONLY in one normal form (zero is exactly (0,0); a nonzero
    coefficient has no removable factor of ten) and ONLY within a deliberately bounded coefficient/exponent
    box chosen to lie FAR inside what pinned Go 1.23 accepts as a source literal (probed: gc parses 1000-digit
    coefficients and 10^6 exponents; we cap at 40 significant digits and |exp10| <= 4096, covering every F32/
    F64 overflow (~e39/e309) and underflow (~e-330) fixture with margin).  Out-of-box / non-canonical pairs
    are UNREPRESENTABLE (no [DecimalFloat] value), not rejected — so every [DecimalFloat] renders to a literal
    the pinned toolchain accepts.  The internal [FloatConst] mathematics is deliberately WIDER than this raw
    literal box.
    ============================================================================ *)

Definition decimal_max_coeff : Z := 10 ^ 40.   (* |coeff| < 10^40  (<= 40 significant digits) *)
Definition decimal_max_exp   : Z := 4096.      (* -4096 <= exp10 <= 4096 *)

(** canonical: zero is exactly (0,0); a nonzero coefficient is not divisible by ten (no removable factor). *)
Definition decimal_canonicalb (c e : Z) : bool :=
  if Z.eqb c 0 then Z.eqb e 0 else negb (Z.eqb (Z.rem c 10) 0).

Definition decimal_wfb (c e : Z) : bool :=
  decimal_canonicalb c e
  && (Z.abs c <? decimal_max_coeff)
  && (- decimal_max_exp <=? e) && (e <=? decimal_max_exp).

Record DecimalFloat := mkDecimal {
  dm_coeff : Z ;
  dm_exp10 : Z ;
  dm_wf    : decimal_wfb dm_coeff dm_exp10 = true
}.

(** equality by canonical representation: a [DecimalFloat] is fixed by its (coeff, exp10) pair — the
    well-formedness witness is proof-irrelevant (UIP over the decidable [bool] equality, axiom-free). *)
Definition dm_eqb (a b : DecimalFloat) : bool :=
  Z.eqb (dm_coeff a) (dm_coeff b) && Z.eqb (dm_exp10 a) (dm_exp10 b).

Lemma dm_eqb_eq : forall a b, dm_eqb a b = true <-> a = b.
Proof.
  intros a b; unfold dm_eqb; split.
  - intro H. apply Bool.andb_true_iff in H as [H1 H2].
    apply Z.eqb_eq in H1; apply Z.eqb_eq in H2.
    destruct a as [ca ea pa], b as [cb eb pb]; cbn in H1, H2; subst.
    f_equal. apply (UIP_dec Bool.bool_dec).
  - intro H; subst b. rewrite !Z.eqb_refl; reflexivity.
Qed.

(** the exact rational value of the literal, as a canonical [FloatConst] (NO rounding — raw interpretation is
    exact).  Nonnegative exponent -> the exact integer coeff*10^e; negative exponent -> the reduced dyadic-
    free rational coeff / 10^(-e). *)
Definition decimal_to_fc (coeff exp : Z) : FloatConst :=
  if 0 <=? exp then fc_of_Z (coeff * 10 ^ exp)
  else reduce_fc coeff (Z.to_pos (10 ^ (- exp))).

Definition decimal_value (d : DecimalFloat) : FloatConst :=
  decimal_to_fc (dm_coeff d) (dm_exp10 d).

Lemma decimal_value_canonical : forall d, fc_canonical (decimal_value d).
Proof.
  intro d; unfold decimal_value, decimal_to_fc.
  destruct (0 <=? dm_exp10 d); [ apply fc_of_Z_canonical | apply reduce_fc_canonical ].
Qed.

(** the ONE zero literal (canonicality forces (0,0)); its exact value is unsigned zero — there is no
    negative-zero decimal literal (a zero coefficient is the same value regardless of any sign spelling). *)
Definition decimal_zero : DecimalFloat := mkDecimal 0 0 eq_refl.

Lemma decimal_value_zero : decimal_value decimal_zero = fc_zero.
Proof. reflexivity. Qed.

Lemma decimal_zero_unique : forall d, dm_coeff d = 0 -> d = decimal_zero.
Proof.
  intro d. pose proof (dm_wf d) as Hwf. unfold decimal_wfb, decimal_canonicalb in Hwf.
  intro Hc. rewrite Hc in Hwf. cbn in Hwf.
  apply Bool.andb_true_iff in Hwf as [Hwf _]. apply Bool.andb_true_iff in Hwf as [Hwf _].
  apply Bool.andb_true_iff in Hwf as [Hcan _]. apply Z.eqb_eq in Hcan.
  apply dm_eqb_eq. unfold dm_eqb, decimal_zero; cbn. rewrite Hc, Hcan; reflexivity.
Qed.

(** ---- §12 boundary + §11 value fixtures (kernel-checked) ---- *)
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
  fc_num (decimal_value (mkDecimal 15 (-1) eq_refl)) = 3
  /\ fc_den (decimal_value (mkDecimal 15 (-1) eq_refl)) = 2%positive.
Proof. split; reflexivity. Qed.
Example decimal_value_1e6 :
  decimal_value (mkDecimal 1 6 eq_refl) = fc_of_Z 1000000.
Proof. reflexivity. Qed.
Example decimal_value_neg :                                       (* -15 * 10^-1 = -3/2 *)
  fc_num (decimal_value (mkDecimal (-15) (-1) eq_refl)) = -3
  /\ fc_den (decimal_value (mkDecimal (-15) (-1) eq_refl)) = 2%positive.
Proof. split; reflexivity. Qed.
Example decimal_value_tenth :                                     (* 1 * 10^-1 = 1/10 (the §29 example) *)
  fc_num (decimal_value (mkDecimal 1 (-1) eq_refl)) = 1
  /\ fc_den (decimal_value (mkDecimal 1 (-1) eq_refl)) = 10%positive.
Proof. split; reflexivity. Qed.

(** ============================================================================
    The runtime float value — a FORMAT-CANONICAL [spec_float] tied to one [FloatType], with a PROOF-CARRYING
    canonical invariant.  A value is canonical for [ft] when it is in the IMAGE of the format normalizer
    [round_float_sf ft] (finite / +/-inf on overflow / +/-0 on underflow — the only source today), OR is NaN
    or an infinity (future runtime ops).  This is future-compatible with every IEEE case (finite, +/-0, inf,
    NaN) and is NOT a "values-from-constants-only" invariant.  Construction from a constant is [eq_refl].
    ============================================================================ *)

Definition sf_is_finite_or_zero (v : spec_float) : bool :=
  match v with S754_finite _ _ _ | S754_zero _ => true | _ => false end.

Definition FloatCanonical (ft : FloatType) (v : spec_float) : Prop :=
  (exists q, v = round_float_sf ft q) \/ v = S754_nan \/ (exists s, v = S754_infinity s).

Record FloatValue (ft : FloatType) : Type := mkFV {
  fv_sf : spec_float ;
  fv_ok : FloatCanonical ft fv_sf
}.
Arguments mkFV {ft} _ _.
Arguments fv_sf {ft} _.

(** rounding an unsigned-zero constant yields +0 (never -0) — the constant zero has no sign. *)
Lemma round_float_sf_zero : forall ft, round_float_sf ft fc_zero = S754_zero false.
Proof. intro ft; destruct ft; reflexivity. Qed.

(** normalize a ZERO result to +0 (a negative underflow rounds to -0, but a CONSTANT has no signed zero — see
    §33; the FloatValue TYPE still admits -0 for future runtime ops). *)
Definition strip_neg_zero (v : spec_float) : spec_float :=
  match v with S754_zero _ => S754_zero false | x => x end.

(** the canonicality of a constant's runtime spec_float — the single-rounding [round_float_sf] result with a
    zero normalized to +0.  There is NO public [FloatConst -> FloatValue] constructor: the runtime is built
    ONLY inside [round_typed_float] (the one authority) and reached ONLY as [tfc_runtime]. *)
Lemma const_runtime_canonical : forall ft q,
  FloatCanonical ft (strip_neg_zero (round_float_sf ft q)).
Proof.
  intros ft q; unfold FloatCanonical, strip_neg_zero.
  destruct (round_float_sf ft q) as [sb|sb| |sb m e] eqn:E.
  - left; exists fc_zero; rewrite round_float_sf_zero; reflexivity.
  - right; right; exists sb; reflexivity.
  - right; left; reflexivity.
  - left; exists q; rewrite E; reflexivity.
Qed.

(** a REPRESENTABLE constant rounds to a finite/zero value — never NaN or infinity (so constant evaluation
    produces no NaN/Inf).  Direct from [sf_to_FloatConst] returning [None] exactly on inf/nan. *)
Lemma representable_finite_or_zero : forall ft q,
  FloatConstRepresentable ft q -> sf_is_finite_or_zero (round_float_sf ft q) = true.
Proof.
  intros ft q [r Hr]. unfold round_float_const in Hr.
  destruct (round_float_sf ft q) as [sb|sb| |sb m e] eqn:E; cbn in Hr; try discriminate; reflexivity.
Qed.

Lemma representable_not_nan : forall ft q,
  FloatConstRepresentable ft q -> round_float_sf ft q <> S754_nan.
Proof.
  intros ft q H HN. pose proof (representable_finite_or_zero ft q H) as Hf.
  rewrite HN in Hf; discriminate.
Qed.

Lemma representable_not_inf : forall ft q s,
  FloatConstRepresentable ft q -> round_float_sf ft q <> S754_infinity s.
Proof.
  intros ft q s H HI. pose proof (representable_finite_or_zero ft q H) as Hf.
  rewrite HI in Hf; discriminate.
Qed.

(** ============================================================================
    §5-8 INTRINSIC TYPED FLOAT CONSTANTS — one package that carries BOTH the exact
    rounded rational AND its canonical runtime IEEE value, plus a proof they denote
    the same value.  Constructed by the ONE authority [round_typed_float], which
    rounds ONCE at the destination format (F32 directly at binary32); the exact and
    runtime representations come from that single rounding event, so evaluation never
    rounds a typed float constant again.
    ============================================================================ *)

(** the constant-origin runtime shape (contract §5.D): a typed float constant's runtime is exactly +0 or a
    finite value — never -0, infinity, or NaN.  (Those inhabit the general [FloatValue] domain, but are not
    constants.) *)
Definition float_constant_runtimeb (v : spec_float) : bool :=
  match v with
  | S754_zero false   => true
  | S754_finite _ _ _ => true
  | _                 => false
  end.

Record TypedFloatConst (ft : FloatType) : Type := mkTFC {
  tfc_exact   : FloatConst ;                                            (* A: exact rounded rational *)
  tfc_runtime : FloatValue ft ;                                         (* B: canonical runtime IEEE value *)
  tfc_coh     : sf_to_FloatConst (fv_sf tfc_runtime) = Some tfc_exact ; (* C: exact/runtime coherence *)
  tfc_shape   : float_constant_runtimeb (fv_sf tfc_runtime) = true      (* D: +0 or finite only *)
}.
Arguments mkTFC {ft} _ _ _ _.
Arguments tfc_exact {ft} _.
Arguments tfc_runtime {ft} _.
Arguments tfc_coh {ft} _.
Arguments tfc_shape {ft} _.

(** [sf_to_FloatConst] ignores a zero's sign, so stripping it does not change the read-back constant. *)
Lemma sf_to_FloatConst_strip : forall w, sf_to_FloatConst (strip_neg_zero w) = sf_to_FloatConst w.
Proof. intro w; destruct w; reflexivity. Qed.

(** the constant runtime is never -0, so once it reads back as an exact constant it is necessarily +0 or
    finite — establishing shape field D from coherence field C. *)
Lemma const_runtime_shape : forall ft q r,
  sf_to_FloatConst (strip_neg_zero (round_float_sf ft q)) = Some r ->
  float_constant_runtimeb (strip_neg_zero (round_float_sf ft q)) = true.
Proof.
  intros ft q r H.
  destruct (round_float_sf ft q) as [sb|sb| |sb m e]; cbn [strip_neg_zero] in *;
    cbn [sf_to_FloatConst float_constant_runtimeb] in *; try reflexivity; discriminate.
Qed.

(** decide the runtime read-back once, CARRYING the proof — a [sumor] value (not a dependent [option] match),
    so downstream reasoning destructs a plain value and never re-abstracts a convoy motive. *)
Definition float_repr_dec (ft : FloatType) (q : FloatConst) :
  {r : FloatConst | sf_to_FloatConst (strip_neg_zero (round_float_sf ft q)) = Some r}
  + {sf_to_FloatConst (strip_neg_zero (round_float_sf ft q)) = None} :=
  match sf_to_FloatConst (strip_neg_zero (round_float_sf ft q)) as o
    return (sf_to_FloatConst (strip_neg_zero (round_float_sf ft q)) = o ->
            {r : FloatConst | sf_to_FloatConst (strip_neg_zero (round_float_sf ft q)) = Some r}
            + {sf_to_FloatConst (strip_neg_zero (round_float_sf ft q)) = None})
  with
  | Some r => fun H => inleft (exist _ r H)
  | None   => fun H => inright H
  end eq_refl.

(** the read-back decision agrees with [sf_to_FloatConst] — immediate from the carried proof. *)
Lemma float_repr_dec_spec : forall ft q,
  match float_repr_dec ft q with
  | inleft (exist _ r _) => sf_to_FloatConst (strip_neg_zero (round_float_sf ft q)) = Some r
  | inright _            => sf_to_FloatConst (strip_neg_zero (round_float_sf ft q)) = None
  end.
Proof. intros ft q; destruct (float_repr_dec ft q) as [[r Hr]|Hn]; assumption. Qed.

(** the ONE typed-float-constant construction authority (contract §6): round the exact rational ONCE at [ft],
    normalize a zero result to +0, reject overflow (infinity) and NaN, and package the exact rounded rational,
    the canonical runtime value (built INLINE here — the sole [FloatValue]-from-a-constant construction), and
    their coherence — all from that single [round_float_sf]. *)
Definition round_typed_float (ft : FloatType) (q : FloatConst) : option (TypedFloatConst ft) :=
  match float_repr_dec ft q with
  | inleft (exist _ r Hr) =>
      Some (mkTFC r (mkFV (strip_neg_zero (round_float_sf ft q)) (const_runtime_canonical ft q))
                  Hr (const_runtime_shape ft q r Hr))
  | inright _ => None
  end.

(** the runtime spec_float of a typed float constant is exactly the single-rounding sign-normalized result. *)
Lemma round_typed_float_runtime_sf : forall ft q tc,
  round_typed_float ft q = Some tc -> fv_sf (tfc_runtime tc) = strip_neg_zero (round_float_sf ft q).
Proof.
  intros ft q tc H. unfold round_typed_float in H.
  destruct (float_repr_dec ft q) as [[r Hr]|Hn];
    [ injection H as <-; reflexivity | discriminate ].
Qed.

(** §7: [round_float_const] is EXACTLY the exact-rational projection of [round_typed_float] — no second
    rounding authority. *)
Lemma round_float_const_typed : forall ft q,
  round_float_const ft q = option_map tfc_exact (round_typed_float ft q).
Proof.
  intros ft q. unfold round_float_const.
  rewrite <- (sf_to_FloatConst_strip (round_float_sf ft q)).
  pose proof (float_repr_dec_spec ft q) as Hspec.
  unfold round_typed_float.
  destruct (float_repr_dec ft q) as [[r Hr]|Hn]; cbn [option_map tfc_exact]; exact Hspec.
Qed.

(** §8: representability is EXACTLY existence of a typed result (reflected through [round_typed_float], not a
    second overflow checker). *)
Lemma round_typed_float_representable : forall ft q,
  float_representableb ft q = true <-> exists tc, round_typed_float ft q = Some tc.
Proof.
  intros ft q. unfold float_representableb, round_float_const.
  rewrite <- (sf_to_FloatConst_strip (round_float_sf ft q)).
  pose proof (float_repr_dec_spec ft q) as Hspec.
  unfold round_typed_float.
  destruct (float_repr_dec ft q) as [[r Hr]|Hn]; rewrite Hspec.
  - split; intro; [ eexists; reflexivity | reflexivity ].
  - split; [ discriminate | intros [tc HH]; discriminate ].
Qed.

(** §30-32 the runtime of a typed float constant is +0 or finite — NEVER negative zero, infinity, or NaN
    (those inhabit the general [FloatValue] domain but are not constants).  Directly from the [tfc_shape]
    field, which no forged runtime can satisfy. *)
Lemma tfc_runtime_not_neg_zero : forall ft (tc : TypedFloatConst ft),
  fv_sf (tfc_runtime tc) <> S754_zero true.
Proof. intros ft tc H; pose proof (tfc_shape tc) as Hs; rewrite H in Hs; discriminate. Qed.
Lemma tfc_runtime_not_nan : forall ft (tc : TypedFloatConst ft),
  fv_sf (tfc_runtime tc) <> S754_nan.
Proof. intros ft tc H; pose proof (tfc_shape tc) as Hs; rewrite H in Hs; discriminate. Qed.
Lemma tfc_runtime_not_inf : forall ft (tc : TypedFloatConst ft) s,
  fv_sf (tfc_runtime tc) <> S754_infinity s.
Proof. intros ft tc s H; pose proof (tfc_shape tc) as Hs; rewrite H in Hs; discriminate. Qed.

(** §30-32 canonical general-domain runtime values that are NOT constants: NaN, infinity, and negative zero
    inhabit [FloatValue] (the domain future runtime ops need) but no [TypedFloatConst] runtime equals them. *)
Definition fv_nan (ft : FloatType) : FloatValue ft :=
  mkFV S754_nan (or_intror (or_introl eq_refl)).
Definition fv_inf (ft : FloatType) (s : bool) : FloatValue ft :=
  mkFV (S754_infinity s) (or_intror (or_intror (ex_intro _ s eq_refl))).
(* the negative-zero image of a negative underflow (proved once via vm_compute so the Definition needs no
   heavy kernel conversion). *)
Lemma neg_zero_F64_canonical : FloatCanonical F64 (S754_zero true).
Proof. left; exists (reduce_fc (-1) (10 ^ 330)%positive); vm_compute; reflexivity. Qed.
Definition fv_neg_zero_F64 : FloatValue F64 := mkFV (S754_zero true) neg_zero_F64_canonical.

(** §33 a negative tiny constant underflows to canonical +0: [round_typed_float] SUCCEEDS, the exact value is
    [fc_zero], and the stored runtime is +0 (never -0) — evaluation returns that +0 with no second round. *)
Example round_typed_neg_underflow_f64 :
  match round_typed_float F64 (reduce_fc (-1) (10 ^ 330)%positive) with
  | Some tc => tfc_exact tc = fc_zero /\ fv_sf (tfc_runtime tc) = S754_zero false
  | None => False
  end.
Proof. vm_compute. split; reflexivity. Qed.
