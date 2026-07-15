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

(** ---- the exact untyped floating constant: an exact rational ---- *)
Record FloatConst := mkFC { fc_num : Z ; fc_den : positive }.

Definition fc_zero : FloatConst := mkFC 0 1.

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
Definition scar_x : FloatConst := mkFC 2305843146652647425 1.

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
  sf_to_Z (round_float_sf F32 (mkFC 16777217 1)) = Some 16777216.
Proof. reflexivity. Qed.

Example round_f64_2p53_plus1 :
  sf_to_Z (round_float_sf F64 (mkFC 9007199254740993 1)) = Some 9007199254740992.
Proof. reflexivity. Qed.

(** small exact values are unchanged. *)
Example round_f32_exact_small : sf_to_Z (round_float_sf F32 (mkFC 3 1)) = Some 3. Proof. reflexivity. Qed.
Example round_f64_exact_small : sf_to_Z (round_float_sf F64 (mkFC 42 1)) = Some 42. Proof. reflexivity. Qed.

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

Definition fc_of_Z (z : Z) : FloatConst := mkFC z 1.

Lemma fc_of_Z_canonical : forall z, fc_canonical (fc_of_Z z).
Proof. intro z; unfold fc_canonical, fc_of_Z; cbn [fc_num fc_den]; apply Z.gcd_1_r. Qed.

Lemma fc_zero_canonical : fc_canonical fc_zero.
Proof. unfold fc_canonical, fc_zero; cbn [fc_num fc_den]; reflexivity. Qed.

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

(** normalize (num, den) to coprime canonical form. *)
Definition reduce_fc (n : Z) (d : positive) : FloatConst :=
  mkFC (n / Z.gcd n (Zpos d)) (Z.to_pos (Zpos d / Z.gcd n (Zpos d))).

Lemma reduce_fc_canonical : forall n d, fc_canonical (reduce_fc n d).
Proof.
  intros n d. unfold fc_canonical, reduce_fc; cbn [fc_num fc_den].
  rewrite reduce_zpos.
  apply Z.gcd_div_gcd; [ pose proof (gcd_den_pos n d); lia | reflexivity ].
Qed.

Lemma reduce_fc_eq : forall n d, fc_eq (reduce_fc n d) (mkFC n d).
Proof.
  intros n d. unfold fc_eq, reduce_fc; cbn [fc_num fc_den].
  rewrite reduce_zpos.
  remember (Z.gcd n (Zpos d)) as g eqn:Hgdef.
  assert (Hgpos : 0 < g) by (rewrite Hgdef; apply gcd_den_pos).
  assert (Hn : n = g * (n / g))
    by (apply Zdivide_Zdiv_eq; [ exact Hgpos | rewrite Hgdef; apply Z.gcd_divide_l ]).
  assert (Hd : Zpos d = g * (Zpos d / g))
    by (apply Zdivide_Zdiv_eq; [ exact Hgpos | rewrite Hgdef; apply Z.gcd_divide_r ]).
  rewrite Hn at 2. rewrite Hd at 1. ring.
Qed.

(** on canonical representatives, rational equality is Leibniz equality (uniqueness of lowest terms). *)
Lemma fc_canonical_unique : forall a b,
  fc_canonical a -> fc_canonical b -> fc_eq a b -> a = b.
Proof.
  intros [na da] [nb db] Ha Hb Heq.
  unfold fc_canonical in Ha, Hb; cbn [fc_num fc_den] in Ha, Hb.
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
  subst nb. reflexivity.
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
  round_float_const F64 (mkFC 1 (10 ^ 330)%positive) = Some fc_zero.
Proof. vm_compute. reflexivity. Qed.

Example round_const_source_zero_f64 :
  round_float_const F64 (mkFC 0 5) = Some fc_zero.
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
Definition decimal_value (d : DecimalFloat) : FloatConst :=
  let c := dm_coeff d in
  let e := dm_exp10 d in
  if 0 <=? e then fc_of_Z (c * 10 ^ e)
  else reduce_fc c (Z.to_pos (10 ^ (- e))).

Lemma decimal_value_canonical : forall d, fc_canonical (decimal_value d).
Proof.
  intro d; unfold decimal_value.
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
Example decimal_value_1p5 :
  decimal_value (mkDecimal 15 (-1) eq_refl) = mkFC 3 2.   (* 15 * 10^-1 = 3/2 *)
Proof. reflexivity. Qed.
Example decimal_value_1e6 :
  decimal_value (mkDecimal 1 6 eq_refl) = fc_of_Z 1000000.
Proof. reflexivity. Qed.
Example decimal_value_neg :
  decimal_value (mkDecimal (-15) (-1) eq_refl) = mkFC (-3) 2.  (* -1.5 *)
Proof. reflexivity. Qed.

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

(** the ONE way a constant enters the runtime: round its exact rational once at [ft].  The canonical
    invariant is discharged by [eq_refl] — the carrier IS [round_float_sf ft q]. *)
Definition float_value_of_const (ft : FloatType) (q : FloatConst) : FloatValue ft :=
  mkFV (round_float_sf ft q) (or_introl (ex_intro _ q eq_refl)).

(** rounding an unsigned-zero constant yields +0 (never -0) — the constant zero has no sign. *)
Lemma round_float_sf_zero : forall ft, round_float_sf ft fc_zero = S754_zero false.
Proof. intro ft; destruct ft; reflexivity. Qed.

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
