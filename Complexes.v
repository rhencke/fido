(** Complexes — the ONE authority for Go's two complex types (complex64, complex128) as EXACT complex
    constants and intrinsically-coherent typed/runtime complex values, COMPOSED from the [Floats] component
    authority.  It imports [Floats] and NOTHING above it (no [GoTypes]) — the dependency direction is
    [Floats] -> [Complexes] -> [GoAST]/[GoTypes]/[GoSafe]/[GoRender].

    The permanent semantic distinction mirrors the scalar float layer, one level up:

      exact untyped [ComplexConst]           (a pair of exact canonical rational [FloatConst] components)
        -> intrinsic [TypedComplexConst ct]  (a pair of coherent [TypedFloatConst] components)
        -> general runtime [ComplexValue ct] (a pair of general [FloatValue] components — may be NaN/Inf/-0)

    A [ComplexType] fixes its component [FloatType] via the ONE mapping [complex_component_type] (C64->F32,
    C128->F64); ALL precision / exponent / keyword / rounding behaviour DERIVES from that mapping and the
    component [Floats] authority.  There is NO complex-specific float format, NO duplicated float coherence,
    and NO complex arithmetic — a compound typed constant is built from already-coherent typed components. *)

From Stdlib Require Import ZArith List String Bool.
From Stdlib Require Import Floats.SpecFloat.
From Fido Require Import Floats.

Local Open Scope Z_scope.

(** PART C — one complex type authority *)

(** exactly the two Go complex types.  No placeholder future constructors. *)
Inductive ComplexType := C64 | C128.

Definition complex_type_eqb (a b : ComplexType) : bool :=
  match a, b with C64, C64 | C128, C128 => true | _, _ => false end.

Lemma complex_type_eqb_eq : forall a b, complex_type_eqb a b = true <-> a = b.
Proof. intros [] []; cbn; split; congruence. Qed.

(** the ONE component-format mapping — every complex precision/exponent/runtime property derives from it. *)
Definition complex_component_type (ct : ComplexType) : FloatType :=
  match ct with C64 => F32 | C128 => F64 end.

Lemma complex_component_C64 : complex_component_type C64 = F32. Proof. reflexivity. Qed.
Lemma complex_component_C128 : complex_component_type C128 = F64. Proof. reflexivity. Qed.

(** the source keyword of a complex type. *)
Definition complex_keyword (ct : ComplexType) : string :=
  match ct with C64 => "complex64" | C128 => "complex128" end.

Lemma complex_keyword_C64 : complex_keyword C64 = "complex64"%string. Proof. reflexivity. Qed.
Lemma complex_keyword_C128 : complex_keyword C128 = "complex128"%string. Proof. reflexivity. Qed.

(** PART D — exact untyped complex constants *)

(** an EXACT complex constant: two exact canonical rational [FloatConst] components — real and imaginary.  It
    carries NO signed zero, infinity, NaN, runtime [spec_float], or source spelling; each component's
    canonicality already lives in its [FloatConst], so no aggregate proof field is added. *)
Record ComplexConst := mkCC { cc_real : FloatConst ; cc_imag : FloatConst }.

(** decidable equality DERIVED from [FloatConst] equality, componentwise (canonical, so it is Leibniz). *)
Definition complex_const_eqb (a b : ComplexConst) : bool :=
  fc_eqb (cc_real a) (cc_real b) && fc_eqb (cc_imag a) (cc_imag b).

Lemma complex_const_eqb_eq : forall a b, complex_const_eqb a b = true <-> a = b.
Proof.
  intros a b; unfold complex_const_eqb; split.
  - intro H; apply andb_true_iff in H as [Hr Hi];
    apply fc_eqb_eq in Hr; apply fc_eqb_eq in Hi;
    destruct a, b; cbn in *; subst; reflexivity.
  - intro H; subst b; apply andb_true_iff; split; apply fc_eqb_eq; reflexivity.
Qed.

(** the exact complex zero (both components the unsigned canonical zero) and the real embedding. *)
Definition complex_zero : ComplexConst := mkCC fc_zero fc_zero.
Definition complex_of_real (q : FloatConst) : ComplexConst := mkCC q fc_zero.

Lemma cc_real_of_real : forall q, cc_real (complex_of_real q) = q. Proof. reflexivity. Qed.
Lemma cc_imag_of_real : forall q, cc_imag (complex_of_real q) = fc_zero. Proof. reflexivity. Qed.

(** decide the exact imaginary component is exactly zero (rational equality over canonical [FloatConst]). *)
Definition cc_imag_is_zero (c : ComplexConst) : bool := fc_eqb (cc_imag c) fc_zero.

(** project the exact real component ONLY when the exact imaginary component is exactly zero (a pure exact
    helper — it does NOT round; complex->scalar destination rounding happens in the ONE [convert_const]). *)
Definition complex_real_if_imag_zero (c : ComplexConst) : option FloatConst :=
  if cc_imag_is_zero c then Some (cc_real c) else None.

Lemma complex_real_if_imag_zero_some : forall c q,
  complex_real_if_imag_zero c = Some q -> cc_imag_is_zero c = true /\ cc_real c = q.
Proof.
  intros c q H; unfold complex_real_if_imag_zero in H.
  destruct (cc_imag_is_zero c) eqn:E; [ injection H as <-; split; reflexivity | discriminate ].
Qed.

(** the intrinsic raw finite-decimal complex literal: two [DecimalFloat] components.  Its exact meaning is
    [decimal_value] applied independently to each component — the internal [ComplexConst] domain is WIDER
    than this raw decimal-literal domain. *)
Record DecimalComplex := mkDC { dc_real : DecimalFloat ; dc_imag : DecimalFloat }.

Definition decimal_complex_value (d : DecimalComplex) : ComplexConst :=
  mkCC (decimal_value (dc_real d)) (decimal_value (dc_imag d)).

Lemma decimal_complex_real : forall d, cc_real (decimal_complex_value d) = decimal_value (dc_real d).
Proof. reflexivity. Qed.
Lemma decimal_complex_imag : forall d, cc_imag (decimal_complex_value d) = decimal_value (dc_imag d).
Proof. reflexivity. Qed.

(** PART F — general runtime complex values and intrinsic typed complex constants *)

(** the GENERAL runtime complex domain: two general [FloatValue] components at the type's component format.
    Because each component is a general [FloatValue], a runtime complex value MAY contain finite, +/-0,
    infinity, or NaN components.  This domain is NOT narrowed to constant-origin values (future runtime
    complex operations need the full IEEE component domain). *)
Record ComplexValue (ct : ComplexType) := mkCV {
  cv_real : FloatValue (complex_component_type ct) ;
  cv_imag : FloatValue (complex_component_type ct)
}.
Arguments mkCV {ct} _ _.
Arguments cv_real {ct} _.
Arguments cv_imag {ct} _.

(** the INTRINSIC typed complex constant: two coherent [TypedFloatConst] components.  Each component already
    carries exact destination-rounded rational meaning, its stored canonical runtime IEEE value, exact/runtime
    coherence, AND the finite-or-+0 constant shape — so NO coherence field is duplicated here. *)
Record TypedComplexConst (ct : ComplexType) := mkTCC {
  tcc_real : TypedFloatConst (complex_component_type ct) ;
  tcc_imag : TypedFloatConst (complex_component_type ct)
}.
Arguments mkTCC {ct} _ _.
Arguments tcc_real {ct} _.
Arguments tcc_imag {ct} _.

(** the exact/runtime projections — BOTH are pure component projections (no rounding, no reconstruction). *)
Definition typed_complex_exact {ct} (tc : TypedComplexConst ct) : ComplexConst :=
  mkCC (tfc_exact (tcc_real tc)) (tfc_exact (tcc_imag tc)).

Definition typed_complex_runtime {ct} (tc : TypedComplexConst ct) : ComplexValue ct :=
  mkCV (tfc_runtime (tcc_real tc)) (tfc_runtime (tcc_imag tc)).

(** ---- componentwise projection laws (short, definitional) ---- *)
Lemma typed_complex_exact_real : forall ct (tc : TypedComplexConst ct),
  cc_real (typed_complex_exact tc) = tfc_exact (tcc_real tc). Proof. reflexivity. Qed.
Lemma typed_complex_exact_imag : forall ct (tc : TypedComplexConst ct),
  cc_imag (typed_complex_exact tc) = tfc_exact (tcc_imag tc). Proof. reflexivity. Qed.
Lemma typed_complex_runtime_real : forall ct (tc : TypedComplexConst ct),
  cv_real (typed_complex_runtime tc) = tfc_runtime (tcc_real tc). Proof. reflexivity. Qed.
Lemma typed_complex_runtime_imag : forall ct (tc : TypedComplexConst ct),
  cv_imag (typed_complex_runtime tc) = tfc_runtime (tcc_imag tc). Proof. reflexivity. Qed.

(** each runtime component reads back to its EXACT component (inherited from [tfc_coh], per component). *)
Lemma typed_complex_runtime_real_coh : forall ct (tc : TypedComplexConst ct),
  sf_to_FloatConst (fv_sf (cv_real (typed_complex_runtime tc)))
    = Some (cc_real (typed_complex_exact tc)).
Proof. intros ct tc; apply (tfc_coh (tcc_real tc)). Qed.
Lemma typed_complex_runtime_imag_coh : forall ct (tc : TypedComplexConst ct),
  sf_to_FloatConst (fv_sf (cv_imag (typed_complex_runtime tc)))
    = Some (cc_imag (typed_complex_exact tc)).
Proof. intros ct tc; apply (tfc_coh (tcc_imag tc)). Qed.

(** each runtime component is finite or +0 (inherited from [tfc_shape]). *)
Lemma typed_complex_runtime_real_shape : forall ct (tc : TypedComplexConst ct),
  float_constant_runtimeb (fv_sf (cv_real (typed_complex_runtime tc))) = true.
Proof. intros ct tc; apply (tfc_shape (tcc_real tc)). Qed.
Lemma typed_complex_runtime_imag_shape : forall ct (tc : TypedComplexConst ct),
  float_constant_runtimeb (fv_sf (cv_imag (typed_complex_runtime tc))) = true.
Proof. intros ct tc; apply (tfc_shape (tcc_imag tc)). Qed.

(** neither runtime component is negative zero, infinity, or NaN (inherited from [tfc_runtime_not_*]). *)
Lemma typed_complex_runtime_real_not_neg_zero : forall ct (tc : TypedComplexConst ct),
  fv_sf (cv_real (typed_complex_runtime tc)) <> S754_zero true.
Proof. intros ct tc; apply tfc_runtime_not_neg_zero. Qed.
Lemma typed_complex_runtime_imag_not_neg_zero : forall ct (tc : TypedComplexConst ct),
  fv_sf (cv_imag (typed_complex_runtime tc)) <> S754_zero true.
Proof. intros ct tc; apply tfc_runtime_not_neg_zero. Qed.
Lemma typed_complex_runtime_real_not_nan : forall ct (tc : TypedComplexConst ct),
  fv_sf (cv_real (typed_complex_runtime tc)) <> S754_nan.
Proof. intros ct tc; apply tfc_runtime_not_nan. Qed.
Lemma typed_complex_runtime_imag_not_nan : forall ct (tc : TypedComplexConst ct),
  fv_sf (cv_imag (typed_complex_runtime tc)) <> S754_nan.
Proof. intros ct tc; apply tfc_runtime_not_nan. Qed.
Lemma typed_complex_runtime_real_not_inf : forall ct (tc : TypedComplexConst ct) s,
  fv_sf (cv_real (typed_complex_runtime tc)) <> S754_infinity s.
Proof. intros ct tc s; apply tfc_runtime_not_inf. Qed.
Lemma typed_complex_runtime_imag_not_inf : forall ct (tc : TypedComplexConst ct) s,
  fv_sf (cv_imag (typed_complex_runtime tc)) <> S754_infinity s.
Proof. intros ct tc s; apply tfc_runtime_not_inf. Qed.

(** the ONE complex-constant construction authority — round each component ONCE at the destination component
    format (via [round_typed_float]); fail if either component overflows; package the two typed floats. *)
Definition round_typed_complex (ct : ComplexType) (c : ComplexConst)
    : option (TypedComplexConst ct) :=
  match round_typed_float (complex_component_type ct) (cc_real c),
        round_typed_float (complex_component_type ct) (cc_imag c) with
  | Some tr, Some ti => Some (mkTCC tr ti)
  | _, _ => None
  end.

(** each component of a successful complex rounding is EXACTLY [round_typed_float] of that source component —
    the "rounds once per component" evidence (no third rounding, no aggregate reconstruction). *)
Lemma round_typed_complex_components : forall ct c tc,
  round_typed_complex ct c = Some tc ->
  round_typed_float (complex_component_type ct) (cc_real c) = Some (tcc_real tc)
  /\ round_typed_float (complex_component_type ct) (cc_imag c) = Some (tcc_imag tc).
Proof.
  intros ct c tc H; unfold round_typed_complex in H.
  destruct (round_typed_float (complex_component_type ct) (cc_real c)) as [tr|] eqn:Hr;
  destruct (round_typed_float (complex_component_type ct) (cc_imag c)) as [ti|] eqn:Hi;
    try discriminate.
  injection H as <-; cbn [tcc_real tcc_imag]; split; reflexivity.
Qed.

(** overflow (or any failure) of EITHER component rejects the WHOLE complex construction. *)
Lemma round_typed_complex_real_none : forall ct c,
  round_typed_float (complex_component_type ct) (cc_real c) = None ->
  round_typed_complex ct c = None.
Proof. intros ct c H; unfold round_typed_complex; rewrite H; reflexivity. Qed.

Lemma round_typed_complex_imag_none : forall ct c,
  round_typed_float (complex_component_type ct) (cc_imag c) = None ->
  round_typed_complex ct c = None.
Proof.
  intros ct c H; unfold round_typed_complex; rewrite H.
  destruct (round_typed_float (complex_component_type ct) (cc_real c)); reflexivity.
Qed.

(** representability is DERIVED from the existence of a typed result (reflected boolean).  If a rational-only
    helper is ever wanted it must PROJECT this, never compete with it. *)
Definition ComplexConstRepresentable (ct : ComplexType) (c : ComplexConst) : Prop :=
  exists tc, round_typed_complex ct c = Some tc.

Definition complex_representableb (ct : ComplexType) (c : ComplexConst) : bool :=
  match round_typed_complex ct c with Some _ => true | None => false end.

Lemma complex_representableb_spec : forall ct c,
  complex_representableb ct c = true <-> ComplexConstRepresentable ct c.
Proof.
  intros ct c; unfold complex_representableb, ComplexConstRepresentable.
  destruct (round_typed_complex ct c) as [tc|] eqn:E; split.
  - intros _; exists tc; reflexivity.
  - intros _; reflexivity.
  - discriminate.
  - intros [tc H]; discriminate.
Qed.
