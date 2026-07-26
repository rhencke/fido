(** Complex — the ONE authority for Go's two complex types (complex64, complex128) as EXACT complex
    constants and intrinsically-coherent typed/runtime complex values, COMPOSED from the [Float] component
    authority.  It imports [Float] and NOTHING above it (no [Typing]) — the dependency direction is
    [Float] -> [Complex] -> [Syntax]/[Typing]/[Property]/[Render].

    The permanent semantic distinction mirrors the scalar float layer, one level up:

      exact untyped [Constant]           (a pair of exact canonical rational [Float.Constant] components)
        -> intrinsic [TypedConstant ct]  (a pair of coherent [Float.TypedConstant] components)
        -> general runtime [Value ct] (a pair of general [Float.Value] components — may be NaN/Inf/-0)

    A [Kind] fixes its component [Float.Kind] via the ONE mapping [component_kind] (C64->F32,
    C128->F64); ALL precision / exponent / keyword / rounding behaviour DERIVES from that mapping and the
    component [Float] authority.  There is NO complex-specific float format, NO duplicated float coherence,
    and NO complex arithmetic — a compound typed constant is built from already-coherent typed components. *)

From Stdlib Require Import ZArith List String Bool.
From Stdlib Require Import Floats.SpecFloat.
From Fido Require Import Float.

Local Open Scope Z_scope.

(** the one complex type authority *)

(** exactly the two Go complex types.  No placeholder future constructors. *)
Inductive Kind := C64 | C128.

Definition kind_equalb (a b : Kind) : bool :=
  match a, b with C64, C64 | C128, C128 => true | _, _ => false end.

Lemma kind_equalb_spec : forall a b, kind_equalb a b = true <-> a = b.
Proof. intros [] []; cbn; split; congruence. Qed.

(** the ONE component-format mapping — every complex precision/exponent/runtime property derives from it. *)
Definition component_kind (ct : Kind) : Float.Kind :=
  match ct with C64 => F32 | C128 => F64 end.

Lemma component_c64 : component_kind C64 = F32. Proof. reflexivity. Qed.
Lemma component_c128 : component_kind C128 = F64. Proof. reflexivity. Qed.

(** exact untyped complex constants *)

(** an EXACT complex constant: two exact canonical rational [Float.Constant] components — real and imaginary.  It
    carries NO signed zero, infinity, NaN, runtime [spec_float], or source spelling; each component's
    canonicality already lives in its [Float.Constant], so no aggregate proof field is added. *)
Record Constant := make_constant { exact_real : Float.Constant ; exact_imaginary : Float.Constant }.

(** decidable equality DERIVED from [Float.Constant] equality, componentwise (canonical, so it is Leibniz). *)
Definition constant_equalb (a b : Constant) : bool :=
  Float.constant_equalb (exact_real a) (exact_real b) && Float.constant_equalb (exact_imaginary a) (exact_imaginary b).

Lemma constant_equalb_spec : forall a b, constant_equalb a b = true <-> a = b.
Proof.
  intros a b; unfold constant_equalb; split.
  - intro H; apply andb_true_iff in H as [Hr Hi];
    apply Float.constant_equalb_eq in Hr; apply Float.constant_equalb_eq in Hi;
    destruct a, b; cbn in *; subst; reflexivity.
  - intro H; subst b; apply andb_true_iff; split; apply Float.constant_equalb_eq; reflexivity.
Qed.

(** the exact complex zero (both components the unsigned canonical zero) and the real embedding. *)
Definition zero : Constant := make_constant Float.constant_zero Float.constant_zero.
Definition of_real (q : Float.Constant) : Constant := make_constant q Float.constant_zero.

Lemma constant_real_of_real : forall q, exact_real (of_real q) = q. Proof. reflexivity. Qed.
Lemma constant_imaginary_of_real : forall q, exact_imaginary (of_real q) = Float.constant_zero. Proof. reflexivity. Qed.

(** decide the exact imaginary component is exactly zero (rational equality over canonical [Float.Constant]). *)
Definition constant_imaginary_is_zero (c : Constant) : bool := Float.constant_equalb (exact_imaginary c) Float.constant_zero.

(** project the exact real component ONLY when the exact imaginary component is exactly zero (a pure exact
    helper — it does NOT round; complex->scalar destination rounding happens in the ONE [Typing.convert_constant]). *)
Definition real_if_imaginary_zero (c : Constant) : option Float.Constant :=
  if constant_imaginary_is_zero c then Some (exact_real c) else None.

Lemma real_if_imaginary_zero_some : forall c q,
  real_if_imaginary_zero c = Some q -> constant_imaginary_is_zero c = true /\ exact_real c = q.
Proof.
  intros c q H; unfold real_if_imaginary_zero in H.
  destruct (constant_imaginary_is_zero c) eqn:E; [ injection H as <-; split; reflexivity | discriminate ].
Qed.

(** the intrinsic raw finite-decimal complex literal: two [Float.Decimal] components.  Its exact meaning is
    [Float.decimal_value] applied independently to each component — the internal [Constant] domain is WIDER
    than this raw decimal-literal domain. *)
Record Decimal := make_decimal { decimal_real : Float.Decimal ; decimal_imaginary : Float.Decimal }.

Definition decimal_value (d : Decimal) : Constant :=
  make_constant (Float.decimal_value (decimal_real d)) (Float.decimal_value (decimal_imaginary d)).

Lemma decimal_value_real : forall d, exact_real (decimal_value d) = Float.decimal_value (decimal_real d).
Proof. reflexivity. Qed.
Lemma decimal_value_imaginary : forall d, exact_imaginary (decimal_value d) = Float.decimal_value (decimal_imaginary d).
Proof. reflexivity. Qed.

(** general runtime complex values and intrinsic typed complex constants *)

(** the GENERAL runtime complex domain: two general [Float.Value] components at the type's component format.
    Because each component is a general [Float.Value], a runtime complex value MAY contain finite, +/-0,
    infinity, or NaN components.  This domain is NOT narrowed to constant-origin values (future runtime
    complex operations need the full IEEE component domain). *)
Record Value (ct : Kind) := make_value {
  runtime_real : Float.Value (component_kind ct) ;
  runtime_imaginary : Float.Value (component_kind ct)
}.
Arguments make_value {ct} _ _.
Arguments runtime_real {ct} _.
Arguments runtime_imaginary {ct} _.

(** the INTRINSIC typed complex constant: two coherent [Float.TypedConstant] components.  Each component already
    carries exact destination-rounded rational meaning, its stored canonical runtime IEEE value, exact/runtime
    coherence, AND the finite-or-+0 constant shape — so NO coherence field is duplicated here. *)
Record TypedConstant (ct : Kind) := make_typed_constant {
  typed_real : Float.TypedConstant (component_kind ct) ;
  typed_imaginary : Float.TypedConstant (component_kind ct)
}.
Arguments make_typed_constant {ct} _ _.
Arguments typed_real {ct} _.
Arguments typed_imaginary {ct} _.

(** the exact/runtime projections — BOTH are pure component projections (no rounding, no reconstruction). *)
Definition typed_exact {ct} (tc : TypedConstant ct) : Constant :=
  make_constant (Float.exact (typed_real tc)) (Float.exact (typed_imaginary tc)).

Definition typed_runtime {ct} (tc : TypedConstant ct) : Value ct :=
  make_value (Float.runtime (typed_real tc)) (Float.runtime (typed_imaginary tc)).

(** ---- componentwise projection laws (short, definitional) ---- *)
Lemma typed_exact_real : forall ct (tc : TypedConstant ct),
  exact_real (typed_exact tc) = Float.exact (typed_real tc). Proof. reflexivity. Qed.
Lemma typed_exact_imaginary : forall ct (tc : TypedConstant ct),
  exact_imaginary (typed_exact tc) = Float.exact (typed_imaginary tc). Proof. reflexivity. Qed.
Lemma typed_runtime_real : forall ct (tc : TypedConstant ct),
  runtime_real (typed_runtime tc) = Float.runtime (typed_real tc). Proof. reflexivity. Qed.
Lemma typed_runtime_imaginary : forall ct (tc : TypedConstant ct),
  runtime_imaginary (typed_runtime tc) = Float.runtime (typed_imaginary tc). Proof. reflexivity. Qed.

(** each runtime component reads back to its EXACT component (inherited from [Float.coherent], per component). *)
Lemma typed_runtime_real_coherent : forall ct (tc : TypedConstant ct),
  Float.ieee_to_constant (Float.ieee (runtime_real (typed_runtime tc)))
    = Some (exact_real (typed_exact tc)).
Proof. intros ct tc; apply (Float.coherent (typed_real tc)). Qed.
Lemma typed_runtime_imaginary_coherent : forall ct (tc : TypedConstant ct),
  Float.ieee_to_constant (Float.ieee (runtime_imaginary (typed_runtime tc)))
    = Some (exact_imaginary (typed_exact tc)).
Proof. intros ct tc; apply (Float.coherent (typed_imaginary tc)). Qed.

(** each runtime component is finite or +0 (inherited from [Float.shape]). *)
Lemma typed_runtime_real_shape : forall ct (tc : TypedConstant ct),
  Float.constant_runtimeb (Float.ieee (runtime_real (typed_runtime tc))) = true.
Proof. intros ct tc; apply (Float.shape (typed_real tc)). Qed.
Lemma typed_runtime_imaginary_shape : forall ct (tc : TypedConstant ct),
  Float.constant_runtimeb (Float.ieee (runtime_imaginary (typed_runtime tc))) = true.
Proof. intros ct tc; apply (Float.shape (typed_imaginary tc)). Qed.

(** neither runtime component is negative zero, infinity, or NaN (inherited from [tfc_runtime_not_*]). *)
Lemma typed_runtime_real_not_neg_zero : forall ct (tc : TypedConstant ct),
  Float.ieee (runtime_real (typed_runtime tc)) <> S754_zero true.
Proof. intros ct tc; apply Float.typed_runtime_not_neg_zero. Qed.
Lemma typed_runtime_imaginary_not_neg_zero : forall ct (tc : TypedConstant ct),
  Float.ieee (runtime_imaginary (typed_runtime tc)) <> S754_zero true.
Proof. intros ct tc; apply Float.typed_runtime_not_neg_zero. Qed.
Lemma typed_runtime_real_not_nan : forall ct (tc : TypedConstant ct),
  Float.ieee (runtime_real (typed_runtime tc)) <> S754_nan.
Proof. intros ct tc; apply Float.typed_runtime_not_nan. Qed.
Lemma typed_runtime_imaginary_not_nan : forall ct (tc : TypedConstant ct),
  Float.ieee (runtime_imaginary (typed_runtime tc)) <> S754_nan.
Proof. intros ct tc; apply Float.typed_runtime_not_nan. Qed.
Lemma typed_runtime_real_not_inf : forall ct (tc : TypedConstant ct) s,
  Float.ieee (runtime_real (typed_runtime tc)) <> S754_infinity s.
Proof. intros ct tc s; apply Float.typed_runtime_not_inf. Qed.
Lemma typed_runtime_imaginary_not_inf : forall ct (tc : TypedConstant ct) s,
  Float.ieee (runtime_imaginary (typed_runtime tc)) <> S754_infinity s.
Proof. intros ct tc s; apply Float.typed_runtime_not_inf. Qed.

(** the ONE complex-constant construction authority — round each component ONCE at the destination component
    format (via [round_typed_float]); fail if either component overflows; package the two typed floats. *)
Definition round_typed (ct : Kind) (c : Constant)
    : option (TypedConstant ct) :=
  match round_typed_float (component_kind ct) (exact_real c),
        round_typed_float (component_kind ct) (exact_imaginary c) with
  | Some tr, Some ti => Some (make_typed_constant tr ti)
  | _, _ => None
  end.

(** each component of a successful complex rounding is EXACTLY [round_typed_float] of that source component —
    the "rounds once per component" evidence (no third rounding, no aggregate reconstruction). *)
Lemma round_typed_components : forall ct c tc,
  round_typed ct c = Some tc ->
  round_typed_float (component_kind ct) (exact_real c) = Some (typed_real tc)
  /\ round_typed_float (component_kind ct) (exact_imaginary c) = Some (typed_imaginary tc).
Proof.
  intros ct c tc H; unfold round_typed in H.
  destruct (round_typed_float (component_kind ct) (exact_real c)) as [tr|] eqn:Hr;
  destruct (round_typed_float (component_kind ct) (exact_imaginary c)) as [ti|] eqn:Hi;
    try discriminate.
  injection H as <-; cbn [typed_real typed_imaginary]; split; reflexivity.
Qed.

(** overflow (or any failure) of EITHER component rejects the WHOLE complex construction. *)
Lemma round_typed_real_none : forall ct c,
  round_typed_float (component_kind ct) (exact_real c) = None ->
  round_typed ct c = None.
Proof. intros ct c H; unfold round_typed; rewrite H; reflexivity. Qed.

Lemma round_typed_imaginary_none : forall ct c,
  round_typed_float (component_kind ct) (exact_imaginary c) = None ->
  round_typed ct c = None.
Proof.
  intros ct c H; unfold round_typed; rewrite H.
  destruct (round_typed_float (component_kind ct) (exact_real c)); reflexivity.
Qed.

(** representability is DERIVED from the existence of a typed result (reflected boolean).  If a rational-only
    helper is ever wanted it must PROJECT this, never compete with it. *)
Definition Representable (ct : Kind) (c : Constant) : Prop :=
  exists tc, round_typed ct c = Some tc.

Definition representableb (ct : Kind) (c : Constant) : bool :=
  match round_typed ct c with Some _ => true | None => false end.

Lemma representableb_spec : forall ct c,
  representableb ct c = true <-> Representable ct c.
Proof.
  intros ct c; unfold representableb, Representable.
  destruct (round_typed ct c) as [tc|] eqn:E; split.
  - intros _; exists tc; reflexivity.
  - intros _; reflexivity.
  - discriminate.
  - intros [tc H]; discriminate.
Qed.
