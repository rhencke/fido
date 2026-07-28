(* The one authority for Go's two complex types, composed componentwise from [Float] and nothing above it. *)

From Stdlib Require Import ZArith List String Bool.
From Stdlib Require Import Floats.SpecFloat.
From Fido Require Import Float.

Local Open Scope Z_scope.

(* Exactly the two Go complex types. *)
Inductive Kind := C64 | C128.

Definition kind_equalb (a b : Kind) : bool :=
  match a, b with C64, C64 | C128, C128 => true | _, _ => false end.

Lemma kind_equalb_spec : forall a b, kind_equalb a b = true <-> a = b.
Proof. intros [] []; cbn; split; congruence. Qed.

(* The one component-format mapping; every complex precision and rounding property derives from it. *)
Definition component_kind (ct : Kind) : Float.Kind :=
  match ct with C64 => F32 | C128 => F64 end.

Lemma component_c64 : component_kind C64 = F32. Proof. reflexivity. Qed.
Lemma component_c128 : component_kind C128 = F64. Proof. reflexivity. Qed.

(* An exact complex constant: two canonical rational components, whose canonicality already lives in each. *)
Record Constant := MakeConstant { exact_real : Float.Constant ; exact_imaginary : Float.Constant }.

(* Componentwise decidable equality; the components are canonical, so this is Leibniz equality. *)
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

(* The exact complex zero, both components the unsigned canonical zero, and the real embedding. *)
Definition zero : Constant := MakeConstant Float.constant_zero Float.constant_zero.
Definition of_real (q : Float.Constant) : Constant := MakeConstant q Float.constant_zero.

Lemma constant_real_of_real : forall q, exact_real (of_real q) = q. Proof. reflexivity. Qed.
Lemma constant_imaginary_of_real : forall q, exact_imaginary (of_real q) = Float.constant_zero. Proof. reflexivity. Qed.

(* Decide that the exact imaginary component is exactly zero. *)
Definition constant_imaginary_is_zero (c : Constant) : bool := Float.constant_equalb (exact_imaginary c) Float.constant_zero.

(* Project the exact real component only when the imaginary component is exactly zero; this never rounds. *)
Definition real_if_imaginary_zero (c : Constant) : option Float.Constant :=
  if constant_imaginary_is_zero c then Some (exact_real c) else None.

Lemma real_if_imaginary_zero_some : forall c q,
  real_if_imaginary_zero c = Some q -> constant_imaginary_is_zero c = true /\ exact_real c = q.
Proof.
  intros c q H; unfold real_if_imaginary_zero in H.
  destruct (constant_imaginary_is_zero c) eqn:E; [ injection H as <-; split; reflexivity | discriminate ].
Qed.

(* The raw finite-decimal complex literal, whose meaning is each component's own decimal value. *)
Record Decimal := MakeDecimal { decimal_real : Float.Decimal ; decimal_imaginary : Float.Decimal }.

Definition decimal_value (d : Decimal) : Constant :=
  MakeConstant (Float.decimal_value (decimal_real d)) (Float.decimal_value (decimal_imaginary d)).

Lemma decimal_value_real : forall d, exact_real (decimal_value d) = Float.decimal_value (decimal_real d).
Proof. reflexivity. Qed.
Lemma decimal_value_imaginary : forall d, exact_imaginary (decimal_value d) = Float.decimal_value (decimal_imaginary d).
Proof. reflexivity. Qed.

(* The general runtime domain, so a runtime complex value may carry a signed zero, an infinity or a NaN. *)
Record Value (ct : Kind) := MakeValue {
  runtime_real : Float.Value (component_kind ct) ;
  runtime_imaginary : Float.Value (component_kind ct)
}.
Arguments MakeValue {ct} _ _.
Arguments runtime_real {ct} _.
Arguments runtime_imaginary {ct} _.

(* The typed complex constant: two already-coherent typed components, so no coherence field is duplicated. *)
Record TypedConstant (ct : Kind) := MakeTypedConstant {
  typed_real : Float.TypedConstant (component_kind ct) ;
  typed_imaginary : Float.TypedConstant (component_kind ct)
}.
Arguments MakeTypedConstant {ct} _ _.
Arguments typed_real {ct} _.
Arguments typed_imaginary {ct} _.

(* Both projections are pure component reads: no rounding, no reconstruction. *)
Definition typed_exact {ct} (tc : TypedConstant ct) : Constant :=
  MakeConstant (Float.exact (typed_real tc)) (Float.exact (typed_imaginary tc)).

Definition typed_runtime {ct} (tc : TypedConstant ct) : Value ct :=
  MakeValue (Float.runtime (typed_real tc)) (Float.runtime (typed_imaginary tc)).

(* The componentwise projection laws. *)
Lemma typed_exact_real : forall ct (tc : TypedConstant ct),
  exact_real (typed_exact tc) = Float.exact (typed_real tc). Proof. reflexivity. Qed.
Lemma typed_exact_imaginary : forall ct (tc : TypedConstant ct),
  exact_imaginary (typed_exact tc) = Float.exact (typed_imaginary tc). Proof. reflexivity. Qed.
Lemma typed_runtime_real : forall ct (tc : TypedConstant ct),
  runtime_real (typed_runtime tc) = Float.runtime (typed_real tc). Proof. reflexivity. Qed.
Lemma typed_runtime_imaginary : forall ct (tc : TypedConstant ct),
  runtime_imaginary (typed_runtime tc) = Float.runtime (typed_imaginary tc). Proof. reflexivity. Qed.

(* Each runtime component reads back to its exact component, inherited per component. *)
Lemma typed_runtime_real_coherent : forall ct (tc : TypedConstant ct),
  Float.ieee_to_constant (Float.ieee (runtime_real (typed_runtime tc)))
    = Some (exact_real (typed_exact tc)).
Proof. intros ct tc; apply (Float.coherent (typed_real tc)). Qed.
Lemma typed_runtime_imaginary_coherent : forall ct (tc : TypedConstant ct),
  Float.ieee_to_constant (Float.ieee (runtime_imaginary (typed_runtime tc)))
    = Some (exact_imaginary (typed_exact tc)).
Proof. intros ct tc; apply (Float.coherent (typed_imaginary tc)). Qed.

(* Each runtime component is finite or positive zero. *)
Lemma typed_runtime_real_shape : forall ct (tc : TypedConstant ct),
  Float.constant_runtimeb (Float.ieee (runtime_real (typed_runtime tc))) = true.
Proof. intros ct tc; apply (Float.shape (typed_real tc)). Qed.
Lemma typed_runtime_imaginary_shape : forall ct (tc : TypedConstant ct),
  Float.constant_runtimeb (Float.ieee (runtime_imaginary (typed_runtime tc))) = true.
Proof. intros ct tc; apply (Float.shape (typed_imaginary tc)). Qed.

(* Neither runtime component is a negative zero, an infinity or a NaN. *)
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

(* The one construction authority: round each component once at the destination format, or fail. *)
Definition round_typed (ct : Kind) (c : Constant)
    : option (TypedConstant ct) :=
  match round_typed_float (component_kind ct) (exact_real c),
        round_typed_float (component_kind ct) (exact_imaginary c) with
  | Some tr, Some ti => Some (MakeTypedConstant tr ti)
  | _, _ => None
  end.

(* Each component of a successful rounding is exactly one [round_typed_float] of that source component. *)
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

(* Failure of either component rejects the whole complex construction. *)
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

(* Representability is the reflected existence of a typed result. *)
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
