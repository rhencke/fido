(** Fido entry point.  (Sibling proof theory [concurrency.v] ties happens-before
    to actual execution traces — [hbt_irrefl], and [reachable_wf]/[reachable_hb_strict]
    which earn it from a concurrent operational semantics; it emits no Go.) *)

From Fido Require Import preamble.
From Stdlib Require Import Numbers.Cyclic.Int63.Uint63.
From Stdlib Require Import Numbers.Cyclic.Int63.Sint63.
From Stdlib Require Import Floats.PrimFloat.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.String.   (* string-literal scope for the String-types demo *)
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope uint63_scope.
Open Scope float_scope.

Definition add (n m : int) : int := PrimInt63.add n m.

Theorem add_comm : forall n m : int, add n m = add m n.
Proof. intros n m. unfold add. apply Uint63.add_comm. Qed.

Theorem add_assoc : forall n m p : int, add n (add m p) = add (add n m) p.
Proof. intros n m p. unfold add. apply Uint63.add_assoc. Qed.

Definition sub (n m : int) : int := PrimInt63.sub n m.

(** Foundational accuracy: [int] is interpreted with SIGNED (Sint63) semantics,
    matching Go's [int64].  In Go, [2 - 5] is [-3]; the signed model agrees.
    (The old unsigned reading would wrongly give [2^63 - 3].)  This lemma is
    machine-checked, so the model provably matches what the extracted Go does. *)
Example sub_signed_matches_go : Sint63.to_Z (sub 2 5) = (-3)%Z.
Proof. now vm_compute. Qed.

(** WHY the plugin REJECTS [Nat.sub] (Coq nat → Go uint): nat subtraction is
    TRUNCATED monus, so [3 - 5 = 0] — lowering it to Go uint's WRAPPING [-]
    ([3 - 5 = 2^64-2]) would be silently wrong.  Machine-checked, so the rejection
    rests on a fact, not a hunch. *)
Example nat_sub_is_truncated : Nat.sub 3 5 = 0%nat.
Proof. reflexivity. Qed.

(** WHY the plugin REJECTS the UNSIGNED [PrimInt63.ltb]/[leb] for [int]: on a
    high-bit value they disagree with Go's SIGNED int64 [<].  Take [-1]
    ([PrimInt63.sub 0 1], i.e. the large [2^63-1] unsigned): unsigned [ltb (-1) 0]
    is [false], but the SIGNED [Sint63.ltb (-1) 0] is [true] — and Go's [-1 < 0]
    on int64 is [true].  So only the signed form (which [Sint63.ltb] reduces to)
    matches Go.  Both machine-checked. *)
Example ltb_unsigned_neg_false : PrimInt63.ltb (PrimInt63.sub 0 1) 0 = false.
Proof. now vm_compute. Qed.
Example ltb_signed_neg_true : Sint63.ltb (PrimInt63.sub 0 1) 0 = true.
Proof. now vm_compute. Qed.

(** OVERFLOW IS PROVABLE — the thing Go cannot do.  Go silently wraps integer
    overflow at runtime and only catches *constant* overflow at compile time.
    Here, "this addition does not overflow" is a Rocq predicate, and when it
    holds the machine result equals the EXACT mathematical sum (no wrap). *)
Definition no_overflow_add (n m : int) : Prop :=
  (Sint63.to_Z Sint63.min_int <= Sint63.to_Z n + Sint63.to_Z m
                                <= Sint63.to_Z Sint63.max_int)%Z.

Theorem add_no_overflow_exact : forall n m : int,
  no_overflow_add n m ->
  Sint63.to_Z (PrimInt63.add n m) = (Sint63.to_Z n + Sint63.to_Z m)%Z.
Proof.
  intros n m H. unfold no_overflow_add in H.
  rewrite Sint63.to_Z_min, Sint63.to_Z_max in H.
  rewrite (Sint63.to_Z_cmodwB (PrimInt63.add n m)).
  rewrite Uint63.add_spec, Sint63.cmod_mod.
  rewrite <- (Sint63.cmod_mod (Uint63.to_Z n + Uint63.to_Z m)).
  replace ((Uint63.to_Z n + Uint63.to_Z m) mod wB)%Z
     with ((Sint63.to_Z n + Sint63.to_Z m) mod wB)%Z by
    (rewrite (Zplus_mod (Sint63.to_Z n) (Sint63.to_Z m));
     rewrite !Sint63.to_Z_mod_Uint63to_Z; reflexivity).
  rewrite Sint63.cmod_mod.
  apply Sint63.cmod_small. lia.
Qed.

(** Concrete instance, machine-checked: 10^12 + 2·10^12 does not overflow and
    is exactly 3·10^12. *)
Example add_exact_demo :
  Sint63.to_Z (PrimInt63.add 1000000000000 2000000000000) = 3000000000000%Z.
Proof. now vm_compute. Qed.

(** Honest about the limit: at the top of the (62-bit) range, addition wraps —
    so [no_overflow_add] fails there and [add_no_overflow_exact] does not apply.
    The model knows exactly where it wraps, which is what makes overflow
    provable: you prove you stay below the boundary. *)
Example add_wraps_at_boundary :
  Sint63.to_Z (PrimInt63.add Sint63.max_int 1) = Sint63.to_Z Sint63.min_int.
Proof. now vm_compute. Qed.

(** SAFE-BY-CONSTRUCTION ARITHMETIC.  Go's [+]/[-]/[*] silently WRAP on overflow;
    overflow-freedom is a *provable* property here (above), but raw [add]/[sub]/
    [mul] don't *force* you to prove it.  [add_nz]/[sub_nz]/[mul_nz] do: each
    DEMANDS a proof that the exact mathematical result is in range, then extracts
    to the raw machine op — which the proof has shown does not wrap, so the result
    equals the exact value (by the [*_no_overflow_exact] theorems).  Raw [add]/
    [sub]/[mul] remain the opt-in WRAPPING forms (like div_nz vs the raw divide).
    The in-range proof is discharged by [now vm_compute] for concrete operands. *)
Definition no_overflow_sub (n m : int) : Prop :=
  (Sint63.to_Z Sint63.min_int <= Sint63.to_Z n - Sint63.to_Z m
                                <= Sint63.to_Z Sint63.max_int)%Z.
Definition no_overflow_mul (n m : int) : Prop :=
  (Sint63.to_Z Sint63.min_int <= Sint63.to_Z n * Sint63.to_Z m
                                <= Sint63.to_Z Sint63.max_int)%Z.

Theorem sub_no_overflow_exact : forall n m : int,
  no_overflow_sub n m ->
  Sint63.to_Z (PrimInt63.sub n m) = (Sint63.to_Z n - Sint63.to_Z m)%Z.
Proof.
  intros n m H. unfold no_overflow_sub in H.
  rewrite Sint63.to_Z_min, Sint63.to_Z_max in H.
  rewrite (Sint63.to_Z_cmodwB (PrimInt63.sub n m)).
  rewrite Uint63.sub_spec, Sint63.cmod_mod.
  rewrite <- (Sint63.cmod_mod (Uint63.to_Z n - Uint63.to_Z m)).
  replace ((Uint63.to_Z n - Uint63.to_Z m) mod wB)%Z
     with ((Sint63.to_Z n - Sint63.to_Z m) mod wB)%Z by
    (rewrite (Zminus_mod (Sint63.to_Z n) (Sint63.to_Z m));
     rewrite !Sint63.to_Z_mod_Uint63to_Z; reflexivity).
  rewrite Sint63.cmod_mod.
  apply Sint63.cmod_small. lia.
Qed.

Theorem mul_no_overflow_exact : forall n m : int,
  no_overflow_mul n m ->
  Sint63.to_Z (PrimInt63.mul n m) = (Sint63.to_Z n * Sint63.to_Z m)%Z.
Proof.
  intros n m H. unfold no_overflow_mul in H.
  rewrite Sint63.to_Z_min, Sint63.to_Z_max in H.
  rewrite (Sint63.to_Z_cmodwB (PrimInt63.mul n m)).
  rewrite Uint63.mul_spec, Sint63.cmod_mod.
  rewrite <- (Sint63.cmod_mod (Uint63.to_Z n * Uint63.to_Z m)).
  replace ((Uint63.to_Z n * Uint63.to_Z m) mod wB)%Z
     with ((Sint63.to_Z n * Sint63.to_Z m) mod wB)%Z by
    (rewrite (Zmult_mod (Sint63.to_Z n) (Sint63.to_Z m));
     rewrite !Sint63.to_Z_mod_Uint63to_Z; reflexivity).
  rewrite Sint63.cmod_mod.
  (* the product is non-linear; abstract it so the bounds are linear for [lia] *)
  apply Sint63.cmod_small.
  set (p := (Sint63.to_Z n * Sint63.to_Z m)%Z) in *. lia.
Qed.

Definition add_nz (n m : int) (_ : no_overflow_add n m) : int := PrimInt63.add n m.
Definition sub_nz (n m : int) (_ : no_overflow_sub n m) : int := PrimInt63.sub n m.
Definition mul_nz (n m : int) (_ : no_overflow_mul n m) : int := PrimInt63.mul n m.

(** Machine-checked: the guarded ops give the exact mathematical result.
    ([now vm_compute] discharges the in-range obligation: [vm_compute] unfolds
    [Z.le] to a comparison, which [now]'s finisher closes — [lia] cannot, as it
    no longer sees arithmetic.) *)
Example add_nz_exact :
  Sint63.to_Z (add_nz 1000000000000 2000000000000 ltac:(now vm_compute))
  = 3000000000000%Z.
Proof. now vm_compute. Qed.
Example mul_nz_exact :
  Sint63.to_Z (mul_nz 1000000 1000000 ltac:(now vm_compute)) = 1000000000000%Z.
Proof. now vm_compute. Qed.

(** Arithmetic you can only call with a proven-in-range result.  Prints
    10^12 + 2·10^12 = 3·10^12 (proven no wrap) and 1000·1000 = 10^6. *)
(** OVERFLOW-SAFE ARITHMETIC AT THE FULL WIDTH (A4.3: the int model migrated off the
    bounded [Sint63] onto the faithful [GoI64]).  Fido's signature property — "this
    arithmetic does not overflow" as a Rocq THEOREM — now holds on the TRUE int64, not
    just [±2^62].  Each guarded op DEMANDS a proof the exact result is representable
    ([in_i64 (exact) = true], dischargeable by [eq_refl] for concrete operands — the
    same shape as [div_nz], and Go's untyped-constant-overflow analog), then the
    wrapping machine op is EXACT (no wrap), by the [*_no_overflow_exact] theorems.  Raw
    [i64_add]/[i64_sub]/[i64_mul] stay the opt-in WRAPPING forms. *)
Theorem i64_sub_no_overflow_exact : forall a b : GoI64,
  in_i64 (i64raw a - i64raw b)%Z = true -> i64raw (i64_sub a b) = (i64raw a - i64raw b)%Z.
Proof.
  intros [a] [b]. unfold in_i64, i64_sub, wrap64. cbn. intros H.
  apply andb_prop in H. destruct H as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  rewrite Z.mod_small by lia. lia.
Qed.
Theorem i64_mul_no_overflow_exact : forall a b : GoI64,
  in_i64 (i64raw a * i64raw b)%Z = true -> i64raw (i64_mul a b) = (i64raw a * i64raw b)%Z.
Proof.
  intros [a] [b]. unfold in_i64, i64_mul, wrap64. cbn. intros H.
  apply andb_prop in H. destruct H as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  rewrite Z.mod_small by lia. lia.
Qed.

Definition i64_no_overflow_add (a b : GoI64) : Prop := in_i64 (i64raw a + i64raw b) = true.
Definition i64_no_overflow_sub (a b : GoI64) : Prop := in_i64 (i64raw a - i64raw b) = true.
Definition i64_no_overflow_mul (a b : GoI64) : Prop := in_i64 (i64raw a * i64raw b) = true.
Definition i64_add_nz (a b : GoI64) (_ : i64_no_overflow_add a b) : GoI64 := i64_add a b.
Definition i64_sub_nz (a b : GoI64) (_ : i64_no_overflow_sub a b) : GoI64 := i64_sub a b.
Definition i64_mul_nz (a b : GoI64) (_ : i64_no_overflow_mul a b) : GoI64 := i64_mul a b.

(** The guarded ops give the EXACT result — proof discharged by [eq_refl] (the in-range
    obligation is a decidable [bool] equation that computes). *)
Example i64_add_nz_exact :
  i64raw (i64_add_nz (1000000000000)%i64 (2000000000000)%i64 eq_refl) = 3000000000000%Z.
Proof. now vm_compute. Qed.
Example i64_mul_nz_exact :
  i64raw (i64_mul_nz (1000000)%i64 (1000000)%i64 eq_refl) = 1000000000000%Z.
Proof. now vm_compute. Qed.

Definition overflow_safe_demo : IO unit :=
  println [ any (i64_add_nz (1000000000000)%i64 (2000000000000)%i64 eq_refl)
          ; any (i64_mul_nz (1000)%i64 (1000)%i64 eq_refl) ].
  (* prints: 3000000000000 1000000 — full-width GoI64, proven no wrap *)

(** SAFE-BY-CONSTRUCTION DIVISION (closes the div-by-zero gap).  Go panics on
    [n / 0]; Rocq's division is total ([_ / 0 = 0]).  Emitting a raw [/] would be
    silently unsound, so the plugin emits no bare integer [/]/[%].  Instead
    [div_nz]/[mod_nz] are evidence-carrying: they DEMAND a proof that the divisor
    is non-zero ([(d =? 0) = false], discharged by [eq_refl] for a literal), and
    only then extract to Go's unguarded [n / d] / [n % d] — the proof has already
    ruled out the panic.  Underneath they are [PrimInt63.divs]/[mods], the signed
    primitives that truncate toward zero exactly like Go's int64.  (Raw
    [PrimInt63.divs] remains the escape hatch — Go panics on a zero divisor.) *)
Definition div_nz (n d : int) (_ : (d =? 0)%uint63 = false) : int := PrimInt63.divs n d.
Definition mod_nz (n d : int) (_ : (d =? 0)%uint63 = false) : int := PrimInt63.mods n d.

(** ===== Go spec conformance: "Integer operators" (go.dev/ref/spec#Integer_operators)
    plus "Integer overflow" (#Integer_overflow) — the SOURCE of div_nz/mod_nz's
    behavior. =====

    Spec: "the integer quotient q = x / y and remainder r = x % y satisfy
    x = q*y + r  and  |r| < |y|, with x / y truncated towards zero".  The spec's
    own example table is reproduced below and machine-checked against our model
    (so this is conformance, not assertion). *)
Example spec_div_5_3    : Sint63.to_Z (div_nz 5 3 eq_refl)            = 1%Z.    Proof. now vm_compute. Qed.
Example spec_mod_5_3    : Sint63.to_Z (mod_nz 5 3 eq_refl)            = 2%Z.    Proof. now vm_compute. Qed.
Example spec_div_n5_3   : Sint63.to_Z (div_nz (-5)%sint63 3 eq_refl)  = (-1)%Z. Proof. now vm_compute. Qed.
Example spec_mod_n5_3   : Sint63.to_Z (mod_nz (-5)%sint63 3 eq_refl)  = (-2)%Z. Proof. now vm_compute. Qed.
Example spec_div_5_n3   : Sint63.to_Z (div_nz 5 (-3)%sint63 eq_refl)  = (-1)%Z. Proof. now vm_compute. Qed.
Example spec_mod_5_n3   : Sint63.to_Z (mod_nz 5 (-3)%sint63 eq_refl)  = 2%Z.    Proof. now vm_compute. Qed.
Example spec_div_n5_n3  : Sint63.to_Z (div_nz (-5)%sint63 (-3)%sint63 eq_refl) = 1%Z.    Proof. now vm_compute. Qed.
Example spec_mod_n5_n3  : Sint63.to_Z (mod_nz (-5)%sint63 (-3)%sint63 eq_refl) = (-2)%Z. Proof. now vm_compute. Qed.

(** Spec, the ONE exception: "if the dividend x is the most negative value for the
    int type of x, the quotient q = x / -1 is equal to x (and r = 0) due to
    two's-complement integer overflow".  For our [int] = Sint63 the most-negative
    value is [Sint63.min_int] (= -2^62, the analogue of int64's -2^63); we honor
    the rule — no panic, wraps to itself. *)
Example spec_div_minint_neg1 :
  div_nz Sint63.min_int (-1)%sint63 eq_refl = Sint63.min_int.
Proof. now vm_compute. Qed.
Example spec_mod_minint_neg1 :
  Sint63.to_Z (mod_nz Sint63.min_int (-1)%sint63 eq_refl) = 0%Z.
Proof. now vm_compute. Qed.

(** Division you can only call with a proven-nonzero divisor.  Prints 17/5 = 3
    and 17%5 = 2.  The [eq_refl] discharges [(5 =? 0) = false] at compile time. *)
Definition div_demo : IO unit :=
  println [any (div_nz 17 5 eq_refl); any (mod_nz 17 5 eq_refl)].   (* prints: 3 2 *)

(** float64 is Rocq's primitive [PrimFloat] = IEEE 754 double, the same as Go's
    float64, so arithmetic agrees bit-for-bit.  This exercises the otherwise-
    unused float primitive end-to-end.  (Go's [println] formats float64 in
    scientific notation — that is Go's builtin behaviour, captured by the
    golden.) *)
Definition float_demo : IO unit :=
  println [ any (PrimFloat.add 1.5 2.25)%float     (* 3.75 *)
          ; any (PrimFloat.div 1.0 4.0)%float ].   (* 0.25 (exact in binary) *)

(** Float COMPARISON lowers to Go's [<]/[<=]/[==] on [float64].  Both Coq's
    [PrimFloat] and Go follow IEEE 754, so the semantics match exactly — including
    NaN (every comparison with NaN is false) and signed zero ([0.0 == -0.0]).
    Comparisons bind looser than arithmetic, so [a + b < c] needs no parens. *)
Definition float_cmp_demo : IO unit :=
  bind (println [any (PrimFloat.ltb 1.5 2.5)%float]) (fun _ =>   (* 1.5 < 2.5  → true  *)
  bind (println [any (PrimFloat.leb 2.5 2.5)%float]) (fun _ =>   (* 2.5 <= 2.5 → true  *)
  bind (println [any (PrimFloat.eqb 1.5 1.5)%float]) (fun _ =>   (* 1.5 == 1.5 → true  *)
  println [any (PrimFloat.ltb 3.0 2.0)%float]))).               (* 3.0 < 2.0  → false *)

(** IEEE NaN faithfulness, MACHINE-CHECKED (Coq side): a NaN ([0.0/0.0]) is
    unordered — [NaN == NaN] and [NaN < x] are both [false].  This is exactly Go's
    float64 behaviour, so lowering [eqb]/[ltb] to [==]/[<] is faithful on the
    corner cases, not merely on ordinary values.  ([float_nan_demo] below shows
    Go agreeing at runtime.) *)
Example nan_eqb_false : PrimFloat.eqb (PrimFloat.div 0 0) (PrimFloat.div 0 0) = false.
Proof. now vm_compute. Qed.
Example nan_ltb_false : PrimFloat.ltb (PrimFloat.div 0 0) 1 = false.
Proof. now vm_compute. Qed.

(** Runtime witness (Go side) of the same NaN corner cases.  [z] is an opaque
    [float64] parameter (call site passes [0.0]) so [z/z] is a *runtime* NaN —
    a literal [0.0/0.0] would be a Go *compile-time* division-by-zero error. *)
Definition float_nan_demo (z : float) : IO unit :=
  bind (println [any (PrimFloat.eqb (PrimFloat.div z z) (PrimFloat.div z z))%float]) (fun _ =>
  println [any (PrimFloat.ltb (PrimFloat.div z z) 1)%float]).   (* NaN==NaN → false ; NaN<1 → false *)

(** Float unary negation [PrimFloat.opp] → Go [-x], IEEE-exact (flips the sign
    bit), needing no package import.  Ordinary values: [opp 1.5 = -1.5] and
    [opp (opp 2.0) = 2.0]. *)
Definition float_opp_demo : IO unit :=
  bind (println [any (PrimFloat.opp 1.5)%float]) (fun _ =>               (* -1.5 *)
  println [any (PrimFloat.opp (PrimFloat.opp 2.0))%float]).             (* 2.0 *)

(** The IEEE corner case: [opp] yields NEGATIVE zero, distinct in sign from [+0.0]
    (even though [-0.0 == +0.0]).  Witnessed by [1 / -0 = -inf < 0] (whereas
    [1 / +0 = +inf], not [< 0]).  MACHINE-CHECKED on the Coq side; the runtime
    [float_opp_sign_demo] — with an opaque [z := 0.0], so no untyped-constant
    folding of [-0.0] to [+0.0] — shows Go agrees. *)
Example opp_zero_is_neg :
  PrimFloat.ltb (PrimFloat.div 1 (PrimFloat.opp 0)) 0 = true.
Proof. now vm_compute. Qed.
Definition float_opp_sign_demo (z : float) : IO unit :=
  println [any (PrimFloat.ltb (PrimFloat.div 1 (PrimFloat.opp z)) 0)%float].  (* true *)

(** uint8 (byte): a precise, COMPUTABLE model of Go's 8-bit unsigned arithmetic.
    Each op masks the result back to [0,256), so it wraps mod 256 exactly like Go.
    The wrap is MACHINE-CHECKED (the model is just [land]/[add] on PrimInt63, which
    [vm_compute] reduces) — not asserted.  Note the contrast with [Nat.sub]: uint8
    subtraction genuinely WRAPS ([0 - 1 = 255]), which we model faithfully, whereas
    Coq's [Nat.sub] truncates ([0 - 1 = 0]) and is therefore rejected. *)
Example u8_add_wraps : u8_add (u8_lit 200 eq_refl) (u8_lit 100 eq_refl) = u8_lit 44 eq_refl.
Proof. now vm_compute. Qed.                                   (* 300 mod 256 = 44 *)
Example u8_mul_wraps : u8_mul (u8_lit 255 eq_refl) (u8_lit 255 eq_refl) = u8_lit 1 eq_refl.
Proof. now vm_compute. Qed.                                   (* 65025 mod 256 = 1 *)
Example u8_sub_wraps : u8_sub (u8_lit 0 eq_refl) (u8_lit 1 eq_refl) = u8_lit 255 eq_refl.
Proof. now vm_compute. Qed.                                   (* 0 - 1 wraps to 255 *)
Definition u8_demo : IO unit :=
  bind (println [any (u8_add (u8_lit 200 eq_refl) (u8_lit 100 eq_refl))]) (fun _ =>   (* 44  *)
  bind (println [any (u8_mul (u8_lit 255 eq_refl) (u8_lit 255 eq_refl))]) (fun _ =>   (* 1   *)
  bind (println [any (u8_sub (u8_lit 0 eq_refl)   (u8_lit 1 eq_refl))])   (fun _ =>   (* 255 *)
  println [any (u8_ltb (u8_lit 10 eq_refl) (u8_lit 20 eq_refl))]))).                  (* true *)

(** int8 (signed): the SAME template extended to two's-complement.  [int8(150)] is
    [-106] (150 sign-extended from 8 bits), and the wrap is machine-checked.  The
    sign-extension is the harder case the model must get right. *)
Example i8_add_wraps : i8_add (i8_lit 100 eq_refl) (i8_lit 50 eq_refl) = i8_lit (-106) eq_refl.
Proof. now vm_compute. Qed.                          (* 100+50=150 → -106 *)
Example i8_sub_wraps : i8_sub (i8_lit (-128) eq_refl) (i8_lit 1 eq_refl) = i8_lit 127 eq_refl.
Proof. now vm_compute. Qed.                          (* -128 - 1 wraps to 127 *)
Definition i8_demo : IO unit :=
  bind (println [any (i8_add (i8_lit 100 eq_refl) (i8_lit 50 eq_refl))])      (fun _ =>   (* -106 *)
  bind (println [any (i8_sub (i8_lit (-128) eq_refl) (i8_lit 1 eq_refl))])    (fun _ =>   (* 127  *)
  bind (println [any (i8_lit (-100) eq_refl)])                                (fun _ =>   (* -100 *)
  println [any (i8_ltb (i8_lit (-5) eq_refl) (i8_lit 3 eq_refl))]))).                     (* true *)

(** uint16 / int16: the SAME template at width 16, fully faithful on the carrier
    (16-bit products are [< 2^32], far below [2^62], so [mul] is exact).  The
    plugin recognises every [uN_*]/[iN_*] width with one parser — these needed
    only the Rocq definitions, no new plugin code. *)
Example u16_mul_wraps : u16_mul (u16_lit 1000 eq_refl) (u16_lit 1000 eq_refl) = u16_lit 16960 eq_refl.
Proof. now vm_compute. Qed.                    (* 1000000 mod 65536 = 16960 *)
Example i16_add_wraps : i16_add (i16_lit 30000 eq_refl) (i16_lit 10000 eq_refl) = i16_lit (-25536) eq_refl.
Proof. now vm_compute. Qed.                    (* 40000 wraps to -25536 in int16 *)
Definition u16_demo : IO unit :=
  bind (println [any (u16_add (u16_lit 60000 eq_refl) (u16_lit 10000 eq_refl))]) (fun _ =>   (* 4464 *)
  bind (println [any (u16_mul (u16_lit 1000 eq_refl)  (u16_lit 1000 eq_refl))])  (fun _ =>   (* 16960 *)
  println [any (i16_add (i16_lit 30000 eq_refl) (i16_lit 10000 eq_refl))])).                 (* -25536 *)

(** Bitwise operators (Go spec "Arithmetic operators": [& | ^ &^] and unary [^]).
    240 = 0b11110000, 60 = 0b00111100: AND=48, OR=252, XOR=204, AND-NOT=192,
    complement(240)=15.  Signed: [^int8(5) = -6], [int8(-1) &^ 5 = -6].  The
    MACHINE-CHECKED proofs below pin the values; this shows Go agreeing at run. *)
Example spec_u8_and    : u8_and    (u8_lit 240 eq_refl) (u8_lit 60 eq_refl) = u8_lit 48  eq_refl. Proof. now vm_compute. Qed.
Example spec_u8_or     : u8_or     (u8_lit 240 eq_refl) (u8_lit 60 eq_refl) = u8_lit 252 eq_refl. Proof. now vm_compute. Qed.
Example spec_u8_xor    : u8_xor    (u8_lit 240 eq_refl) (u8_lit 60 eq_refl) = u8_lit 204 eq_refl. Proof. now vm_compute. Qed.
Example spec_u8_andnot : u8_andnot (u8_lit 240 eq_refl) (u8_lit 60 eq_refl) = u8_lit 192 eq_refl. Proof. now vm_compute. Qed.
Example spec_u8_not    : u8_not    (u8_lit 240 eq_refl)                     = u8_lit 15  eq_refl. Proof. now vm_compute. Qed.
Example spec_i8_not    : i8_not    (i8_lit 5 eq_refl)                       = i8_lit (-6) eq_refl. Proof. now vm_compute. Qed.
Example spec_i8_andnot : i8_andnot (i8_lit (-1) eq_refl) (i8_lit 5 eq_refl) = i8_lit (-6) eq_refl. Proof. now vm_compute. Qed.
Definition bitwise_demo : IO unit :=
  bind (println [ any (u8_and    (u8_lit 240 eq_refl) (u8_lit 60 eq_refl))      (* 48  *)
                ; any (u8_or     (u8_lit 240 eq_refl) (u8_lit 60 eq_refl))      (* 252 *)
                ; any (u8_xor    (u8_lit 240 eq_refl) (u8_lit 60 eq_refl)) ])   (* 204 *)
       (fun _ =>
  bind (println [ any (u8_andnot (u8_lit 240 eq_refl) (u8_lit 60 eq_refl))      (* 192 *)
                ; any (u8_not    (u8_lit 240 eq_refl)) ])                       (* 15  *)
       (fun _ =>
  println [ any (i8_not    (i8_lit 5 eq_refl))                                  (* -6  *)
          ; any (i8_andnot (i8_lit (-1) eq_refl) (i8_lit 5 eq_refl)) ])).       (* -6  *)

(** Shifts (Go spec "Arithmetic operators": [<< >>]).  Evidence-carrying: the
    count must be proven non-negative ([eq_refl] for a literal); a negative count
    is unrepresentable (`u8_shl_neg`, a `Fail` in builtins.v).  MACHINE-CHECKED:
    over-width `<<` → 0 (no upper limit); signed `<<` wraps two's-complement;
    `>>` is ARITHMETIC for signed — `-3>>1 = -2` (toward −∞), distinct from
    `-3/2 = -1` (toward zero), and `-1>>3 = -1` (NOT 0). *)
Example spec_u8_shl     : u8_shl (u8_lit 1   eq_refl) 3 eq_refl = u8_lit 8    eq_refl. Proof. now vm_compute. Qed.
Example spec_u8_shl_ovf : u8_shl (u8_lit 1   eq_refl) 8 eq_refl = u8_lit 0    eq_refl. Proof. now vm_compute. Qed.
Example spec_u8_shr     : u8_shr (u8_lit 255 eq_refl) 4 eq_refl = u8_lit 15   eq_refl. Proof. now vm_compute. Qed.
Example spec_i8_shl_wrp : i8_shl (i8_lit 64  eq_refl) 1 eq_refl = i8_lit (-128) eq_refl. Proof. now vm_compute. Qed.
Example spec_i8_shr_flr : i8_shr (i8_lit (-3) eq_refl) 1 eq_refl = i8_lit (-2) eq_refl. Proof. now vm_compute. Qed.
Example spec_i8_shr_neg : i8_shr (i8_lit (-1) eq_refl) 3 eq_refl = i8_lit (-1) eq_refl. Proof. now vm_compute. Qed.
Definition shift_demo : IO unit :=
  bind (println [ any (u8_shl (u8_lit 1   eq_refl) 3 eq_refl)      (* 8  *)
                ; any (u8_shl (u8_lit 1   eq_refl) 8 eq_refl)      (* 0  (over-width) *)
                ; any (u8_shr (u8_lit 255 eq_refl) 4 eq_refl) ])   (* 15 *)
       (fun _ =>
  println [ any (i8_shl (i8_lit 64  eq_refl) 1 eq_refl)           (* -128 (wrap) *)
          ; any (i8_shr (i8_lit (-3) eq_refl) 1 eq_refl) ]).      (* -2 (arithmetic) *)

(** Numeric conversions (Go spec "Conversions").  Widen ([int_of_*]) preserves the
    value; narrow ([*_of_int]) TRUNCATES to the width — Go's [uint8(x)]/[int8(x)].
    Distinct types mix ONLY through an explicit conversion (the type checker
    rejects implicit mixing — `*_no_implicit`, `u8_of_i16_direct` `Fail`s), so the
    conversions are what make the distinct numeric types usable together.
    MACHINE-CHECKED: [uint8(1000)=232] (mod 256), [uint8(-1)=255], [int8(200)=-56]
    (two's-complement), widen [int(uint8 200)=200], cross-width [int16(uint8 200)]. *)
Example spec_u8_of_int_trunc : u8_of_int 1000        = u8_lit 232 eq_refl. Proof. now vm_compute. Qed.
Example spec_u8_of_int_neg   : u8_of_int (-1)%sint63 = u8_lit 255 eq_refl. Proof. now vm_compute. Qed.
Example spec_i8_of_int_wrap  : i8_of_int 200         = i8_lit (-56) eq_refl. Proof. now vm_compute. Qed.
Example spec_int_of_u8_widen : int_of_u8 (u8_lit 200 eq_refl) = 200%uint63. Proof. now vm_compute. Qed.
Example spec_i16_of_u8_cross : i16_of_int (int_of_u8 (u8_lit 200 eq_refl)) = i16_lit 200 eq_refl. Proof. now vm_compute. Qed.
Definition convert_demo : IO unit :=
  let a := u8_lit 200 eq_refl in           (* uint8 200 *)
  let b := i16_lit 1000 eq_refl in         (* int16 1000 *)
  bind (println [ any (int_of_u8 a)                      (* 200 (widen u8 → int) *)
                ; any (u8_of_int (int_of_i16 b)) ])      (* int16 1000 → uint8 = 232 *)
       (fun _ =>
  (* mix distinct types: widen the uint8 into int16 arithmetic via explicit conv *)
  println [ any (i16_add b (i16_of_int (int_of_u8 a))) ]).  (* 1000 + 200 = 1200 *)

(** Fixed-width division / remainder (Go spec "Arithmetic operators": [/ %]).
    Evidence-carrying: the divisor must be proven non-zero (`u8_div_zero` `Fail`).
    Signed division truncates toward zero (`-7/2 = -3`); the most-negative / `-1`
    case wraps two's-complement (`int8(-128)/int8(-1) = -128`). *)
Example spec_u8_div       : u8_div (u8_lit 200 eq_refl) (u8_lit 7 eq_refl) eq_refl = u8_lit 28 eq_refl. Proof. now vm_compute. Qed.
Example spec_u8_mod       : u8_mod (u8_lit 200 eq_refl) (u8_lit 7 eq_refl) eq_refl = u8_lit 4  eq_refl. Proof. now vm_compute. Qed.
Example spec_i8_div_trunc : i8_div (i8_lit (-7) eq_refl) (i8_lit 2 eq_refl) eq_refl = i8_lit (-3) eq_refl. Proof. now vm_compute. Qed.
Example spec_i8_div_ovf   : i8_div (i8_lit (-128) eq_refl) (i8_lit (-1) eq_refl) eq_refl = i8_lit (-128) eq_refl. Proof. now vm_compute. Qed.
Definition divmod_demo : IO unit :=
  println [ any (u8_div (u8_lit 200 eq_refl) (u8_lit 7 eq_refl) eq_refl)            (* 28 *)
          ; any (u8_mod (u8_lit 200 eq_refl) (u8_lit 7 eq_refl) eq_refl)            (* 4  *)
          ; any (i8_div (i8_lit (-128) eq_refl) (i8_lit (-1) eq_refl) eq_refl) ].   (* -128 (overflow) *)

(** uint32 / int32: the same template at width 32.  `4e9 + 1e9` wraps mod 2^32 →
    705032704; `2e9 + 2e9` wraps int32 → -294967296.  MULTIPLY is exact too: a
    32-bit product can exceed the 63-bit carrier, but the masked LOW 32 bits survive
    ([2^32 | 2^63]), so no Z model is needed — `100000*100000 = 1e10` wraps mod 2^32
    → 1410065408; `46341^2 = 2147488281 > 2^31` wraps int32 → -2147479015. *)
Example spec_u32_add_wrap : u32_add (u32_lit 4000000000 eq_refl) (u32_lit 1000000000 eq_refl) = u32_lit 705032704 eq_refl. Proof. now vm_compute. Qed.
Example spec_i32_add_wrap : i32_add (i32_lit 2000000000 eq_refl) (i32_lit 2000000000 eq_refl) = i32_lit (-294967296) eq_refl. Proof. now vm_compute. Qed.
Example spec_u32_mul_wrap : u32_mul (u32_lit 100000 eq_refl) (u32_lit 100000 eq_refl) = u32_lit 1410065408 eq_refl. Proof. now vm_compute. Qed.
Example spec_u32_mul_max  : u32_mul (u32_lit 4294967295 eq_refl) (u32_lit 4294967295 eq_refl) = u32_lit 1 eq_refl. Proof. now vm_compute. Qed.
Example spec_i32_mul_wrap : i32_mul (i32_lit 46341 eq_refl) (i32_lit 46341 eq_refl) = i32_lit (-2147479015) eq_refl. Proof. now vm_compute. Qed.
Definition u32_demo : IO unit :=
  bind (println [ any (u32_add (u32_lit 4000000000 eq_refl) (u32_lit 1000000000 eq_refl))  (* 705032704 *)
                ; any (i32_add (i32_lit 2000000000 eq_refl) (i32_lit 2000000000 eq_refl)) ])  (* -294967296 *)
       (fun _ =>
  bind (println [ any (u32_shl (u32_lit 1 eq_refl) 31 eq_refl) ])  (* 2147483648 = 2^31 *)
       (fun _ =>
  println [ any (u32_mul (u32_lit 100000 eq_refl) (u32_lit 100000 eq_refl))   (* 1410065408 *)
          ; any (i32_mul (i32_lit 46341 eq_refl) (i32_lit 46341 eq_refl)) ])).  (* -2147479015 *)

(** int64 — FULL-WIDTH signed 64-bit (Go spec "Numeric types"), the genuine
    Z-carried model.  Faithful across the WHOLE int64 range and wrapping at the TRUE
    2^63 — unlike the [Sint63] [int], which is faithful only within [-2^62, 2^62).
    [2^63-1 + 1] wraps to [-2^63]; [-2^63 - 1] wraps to [2^63-1]; [2^32 * 2^32 = 2^64]
    wraps to 0.  And a sum the OLD 2^62 model could not even represent is now exact. *)
Example spec_i64_add_wrap : i64_add (i64_lit 9223372036854775807 eq_refl) (i64_lit 1 eq_refl) = i64_lit (-9223372036854775808) eq_refl. Proof. now vm_compute. Qed.
Example spec_i64_sub_wrap : i64_sub (i64_lit (-9223372036854775808) eq_refl) (i64_lit 1 eq_refl) = i64_lit 9223372036854775807 eq_refl. Proof. now vm_compute. Qed.
Example spec_i64_mul_wrap : i64_mul (i64_lit 4294967296 eq_refl) (i64_lit 4294967296 eq_refl) = i64_lit 0 eq_refl. Proof. now vm_compute. Qed.
Example spec_i64_beyond62 : i64_add (i64_lit 4611686018427387904 eq_refl) (i64_lit 4611686018427387903 eq_refl) = i64_lit 9223372036854775807 eq_refl. Proof. now vm_compute. Qed.
(* No-overflow ⇒ EXACT, now at the TRUE int64 width (cf. [add_no_overflow_exact] at 2^62). *)
Theorem i64_add_no_overflow_exact : forall a b : GoI64,
  in_i64 (i64raw a + i64raw b)%Z = true -> i64raw (i64_add a b) = (i64raw a + i64raw b)%Z.
Proof.
  intros [a] [b]. unfold in_i64, i64_add, wrap64. cbn. intros H.
  apply andb_prop in H. destruct H as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  rewrite Z.mod_small by lia. lia.
Qed.
(* The demo shows full-width arithmetic on values that EXCEED the old [Sint63] [int]
   range ([2^62 ≈ 4.6e18]) yet fit int64 — impossible to even represent before.  The
   2^63 WRAP itself is proven by the witnesses above (machine-checked [vm_compute]),
   NOT re-shown at runtime: an extracted [MAX + 1] is a Go *untyped-constant*
   expression, so Go applies its COMPILE-TIME overflow check (a compile error) rather
   than the runtime int64 wrap [i64_add] models — exactly the untyped-constant gap
   (PRE_IMPORT_PLAN A5 / Known gaps #5).  [i64_add] models RUNTIME int64 addition,
   faithful for non-constant operands; the demo keeps its constant results in range. *)

(* Ergonomic full-width int64: range-checked [%i64] literals + scoped arithmetic
   (A4.2).  Reads like ordinary integer code, but is the faithful [Z]-carried int64. *)
Definition i64_demo : IO unit :=
  println [ any (9000000000000000000 + 200000000000000000)%i64  (* 9200000000000000000 (> 2^62) *)
          ; any (3000000000 * 3000000000)%i64 ].  (* 9000000000000000000 (> 2^62) *)

(** int64 div/mod (truncate toward zero — NOT Coq's floor), bitwise, and shifts —
    all at the full width.  Machine-checked corner cases: [-7/2 = -3] (trunc, not the
    flooring [-4]); [-7%2 = -1] (sign of dividend); [MININT/-1 = MININT] (two's-
    complement overflow wraps); [1<<63 = MININT]; [-8>>1 = -4] (arithmetic shift). *)
Example spec_i64_div_trunc : i64_div (i64_lit (-7) eq_refl) (i64_lit 2 eq_refl) eq_refl = i64_lit (-3) eq_refl. Proof. now vm_compute. Qed.
Example spec_i64_mod_sign  : i64_mod (i64_lit (-7) eq_refl) (i64_lit 2 eq_refl) eq_refl = i64_lit (-1) eq_refl. Proof. now vm_compute. Qed.
Example spec_i64_div_ovf   : i64_div (i64_lit (-9223372036854775808) eq_refl) (i64_lit (-1) eq_refl) eq_refl = i64_lit (-9223372036854775808) eq_refl. Proof. now vm_compute. Qed.
Example spec_i64_shl_wrap  : i64_shl (i64_lit 1 eq_refl) 63 eq_refl = i64_lit (-9223372036854775808) eq_refl. Proof. now vm_compute. Qed.
Example spec_i64_shr_arith : i64_shr (i64_lit (-8) eq_refl) 1 eq_refl = i64_lit (-4) eq_refl. Proof. now vm_compute. Qed.
Example spec_i64_and       : i64_and (i64_lit (-1) eq_refl) (i64_lit 255 eq_refl) = i64_lit 255 eq_refl. Proof. now vm_compute. Qed.
Example spec_i64_not       : i64_not (i64_lit 5 eq_refl) = i64_lit (-6) eq_refl. Proof. now vm_compute. Qed.
Definition i64_ops_demo : IO unit :=
  bind (println [ any (i64_div (i64_lit 9000000000000000000 eq_refl) (i64_lit 7 eq_refl) eq_refl)  (* 1285714285714285714 *)
                ; any (i64_shl (i64_lit 1 eq_refl) 40 eq_refl) ])  (* 1099511627776 = 2^40 *)
       (fun _ =>
  println [ any (i64_and (i64_lit (-1) eq_refl) (i64_lit 4294967295 eq_refl))   (* 4294967295 *)
          ; any (i64_not (i64_lit 5 eq_refl)) ]).  (* -6 *)

(** ===== GoU64: FULL-WIDTH unsigned 64-bit integer =====
    Machine-checked witnesses:
    - [spec_u64_add_wrap]: 2^63 + 2^63 = 0 (mod 2^64) — the true unsigned wrap boundary.
    - [spec_u64_sub_wrap]: 0 - 1 = 2^64-1 — unsigned underflow wraps to max.
    - [spec_u64_not]:      ~0 = 2^64-1 (all 64 bits set).
    - [spec_u64_shr]:      8 >> 1 = 4 (logical right shift, not arithmetic).
    - [spec_u64_beyond63]: value > 2^62 unrepresentable in the old Sint63 model.
    All axiom-free (Print Assumptions = Closed under the global context). *)
Example spec_u64_add_wrap : u64_add (u64_lit 9223372036854775808%Z eq_refl) (u64_lit 9223372036854775808%Z eq_refl)
                            = u64_lit 0%Z eq_refl. Proof. now vm_compute. Qed.
Example spec_u64_sub_wrap : u64_sub (u64_lit 0%Z eq_refl) (u64_lit 1%Z eq_refl)
                            = u64_lit 18446744073709551615%Z eq_refl. Proof. now vm_compute. Qed.
Example spec_u64_not      : u64_not (u64_lit 0%Z eq_refl) = u64_lit 18446744073709551615%Z eq_refl. Proof. now vm_compute. Qed.
Example spec_u64_shr      : u64_shr (u64_lit 8%Z eq_refl) 1 eq_refl = u64_lit 4%Z eq_refl. Proof. now vm_compute. Qed.
Example spec_u64_beyond63 : u64raw (u64_add (u64_lit 5000000000000000000%Z eq_refl)
                                            (u64_lit 5000000000000000000%Z eq_refl))
                            = 10000000000000000000%Z. Proof. now vm_compute. Qed.

(** Runtime demo: two values > 2^62 (unrepresentable in the old Sint63 carrier);
    their sum and product both fit in Go's int64, so no untyped-constant issue
    (PRE_IMPORT_PLAN A5 / Known gaps #5).  The wrapping corner cases above are
    proof witnesses only (proof-only path never emitted). *)
Definition u64_demo : IO unit :=
  println [ any (5000000000000000000 + 3000000000000000000)%u64  (* 8000000000000000000 (> 2^62) *)
          ; any (3000000000 * 3000000000)%u64 ].               (* 9000000000000000000 *)

(** A4.2b: int64 flows through the FULL pipeline — a buffered CHANNEL and a MAP —
    proving [GoI64] is first-class in every position [int] occupies (not just
    arithmetic).  A [> 2^62] value is sent on a [chan int64], received, then stored
    under an int64 key in a [map[int64]int64] and read back.  [comparable_TI64]
    justifies the int64 map key. *)
(** Regression: [recv_ok] with the value USED but the ok-flag UNUSED ([fun x _ =>])
    must lower to [x, _ := <-ch], not the uncompilable [x, x := <-ch] (an unused
    binder the extractor left named).  Detected by de Bruijn freeness in the plugin. *)
Definition recv_unused_ok_demo : IO unit :=
  ch <-' make_chan_buf TI64 1 ;;
  send TI64 ch (77)%i64 >>'
  recv_ok TI64 ch (fun x _ => println [ any x ]).   (* prints: 77 *)

Definition i64_pipeline_demo : IO unit :=
  ch <-' make_chan_buf TI64 1 ;;
  send TI64 ch (9000000000000000001)%i64 >>'
  bind (recv TI64 ch) (fun x =>                                 (* x = 9000000000000000001 *)
  bind (map_make_typed TI64 TI64) (fun m =>
  bind (map_set TI64 TI64 (42)%i64 x m) (fun _ =>               (* m[int64(42)] = x *)
  bind (@map_get_or GoI64 GoI64 TI64 TI64 (42)%i64 (0)%i64 m) (fun hit =>
  println [ any hit ])))).                                      (* prints: 9000000000000000001 *)

(** A4.2b: a uint64 in the UPPER HALF ([>= 2^63], unrepresentable as signed int64)
    flows through a typed pipeline — proving the full uint64 range is faithful end to
    end, not just in arithmetic.  [18000000000000000000 > 2^63]; it is rendered
    UNSIGNED ([%Lu]) and pinned to [uint64] by the channel / map element types
    (the map default [(0)%u64] pins [uint64(0)] via the value tag). *)
Definition u64_pipeline_demo : IO unit :=
  ch <-' make_chan_buf TU64 1 ;;
  send TU64 ch (18000000000000000000)%u64 >>'
  bind (recv TU64 ch) (fun x =>                                 (* x = 18000000000000000000 *)
  bind (map_make_typed TU64 TU64) (fun m =>
  bind (map_set TU64 TU64 (7)%u64 x m) (fun _ =>                (* m[uint64(7)] = x *)
  bind (@map_get_or GoU64 GoU64 TU64 TU64 (7)%u64 (0)%u64 m) (fun hit =>
  println [ any hit ])))).                                      (* prints: 18000000000000000000 *)

(** Predeclared builtins (Go spec "Built-in functions"): [min]/[max] (Go 1.21) on
    [int], slice [make([]T,n)], and map [clear].  [min]/[max] machine-checked;
    [slice_make]'s length is a THEOREM; [clear] empties the map (get-after-clear is
    a theorem, [map_get_clear]). *)
Example spec_go_min       : go_min 3 5 = 3%uint63. Proof. now vm_compute. Qed.
Example spec_go_max       : go_max 3 5 = 5%uint63. Proof. now vm_compute. Qed.
Example spec_go_min_neg   : go_min (-2)%sint63 1 = (-2)%sint63. Proof. now vm_compute. Qed.
Example spec_slice_make_n : List.length (slice_make TInt64 3) = 3%nat. Proof. reflexivity. Qed.
Definition builtins_demo : IO unit :=
  bind (println [ any (go_min (3 : int) (5 : int)); any (go_max (3 : int) (5 : int)) ]) (fun _ =>  (* 3 5 *)
  bind (println [ any (len (slice_make TInt64 3)) ]) (fun _ =>                                     (* 3 *)
  bind (map_make_typed TInt64 TInt64) (fun m =>
  bind (map_set TInt64 TInt64 (1 : int) (10 : int) m) (fun _ =>
  bind (map_clear TInt64 TInt64 m) (fun _ =>                                                                     (* clear → empty *)
  bind (map_len m) (fun n =>
  println [ any n ])))))).                                                                         (* 0 (cleared) *)

(** ===== Go spec conformance: "String types" (go.dev/ref/spec#String_types):
    "a string value is a (possibly empty) sequence of bytes ... strings are
    immutable.  The length ... can be discovered using len.  A string's bytes can
    be accessed by integer indices 0 <= i < len(s)."  We model [string] as Coq's
    byte-sequence [string], so these are THEOREMS (computable), not assertions:
    [str_len] is the BYTE count, [str_concat] is byte append, and a string is its
    OWN type (no implicit conversion from [int], per "Numeric/string distinct"). *)
Example spec_str_len_Go    : str_len "Go"%string  = 2%uint63. Proof. reflexivity. Qed.
Example spec_str_len_empty : str_len ""%string    = 0%uint63. Proof. reflexivity. Qed.
Example spec_str_concat    : str_concat "Go"%string "!"%string = "Go!"%string.
Proof. reflexivity. Qed.
(* Build-checked: a string does not implicitly accept an [int] (distinct types). *)
Fail Definition str_no_implicit : GoString := str_concat "x"%string (5 : int).

(** Operator-precedence PARENS: nested arithmetic parenthesises only where the
    precedence requires it ([a*b + c] no parens; [(a+b) * c] needs them).  gofmt
    handles the spacing (it tightens to [a*b+c]); the printer handles the parens. *)
Definition prec_demo : IO unit :=
  let a := 2%uint63 in let b := 3%uint63 in let c := 4%uint63 in
  println [ any (PrimInt63.add (PrimInt63.mul a b) c)     (* a*b + c   = 10 *)
          ; any (PrimInt63.mul (PrimInt63.add a b) c) ].  (* (a+b) * c = 20 *)

(** Negative integer LITERALS print correctly.  [int] is signed (Sint63) whose
    underlying representation is unsigned, so a naive printer would emit [-7] as
    the unsigned 9223372036854775801 — the plugin must emit the signed decimal. *)
Definition neglit_demo : IO unit :=
  println [any (-7)%sint63; any (-1)%sint63; any (-2147483648)%sint63].
  (* prints: -7 -1 -2147483648 *)

(** Panic with [n], then recover it and print [n] and [n+1].
    Demonstrates the full panic → catch → type_assert cycle. *)
Definition panic_and_recover (n : GoI64) : IO unit :=
  catch
    (@panic unit (any n))
    (fun v =>
     bind (type_assert TI64 v) (fun recovered =>
     println [any recovered; any (i64_add recovered (1)%i64)])).

(** Map reads are now in [IO] (they observe the map's current contents), so [sz]/
    [hit]/[mis] are [bind]-sequenced after the writes — and the old box/assert
    roundtrip is gone ([map_get_or] returns the value directly). *)
Definition map_demo : IO unit :=
  bind (map_make_typed TI64 TI64) (fun m =>            (* make(map[int64]int64) *)
  bind (map_set TI64 TI64 (1)%i64 (100)%i64 m) (fun _ =>            (* m[1] = 100 *)
  bind (map_set TI64 TI64 (2)%i64 (200)%i64 m) (fun _ =>            (* m[2] = 200 *)
  bind (map_set TI64 TI64 (3)%i64 (300)%i64 m) (fun _ =>            (* m[3] = 300 *)
  bind (map_set TI64 TI64 (2)%i64 (999)%i64 m) (fun _ =>            (* m[2] = 999  (overwrite) *)
  bind (map_len m) (fun sz =>
  bind (@map_get_or GoI64 GoI64 TI64 TI64 (2)%i64 (0)%i64 m) (fun hit =>  (* key present → 999 *)
  bind (@map_get_or GoI64 GoI64 TI64 TI64 (9)%i64 (0)%i64 m) (fun mis =>  (* key absent  → 0   *)
  println [any sz; any hit; any mis])))))))).             (* prints: 3 999 0 *)

Definition slice_demo : IO unit :=
  let xs := slice_of_list TInt64 [1%uint63; 2%uint63; 3%uint63; 4%uint63; 5%uint63] in
  let n  := len xs in
  bind (slice_get TInt64 xs (2:int)) (fun v =>   (* xs[2] = 3, valid *)
  println [any n; any v] >>'                      (* prints: 5 3 *)
  catch
    (bind (@slice_get int TInt64 xs (9:int)) (fun _ =>  (* xs[9] panics — OOB *)
     ret tt))
    (fun _ => println [any false])).              (* caught: prints false *)

(** Buffered channel: send 42, close, then recv_ok twice.
    First recv: value=42, ok=true  (buffered value still present after close).
    Second recv: value=0,  ok=false (channel drained and closed). *)
Definition chan_demo : IO unit :=
  ch <-' make_chan_buf TI64 1 ;;
  send TI64 ch (42)%i64 >>'
  close_chan TI64 ch >>'
  recv_ok TI64 ch (fun x ok =>                   (* prints: 42 true *)
  println [any x; any ok] >>'
  recv_ok TI64 ch (fun x2 ok2 =>
  println [any x2; any ok2])).

(** select (Go spec "Select statements"): choose among ready channel ops.  [ch1]
    is buffered with 42 (ready), [ch2] is empty — so select picks [ch1].  (The
    choice is Go's at runtime; the demo makes exactly ONE case ready so the golden
    is stable.)  The lowering is a faithful Go [select { case … }]; the choice /
    blocking semantics is the tracked frontier (like [recv]'s blocking). *)
Definition select_demo : IO unit :=
  ch1 <-' make_chan_buf TI64 1 ;;
  ch2 <-' make_chan_buf TI64 1 ;;
  send TI64 ch1 (42)%i64 >>'
  select_recv2 TI64 ch1 (fun x => println [any x])     (* ch1 ready → 42 *)
               TI64 ch2 (fun y => println [any y]).

(** select with a default (the NON-BLOCKING form): [ch] is empty, so no case is
    ready and the [default] runs. *)
Definition select_default_demo : IO unit :=
  ch <-' make_chan_buf TI64 1 ;;
  select_recv_default TI64 ch (fun x => println [any x])   (* ch empty → default *)
                      (println [any (99)%i64]).            (* prints: 99 *)

(** Unbuffered channel + goroutine: the goroutine sends while main recvs.
    The pattern that required goroutines — unbuffered send deadlocks solo. *)
Definition goroutine_demo : IO unit :=
  bind (make_chan TI64)              (fun ch =>
  bind (go_spawn (send TI64 ch (42)%i64)) (fun _ =>
  bind (recv TI64 ch)               (fun x =>
  println [any x]))).                  (* prints: 42 *)

(** Session-typed ping-pong, with LINEAR sessions (the indexed monad [Sess]).
    Protocol (client view): send int → recv int → end.  The server realises the
    dual: recv int → send int → end.  The protocol state lives in the TYPE
    INDEX, so wrong order/direction/payload AND non-linear misuse (double-send,
    incomplete protocol) are all Rocq compile-time errors — there is no endpoint
    value to reuse. *)

Definition PingPong : Proto := PSend GoI64 (PRecv GoI64 PEnd).

(* Client and server are inlined into [run_session] so the plugin lowers each
   role's body directly against the shared channel.  Their *types* (below) still
   pin them to [PingPong] / [dual PingPong] ending at [PEnd], so the linearity
   guarantee holds; the [Fail] tests cover the rejections. *)
Definition session_demo : IO unit :=
  run_session
    (* client : Sess PingPong PEnd unit — send 21, recv, print *)
    (ssend (21)%i64 >>>
     result <<- srecv TI64 ;;;
     slift (println [any result]))            (* prints: 42 *)
    (* server : Sess (dual PingPong) PEnd unit — recv n, send n+n *)
    (n <<- srecv TI64 ;;;
     ssend (i64_add n n)).

(** ---- Protocol compliance is enforced at compile time ----

    Each [Fail] below asserts that the enclosed definition does NOT type-check.
    The build runs these: if any violation ever started compiling, [Fail] would
    error and break the build.  They are machine-checked proofs that the session
    discipline rejects misuse, at zero runtime cost. *)

(* Receiving first violates the protocol head (PSend ≠ PRecv) — type error. *)
Fail Definition bad_recv_first : Sess PingPong PEnd unit :=
  sbind (srecv TI64) (fun _ => sret tt).

(* Sending a bool where the protocol pins int — type error. *)
Fail Definition bad_send_type : Sess PingPong PEnd unit :=
  sbind (ssend true) (fun _ => sret tt).

(* Stopping before [PEnd]: the ascribed type demands the protocol be fully
   consumed, so an incomplete session is a type error. *)
Fail Definition bad_incomplete : Sess PingPong PEnd unit :=
  ssend (21)%i64.

(* NON-LINEAR double send — the violation the old CPS API silently ACCEPTED.
   After one [ssend] the state is [PRecv int PEnd]; a second [ssend] needs
   [PSend] at the head, so it no longer type-checks. *)
Fail Definition bad_double_send : Sess PingPong PEnd unit :=
  sbind (ssend (21)%i64) (fun _ =>
  sbind (ssend (99)%i64) (fun _ => sret tt)).

(* The server's dual receives first; sending first is a type error. *)
Fail Definition bad_server_sends : Sess (dual PingPong) PEnd unit :=
  sbind (ssend (1)%i64) (fun _ => sret tt).

(** A longer protocol: the client sends two numbers, the server replies with
    their sum.  Exercises consecutive same-direction steps — two sends in a row
    (client), two receives in a row (server) — which ping-pong does not. *)

Definition Adder : Proto := PSend GoI64 (PSend GoI64 (PRecv GoI64 PEnd)).

Definition adder_demo : IO unit :=
  run_session
    (* client : Sess Adder PEnd unit — send 20, send 22, recv sum, print *)
    (ssend (20)%i64 >>>
     ssend (22)%i64 >>>
     sum <<- srecv TI64 ;;;
     slift (println [any sum]))               (* prints: 42 *)
    (* server : Sess (dual Adder) PEnd unit — recv a, recv b, send a+b *)
    (a <<- srecv TI64 ;;;
     b <<- srecv TI64 ;;;
     ssend (i64_add a b)).

(** ---- Control flow: if/else (step 7a) ----

    [if c then _ else _] is Rocq sugar for [match c with true | false]; the
    plugin lowers it to a Go [if]/[else] statement.  Two positions:

    [sign_demo] uses the branch in tail position (each arm is a statement).
    [pick_demo] uses it as an IO value feeding a continuation — the plugin
    threads the continuation into both arms (bind distributes over case). *)

Definition sign_demo (n : GoI64) : IO unit :=
  if (n <? 10)%i64                    (* SIGNED comparison, faithful to Go int64 *)
  then println [any n; any true]      (* n < 10  → e.g. "5 true"   *)
  else println [any n; any false].    (* n >= 10 → e.g. "20 false" *)

Definition pick_demo (b : bool) : IO unit :=
  bind (if b then ret (1)%i64 else ret (2)%i64) (fun x =>
  println [any x]).                    (* b → 1, else 2 *)

(** Signed subtraction extracts to Go's [2 - 5] and prints [-3] — full-width [GoI64]. *)
Definition neg_demo : IO unit :=
  println [any (i64_sub (2)%i64 (5)%i64)].   (* Go prints: -3 *)

Definition control_flow_demo : IO unit :=
  bind (sign_demo (5)%i64)  (fun _ =>   (* prints: 5 true  *)
  bind (sign_demo (20)%i64) (fun _ =>   (* prints: 20 false *)
  bind (pick_demo true)       (fun _ =>   (* prints: 1 *)
  neg_demo))).                            (* prints: -3 *)

(** Go spec conformance: "Logical operators" (go.dev/ref/spec#Logical_operators)
    — the SOURCE of &&/||/!.  Spec: [p && q] is "if p then q else false", [p || q]
    is "if p then true else q", [!p] is "not p".  Coq's [andb]/[orb]/[negb] ARE
    those definitions — machine-checked by [reflexivity], so the lowering is
    faithful to the spec phrasing (short-circuit is unobservable: the operands are
    pure total bools). *)
Example spec_andb : forall p q, andb p q = if p then q else false. Proof. reflexivity. Qed.
Example spec_orb  : forall p q, orb  p q = if p then true else q.  Proof. reflexivity. Qed.
Example spec_negb : forall p,   negb p   = if p then false else true. Proof. reflexivity. Qed.

(** Boolean operators [andb]/[orb]/[negb] lower to Go's [&&]/[||]/[!].  The
    operands are pure, total [bool] values, so Go's short-circuit evaluation is
    observationally identical (no effects, no divergence to skip).  Parameters
    are opaque [bool]s (typed [bool] in Go), so the operators survive extraction
    rather than constant-folding, and precedence is exercised: the last line is
    [(a || b) && c], so the looser [||] is parenthesised inside [&&]. *)
Definition bool_op_demo (a b c : bool) : IO unit :=
  bind (println [any (andb a b)]) (fun _ =>          (* a && b *)
  bind (println [any (orb  a b)]) (fun _ =>          (* a || b *)
  bind (println [any (negb b)])   (fun _ =>          (* !b *)
  println [any (andb (orb a b) c)]))).               (* (a || b) && c *)

(** The primary use of the boolean operators: COMPOUND CONDITIONS in [if].  Each
    [if] is a match on [bool] whose scrutinee is a compound expression, so the
    condition lowers to Go's [a && b] / [a || b] / [!a] directly inside the
    [if (...)].  One conditional per function (mirroring [sign_demo]) so the
    [bind] continuation follows the call as a single statement — chaining several
    inline [if]s in one [bind] instead would duplicate the continuation into both
    arms (see the "inline-if continuation duplication" note in CLAUDE.md). *)
Definition and_cond (a b : GoI64) : IO unit :=
  if andb (a <? 10)%i64 (b <? 10)%i64                 (* a<10 && b<10 *)
  then println [any (1)%i64] else println [any (0)%i64].
Definition or_cond (a b : GoI64) : IO unit :=
  if orb (a <? 10)%i64 (b <? 10)%i64                  (* a<10 || b<10 *)
  then println [any (1)%i64] else println [any (0)%i64].
Definition not_cond (a : GoI64) : IO unit :=
  if negb (a <? 10)%i64                               (* !(a<10) *)
  then println [any (1)%i64] else println [any (0)%i64].
Definition cond_op_demo : IO unit :=
  bind (and_cond (3)%i64 (4)%i64)  (fun _ =>   (* T && T → 1 *)
  bind (or_cond (30)%i64 (4)%i64)  (fun _ =>   (* F || T → 1 *)
  not_cond (30)%i64)).                   (* !F      → 1 *)

(** Regression for inline-[if] continuation de-duplication: three INLINE [if]s
    chained in one [bind], each discarding its [unit] result.  Because the result
    is discarded, the continuation is emitted ONCE after each [if] (both arms fall
    through) instead of being duplicated into both arms — so this lowers to three
    flat sequential [if/else]s, not a 2^2-copy tree.  Prints 1 / 0 / 1. *)
Definition inline_if_demo : IO unit :=
  bind (if Sint63.ltb 3 10  then println [any (1:int)] else println [any (0:int)]) (fun _ =>
  bind (if Sint63.ltb 30 10 then println [any (1:int)] else println [any (0:int)]) (fun _ =>
  if Sint63.ltb 5 10        then println [any (1:int)] else println [any (0:int)])).

(** [map_get_opt] is an IO read; binding it then matching the [option] lowers to
    Go's comma-ok lookup: [bind (map_get_opt k m) (fun o => match o with Some v =>
    _ | None => _)] becomes [if v, ok := m[k]; ok { _ } else { _ }] — no [option]
    value is built. *)
Definition lookup_demo : IO unit :=
  m <-' map_make_typed TI64 TI64 ;;
  map_set TI64 TI64 (7)%i64 (700)%i64 m >>'
  (o <-' map_get_opt TI64 TI64 (7)%i64 m ;;                 (* present → 700 true *)
   match o with
   | Some v => println [any v; any true]
   | None   => println [any false]
   end) >>'
  (o <-' map_get_opt TI64 TI64 (9)%i64 m ;;                 (* absent → false *)
   match o with
   | Some v => println [any v; any true]
   | None   => println [any false]
   end).

(** List/slice match: [match xs with [] | x :: rest] lowers to
    [if len(xs) == 0 { … } else { x := xs[0]; rest := xs[1:]; … }].
    The [cons] arm binds two variables (head and tail) — a two-binder case the
    earlier matches did not exercise. *)
Definition list_demo : IO unit :=
  let xs := slice_of_list TInt64 [10%uint63; 20%uint63; 30%uint63] in
  match xs with
  | nil         => println [any false]
  | cons x rest => println [any x; any (len rest)]   (* head=10, len tail=2 *)
  end.

(** Safe slice access: [slice_at_ok] bounds-checks and forces handling the
    out-of-bounds case, so it cannot panic — the safe-by-construction default,
    versus the [slice_get] escape hatch used in [slice_demo] above. *)
Definition slice_safe_demo : IO unit :=
  let xs := slice_of_list TInt64 [10%uint63; 20%uint63; 30%uint63] in
  slice_at_ok TInt64 xs (1 : int) (fun v ok =>      (* in bounds → 20 true *)
  println [any v; any ok] >>'
  slice_at_ok TInt64 xs (9 : int) (fun v2 ok2 =>    (* above range → 0 false *)
  println [any v2; any ok2] >>'
  (* runtime-NEGATIVE index (sub 0 1 = -1) — a *constant* negative index is a Go
     compile error, so use a computed one; the lower-bound check must reject it. *)
  slice_at_ok TInt64 xs (sub 0 1) (fun v3 ok3 =>    (* negative (signed) → 0 false *)
  println [any v3; any ok3]))).

(** Safe type assertion: [type_assert_safe] is Go's [v, ok := x.(T)] — no panic
    on a type mismatch, the caller handles [ok = false].  Safe-by-construction
    default versus the [type_assert] escape hatch.  We assert on a recovered
    panic value [r : GoAny] (a genuine [any], like [panic_and_recover]). *)
Definition assert_safe_demo (n : int) : IO unit :=
  catch (@panic unit (any n))
    (fun r =>
     type_assert_safe TInt64 r (fun v ok =>        (* r holds int64 → n true *)
     println [any v; any ok] >>'
     type_assert_safe TBool r (fun b ok2 =>        (* r is not a bool → false false *)
     println [any b; any ok2]))).

(** Strings (Go spec "String types"): a byte sequence.  [str_len] is the BYTE
    count; [str_at_ok] is the safe byte index (forced OOB handling, like
    [slice_at_ok]); [str_concat] is Go's [+].  Index 5 of "Go" (len 2) is out of
    range, so it yields the zero byte and [ok = false] — no panic. *)
Definition string_demo : IO unit :=
  let s := "Go"%string in
  println [any (str_len s)] >>'                     (* 2 *)
  str_at_ok s (0 : int) (fun b ok =>                (* 71 ('G') true *)
  println [any b; any ok] >>'
  str_at_ok s (5 : int) (fun b2 ok2 =>              (* out of range → 0 false *)
  println [any b2; any ok2] >>'
  println [any (str_concat s "!"%string)])).        (* Go! *)

(** Capture in a goto loop: each iteration defers [println iv].  The loop-temp
    [iv] is captured BY VALUE per iteration, so the deferred calls (LIFO at
    return) print 2, 1, 0 — not 2, 2, 2 (which a shared cell would give). *)
Definition defer_loop_demo : IO unit :=
  bind (ref_new TInt64 (0 : int)) (fun i =>
  run_blocks 0%nat [
    bind (ref_get TInt64 i) (fun iv =>
      if Sint63.ltb iv 3 then
        bind (defer_call (println [any iv]))  (fun _ =>
        bind (ref_set i (add iv 1))           (fun _ =>
        ret (Jump 0%nat)))
      else ret (Jump 1%nat)) ;
    ret Done
  ]).

(** Function-scoped defer: [defer_call] runs at function return, LIFO across all
    defers — distinct from block-scoped [with_defer].  Prints 3, then 2, then 1. *)
Definition defer_demo : IO unit :=
  bind (defer_call (println [any (1 : int)])) (fun _ =>   (* runs 3rd (LIFO) *)
  bind (defer_call (println [any (2 : int)])) (fun _ =>   (* runs 2nd *)
  println [any (3 : int)])).                               (* runs now *)

(** Mutable local variable: declare, read, reassign, read again — straight-line
    (no control flow, so trivially scope-correct). *)
Definition mut_demo : IO unit :=
  bind (ref_new TInt64 (10 : int))        (fun r =>  (* r := 10        *)
  bind (ref_get TInt64 r)          (fun a =>  (* a := r  (= 10) *)
  bind (ref_set r (add a 5))       (fun _ =>  (* r = a + 5 (= 15) *)
  bind (ref_get TInt64 r)          (fun b =>  (* b := r  (= 15) *)
  println [any b])))).                         (* prints 15 *)

(** Backward-goto counting loop: a [Ref] counter + [goto] back to the header.
    The read [iv := ref_get i] cannot use [:=] (it re-runs each iteration), so
    its declaration is hoisted to [var iv int64] (dominating the loop) and
    assigned with [=].  [ref_set] also assigns with [=].  Prints 0,1,2. *)
Definition count_demo : IO unit :=
  bind (ref_new TInt64 (0 : int)) (fun i =>
  run_blocks 0%nat [
    bind (ref_get TInt64 i) (fun iv =>            (* block 0: loop header *)
      if Sint63.ltb iv 3 then
        bind (println [any iv])      (fun _ =>
        bind (ref_set i (add iv 1))  (fun _ =>
        ret (Jump 0%nat)))                        (* goto block0 (backward) *)
      else ret (Jump 1%nat)) ;                    (* exit *)
    ret Done                                       (* block 1 *)
  ]).

(** Control flow as a goto-CFG.  Three blocks; block 0 conditionally jumps to
    the merge (block 2), skipping block 1.  The structurer lifts this to a clean
    one-armed [if !early { println(2) }] — block 1 runs only when not early.
    early ⇒ 1,3 ; else ⇒ 1,2,3. *)
Definition cond_goto_demo (early : bool) : IO unit :=
  run_blocks 0%nat [
    bind (println [any (1 : int)]) (fun _ =>
      if early then ret (Jump 2%nat) else ret (Jump 1%nat)) ;
    bind (println [any (2 : int)]) (fun _ => ret (Jump 2%nat)) ;
    bind (println [any (3 : int)]) (fun _ => ret Done)
  ].

(** Diamond: block 0 branches to two non-empty arms (blocks 1 and 2) that
    reconverge at the merge (block 3).  The structurer finds the merge (the
    immediate post-dominator) and lifts this to [if b { 10 } else { 20 }; 99],
    emitting the merge once.  b ⇒ 1,10,99 ; else ⇒ 1,20,99. *)
Definition diamond_demo (b : bool) : IO unit :=
  run_blocks 0%nat [
    bind (println [any (1 : int)]) (fun _ =>
      if b then ret (Jump 1%nat) else ret (Jump 2%nat)) ;
    bind (println [any (10 : int)]) (fun _ => ret (Jump 3%nat)) ;
    bind (println [any (20 : int)]) (fun _ => ret (Jump 3%nat)) ;
    bind (println [any (99 : int)]) (fun _ => ret Done)
  ].

(** Loop containing a branch: a counting loop (block 0 header, block 3 the
    increment/loop tail) whose body has an in-loop one-armed [if] (block 1 → 2).
    Exercises the relooper nesting a conditional inside a [for]: the header
    becomes [for { … if iv < 3 { … } else { break } }], and block 1's branch a
    nested [if … < 1 { println(100) }].  Counter is a [Ref], re-read per block
    (separate goto-blocks don't share Rocq scope).  Prints 100, 0, 1, 2. *)
Definition loopif_demo : IO unit :=
  bind (ref_new TInt64 (0 : int)) (fun i =>
  run_blocks 0%nat [
    bind (ref_get TInt64 i) (fun iv =>                              (* block 0: header *)
      if Sint63.ltb iv 3 then ret (Jump 1%nat) else ret (Jump 4%nat)) ;
    bind (ref_get TInt64 i) (fun iv =>                              (* block 1: in-loop branch *)
      if Sint63.ltb iv 1 then ret (Jump 2%nat) else ret (Jump 3%nat)) ;
    bind (println [any (100 : int)]) (fun _ => ret (Jump 3%nat)) ;  (* block 2: first-iter marker *)
    bind (ref_get TInt64 i) (fun iv =>                              (* block 3: body, incr, loop *)
    bind (println [any iv]) (fun _ =>
    bind (ref_set i (add iv 1)) (fun _ => ret (Jump 0%nat)))) ;
    ret Done                                                        (* block 4: exit *)
  ]).

(** Nested loops: an outer counter [i] (header block 0, tail block 4) wrapping an
    inner counter [j] (header block 2, tail block 3).  Exercises the relooper
    nesting one [for] inside another — [loopctx] stacks, so the inner [jv >= 2]
    exit becomes the inner [break] (to block 4) and the outer [iv >= 2] exit the
    outer [break] (to block 5).  Two [Ref]s; [j] is reset each outer pass.
    Prints 0,1 (inner, i=0) then 0,1 (inner, i=1). *)
Definition nested_loop_demo : IO unit :=
  bind (ref_new TInt64 (0 : int)) (fun i =>
  bind (ref_new TInt64 (0 : int)) (fun j =>
  run_blocks 0%nat [
    bind (ref_get TInt64 i) (fun iv =>                              (* block 0: outer header *)
      if Sint63.ltb iv 2 then ret (Jump 1%nat) else ret (Jump 5%nat)) ;
    bind (ref_set j (0 : int)) (fun _ => ret (Jump 2%nat)) ;        (* block 1: reset j *)
    bind (ref_get TInt64 j) (fun jv =>                              (* block 2: inner header *)
      if Sint63.ltb jv 2 then ret (Jump 3%nat) else ret (Jump 4%nat)) ;
    bind (ref_get TInt64 j) (fun jv =>                              (* block 3: inner body *)
    bind (println [any jv]) (fun _ =>
    bind (ref_set j (add jv 1)) (fun _ => ret (Jump 2%nat)))) ;
    bind (ref_get TInt64 i) (fun iv =>                              (* block 4: outer tail *)
    bind (ref_set i (add iv 1)) (fun _ => ret (Jump 0%nat))) ;
    ret Done                                                        (* block 5: exit *)
  ])).

(** Early return from inside a loop: block 1 returns ([Done]) when [iv] reaches 2,
    mid-loop — distinct from the loop's normal [break] (block 0 → block 3) and the
    post-loop code.  The relooper emits [return] for the in-loop [Done], [break]
    for the exit edge, and the block-3 tail after the [for].  Prints 0, 1, then
    returns (so block 3's 999 is never reached). *)
Definition early_return_demo : IO unit :=
  bind (ref_new TInt64 (0 : int)) (fun i =>
  run_blocks 0%nat [
    bind (ref_get TInt64 i) (fun iv =>                              (* block 0: header *)
      if Sint63.ltb iv 9 then ret (Jump 1%nat) else ret (Jump 3%nat)) ;
    bind (ref_get TInt64 i) (fun iv =>                              (* block 1: early return *)
      if Sint63.ltb iv 2 then ret (Jump 2%nat) else ret Done) ;
    bind (ref_get TInt64 i) (fun iv =>                              (* block 2: body, incr, loop *)
    bind (println [any iv]) (fun _ =>
    bind (ref_set i (add iv 1)) (fun _ => ret (Jump 0%nat)))) ;
    bind (println [any (999 : int)]) (fun _ => ret Done)           (* block 3: normal exit *)
  ]).

(** Labeled break: from inside the inner loop, block 3 jumps to the *outer*
    loop's exit (block 6) when [jv] reaches 2 — escaping both loops at once.
    That is more than the innermost loop can [break], so the relooper labels the
    outer [for] [L0:] and emits [break L0].  The inner loop is multi-exit (its
    normal exit is block 5, plus the labeled escape to block 6), which the
    primary-exit analysis accepts.  Prints 0, 1, 2 then stops entirely. *)
Definition labeled_break_demo : IO unit :=
  bind (ref_new TInt64 (0 : int)) (fun i =>
  bind (ref_new TInt64 (0 : int)) (fun j =>
  run_blocks 0%nat [
    bind (ref_get TInt64 i) (fun iv =>                              (* block 0: outer header *)
      if Sint63.ltb iv 3 then ret (Jump 1%nat) else ret (Jump 6%nat)) ;
    bind (ref_set j (0 : int)) (fun _ => ret (Jump 2%nat)) ;        (* block 1: reset j *)
    bind (ref_get TInt64 j) (fun jv =>                              (* block 2: inner header *)
      if Sint63.ltb jv 3 then ret (Jump 3%nat) else ret (Jump 5%nat)) ;
    bind (ref_get TInt64 j) (fun jv =>                              (* block 3: print; break L0 at 2 *)
    bind (println [any jv]) (fun _ =>
      if Sint63.ltb jv 2 then ret (Jump 4%nat) else ret (Jump 6%nat))) ;
    bind (ref_get TInt64 j) (fun jv =>                              (* block 4: inner tail, j++ *)
    bind (ref_set j (add jv 1)) (fun _ => ret (Jump 2%nat))) ;
    bind (ref_get TInt64 i) (fun iv =>                              (* block 5: outer tail, i++ *)
    bind (ref_set i (add iv 1)) (fun _ => ret (Jump 0%nat))) ;
    ret Done                                                        (* block 6: exit *)
  ])).

(** Labeled continue: from inside the inner loop, block 3 jumps to the *outer*
    header (block 0) once [jv] reaches 1 — abandoning the inner loop to restart
    the outer one.  That escapes the innermost loop, so it lowers to
    [continue L0] (the outer [for] is labeled).  The outer header increments [i]
    so it still terminates.  Prints 0, 1 (inner, i=0) then 0, 1 (i=1). *)
Definition labeled_continue_demo : IO unit :=
  bind (ref_new TInt64 (0 : int)) (fun i =>
  bind (ref_new TInt64 (0 : int)) (fun j =>
  run_blocks 0%nat [
    bind (ref_get TInt64 i) (fun iv =>                              (* block 0: outer header, i++ *)
    bind (ref_set i (add iv 1)) (fun _ =>
      if Sint63.ltb iv 2 then ret (Jump 1%nat) else ret (Jump 5%nat))) ;
    bind (ref_set j (0 : int)) (fun _ => ret (Jump 2%nat)) ;        (* block 1: reset j *)
    bind (ref_get TInt64 j) (fun jv =>                              (* block 2: inner header *)
      if Sint63.ltb jv 3 then ret (Jump 3%nat) else ret (Jump 4%nat)) ;
    bind (ref_get TInt64 j) (fun jv =>                              (* block 3: print; continue L0 *)
    bind (println [any jv]) (fun _ =>
    bind (ref_set j (add jv 1)) (fun _ =>
      if Sint63.ltb jv 1 then ret (Jump 2%nat) else ret (Jump 0%nat)))) ;
    ret (Jump 0%nat) ;                                              (* block 4: inner exit → outer *)
    ret Done                                                        (* block 5: exit *)
  ])).

(** Irreducible CFG (a two-entry loop): block 0 jumps into the {1,2} cycle at
    *either* block 1 or block 2, so neither dominates the other and there is no
    back-edge to make a loop header.  No structured [for] can express this, so it
    takes the raw labels+goto fallback — the completeness guarantee that *any*
    control flow lowers, structured or not.  enter_high ⇒ 2,1,2,1,2 ; else ⇒
    1,2,1,2. *)
Definition irreducible_demo (enter_high : bool) : IO unit :=
  bind (ref_new TInt64 (0 : int)) (fun n =>
  run_blocks 0%nat [
    (if enter_high then ret (Jump 2%nat) else ret (Jump 1%nat)) ;  (* block 0: two-entry *)
    bind (ref_get TInt64 n) (fun nv =>                             (* block 1 *)
    bind (println [any (1 : int)]) (fun _ =>
    bind (ref_set n (add nv 1)) (fun _ => ret (Jump 2%nat)))) ;
    bind (ref_get TInt64 n) (fun nv =>                             (* block 2 *)
    bind (println [any (2 : int)]) (fun _ =>
    bind (ref_set n (add nv 1)) (fun _ =>
      if Sint63.ltb nv 3 then ret (Jump 1%nat) else ret (Jump 3%nat)))) ;
    ret Done                                                       (* block 3: exit *)
  ]).

(** Bounded loop: [for_each] over a slice lowers to a Go [for ... range]. *)
Definition foreach_demo : IO unit :=
  let xs := slice_of_list TInt64 [10%uint63; 20%uint63; 30%uint63] in
  for_each xs (fun x => println [any x]).   (* prints 10 / 20 / 30 *)

(** Fold: sum a slice into an accumulator — lowers to an accumulator [for]
    loop ([total := 0; for _, x := range xs { total = total + x }]). *)
Definition sum_demo : IO unit :=
  let xs    := slice_of_list TInt64 [1%uint63; 2%uint63; 3%uint63; 4%uint63] in
  let total := slice_fold xs (0 : int) (fun acc x => add acc x) in
  println [any total].   (* 1+2+3+4 = 10 *)

(** ── Structs (Go value-structs from Rocq Records) ───────────────────────────
    A Rocq [Record] is a Go value-struct: both have copy/value semantics, so no
    aliasing model is needed.  The type → a Go [struct], the single constructor →
    a struct literal [T{…}], each projection → field access [x.Field].  [Point]'s
    fields are plain [int], so they lower to [int64].  This is the Stage-A gateway
    to methods, interfaces, typestate, and representation invariants (the
    closed-world wishlist).

    Because a record is an ordinary Rocq type, struct INVARIANTS are already
    provable by hand here: [px] of a [MkPoint a b] is definitionally [a]. *)
Record Point := MkPoint { px : GoI64 ; py : GoI64 }.

Example point_proj_px : forall a b, px (MkPoint a b) = a.
Proof. reflexivity. Qed.
Example point_proj_py : forall a b, py (MkPoint a b) = b.
Proof. reflexivity. Qed.

Definition point_demo : IO unit :=
  let p := MkPoint (3)%i64 (4)%i64 in
  bind (println [any (px p)])           (fun _ =>   (* 3 *)
  bind (println [any (py p)])           (fun _ =>   (* 4 *)
  println [any (i64_add (px p) (py p))])).  (* 7 *)

(** Heterogeneous fields prove the struct field-type printer is general, not
    hardcoded to [int64]: [flag : bool] lowers to a Go [bool] field, [qty : int]
    to [int64].  (Mixing field types in one struct is the common case.) *)
Record Labeled := MkLabeled { flag : bool ; qty : GoI64 }.

Definition labeled_demo : IO unit :=
  let r := MkLabeled true (5)%i64 in
  bind (println [any (flag r)])   (fun _ =>   (* true *)
  println [any (qty r)]).                     (* 5 *)

(** Methods (value receiver).  A function whose FIRST parameter is a struct
    lowers to a Go value-receiver method — [sum_coords] → [func (p Point)
    Sum_coords() int64], [shifted] → [func (p Point) Shifted(dx int64) Point] —
    and a call [m p …] to [p.M(…)].  This is faithful ([p.M(a)] denotes the same
    as [M(p, a)]) and idiomatic; the receiver is the SAME de Bruijn binding, only
    the signature pulls it out front.  (Method↔type association is what Stage C's
    interfaces will check: the method set of [Point] is every such function.) *)
Definition sum_coords (p : Point) : GoI64 := i64_add (px p) (py p).
Definition shifted (p : Point) (dx : GoI64) : Point :=
  MkPoint (i64_add (px p) dx) (i64_add (py p) dx).

(** Method behaviour is provable in Rocq: shifting moves each coordinate by [d].
    Both hold by computation (the method unfolds to a constructor + projection). *)
Example shifted_px : forall p d, px (shifted p d) = i64_add (px p) d.
Proof. reflexivity. Qed.
Example shifted_py : forall p d, py (shifted p d) = i64_add (py p) d.
Proof. reflexivity. Qed.

Definition method_demo : IO unit :=
  let p := MkPoint (3)%i64 (4)%i64 in
  let q := shifted p (10)%i64 in
  bind (println [any (sum_coords p)])   (fun _ =>   (* 7 *)
  bind (println [any (px q)])           (fun _ =>   (* 13 *)
  bind (println [any (py q)])           (fun _ =>   (* 14 *)
  println [any (sum_coords q)]))).                  (* 27 *)

(** An IO-returning method (a method with effects) — the receiver threads through
    the [pp_io_body] path just like a pure one: [func (p Point) Describe() { … }],
    and the statement-position call [describe p] lowers to [p.Describe()]. *)
Definition describe (p : Point) : IO unit :=
  bind (println [any (px p)]) (fun _ => println [any (py p)]).

Definition io_method_demo : IO unit :=
  let p := MkPoint (8)%i64 (9)%i64 in
  describe p.   (* prints: 8 / 9 *)

(** ── Interfaces (the method-dictionary model) ───────────────────────────────
    A Go interface is a method DICTIONARY that is EXISTENTIAL at runtime: it holds
    the methods (a vtable) with the concrete type ERASED.  We model that directly —
    an interface is a Rocq [Record] whose fields are the methods, already CLOSED
    OVER the underlying value, so the concrete type is hidden inside the closures.
    It lowers to a Go struct of function fields (the vtable); building it from a
    concrete value ERASES that value into the closures (existential — a [Shape]
    cannot be turned back into the rectangle it came from); a method call
    [area sh x] is dynamic dispatch [sh.Area(x)].  Satisfaction is checked in Rocq:
    to build a [Shape] you MUST supply real [int -> int] methods, so a value lacking
    a method cannot be packaged.

    (Two methods, not one: Coq UNBOXES a single-field record — [{m}] ≡ [m] — so a
    one-method interface would erase to a bare function and need curried-return
    handling in the lowering; that is a tracked follow-up.  A ≥2-method interface
    stays a boxed record, i.e. a genuine vtable struct, which is the common case.) *)
Record Shape := MkShape { area : GoI64 -> GoI64 ; perim : GoI64 -> GoI64 }.

(* Two DIFFERENT concrete carriers behind one [Shape] — the existential payoff:
   [show_shape] dispatches uniformly, never seeing which one it holds.  The methods
   take a scale [s] (so the dictionary entries are real closures, not bare data);
   [mk_rect] closes over [w]/[h], [mk_square] over just [side]. *)
Definition mk_rect (w h : GoI64) : Shape :=
  MkShape (fun s => i64_add (i64_add (i64_add w h) (i64_add w h)) s)   (* perimeter-ish + scale *)
          (fun s => i64_add (i64_add w h) s).
Definition mk_square (side : GoI64) : Shape :=
  MkShape (fun s => i64_add (i64_add (i64_add side side) (i64_add side side)) s)
          (fun s => i64_add (i64_add side side) s).

Definition show_shape (sh : Shape) : IO unit :=
  bind (println [any (area sh 0)])    (fun _ =>   (* the first method, scale 0 *)
  println [any (perim sh 1000)]).                 (* the second method, scale 1000 *)

(** Dispatch is provable in Rocq — a dictionary entry IS the supplied method, so
    [area (mk_rect w h) s] computes to the closure [mk_rect] put there. *)
Example dispatch_area  : forall w h s, area  (mk_rect w h) s = i64_add (i64_add (i64_add w h) (i64_add w h)) s.
Proof. reflexivity. Qed.
Example dispatch_perim : forall side s, perim (mk_square side) s = i64_add (i64_add side side) s.
Proof. reflexivity. Qed.

Definition iface_demo : IO unit :=
  bind (show_shape (mk_rect (3)%i64 (4)%i64))   (fun _ =>   (* area: 2*(3+4)+0=14 ; perim: 7+1000=1007 *)
  show_shape (mk_square (5)%i64)).                     (* area: 2*(5+5)+0=20 ; perim: 10+1000=1010 *)

(** ── Typestate (a state machine that CANNOT compile to a broken transition) ──
    The payoff of structs+methods.  A value carries its FSM state in a PHANTOM type
    index ([Light c]); each transition's type names the legal from/to states, so an
    illegal transition is a Rocq TYPE ERROR — checked at compile time, never emitted
    as Go.  The index is erased at runtime (it is compile-time only), so [Light c]
    lowers to a plain struct and transitions to ordinary methods; what Go runs is
    ALWAYS a legal trace.

    The index lives in [Prop] so extraction ERASES it (a phantom): [CRed]/[CGreen]
    carry no runtime data, yet [Light CRed] and [Light CGreen] stay DISTINCT types
    (constructors are definitionally distinct even in [Prop]), which is exactly what
    makes the bad transition a type error while both erase to the same Go struct. *)
Inductive LightColor : Prop := CRed | CGreen.
(* Two fields keep the record BOXED (Coq unboxes a single-field record), i.e. a
   genuine Go struct; [serial] is just a second datum so the struct stays a struct. *)
Record Light (c : LightColor) := MkLight { ticks : GoI64 ; serial : GoI64 }.

Definition fresh_light : Light CRed := MkLight CRed (0)%i64 (7)%i64.
Definition go_green (l : Light CRed) : Light CGreen :=
  MkLight CGreen (i64_add (ticks CRed l) (1)%i64) (serial CRed l).
Definition go_red   (l : Light CGreen) : Light CRed :=
  MkLight CRed (ticks CGreen l) (serial CGreen l).

Definition typestate_demo : IO unit :=
  let l0 := fresh_light in        (* Light CRed *)
  let l1 := go_green l0 in        (* Light CGreen *)
  let l2 := go_red l1 in          (* Light CRed *)
  bind (println [any (ticks CRed l2)])    (fun _ =>   (* 1 — one Red→Green→Red cycle *)
  println [any (serial CRed l2)]).                    (* 7 — carried through unchanged *)

(** The negative tests: a broken FSM does NOT type-check (the build gate proves the
    bad transitions are unrepresentable).  [go_green] expects [Light CRed], so feeding
    it a [Light CGreen] — two greens in a row — is a type error; likewise [go_red] on
    a fresh ([CRed]) light.  These are genuine STATE mismatches: the positive trace
    [go_red (go_green fresh_light)] type-checks (it is used in [typestate_demo]), so
    the only reason these fail is the index. *)
Fail Definition bad_double_green : Light CGreen := go_green (go_green fresh_light).
Fail Definition bad_red_on_fresh : Light CRed   := go_red fresh_light.

(** ── Representation invariants (a struct invariant every method preserves) ───
    Another closed-world payoff.  A struct can carry a PROOF of its invariant as an
    ERASED ([Prop]) field, so the SMART CONSTRUCTOR demands the invariant hold and an
    out-of-invariant value is unrepresentable.  Here [Sorted2] bundles two ints with
    a proof [s_a <= s_b]; the proof field erases, so it lowers to a plain
    [struct { S_a, S_b int64 }] — zero runtime cost — yet the invariant is available
    to reason with.  [max_of] returns [s_b] directly as the maximum with NO runtime
    comparison, JUSTIFIED by the carried proof. *)
Record Sorted2 := MkSorted2 { s_a : GoI64 ; s_b : GoI64 ; s_ok : i64_leb s_a s_b = true }.

Definition min_of (p : Sorted2) : GoI64 := s_a p.
Definition max_of (p : Sorted2) : GoI64 := s_b p.

(* The invariant is usable: the max is provably >= the min, from the erased proof. *)
Example max_ge_min : forall p, i64_leb (min_of p) (max_of p) = true.
Proof. intros [a b ok]. exact ok. Qed.

Definition demo_pair : Sorted2 := MkSorted2 (3)%i64 (7)%i64 eq_refl.

Definition repinv_demo : IO unit :=
  bind (println [any (min_of demo_pair)])   (fun _ =>   (* 3 *)
  println [any (max_of demo_pair)]).                    (* 7 — the max, no compare *)

(** The negative test: a value VIOLATING the invariant cannot be built — [s_a <= s_b]
    fails for [7, 3], so [eq_refl] does not type-check and the struct is unconstructible. *)
Fail Definition bad_unsorted : Sorted2 := MkSorted2 (7)%i64 (3)%i64 eq_refl.

(** Sequenced with the [>>'] notation ([m >>' k := bind m (fun _ => k)]) — each
    demo's [unit] result is discarded, so this is a flat sequence, not a 45-deep
    nest of [bind … (fun _ => …)] closed by a wall of parens.  ([>>'] is
    left-associative; monad associativity makes the grouping irrelevant, and the
    plugin flattens it to the same straight-line Go.) *)
Definition main_effect : IO unit :=
  println [any (add 1 2)]       >>'   (* prints: 3 *)
  panic_and_recover (i64_add (40)%i64 (2)%i64)  >>'   (* prints: 42 43 *)
  div_demo                      >>'   (* prints: 3 2 *)
  overflow_safe_demo            >>'   (* prints: 3000000000000 1000000 *)
  float_demo                    >>'   (* prints: 3.75 / 0.25 (sci) *)
  float_cmp_demo                >>'   (* prints: true / true / true / false *)
  float_nan_demo 0              >>'   (* prints: false / false (NaN unordered) *)
  float_opp_demo                >>'   (* prints: -1.5 / 2.0 *)
  float_opp_sign_demo 0         >>'   (* prints: true (opp made -0 at runtime) *)
  u8_demo                       >>'   (* prints: 44 / 1 / 255 / true *)
  i8_demo                       >>'   (* prints: -106 / 127 / -100 / true *)
  u16_demo                      >>'   (* prints: 4464 / 16960 / -25536 *)
  bitwise_demo                  >>'   (* prints: 48 252 204 / 192 15 / -6 -6 *)
  shift_demo                    >>'   (* prints: 8 0 15 / -128 -2 *)
  convert_demo                  >>'   (* prints: 200 232 / 1200 *)
  divmod_demo                   >>'   (* prints: 28 4 -128 *)
  u32_demo                      >>'   (* prints: 705032704 -294967296 / 2147483648 / 1410065408 -2147479015 *)
  i64_demo                      >>'   (* prints: 9200000000000000000 9000000000000000000 *)
  i64_ops_demo                  >>'   (* prints: 1285714285714285714 1099511627776 / 4294967295 -6 *)
  u64_demo                      >>'   (* prints: 8000000000000000000 9000000000000000000 *)
  i64_pipeline_demo             >>'   (* prints: 9000000000000000001 (int64 through chan + map) *)
  u64_pipeline_demo             >>'   (* prints: 18000000000000000000 (uint64 >= 2^63 through chan + map) *)
  recv_unused_ok_demo           >>'   (* prints: 77 (recv_ok with unused ok-flag) *)
  builtins_demo                 >>'   (* prints: 3 5 / 3 / 0 *)
  prec_demo                     >>'   (* prints: 10 20 *)
  neglit_demo                   >>'   (* prints: -7 -1 -2147483648 *)
  map_demo                      >>'   (* prints: 3 999 0 *)
  slice_demo                    >>'   (* prints: 5 3 / false *)
  chan_demo                     >>'   (* prints: 42 true / 0 false *)
  select_demo                   >>'   (* prints: 42 (ch1 ready) *)
  select_default_demo           >>'   (* prints: 99 (default, ch empty) *)
  goroutine_demo                >>'   (* prints: 42 *)
  session_demo                  >>'   (* prints: 42 *)
  adder_demo                    >>'   (* prints: 42 *)
  control_flow_demo             >>'   (* prints: 5 true / 20 false / 1 *)
  bool_op_demo true false true  >>'   (* prints: false / true / true / true *)
  cond_op_demo                  >>'   (* prints: 1 / 1 / 1 *)
  inline_if_demo                >>'   (* prints: 1 / 0 / 1 *)
  lookup_demo                   >>'   (* prints: 700 true / false *)
  list_demo                     >>'   (* prints: 10 2 *)
  slice_safe_demo               >>'   (* prints: 20 true / 0 false *)
  assert_safe_demo (7 : int)    >>'   (* prints: 7 true / false false *)
  string_demo                   >>'   (* prints: 2 / 71 true / 0 false / Go! *)
  foreach_demo                  >>'   (* prints: 10 / 20 / 30 *)
  sum_demo                      >>'   (* prints: 10 *)
  cond_goto_demo true           >>'   (* prints: 1 / 3 *)
  cond_goto_demo false          >>'   (* prints: 1 / 2 / 3 *)
  diamond_demo true             >>'   (* prints: 1 / 10 / 99 *)
  diamond_demo false            >>'   (* prints: 1 / 20 / 99 *)
  loopif_demo                   >>'   (* prints: 100 / 0 / 1 / 2 *)
  nested_loop_demo              >>'   (* prints: 0 / 1 / 0 / 1 *)
  early_return_demo             >>'   (* prints: 0 / 1 *)
  labeled_break_demo            >>'   (* prints: 0 / 1 / 2 *)
  labeled_continue_demo         >>'   (* prints: 0 / 1 / 0 / 1 *)
  irreducible_demo false        >>'   (* prints: 1 / 2 / 1 / 2 *)
  irreducible_demo true         >>'   (* prints: 2 / 1 / 2 / 1 / 2 *)
  mut_demo                      >>'   (* prints: 15 *)
  count_demo                    >>'   (* prints: 0 / 1 / 2 *)
  defer_demo                    >>'   (* prints: 3 / 2 / 1 *)
  defer_loop_demo               >>'   (* prints: 2 / 1 / 0 *)
  point_demo                    >>'   (* prints: 3 / 4 / 7 *)
  labeled_demo                  >>'   (* prints: true / 5 *)
  method_demo                   >>'   (* prints: 7 / 13 / 14 / 27 *)
  io_method_demo                >>'   (* prints: 8 / 9 *)
  iface_demo                    >>'   (* prints: 14 / 1007 / 20 / 1010 *)
  typestate_demo                >>'   (* prints: 1 / 7 *)
  repinv_demo                   >>'   (* prints: 3 / 7 *)
  ret tt.

(** The IO ops are now DEFINITIONS (zero-axioms refactor); [Extraction NoInline]
    stops Coq from inlining their proof-only world-threading bodies, so the plugin
    still lowers each BY NAME to its Go primitive (and the abstract state — [ref_sel],
    [chan_buf], … — never reaches the emitted Go).  See ZERO_AXIOMS_PLAN.md. *)
Extraction NoInline
  ret bind panic catch run_io
  ref_get ref_set ref_new
  make_chan make_chan_buf send recv close_chan recv_ok select_recv2 select_recv_default go_spawn
  map_empty map_make map_make_typed
  map_get_opt map_len map_get_or map_set map_delete map_clear
  print println defer_call append slice_of_list run_blocks
  len cap slice_get slice_at_ok str_at_ok
  i64_lit i64_add i64_sub i64_mul i64_add_nz i64_sub_nz i64_mul_nz i64_eqb i64_ltb i64_leb
  i64_div i64_mod i64_and i64_or i64_xor i64_andnot i64_not i64_shl i64_shr
  u64_lit u64_add u64_sub u64_mul u64_eqb u64_ltb u64_leb
  u64_div u64_mod u64_and u64_or u64_xor u64_andnot u64_not u64_shl u64_shr
  sret sbind ssend srecv slift run_session.

Go Main Extraction main "main_effect".
