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

(** [add]/[sub] over the [Sint63] [int] survive ONLY as INDEX arithmetic (loop
    counters, computed slice indices like [sub 0 1]) — the Go [int] index type.
    All int64 VALUE arithmetic was migrated to the full-width [GoI64] (A4.3); the
    Sint63 VALUE-overflow theory ([add_nz]/[no_overflow_*]/[*_no_overflow_exact]/
    the signed-value conformance) is gone, replaced by the [GoI64] versions below. *)
Definition add (n m : int) : int := PrimInt63.add n m.
Definition sub (n m : int) : int := PrimInt63.sub n m.

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

(** PURE-FUNCTION TAIL-MATCH LOWERING (ladder 7b — value-position [if], tail case).
    Go has no conditional EXPRESSION, so an [if] in value position cannot be inlined
    as one.  But when the [if]/[match] is the whole function BODY (tail position),
    it lowers to a Go [if]/[else] whose arms each [return] — the idiomatic form.
    [i64_abs] is the canonical demo: Go has no integer [abs] builtin, so it is
    written by hand with exactly such an [if].  Faithful across the FULL int64
    range, INCLUDING the [MININT] corner ([|MININT| = MININT], the [0 - a]
    two's-complement overflow Go also exhibits) — machine-checked below. *)
Example i64_abs_pos    : i64_abs (7)%i64 = (7)%i64.   Proof. vm_compute. reflexivity. Qed.
Example i64_abs_neg    : i64_abs (-7)%i64 = (7)%i64.  Proof. vm_compute. reflexivity. Qed.
Example i64_abs_minint :
  i64_abs (-9223372036854775808)%i64 = (-9223372036854775808)%i64.
Proof. vm_compute. reflexivity. Qed.

Definition i64_abs_demo : IO unit :=
  println [ any (i64_abs (-7)%i64) ; any (i64_abs (7)%i64)
          ; any (i64_abs (-9223372036854775808)%i64) ].
  (* prints: 7 7 -9223372036854775808  (|MININT| wraps to MININT) *)

(** Unary integer negation (Go's unary [-]): the DIRECT prefix [-x], not the encoded
    [0 - x].  Faithful incl. the wrap corners ([-MININT = MININT], [-1 = 2^64-1] for
    uint64) — machine-checked. *)
Example i64_neg_5      : i64_neg (5)%i64 = (-5)%i64.   Proof. vm_compute. reflexivity. Qed.
Example i64_neg_minint : i64_neg (-9223372036854775808)%i64 = (-9223372036854775808)%i64.
Proof. vm_compute. reflexivity. Qed.
Example u64_neg_1      : u64_neg (1)%u64 = (18446744073709551615)%u64. Proof. vm_compute. reflexivity. Qed.
Definition neg_op_demo : IO unit :=
  println [ any (i64_neg (5)%i64)                       (* -5 *)
          ; any (i64_neg (i64_sub (0)%i64 (7)%i64)) ].  (* -(0 - 7) = 7 *)

(** Full-width int64 <-> uint64 CONVERSION (Go [uint64(x)] / [int64(x)]): a
    two's-complement REINTERPRET of the 64-bit pattern, EXACT (no rounding) --
    [-1 <-> 2^64-1], in-range values unchanged, round-trip = identity.  All
    machine-checked below; faithful by [wrap64_wrapU64] (the two normalisers agree
    mod 2^64).  Lowers to a small NAMED function
    [func U64_of_i64(a int64) uint64 { return uint64(a) }] so the cast applies to the
    parameter VARIABLE -- Go rejects [uint64(-1)] on an untyped CONSTANT but accepts it
    on an int64-typed value, so the demo's literals work directly. *)
Example conv_u64_of_neg1 : u64_of_i64 (-1)%i64 = (18446744073709551615)%u64.
Proof. vm_compute. reflexivity. Qed.
Example conv_i64_of_max  : i64_of_u64 (18446744073709551615)%u64 = (-1)%i64.
Proof. vm_compute. reflexivity. Qed.
Example conv_roundtrip   : i64_of_u64 (u64_of_i64 (-12345)%i64) = (-12345)%i64.
Proof. vm_compute. reflexivity. Qed.

Definition conv64_demo : IO unit :=
  println [ any (u64_of_i64 (-1)%i64)                       (* uint64(-1)    = 18446744073709551615 *)
          ; any (i64_of_u64 (18446744073709551615)%u64)     (* int64(2^64-1) = -1 *)
          ; any (u64_of_i64 (255)%i64) ].                   (* uint64(255)   = 255 *)

(** Direct [>] / [>=] / [!=] (completing Go's six comparison operators for
    int64/uint64) — each lowers to the DIRECT Go operator, not a swapped encoding.
    [u64_gtb] uses the UNSIGNED order ([2^64-1 > 1] is true). *)
Example i64_gtb_t     : i64_gtb  (5)%i64 (3)%i64 = true.   Proof. reflexivity. Qed.
Example i64_geb_t     : i64_geb  (5)%i64 (5)%i64 = true.   Proof. reflexivity. Qed.
Example i64_neqb_t    : i64_neqb (5)%i64 (3)%i64 = true.   Proof. reflexivity. Qed.
Example i64_neqb_f    : i64_neqb (5)%i64 (5)%i64 = false.  Proof. reflexivity. Qed.
Example u64_gtb_high  : u64_gtb (18446744073709551615)%u64 (1)%u64 = true.  Proof. reflexivity. Qed.
Example u64_geb_eq    : u64_geb (7)%u64 (7)%u64 = true.    Proof. reflexivity. Qed.

Definition cmp_ops_demo : IO unit :=
  println [ any (i64_gtb (5)%i64 (3)%i64)                        (* true *)
          ; any (i64_geb (5)%i64 (5)%i64)                        (* true *)
          ; any (i64_neqb (5)%i64 (3)%i64)                       (* true *)
          ; any (u64_gtb (18446744073709551615)%u64 (1)%u64) ].  (* true (unsigned) *)

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

(** Float [min]/[max] (Go 1.21 builtins, float rules) → Go [min(a,b)]/[max(a,b)].
    Faithful on the two IEEE corners Go's builtin handles: NaN PROPAGATION (a NaN arg
    gives a NaN result — witnessed via [eqb r r = false]) and SIGNED ZERO
    ([min(-0,+0) = -0], [max(-0,+0) = +0] — witnessed via [1/r], which is [-inf < 0]
    iff [r] is [-0]).  Plus the ordinary smaller/larger. *)
Example f64_min_ord     : f64_min 3 5 = 3%float. Proof. now vm_compute. Qed.
Example f64_max_ord     : f64_max 3 5 = 5%float. Proof. now vm_compute. Qed.
Example f64_min_nan     : PrimFloat.eqb (f64_min (PrimFloat.div 0 0) 1) (f64_min (PrimFloat.div 0 0) 1) = false.
Proof. now vm_compute. Qed.
Example f64_max_nan_b   : PrimFloat.eqb (f64_max 1 (PrimFloat.div 0 0)) (f64_max 1 (PrimFloat.div 0 0)) = false.
Proof. now vm_compute. Qed.
Example f64_min_negzero : PrimFloat.ltb (PrimFloat.div 1 (f64_min (PrimFloat.opp 0) 0)) 0 = true.
Proof. now vm_compute. Qed.
Example f64_max_poszero : PrimFloat.ltb (PrimFloat.div 1 (f64_max (PrimFloat.opp 0) 0)) 0 = false.
Proof. now vm_compute. Qed.

Definition fminmax_demo : IO unit :=
  println [ any (f64_min 3 5)%float ; any (f64_max 3 5)%float ].   (* min/max of two floats *)

(** Direct float [>] / [>=] / [!=] (completing the operator set).  Ordinary values
    plus the NaN corners: [NaN >= 1] is FALSE (the reason [f64_geb] is [leb b a], not
    [¬(<)], which would be true), and [NaN != 1] is TRUE. *)
Example f64_gtb_t   : f64_gtb 5 3 = true.   Proof. now vm_compute. Qed.
Example f64_geb_eq  : f64_geb 3 3 = true.   Proof. now vm_compute. Qed.
Example f64_geb_nan : f64_geb (PrimFloat.div 0 0) 1 = false. Proof. now vm_compute. Qed.
Example f64_neqb_nan: f64_neqb (PrimFloat.div 0 0) 1 = true. Proof. now vm_compute. Qed.

Definition fcmp_demo : IO unit :=
  println [ any (f64_gtb 5 3) ; any (f64_geb 3 3) ; any (f64_neqb 5 3) ]%float.  (* true true true *)

(** int64 -> float64 conversion ([f64_of_i64], Go [float64(i)]) -- MODELED + machine-
    checked: [7 -> 7.0] and the SIGNED case [-3 -> -3.0] (the Z-carried [GoI64] splits
    the sign over [PrimFloat.of_uint63]; >= 2^53 rounds exactly like Go).  *Runtime
    lowering still deferred, but no longer for the if-reason:* the ladder-7b value-
    position-[if] gap is now CLOSED for the tail case (see [i64_abs] above), so a pure
    function whose body is an [if] DOES extract.  What [f64_of_i64] still needs is a
    Go int->float CONVERSION primitive: its body uses [Z.leb]/[PrimFloat.of_uint63]
    (no Go lowering), and the [of_uint63] sign-split cannot represent [|MININT| = 2^63]
    (uint63 caps at 2^63-1).  The clean path is a dedicated [i64_to_f64] lowering to
    Go's native [float64(x)] (which handles the sign and the [MININT] corner directly),
    NOT extracting this proof-only sign-split body -- so it stays proof-only for now.
    *float64 -> int64 truncation:* a BOUNDARY -- [PrimFloat] has no truncation
    primitive (like [math.Abs]/[math.Sqrt]). *)
Example f64_of_i64_pos : PrimFloat.eqb (f64_of_i64 (7)%i64) 7%float = true.
Proof. now vm_compute. Qed.
Example f64_of_i64_neg : PrimFloat.eqb (f64_of_i64 (-3)%i64) (PrimFloat.opp 3%float) = true.
Proof. now vm_compute. Qed.

(** int → float64 (Go [float64(i)]) — DOES lower (unlike [f64_of_i64]): the [int] (Sint63)
    is already an int63, so the body needs only the leaf primitive [of_uint63] (no
    match-bodied [Uint63.of_Z]); recognized by name → native [float64(i)], the sign-split
    body suppressed.  Machine-checked across the sign. *)
Example f64_of_int_pos : PrimFloat.eqb (f64_of_int 5%sint63) 5%float = true.
Proof. now vm_compute. Qed.
Example f64_of_int_neg : PrimFloat.eqb (f64_of_int (-3)%sint63) (PrimFloat.opp 3%float) = true.
Proof. now vm_compute. Qed.
Definition f64_of_int_demo : IO unit :=
  println [ any (f64_of_int 5%sint63) ; any (f64_of_int (-3)%sint63) ].
  (* prints: +5.000000e+000 -3.000000e+000 (int → float64 cast) *)

(** GoI64 → float64 (Go [float64(i64)]) — NOW lowers too: same recognize-and-suppress as
    [f64_of_int], plus suppressing the [Z]→int63 helpers [of_Z]/[of_pos] its [Z] carrier
    drags (the [Z]/[positive] arithmetic was already suppressed by module).  It returns
    [float], so it stays a NAMED call — the lowering [f64_of_i64] left deferred is closed. *)
Definition f64_of_i64_demo : IO unit :=
  println [ any (f64_of_i64 (7)%i64) ; any (f64_of_i64 (-3)%i64) ].
  (* prints: +7.000000e+000 -3.000000e+000 (int64 → float64 cast) *)

(** float64 → int64 (Go [int64(f)]): TRUNCATE toward zero, via the verified [Prim2SF]
    decomposition.  Machine-checked across the sign, the exact case, and zero. *)
Example i64_of_f64_pos   : i64_of_f64 3.7%float       = (3)%i64.       Proof. now vm_compute. Qed.
Example i64_of_f64_neg   : i64_of_f64 (-3.7)%float    = (-3)%i64.      Proof. now vm_compute. Qed.
Example i64_of_f64_exact : i64_of_f64 100%float       = (100)%i64.     Proof. now vm_compute. Qed.
Example i64_of_f64_zero  : i64_of_f64 0%float         = (0)%i64.       Proof. now vm_compute. Qed.
Example i64_of_f64_big   : i64_of_f64 1000000.9%float = (1000000)%i64. Proof. now vm_compute. Qed.
(** *Lowering DEFERRED* (proof-only, like [f64_of_i64] once was): [i64_of_f64] returns
    [GoI64] (a single-field record), so its Z-from-[Prim2SF] body hits the SAME wall as the
    narrow→int64 widening — Coq's case-of-case fusion inlines the [match] into value position
    regardless of [NoInline] / splitting out [f64_trunc_Z].  (The int→float directions lower
    because they return [float], a PRIMITIVE, not a record.)  The MODEL is faithful and
    machine-checked above; the intended lowering is the native [int64(f)] once the
    record-result fusion is solved. *)


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

(** Direct [>] / [>=] / [!=] for the fixed-width types (uint8/int8 here; the plugin
    recognizes the same op on every width).  Each lowers to the DIRECT Go operator. *)
Example u8_gtb_t  : u8_gtb (u8_lit 200 eq_refl) (u8_lit 100 eq_refl) = true. Proof. now vm_compute. Qed.
Example i8_geb_eq : i8_geb (i8_lit 5 eq_refl) (i8_lit 5 eq_refl) = true.     Proof. now vm_compute. Qed.
Example i8_neqb_t : i8_neqb (i8_lit 5 eq_refl) (i8_lit (-5) eq_refl) = true. Proof. now vm_compute. Qed.
Example u32_gtb_t : u32_gtb (u32_lit 4000000000 eq_refl) (u32_lit 1 eq_refl) = true. Proof. now vm_compute. Qed.
Example i16_neqb_t: i16_neqb (i16_lit 5 eq_refl) (i16_lit (-5) eq_refl) = true. Proof. now vm_compute. Qed.
Definition fw_cmp_demo : IO unit :=
  println [ any (u8_gtb (u8_lit 200 eq_refl) (u8_lit 100 eq_refl))   (* 200 > 100 → true *)
          ; any (i8_geb (i8_lit 5 eq_refl) (i8_lit 5 eq_refl))       (* 5 >= 5 → true *)
          ; any (i8_neqb (i8_lit 5 eq_refl) (i8_lit (-5) eq_refl))   (* 5 != -5 → true *)
          ; any (u32_gtb (u32_lit 4000000000 eq_refl) (u32_lit 1 eq_refl)) ].  (* big > 1 → true *)

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

(** Narrow -> int64 WIDENING (Go [int64(x)]): value-PRESERVING (a byte/short fits
    int64), so the byte/short value lands unchanged in the canonical [GoI64].
    Unsigned narrows stay non-negative; a signed narrow keeps its sign
    ([int64(int8 -5) = -5]).  MODELED + machine-checked across signed/unsigned and
    small/large widths.  *Runtime lowering deferred (would be IDENTITY — the narrow
    already erases to a Go int64 holding exactly this value):* the faithful Coq body
    crosses the PrimInt63 -> Z carrier via [Sint63.to_Z], whose stdlib chain
    ([Sint63Axioms.to_Z] -> [Uint63.ltb] …) includes the DELIBERATELY-REJECTED unsigned
    [Uint63.ltb] (Tier 3 #9), so extracting the body drags a banned decl.  Kept proof-only.
    *Root cause (deepened diagnosis 2026-06-19):* the single-field [GoI64]/[GoU8] records
    UNBOX, so EVERY faithful widening body η-reduces to a RENAMING of [Sint63.to_Z], which
    Coq's extraction force-inlines regardless of [Extraction NoInline] — splicing [to_Z]'s
    [if]-body (an [MLcase] over the rejected [Uint63.ltb]) into VALUE position, where the
    pure value-position match cannot lower (ladder 7b).  Confirmed exhaustively: routing
    through a FIDO wrapper [i64_of_int63] (NON-renaming match body, NON-match [Z.add … 0]
    body, called directly or via the narrows) STILL inlines into value position — yet the
    STRUCTURALLY-IDENTICAL [i64_abs] ([GoI64 -> GoI64], match body, same NoInline list) stays
    a named decl whose [if] lowers fine in TAIL position.  The differentiator is the
    [int -> GoI64] carrier crossing, not NoInline per se.  The robust fix is the
    **narrow-stored-in-Z model** (re-base [GoU8]… on [Z] like [GoI64]): then [i64_of_u8 a =
    MkI64 (u8raw a)] is a pure IDENTITY ([u8raw : GoU8 -> Z], no [to_Z], no match), lowering
    to [a].  A focused all-6-types carrier refactor, deferred to its own iteration. *)
Example widen_u8  : i64_of_u8  (u8_lit 200 eq_refl)         = (200)%i64.        Proof. vm_compute. reflexivity. Qed.
Example widen_i8  : i64_of_i8  (i8_of_int (-5)%sint63)      = (-5)%i64.         Proof. vm_compute. reflexivity. Qed.
Example widen_u16 : i64_of_u16 (u16_lit 60000 eq_refl)      = (60000)%i64.      Proof. vm_compute. reflexivity. Qed.
Example widen_u32 : i64_of_u32 (u32_lit 4000000000 eq_refl) = (4000000000)%i64. Proof. vm_compute. reflexivity. Qed.
Example widen_i32 : i64_of_i32 (i32_of_int (-7)%sint63)     = (-7)%i64.         Proof. vm_compute. reflexivity. Qed.

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
(* No-overflow ⇒ EXACT, at the TRUE int64 width (the canonical overflow theorem;
   the bounded Sint63 version was removed when the int model migrated to GoI64). *)
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

(** ===== A5: untyped INTEGER constants (Go spec "Constants") =====
    [i64c]/[u64c] take a closed [Z] constant EXPRESSION, evaluate it at arbitrary
    precision ([vm_compute]) and acquire the fixed-width type at use, demanding
    representability.  Witnesses:
    - constant arithmetic is EXACT and an INTERMEDIATE may exceed the target as long
      as the final value fits: [(1<<70) >> 8 = 2^62] — the [1<<70] intermediate is far
      past int64, yet the result is a valid int64 ([const_intermediate_exceeds]).
    - the type is acquired at USE: [2^63] fits uint64 but NOT int64 ([const_u64_upper]).
    - an out-of-range constant FAILS to elaborate = Go's untyped-constant overflow
      compile error ([const_oob_i64]/[const_oob_u64] `Fail`). *)
Example const_intermediate_exceeds :
  i64c (Z.shiftr (Z.shiftl 1 70) 8) = i64_lit 4611686018427387904 eq_refl.
Proof. reflexivity. Qed.
Example const_exact_arith :
  i64raw (i64c (1000 * 1000 * 1000 * 1000)%Z) = 1000000000000%Z.
Proof. reflexivity. Qed.
Example const_u64_upper :
  u64raw (u64c (Z.shiftl 1 63)) = 9223372036854775808%Z.
Proof. reflexivity. Qed.
(* OUT-OF-RANGE untyped constants — do NOT elaborate (the representability proof
   cannot be built): Go's untyped-constant overflow. *)
Fail Definition const_oob_i64 : GoI64 := i64c (Z.shiftl 1 70).   (* 2^70 > int64 max *)
Fail Definition const_oob_u64 : GoU64 := u64c (Z.shiftl 1 64).   (* 2^64 > uint64 max *)

(** Runtime demo: two int64 constants built by arbitrary-precision constant
    arithmetic.  10^12 is exact; [(1<<70)>>8 = 2^62] has an intermediate ([1<<70])
    that overflows int64, yet the result is in range.  Both < 2^63, so they also fit
    Go's untyped-constant default [int] in [println]. *)
Definition const_demo : IO unit :=
  println [ any (i64c (1000 * 1000 * 1000 * 1000)%Z)      (* 1000000000000 *)
          ; any (i64c (Z.shiftr (Z.shiftl 1 70) 8)) ].    (* 4611686018427387904 = 2^62 *)

(** Predeclared builtins (Go spec "Built-in functions"): [min]/[max] (Go 1.21) on
    [int], slice [make([]T,n)], and map [clear].  [min]/[max] machine-checked;
    [slice_make]'s length is a THEOREM; [clear] empties the map (get-after-clear is
    a theorem, [map_get_clear]). *)
Example spec_go_min       : go_min 3 5 = 3%uint63. Proof. now vm_compute. Qed.
Example spec_go_max       : go_max 3 5 = 5%uint63. Proof. now vm_compute. Qed.
Example spec_go_min_neg   : go_min (-2)%sint63 1 = (-2)%sint63. Proof. now vm_compute. Qed.
(** [min]/[max] on the canonical full-width types: int64 (SIGNED — so a negative is
    the min) and uint64 (UNSIGNED — so a value >= 2^63 is LARGER than a small one,
    NOT negative).  [u64_max] of [2^64-1] and [1] is [2^64-1] (unsigned), the case
    that distinguishes the uint64 order from a signed one.  All theorems. *)
Example spec_i64_min      : i64_min (-2)%i64 (1)%i64 = (-2)%i64. Proof. vm_compute. reflexivity. Qed.
Example spec_i64_max      : i64_max (-2)%i64 (1)%i64 = (1)%i64.  Proof. vm_compute. reflexivity. Qed.
Example spec_u64_max_high : u64_max (18446744073709551615)%u64 (1)%u64 = (18446744073709551615)%u64.
Proof. vm_compute. reflexivity. Qed.
Example spec_u64_min_high : u64_min (18446744073709551615)%u64 (1)%u64 = (1)%u64.
Proof. vm_compute. reflexivity. Qed.

(** [min]/[max] on int64/uint64 → Go's builtins.  The uint64 [max] uses a RUNTIME
    [2^64-1] ([u64_of_i64 (-1)], a function call, NOT a constant) — both so it prints
    as a typed uint64 (a constant [>= 2^63] would overflow [println]'s default [int])
    AND so it isn't constant-folded under the SIGNED reading: the genuine unsigned
    [max(2^64-1, 1) = 2^64-1] is the case a signed order would get wrong. *)
Definition minmax64_demo : IO unit :=
  println [ any (i64_min (-2)%i64 (1)%i64)                        (* -2 *)
          ; any (i64_max (-2)%i64 (1)%i64)                        (* 1 *)
          ; any (u64_max (u64_of_i64 (-1)%i64) (1)%u64) ].        (* 18446744073709551615 (unsigned: big > 1) *)
Example spec_slice_make_n : List.length (slice_make TI64 3) = 3%nat. Proof. reflexivity. Qed.
Definition builtins_demo : IO unit :=
  bind (println [ any (go_min (3 : int) (5 : int)); any (go_max (3 : int) (5 : int)) ]) (fun _ =>  (* 3 5 — go_min/max are the min/max BUILTIN demo, kept on int *)
  bind (println [ any (len (slice_make TI64 3)) ]) (fun _ =>                                     (* 3 *)
  bind (map_make_typed TI64 TI64) (fun m =>
  bind (map_set TI64 TI64 (1)%i64 (10)%i64 m) (fun _ =>
  bind (map_clear TI64 TI64 m) (fun _ =>                                                                     (* clear → empty *)
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

(** String slicing [s[a:b]] (the byte-substring) — proof-gated, so it cannot panic.  THEOREM:
    [s[7:12]] of "Hello, world" is "world".  Build-checked negative: out-of-range bounds
    ([13 > len]) do NOT type-check (the bounds proof cannot be built). *)
Example spec_str_slice : str_slice "Hello, world"%string 7 12 eq_refl = "world"%string.
Proof. reflexivity. Qed.
Fail Definition str_slice_oob : GoString := str_slice "Hello"%string 0 13 eq_refl.
Definition str_slice_demo : IO unit :=
  println [ any (str_slice "Hello, world"%string 7 12 eq_refl) ].   (* prints: world *)

(** String COMPARISON (Go [==] / [<]): byte-sequence equality and LEXICOGRAPHIC
    byte-order — both THEOREMS.  Equality decides same/different bytes; ordering
    compares byte-by-byte with a proper prefix ordered before the longer string
    (["ab" < "abc"]) and by byte value at the first difference (["abc" < "abd"]). *)
Example spec_str_eq_same  : str_eqb "Go"%string "Go"%string = true.   Proof. reflexivity. Qed.
Example spec_str_eq_diff  : str_eqb "Go"%string "No"%string = false.  Proof. reflexivity. Qed.
Example spec_str_lt_byte  : str_ltb "abc"%string "abd"%string = true. Proof. reflexivity. Qed.
Example spec_str_lt_prefix: str_ltb "ab"%string "abc"%string = true.  Proof. reflexivity. Qed.
Example spec_str_lt_false : str_ltb "b"%string "a"%string = false.    Proof. reflexivity. Qed.
Example spec_str_lt_eq    : str_ltb "Go"%string "Go"%string = false.  Proof. reflexivity. Qed.
(* Direct >/>=/!= for strings (lexicographic total order). *)
Example spec_str_gt       : str_gtb  "b"%string "a"%string = true.   Proof. reflexivity. Qed.
Example spec_str_ge_eq    : str_geb  "a"%string "a"%string = true.   Proof. reflexivity. Qed.
Example spec_str_ne       : str_neqb "a"%string "b"%string = true.   Proof. reflexivity. Qed.
Definition scmp_demo : IO unit :=
  println [ any (str_gtb "b"%string "a"%string) ; any (str_geb "a"%string "a"%string)
          ; any (str_neqb "a"%string "b"%string) ].   (* true true true *)

(** Operator-precedence PARENS: nested arithmetic parenthesises only where the
    precedence requires it ([a*b + c] no parens; [(a+b) * c] needs them).  gofmt
    handles the spacing (it tightens to [a*b+c]); the printer handles the parens. *)
Definition prec_demo : IO unit :=
  let a := (2)%i64 in let b := (3)%i64 in let c := (4)%i64 in
  println [ any (a * b + c)%i64        (* a*b + c   = 10 *)
          ; any ((a + b) * c)%i64 ].   (* (a+b) * c = 20 *)

(** Negative [int64] LITERALS print correctly.  A [GoI64] is [Z]-carried, so a
    negative is a genuine [Zneg]; the plugin emits its signed decimal (the bare-[Z]
    arm distinguishes a real negative from a [uint64 >= 2^63]). *)
Definition neglit_demo : IO unit :=
  println [any (-7)%i64; any (-1)%i64; any (-2147483648)%i64].
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
  let xs := slice_of_list TI64 [(1)%i64; (2)%i64; (3)%i64; (4)%i64; (5)%i64] in
  let n  := len xs in
  bind (slice_get TI64 xs (2:int)) (fun v =>   (* xs[2] = 3, valid (index is Go int) *)
  println [any n; any v] >>'                      (* prints: 5 3 *)
  catch
    (bind (@slice_get GoI64 TI64 xs (9:int)) (fun _ =>  (* xs[9] panics — OOB *)
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
  let xs := slice_of_list TI64 [(10)%i64; (20)%i64; (30)%i64] in
  match xs with
  | nil         => println [any false]
  | cons x rest => println [any x; any (len rest)]   (* head=10, len tail=2 *)
  end.

(** Safe slice access: [slice_at_ok] bounds-checks and forces handling the
    out-of-bounds case, so it cannot panic — the safe-by-construction default,
    versus the [slice_get] escape hatch used in [slice_demo] above. *)
Definition slice_safe_demo : IO unit :=
  let xs := slice_of_list TI64 [(10)%i64; (20)%i64; (30)%i64] in
  slice_at_ok TI64 xs (1 : int) (fun v ok =>      (* in bounds → 20 true *)
  println [any v; any ok] >>'
  slice_at_ok TI64 xs (9 : int) (fun v2 ok2 =>    (* above range → 0 false *)
  println [any v2; any ok2] >>'
  (* runtime-NEGATIVE index (sub 0 1 = -1) — a *constant* negative index is a Go
     compile error, so use a computed one; the lower-bound check must reject it.
     The index is a Go [int], so [sub] (Sint63) is kept for index arithmetic. *)
  slice_at_ok TI64 xs (sub 0 1) (fun v3 ok3 =>    (* negative (signed) → 0 false *)
  println [any v3; any ok3]))).

(** Array (Go spec "Array types"): a FIXED-SIZE [3]int64 VALUE.  [arr_lit] lowers to
    the [[3]int64{…}] literal (the size from the list length, not the Coq type), bound
    to a local whose Go type is INFERRED.  [arr_get_ok] is the bounds-checked read (Go
    arrays panic on OOB), identical lowering to [slice_at_ok].  Distinct from a slice:
    a fixed-size [N]T value (value-copy + comparability are later B4 pieces). *)
Definition arr_demo : IO unit :=
  let a := arr_lit TI64 [(10)%i64; (20)%i64; (30)%i64] in   (* [3]int64{10,20,30} *)
  arr_get_ok TI64 a (1 : int) (fun v ok =>        (* a[1] in bounds → 20 true *)
  println [any v; any ok] >>'
  (* a CONSTANT out-of-range index on an array is a Go COMPILE error (arrays are
     statically bounds-checked, unlike slices), so use a COMPUTED index [sub 10 5 = 5]
     (lowers to a runtime [Sub(10,5)]); [arr_get_ok]'s guard then rejects it at runtime *)
  arr_get_ok TI64 a (sub 10 5) (fun v2 ok2 =>     (* a[5] out of range → 0 false *)
  println [any v2; any ok2])).

(** Array COMPARABILITY (Go [==], field-wise): arrays are comparable (slices are NOT).
    [arr_eqb] decides array equality element-wise — a THEOREM — and lowers to the bare
    Go [a == b].  Distinct from slices, which support only [== nil]. *)
Example arr_eqb_t : arr_eqb (arr_lit TI64 [(1)%i64;(2)%i64;(3)%i64])
                            (arr_lit TI64 [(1)%i64;(2)%i64;(3)%i64]) = true.
Proof. reflexivity. Qed.
Example arr_eqb_f : arr_eqb (arr_lit TI64 [(1)%i64;(2)%i64;(3)%i64])
                            (arr_lit TI64 [(1)%i64;(2)%i64;(9)%i64]) = false.
Proof. reflexivity. Qed.
Definition arr_eq_demo : IO unit :=
  let a := arr_lit TI64 [(1)%i64; (2)%i64; (3)%i64] in
  let b := arr_lit TI64 [(1)%i64; (2)%i64; (3)%i64] in
  let c := arr_lit TI64 [(1)%i64; (2)%i64; (9)%i64] in
  println [any (arr_eqb a b); any (arr_eqb a c)].   (* true false *)

(** Array VALUE-COPY (the defining array-vs-slice distinction): [arr_set a i v] is a
    FUNCTIONAL update (a copy-mutate-return IIFE), so [a] is UNCHANGED — a slice would
    share the backing.  The size [3] is passed explicitly (it is erased from the Coq
    type).  Machine-checked that the update lands and the original is untouched. *)
Example arr_set_copy :
  arr_data (arr_set 3 TI64 (arr_lit TI64 [(10)%i64;(20)%i64;(30)%i64]) (0:int) (99)%i64)
  = [(99)%i64;(20)%i64;(30)%i64].
Proof. reflexivity. Qed.
Definition arr_copy_demo : IO unit :=
  let a := arr_lit TI64 [(10)%i64; (20)%i64; (30)%i64] in
  let b := arr_set 3 TI64 a (0:int) (99)%i64 in   (* b = a with [0]=99; a UNCHANGED (value-copy) *)
  println [ any (arr_eqb a (arr_lit TI64 [(10)%i64;(20)%i64;(30)%i64]))    (* a STILL [10,20,30] → true *)
          ; any (arr_eqb b (arr_lit TI64 [(99)%i64;(20)%i64;(30)%i64])) ]. (* b IS [99,20,30] → true *)

(** Safe type assertion: [type_assert_safe] is Go's [v, ok := x.(T)] — no panic
    on a type mismatch, the caller handles [ok = false].  Safe-by-construction
    default versus the [type_assert] escape hatch.  We assert on a recovered
    panic value [r : GoAny] (a genuine [any], like [panic_and_recover]). *)
Definition assert_safe_demo (n : GoI64) : IO unit :=
  catch (@panic unit (any n))
    (fun r =>
     type_assert_safe TI64 r (fun v ok =>        (* r holds int64 → n true *)
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

(** String COMPARISON (Go [==] / [<]): byte-sequence equality and lexicographic
    byte ordering.  Lowers to the bare Go operators on string operands. *)
Definition str_cmp_demo : IO unit :=
  println [ any (str_eqb "Go"%string "Go"%string)    (* true  *)
          ; any (str_eqb "Go"%string "No"%string)    (* false *)
          ; any (str_ltb "abc"%string "abd"%string)  (* true  *)
          ; any (str_ltb "b"%string "a"%string) ].   (* false *)

(** Type switch (Go spec "Type switches"): [switch v := a.(type) { case bool: …;
    case string: …; default: … }] dispatches on the RUNTIME type of the [any] value
    [a].  Built on [type_switch2] (axiom-free, the same [tag_coerce] basis as
    [type_assert_safe]); lowers to Go's native type switch.  The matching arm binds the
    correctly-typed value; the default fires for any type matching neither arm (here an
    int64-valued [any]). *)
Definition tsw_demo (a : GoAny) : IO unit :=
  type_switch2 a
    TBool   (fun b => println [any b; any (1)%i64])      (* case bool   → b, 1 *)
    TString (fun s => println [any s; any (2)%i64])       (* case string → s, 2 *)
    (println [any (9)%i64]).                              (* default     → 9   *)

(** N-ary type switch (3 cases): same combinator, one more arm.  The int64 case is
    driven by a value of Go type [int64] (a function RETURN, [i64_abs]) so it boxes as
    [int64] and matches — a bare int literal would box as Go [int] and miss it. *)
Definition tsw3_demo (a : GoAny) : IO unit :=
  type_switch3 a
    TBool   (fun b => println [any b; any (1)%i64])      (* case bool   → b, 1 *)
    TString (fun s => println [any s; any (2)%i64])       (* case string → s, 2 *)
    TI64    (fun n => println [any n; any (3)%i64])        (* case int64  → n, 3 *)
    (println [any (9)%i64]).                              (* default     → 9   *)

(** Multi-type case (Go's [case T1, T2:]): one arm matching EITHER type, value not
    narrowed.  [type_switch_or2] runs the thunk when the type is bool OR string. *)
Definition tsw_or_demo (a : GoAny) : IO unit :=
  type_switch_or2 a TBool TString
    (println [any (1)%i64])      (* case bool, string → 1 *)
    (println [any (0)%i64]).     (* default           → 0 *)

(** N-type multi-case (Go's [case T1, T2, T3:]): one arm matching ANY of three types.
    [type_switch_or3] runs the thunk when the type is bool OR string OR int64 (the int64
    case is machine-checked by [type_switch_or3_third]; an int LITERAL boxes as Go [int],
    distinct from [int64], so it hits the default). *)
Definition tsw_or3_demo (a : GoAny) : IO unit :=
  type_switch_or3 a TBool TString TI64
    (println [any (1)%i64])      (* case bool, string, int64 → 1 *)
    (println [any (0)%i64]).     (* default                  → 0 *)

(** Native EXPRESSION switch (Go's [switch x { case 1: …; case 2: …; default: … }]) on an
    int64 value.  [int_switch2] is an equality if-chain (faithful) lowered to native Go. *)
Definition int_sw_demo (x : GoI64) : IO unit :=
  int_switch2 x
    (1)%i64 (println [any (10)%i64])    (* case 1 → 10 *)
    (2)%i64 (println [any (20)%i64])    (* case 2 → 20 *)
    (println [any (99)%i64]).           (* default → 99 *)

(** N-ary expression switch (3 cases) — confirms the generalised arm lowers >2 cases. *)
Definition int_sw3_demo (x : GoI64) : IO unit :=
  int_switch3 x
    (1)%i64 (println [any (10)%i64])    (* case 1 → 10 *)
    (2)%i64 (println [any (20)%i64])    (* case 2 → 20 *)
    (3)%i64 (println [any (30)%i64])    (* case 3 → 30 *)
    (println [any (99)%i64]).           (* default → 99 *)

(** Complex numbers (Go's predeclared [complex]/[real]/[imag]): build a [complex128] from
    two float64 components, then extract them.  [go_real (go_complex re im) = re] holds by
    [reflexivity] (see builtins.v); lowers to native [complex(…)]/[real(…)]/[imag(…)]. *)
Definition complex_demo : IO unit :=
  let c := go_complex (1.5)%float (2.5)%float in
  println [any (go_real c); any (go_imag c)].   (* the two components (Go float format) *)

(** Complex [+] / [-] (component-wise, native Go operators): (1+2i)+(3+4i) = 4+6i,
    (1+2i)-(3+4i) = -2-2i.  Extract each component to print. *)
Definition complex_arith_demo : IO unit :=
  let a := go_complex (1.0)%float (2.0)%float in
  let b := go_complex (3.0)%float (4.0)%float in
  let s := complex_add a b in
  let d := complex_sub a b in
  println [any (go_real s); any (go_imag s); any (go_real d); any (go_imag d)].

(** Complex unary [-] (component-wise sign-flip, native operator): -(3+4i) = -3-4i. *)
Definition complex_neg_demo : IO unit :=
  let c := go_complex (3.0)%float (4.0)%float in
  let n := complex_neg c in
  println [any (go_real n); any (go_imag n)].   (* -3 -4 *)

(** Complex [*] (gc's naive cross-product, native operator): (1+2i)*(3+4i) = -5+10i. *)
Definition complex_mul_demo : IO unit :=
  let a := go_complex (1.0)%float (2.0)%float in
  let b := go_complex (3.0)%float (4.0)%float in
  let p := complex_mul a b in
  println [any (go_real p); any (go_imag p)].   (* -5 10 *)

(** Complex [/] (Smith's algorithm = gc's runtime.complex128div, native operator):
    (1+2i)/(3+4i) = 0.44 + 0.08i. *)
Definition complex_div_demo : IO unit :=
  let a := go_complex (1.0)%float (2.0)%float in
  let b := go_complex (3.0)%float (4.0)%float in
  let q := complex_div a b in
  println [any (go_real q); any (go_imag q)].   (* 0.44 0.08 *)

(** Complex [==] / [!=] (component-wise, native operators): equal complexes compare equal,
    a differing imaginary part makes them unequal. *)
Definition complex_cmp_demo : IO unit :=
  let a := go_complex (1.0)%float (2.0)%float in
  let b := go_complex (1.0)%float (2.0)%float in
  let c := go_complex (1.0)%float (3.0)%float in
  println [any (complex_eqb a b); any (complex_eqb a c); any (complex_neqb a c)].  (* true false true *)

(** Expression switch on a STRING (Go's [switch s { case "a": …; default: … }]). *)
Definition str_sw_demo (x : GoString) : IO unit :=
  str_switch2 x
    "a"%string (println [any (1)%i64])   (* case "a" → 1 *)
    "b"%string (println [any (2)%i64])   (* case "b" → 2 *)
    (println [any (9)%i64]).             (* default  → 9 *)

(** N-ary string expression switch (3 cases). *)
Definition str_sw3_demo (x : GoString) : IO unit :=
  str_switch3 x
    "a"%string (println [any (1)%i64])   (* case "a" → 1 *)
    "b"%string (println [any (2)%i64])   (* case "b" → 2 *)
    "c"%string (println [any (3)%i64])   (* case "c" → 3 *)
    (println [any (9)%i64]).             (* default  → 9 *)

(** [[]byte] / [string] conversions (Go's byte-slice interop): [[]byte("Hi")] is the
    byte sequence, [string(b)] reconstructs the string.  Round-trips "Hi" → bytes → "Hi"
    (value round-trip golden-checked; byte-count preservation is the theorem
    [str_to_bytes_length]). *)
Definition bytes_demo : IO unit :=
  let b := str_to_bytes "Hi"%string in   (* []byte("Hi") *)
  println [any (str_from_bytes b)].        (* string(b) → "Hi" *)

(** Rune view ([[]rune] / [string([]rune)], UTF-8): decode a string to code points and
    encode back.  Round-trips "Go" → runes → "Go" (the codec is verified for ASCII and a
    3-byte CJK point by [rune_roundtrip_ascii]/[_cjk]; runtime is native UTF-8). *)
Definition rune_demo : IO unit :=
  let rs := str_to_runes "Go"%string in   (* []rune("Go") *)
  println [any (runes_to_str rs)].          (* string(rs) → "Go" *)

(** Single rune → string (Go's [string(rune)]): code point 65 → "A". *)
Definition rune_to_str_demo : IO unit :=
  println [any (rune_to_str (MkI32 65%uint63))].   (* string(rune(65)) → "A" *)

(** Go [for i, r := range s]: [i] the BYTE offset of each code point, [r] the rune.
    Byte offsets are faithful to UTF-8 widths — for [A 中 B] (1/3/1 bytes) the offsets are
    [0 1 4], machine-checked here on the model; [str_range] lowers to the native two-variable
    range loop.  The decode round-trips ([str_to_runes ∘ runes_to_str = id], [rune_roundtrip_*]). *)
Example str_range_offsets :
  runes_with_offsets 0%uint63
    (str_to_runes (runes_to_str (MkI32 65%uint63 :: MkI32 20013%uint63 :: MkI32 66%uint63 :: nil)))
  = (0%uint63, MkI32 65%uint63) :: (1%uint63, MkI32 20013%uint63) :: (4%uint63, MkI32 66%uint63) :: nil.
Proof. vm_compute. reflexivity. Qed.
Definition str_range_demo : IO unit :=
  str_range (str_concat (rune_to_str (MkI32 72%uint63))
            (str_concat (rune_to_str (MkI32 8364%uint63))
                        (rune_to_str (MkI32 33%uint63))))   (* "H€!" — H(1 byte) €(3) !(1) *)
    (fun i r => println [any i; any r]).   (* 0 72 / 1 8364 / 4 33 (byte offset, rune) *)

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

(** Phase B1: POINTERS (Go spec "Pointer types").  [ptr_new] allocates a fresh
    [*int64] holding 10; [*p] reads it; [*p = v] writes through it.  Distinct from a
    [Ref] (a local var): a [Ptr] lowers to Go [*T], so a COPY of the pointer aliases
    the SAME cell — the [ptr_alias] THEOREM (builtins.v) proves a write through one
    handle is seen through another.  Read-after-write is [ptr_get_set_same]. *)
Definition ptr_demo : IO unit :=
  bind (ptr_new TI64 (10)%i64) (fun p =>      (* p := new(int64) ← 10 *)
  bind (ptr_get TI64 p)        (fun a =>      (* a := *p  (= 10) *)
  bind (println [any a])       (fun _ =>      (* prints 10 *)
  bind (ptr_set p (99)%i64)    (fun _ =>      (* *p = 99 *)
  bind (ptr_get TI64 p)        (fun b =>      (* b := *p  (= 99) *)
  println [any b]))))).                        (* prints 99 *)

(** [new(T)] (Go's predeclared builtin): a fresh [*int64] pointing to the ZERO value;
    dereferencing it reads 0.  Now unblocked by the pointer model (B1). *)
Definition new_demo : IO unit :=
  bind (go_new TI64) (fun p =>          (* p := new(int64) *)
  bind (ptr_get TI64 p) (fun v =>       (* v := *p  (= 0, the zero value) *)
  println [any v])).                     (* prints 0 *)

(** Phase B1b: SAFE (nil-checked) deref.  [ptr_get_ok] is the safe-by-construction
    default — it BRANCHES on [p != nil], forcing the nil case, so the nil-deref panic
    is unreachable ([ptr_get_ok_nil] THEOREM).  A live pointer reads through ([ok=true]);
    a nil pointer yields the zero value with [ok=false] — never a panic. *)
Definition ptr_safe_demo : IO unit :=
  bind (ptr_new TI64 (42)%i64) (fun p =>           (* live pointer to 42 *)
  ptr_get_ok TI64 p (fun v ok =>                    (* p != nil → v=42, ok=true *)
  bind (println [any v; any ok]) (fun _ =>          (* prints 42 true *)
  ptr_get_ok TI64 (ptr_nil TI64) (fun v2 ok2 =>     (* nil → v2=0, ok2=false, NO panic *)
  println [any v2; any ok2])))).                     (* prints 0 false *)

(** Phase B3a: SLICE ALIASING.  A [SliceH] is an aliasing handle into a backing array;
    a SUB-SLICE [s[1:3]] SHARES that backing, so a write through the sub-slice is seen
    through the parent — the [subslice_alias] THEOREM.  Here [s[1:3][0] = 99] writes
    [s[1]], read back as 99 — impossible for the value (list-based) slice model. *)
Definition slice_alias_demo : IO unit :=
  bind (slice_make_h TI64 (3:int)) (fun s =>                                  (* s := make([]int64, 3) *)
  bind (slice_idx_set s (0:int) (10)%i64) (fun _ =>                           (* s[0] = 10 *)
  bind (slice_idx_set s (1:int) (20)%i64) (fun _ =>                           (* s[1] = 20 *)
  bind (slice_idx_set (subslice s (1:int) (3:int)) (0:int) (99)%i64) (fun _ =>  (* s[1:3][0] = 99 (= s[1]) *)
  bind (slice_idx_get TI64 s (1:int)) (fun v =>                               (* v := s[1] — sees 99 (aliasing) *)
  println [any v]))))).                                                        (* prints 99 *)

(** Phase B3b: APPEND.  Go's [append] extends in place when [len < cap] (aliasing the
    backing — the [slice_append_incap_aliases] THEOREM) and REALLOCATES a fresh backing
    when [len = cap] (no aliasing).  Here [s] is full ([len = cap = 2]), so [append]
    reallocates; [s2 = [5, 0, 9]] (len 3) and the appended element [s2[2] = 9]. *)
Definition slice_append_demo : IO unit :=
  bind (slice_make_h TI64 (2:int)) (fun s =>             (* make([]int64, 2), len=cap=2 *)
  bind (slice_idx_set s (0:int) (5)%i64) (fun _ =>       (* s[0] = 5 *)
  bind (slice_append TI64 s (9)%i64) (fun s2 =>          (* s2 := append(s, 9) — reallocates, appends at index len=2 *)
  bind (slice_idx_get TI64 s2 (2:int)) (fun v =>         (* v := s2[2] = 9 (the appended element) *)
  println [any v])))).                                    (* prints 9 *)

(** Phase B3c: [make([]T, len, cap)] gives a slice SPARE capacity, so [append] is
    IN PLACE and KEEPS the backing shared — the in-place-append aliasing of B3b, shown
    at runtime.  [s] has len 1, cap 3; [append] writes index 1 in place (no realloc), so
    [s2] shares [s]'s backing — writing [s2[0]] is seen through [s[0]]. *)
Definition slice_makecap_demo : IO unit :=
  bind (slice_make_lc TI64 (1:int) (3:int)) (fun s =>    (* make([]int64, 1, 3): len=1, cap=3 *)
  bind (slice_idx_set s (0:int) (5)%i64) (fun _ =>        (* s[0] = 5 *)
  bind (slice_append TI64 s (8)%i64) (fun s2 =>           (* s2 := append(s, 8) — IN PLACE (len<cap), shares backing *)
  bind (slice_idx_set s2 (0:int) (77)%i64) (fun _ =>      (* s2[0] = 77 *)
  bind (slice_idx_get TI64 s (0:int)) (fun v =>           (* v := s[0] — sees 77 (shared backing!) *)
  println [any v]))))).                                    (* prints 77 *)

(** Phase B3c: [clear] zeros a slice's elements; [copy] copies elements src→dst. *)
Definition slice_clear_demo : IO unit :=
  bind (slice_make_h TI64 (2:int)) (fun s =>
  bind (slice_idx_set s (0:int) (5)%i64) (fun _ =>        (* s[0] = 5 *)
  bind (slice_clear_h TI64 s) (fun _ =>                   (* clear(s) → all zero *)
  bind (slice_idx_get TI64 s (0:int)) (fun v =>           (* v := s[0] = 0 *)
  println [any v])))).                                     (* prints 0 *)
Definition slice_copy_demo : IO unit :=
  bind (slice_make_h TI64 (2:int)) (fun dst =>
  bind (slice_make_h TI64 (2:int)) (fun src =>
  bind (slice_idx_set src (0:int) (7)%i64) (fun _ =>       (* src[0] = 7 *)
  bind (slice_copy TI64 dst src) (fun _n =>               (* copy(dst, src) *)
  bind (slice_idx_get TI64 dst (0:int)) (fun v =>          (* v := dst[0] = 7 *)
  println [any v]))))).                                    (* prints 7 *)

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

(** User VARIADIC function (Go [func f(xs ...int64)]): inside the func the param is a slice;
    the call SPREADS ([f(xs...)]).  [Variadic] keeps the param type distinct so it renders
    [...int64] (not [[]int64]); [vararg] is the call-site spread, [va_slice] recovers the slice. *)
Definition sum_print (xs : Variadic GoI64) : IO unit :=
  for_each (va_slice xs) (fun x => println [any x]).
Definition variadic_demo : IO unit :=
  let xs := slice_of_list TI64 [(7)%i64; (8)%i64; (9)%i64] in
  sum_print (vararg xs).   (* prints 7 / 8 / 9 *)

(** The common form: a variadic param AFTER fixed leading params — [func f(prefix string,
    xs ...int64)].  Go requires the variadic param LAST; here it follows a fixed [string]. *)
Definition log_prefixed (prefix : GoString) (xs : Variadic GoI64) : IO unit :=
  for_each (va_slice xs) (fun x => println [any prefix; any x]).
Definition variadic_mixed_demo : IO unit :=
  let xs := slice_of_list TI64 [(4)%i64; (5)%i64] in
  log_prefixed "n="%string (vararg xs).   (* prints: n= 4 / n= 5 *)

(** Passing INDIVIDUAL values (a slice literal straight to [vararg]) → the idiomatic
    multi-value call [f(v1, v2, v3)] (not the [[]T{…}...] spread used for a slice var). *)
Definition variadic_lit_demo : IO unit :=
  sum_print (vararg (slice_of_list TI64 [(1)%i64; (2)%i64; (3)%i64])).   (* Sum_print(1, 2, 3) → 1 / 2 / 3 *)

(** Indexed slice range: [for i, x := range xs] — [i] the element index, [x] the element
    (the indexed counterpart of [for_each]); lowers to the native two-variable range loop. *)
Definition foreach_idx_demo : IO unit :=
  let xs := slice_of_list TI64 [(10)%i64; (20)%i64; (30)%i64] in
  for_each_idx xs (fun i x => println [any i; any x]).   (* prints 0 10 / 1 20 / 2 30 *)

(** Integer range (Go 1.22): [for i := range n] iterates [i = 0 … n-1] (zero times when
    [n <= 0]); lowers to the native [for i := range n]. *)
Definition int_range_demo : IO unit :=
  int_range 4 (fun i => println [any i]).   (* prints 0 / 1 / 2 / 3 *)

(** Fold: sum a slice into an accumulator — lowers to an accumulator [for]
    loop ([total := 0; for _, x := range xs { total = total + x }]). *)
Definition sum_demo : IO unit :=
  let xs    := slice_of_list TI64 [(1)%i64; (2)%i64; (3)%i64; (4)%i64] in
  let total := slice_fold xs (0)%i64 (fun acc x => i64_add acc x) in
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

(** METHOD VALUE (Go's [p.M] as a first-class closure): [shifted p] is the method
    [Shifted] with its receiver [p] already bound — a [func(int64) Point] passed to a
    higher-order function.  The plugin detects the under-application (only the receiver,
    not the full args) and emits the bare [p.Shifted] (a method value), not a call.
    [call_shift10] then invokes it with [10]. *)
Definition call_shift10 (f : GoI64 -> Point) : Point := f (10)%i64.
Definition method_value_demo : IO unit :=
  let p := MkPoint (1)%i64 (2)%i64 in
  let q := call_shift10 (shifted p) in   (* call_shift10(p.Shifted) = p.Shifted(10) = (11,12) *)
  println [any (px q); any (py q)].       (* 11 12 *)

(** METHOD EXPRESSION (Go's [T.M]): the method [Sum_coords] referenced UNBOUND — a
    [func(Point) GoI64] whose first argument is the receiver.  In Coq it is the method
    used bare (no application at all); the plugin emits [Point.Sum_coords].  [apply_pt]
    applies it to [p]. *)
Definition apply_pt (f : Point -> GoI64) (p : Point) : GoI64 := f p.
Definition method_expr_demo : IO unit :=
  let p := MkPoint (5)%i64 (6)%i64 in
  println [any (apply_pt sum_coords p)].   (* Point.Sum_coords(p) = 5+6 = 11 *)

(** MULTIPLE RETURN VALUES (Go's [func f() (A, B)] + [x, y := f()]): a function returning
    a PAIR lowers to a Go multi-value return [(int64, int64)] / [return b, a]; the caller's
    destructuring [let '(x,y) := …] lowers to [x, y := Swap2(…)].  [swap2_spec] proves the
    swap. *)
Definition swap2 (a b : GoI64) : GoI64 * GoI64 := (b, a).
Lemma swap2_spec : forall a b, swap2 a b = (b, a).
Proof. reflexivity. Qed.
Definition multiret_demo : IO unit :=
  let '(x, y) := swap2 (3)%i64 (4)%i64 in   (* (4, 3) *)
  println [any x; any y].                    (* 4 3 *)

(** An IO-returning method (a method with effects) — the receiver threads through
    the [pp_io_body] path just like a pure one: [func (p Point) Describe() { … }],
    and the statement-position call [describe p] lowers to [p.Describe()]. *)
Definition describe (p : Point) : IO unit :=
  bind (println [any (px p)]) (fun _ => println [any (py p)]).

Definition io_method_demo : IO unit :=
  let p := MkPoint (8)%i64 (9)%i64 in
  describe p.   (* prints: 8 / 9 *)

(** Struct COMPARABILITY (Go spec "Comparison operators": struct values are comparable
    if all fields are; [a == b] is FIELD-WISE).  [point_eqb] is exactly that field-wise
    comparison — it lowers via the existing [&&]/[==]/projection ops (no value-position
    [if], no new lowering), so it is faithful to Go's [p == q].  [point_eqb_spec] proves
    it DECIDES Point equality (the comparability guarantee).  *(The idiomatic direct
    [p == q] is now also modeled — see [struct_eqb] / [struct_eq_native_demo] below.)* *)
Definition point_eqb (a b : Point) : bool :=
  andb (i64_eqb (px a) (px b)) (i64_eqb (py a) (py b)).
Lemma point_eqb_spec : forall a b, point_eqb a b = true <-> a = b.
Proof.
  intros [xa ya] [xb yb]. unfold point_eqb. cbn. split.
  - intro H. apply andb_prop in H. destruct H as [Hx Hy].
    apply (comparable_TI64 xa xb) in Hx. apply (comparable_TI64 ya yb) in Hy.
    subst. reflexivity.
  - intro H. injection H as -> ->.
    unfold i64_eqb. rewrite !Z.eqb_refl. reflexivity.
Qed.
Definition struct_eq_demo : IO unit :=
  let p := MkPoint (3)%i64 (4)%i64 in
  let q := MkPoint (3)%i64 (4)%i64 in
  let r := MkPoint (3)%i64 (5)%i64 in
  println [any (point_eqb p q); any (point_eqb p r)].   (* true false *)

(** NATIVE struct equality — Go's [a == b] OPERATOR (not the field-wise emulation).
    [struct_eqb] is evidence-carrying: it demands the comparability witness [point_eqb]
    (Go requires the struct be comparable to use [==]) and lowers to the bare Go [p == q].
    [struct_eqb_native_spec] proves the native form STILL decides Point equality — same
    guarantee as [point_eqb], now via the actual operator. *)
Lemma struct_eqb_native_spec : forall a b, struct_eqb point_eqb a b = true <-> a = b.
Proof. intros. unfold struct_eqb. apply point_eqb_spec. Qed.
Definition struct_eq_native_demo : IO unit :=
  let p := MkPoint (3)%i64 (4)%i64 in
  let q := MkPoint (3)%i64 (4)%i64 in
  let r := MkPoint (3)%i64 (5)%i64 in
  println [any (struct_eqb point_eqb p q); any (struct_eqb point_eqb p r)].   (* true false *)

(** NESTED struct fields (Go struct composition): a struct with a field whose type is
    another struct.  Tests that the field-type printer handles a struct-typed field and
    that chained projections lower to chained Go field access [o.W_inner.Iv]. *)
Record Inner := MkInner { iv : GoI64 ; ikind : GoI64 }.   (* 2 fields: avoid Coq's single-field unboxing *)
Record Wrap  := MkWrap { w_inner : Inner ; wz : GoI64 }.
Definition nested_struct_demo : IO unit :=
  let o := MkWrap (MkInner (5)%i64 (1)%i64) (9)%i64 in
  println [any (iv (w_inner o)); any (wz o)].   (* 5 9 (chained: o.W_inner.Iv, o.Wz) *)

(** Struct POINTER (Phase Bs.2): a heap-backed [*Cell] with mutation THROUGH the
    pointer.  [sptr_new] → [&Cell{…}]; [sptr_set_field p cx … 7] → [p.Cx = 7] (mutate);
    [sptr_get_field p cx …] → [p.Cx] (read back the new value).  The [StructRep]
    ([mkSR2 …]) is proof-only (decomposes/reconstructs the struct across field cells —
    it gives the read-after-write/aliasing THEOREMS [sptr_field_get_set]/
    [sptr_field_alias]); the lowering emits native Go pointer syntax, never the rep. *)
Record Cell := MkCell { cx : GoI64 ; cy : GoI64 }.
Lemma cell_eta : forall v, MkCell (cx v) (cy v) = v.
Proof. intros [a b]; reflexivity. Qed.
Definition sptr_demo : IO unit :=
  bind (sptr_new (mkSR2 cx cy MkCell cell_eta) (MkCell (3)%i64 (4)%i64)) (fun p =>  (* p := &Cell{3,4} *)
  bind (sptr_set_field p 0%uint63 cx TI64 (7)%i64) (fun _ =>     (* p.Cx = 7 (mutate through *p) *)
  bind (sptr_get_field p 0%uint63 cx TI64) (fun a =>            (* a := p.Cx → 7 *)
  bind (sptr_get_field p 1%uint63 cy TI64) (fun b =>            (* b := p.Cy → 4 *)
  println [any a; any b])))).                                   (* prints: 7 4 *)

(** POINTER-RECEIVER method (Phase B2): a method whose first param is [SPtr Cell] (a
    [*Cell]) and MUTATES the receiver.  The plugin detects the [SPtr (record)] first
    param → [func (p *Cell) Cell_incx() { … }] (and a call [cell_incx p] → [p.Cell_incx()]),
    exactly the value-receiver path but through a pointer.  The mutation is observed by
    the CALLER (the defining pointer-receiver behaviour), backed by [sptr_field_get_set]. *)
Definition cell_incx (p : SPtr Cell) : IO unit :=
  bind (sptr_get_field p 0%uint63 cx TI64) (fun a =>          (* read p.Cx *)
        sptr_set_field p 0%uint63 cx TI64 (i64_add a (1)%i64)).  (* p.Cx = p.Cx + 1 *)

Definition ptr_method_demo : IO unit :=
  bind (sptr_new (mkSR2 cx cy MkCell cell_eta) (MkCell (10)%i64 (20)%i64)) (fun p =>
  bind (cell_incx p) (fun _ =>                                (* p.Cell_incx() — mutates p.Cx *)
  bind (sptr_get_field p 0%uint63 cx TI64) (fun a =>          (* a := p.Cx → 11 *)
  println [any a]))).                                          (* prints: 11 *)

(** POINTER-receiver method EXPRESSION (the parenthesized-star-Cell dot Cell_incx form) — the
    pointer-receiver method referenced UNBOUND is Go's [func] taking a [*Cell] receiver.
    Passed to a HOF [apply_cell] taking that func; the plugin records the receiver type as the
    PARENTHESIZED pointer form (vs the value-receiver [Point.Sum_coords]). *)
Definition apply_cell (f : SPtr Cell -> IO unit) (p : SPtr Cell) : IO unit := f p.
Definition ptr_method_expr_demo : IO unit :=
  bind (sptr_new (mkSR2 cx cy MkCell cell_eta) (MkCell (5)%i64 (6)%i64)) (fun p =>
  bind (apply_cell cell_incx p) (fun _ =>                     (* pointer-receiver method expr via the HOF — mutates p.Cx *)
  bind (sptr_get_field p 0%uint63 cx TI64) (fun a =>          (* a := p.Cx → 6 *)
  println [any a]))).                                          (* prints: 6 *)

(** N-FIELD struct pointer: a 3-field [*Cell3] with a pointer-receiver method that mutates
    a field.  Same generic field-cell substrate as the 2-field case ([sptr3_field_get_set]
    backs the mutation); shows the pointer story is not limited to 2 fields. *)
Record Cell3 := MkCell3 { c3x : GoI64 ; c3y : GoI64 ; c3z : GoI64 }.
Lemma cell3_eta : forall v, MkCell3 (c3x v) (c3y v) (c3z v) = v.
Proof. intros [a b c]; reflexivity. Qed.
Definition cell3_inc_z (p : SPtr3 Cell3) : IO unit :=
  bind (sptr3_get_field p 2%uint63 c3z TI64) (fun z =>          (* read p.C3z *)
        sptr3_set_field p 2%uint63 c3z TI64 (i64_add z (1)%i64)).  (* p.C3z = p.C3z + 1 *)
Definition nfield_ptr_demo : IO unit :=
  bind (sptr3_new (mkSR3 c3x c3y c3z MkCell3 cell3_eta) (MkCell3 (10)%i64 (20)%i64 (30)%i64)) (fun p =>
  bind (cell3_inc_z p) (fun _ =>                                (* p.Cell3_inc_z() — mutates p.C3z *)
  bind (sptr3_get_field p 2%uint63 c3z TI64) (fun z =>          (* z := p.C3z → 31 *)
  println [any z]))).                                           (* prints: 31 *)

(** HETEROGENEOUS struct pointer: a [*Pair] whose two fields have DIFFERENT types
    ([N int64], [B bool]) — the common real-Go case.  Same generic field-cell substrate
    ([sptrh_field_get_set] backs the mutation); the rep just carries the per-field types
    and tags.  The pointer-receiver method bumps the int64 field, leaving the bool. *)
Record Pair := MkPair { p_n : GoI64 ; p_b : bool }.
Lemma pair_eta : forall v, MkPair (p_n v) (p_b v) = v.
Proof. intros [a b]; reflexivity. Qed.
Definition pair_bump (p : SPtrH Pair GoI64 bool) : IO unit :=
  bind (sptrh_get_field p 0%uint63 p_n TI64) (fun n =>          (* read p.P_n *)
        sptrh_set_field p 0%uint63 p_n TI64 (i64_add n (1)%i64)).  (* p.P_n = p.P_n + 1 *)
Definition het_ptr_demo : IO unit :=
  bind (sptrh_new (mkSR2H p_n p_b TI64 TBool MkPair pair_eta) (MkPair (10)%i64 true)) (fun p =>
  bind (pair_bump p) (fun _ =>                                  (* p.Pair_bump() — mutates p.P_n *)
  bind (sptrh_get_field p 0%uint63 p_n TI64) (fun n =>          (* n := p.P_n → 11 *)
  bind (sptrh_get_field p 1%uint63 p_b TBool) (fun b =>         (* b := p.P_b → true *)
  println [any n; any b])))).                                  (* prints: 11 true *)

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

(** SINGLE-METHOD interface (Go's [interface { Greet(int64) int64 }]).  A 1-method
    dictionary record would be UNBOXED by Coq ([{m} ≡ m]), erasing the struct; we keep it
    a real dictionary by carrying the underlying value as an explicit SECOND field
    [gr_self : GoAny].  This both sidesteps the unboxing AND is more faithful — a Go
    interface value IS a (method-table, value) pair.  [mk_adder base] builds a [Greeter]
    whose method adds [base] (and stashes [base] as the hidden value); dispatch
    [greet g x] → [g.Greet(x)], never seeing the concrete carrier. *)
Record Greeter := MkGreeter { greet : GoI64 -> GoI64 ; gr_self : GoAny }.
Definition mk_adder (base : GoI64) : Greeter :=
  MkGreeter (fun x => i64_add base x) (any base).
Example dispatch_greet : forall base x, greet (mk_adder base) x = i64_add base x.
Proof. reflexivity. Qed.
Definition single_iface_demo : IO unit :=
  println [any (greet (mk_adder (5)%i64) (10)%i64)].   (* 5 + 10 = 15 *)

(** NULLARY method (Go's [interface { String() string }] — no args beyond the receiver).
    In the dictionary model the method is a [unit -> R] thunk (the unit triggers it, the
    value is captured); it should lower to an idiomatic Go [func() string] with the call
    [d.Sg_str()] — i.e. the [unit] param/arg erased. *)
Record Stringer := MkStringer { sg_str : unit -> GoString ; sg_self : GoAny }.
Definition mk_namer (nm : GoString) : Stringer :=
  MkStringer (fun _ => nm) (any nm).
Example dispatch_str : forall nm, sg_str (mk_namer nm) tt = nm.
Proof. reflexivity. Qed.
Definition nullary_iface_demo : IO unit :=
  println [any (sg_str (mk_namer "fido"%string) tt)].   (* "fido" *)

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

(** A DEFINED TYPE over a primitive (Go [type MyI64 int64]) with a method.  The
    [GoTypeTag] phantom field stops Coq unboxing the single value field, keeping
    [MyI64] a distinct method-receiver type (the same trick as the variadic wrapper). *)
Record MyI64 := MkMyI64 { my_val : GoI64 ; my_tag : GoTypeTag GoI64 }.
Definition mk_myi64 (v : GoI64) : MyI64 := MkMyI64 v TI64.
Definition myi64_double (m : MyI64) : MyI64 := mk_myi64 (i64_add (my_val m) (my_val m)).
Definition deftype_demo : IO unit :=
  println [any (my_val (myi64_double (mk_myi64 (21)%i64)))].   (* 42 *)

(** The defined-type underlying is GENERIC (computed via [pp_type] of the value field),
    so a defined type over a STRING works the same: [type Greeting string], ctor cast
    [Greeting(s)], projection cast [string(x)].  [greeting_with] is a value-receiver
    method whose body concatenates ([str_concat] → Go [+]). *)
Record Greeting := MkGreeting { gr_text : GoString ; gr_tag : GoTypeTag GoString }.
Definition mk_greeting (s : GoString) : Greeting := MkGreeting s TString.
Definition greeting_with (g : Greeting) (who : GoString) : GoString :=
  str_concat (gr_text g) who.
Definition deftype_str_demo : IO unit :=
  println [any (greeting_with (mk_greeting "Hi, "%string) "fido"%string)].   (* "Hi, fido" *)

(** A DEFINED TYPE satisfying an INTERFACE — behavioral satisfaction for a defined type
    (the closed-world wishlist's gateway, now reachable here).  [type Celsius int64] carries
    a value-receiver method [reading]; [celsius_measurable] wires that method into a
    [Measurable] dictionary, so the defined type's method IS what satisfies the contract.
    Dispatch [measure d tt] → [d.Measure()] runs the captured [c.Reading()]. *)
Record Celsius := MkCelsius { c_val : GoI64 ; c_tag : GoTypeTag GoI64 }.
Definition mk_celsius (v : GoI64) : Celsius := MkCelsius v TI64.
Definition reading (c : Celsius) : GoI64 := i64_add (c_val c) (100)%i64.   (* a real method, +100 offset *)

Record Measurable := MkMeasurable { measure : unit -> GoI64 ; meas_self : GoAny }.
Definition celsius_measurable (c : Celsius) : Measurable :=
  MkMeasurable (fun _ => reading c) (any (c_val c)).   (* self stashes the underlying repr *)
Definition deftype_iface_demo : IO unit :=
  println [any (measure (celsius_measurable (mk_celsius (20)%i64)) tt)].   (* 120 *)

(** A NAMED FUNCTION TYPE (Go's [type Handler func(int64) int64] — the [http.HandlerFunc]
    idiom): a defined type whose UNDERLYING is a func.  The [GoTypeTag] phantom needs an
    arrow tag ([TArrow]), and the underlying renders via [pp_type] of the arrow → the
    func type.  A value-receiver method [handler_run] CALLS the wrapped func: projecting it
    is the cast [(func(int64) int64)(h)], and applying an arg calls THROUGH that cast —
    [(func(int64) int64)(h)(x)].  [hinc] is a plain function (its first param is not a
    record, so it stays a function, not a method) wrapped by [mk_handler]. *)
Record Handler := MkHandler { h_fn : GoI64 -> GoI64 ; h_tag : GoTypeTag (GoI64 -> GoI64) }.
Definition mk_handler (f : GoI64 -> GoI64) : Handler := MkHandler f (TArrow TI64 TI64).
Definition handler_run (h : Handler) (x : GoI64) : GoI64 := h_fn h x.
Definition hinc (n : GoI64) : GoI64 := i64_add n (1)%i64.
(* dispatch is provable: the wrapped func IS what [handler_run] calls *)
Example handler_run_spec : forall f x, handler_run (mk_handler f) x = f x.
Proof. reflexivity. Qed.
Definition named_func_demo : IO unit :=
  println [any (handler_run (mk_handler hinc) (41)%i64)].   (* 42 *)

(** A DEFINED TYPE over a SLICE underlying (Go's [type IntList []int64] — the
    [sort.Interface] [type ByLen []T] idiom).  No new plugin work: the underlying
    [GoTypeTag] is the existing [TSlice], and a slice conversion [[]int64(l)] is valid Go
    WITHOUT parens (only [*]/[<-]/[func] types need them — cf. the canonical [[]byte(s)]),
    so the projection cast emits fine and there is no call-through.  [il_len] is a
    value-receiver method projecting the slice and taking its [len]. *)
Record IntList := MkIntList { il_val : GoSlice GoI64 ; il_tag : GoTypeTag (GoSlice GoI64) }.
Definition mk_intlist (s : GoSlice GoI64) : IntList := MkIntList s (TSlice TI64).
Definition il_len (l : IntList) : GoInt := len (il_val l).
Definition deftype_slice_demo : IO unit :=
  println [any (il_len (mk_intlist (slice_make TI64 3)))].   (* 3 *)

(** STRUCT EMBEDDING (Go's [type Dog struct { Animal; Breed string }]) — composition with
    field/method PROMOTION.  Modeled as a record field whose name EQUALS its (record) type's
    name ([animal : Animal]); the plugin emits it as an ANONYMOUS embedded field, so the Go
    struct genuinely embeds [Animal] and Go promotes its method set.  [Animal] needs >= 2
    fields (a 1-field record is unboxed by Coq).  Accessing the embedded type's field/method
    is through the embedded field — [species (animal d)] → [(d.Animal).Species], and the
    promoted method [speak (animal d)] → [(d.Animal).Speak()] — both valid, faithful Go. *)
Record Animal := MkAnimal { species : GoString ; legs : GoI64 }.
Definition speak (a : Animal) : GoString := species a.   (* a value-receiver method on Animal *)
Record Dog := MkDog { animal : Animal ; breed : GoString }.   (* field name = type name → embedded *)
Definition mk_dog (sp br : GoString) : Dog := MkDog (MkAnimal sp (4)%i64) br.
(* the embedded type's method is reachable on the composite (its method set is promoted) *)
Example embed_speak : forall sp br, speak (animal (mk_dog sp br)) = sp.
Proof. reflexivity. Qed.
Definition embed_demo : IO unit :=
  bind (println [any (species (animal (mk_dog "canine"%string "lab"%string)))])  (fun _ =>   (* canine *)
  println [any (speak (animal (mk_dog "canine"%string "lab"%string)))]).                   (* canine *)

(** GO GENERICS (type parameters, Go 1.18+).  Rocq's parametric polymorphism maps directly
    to a Go generic: a function's type VARIABLES become a [func F[T1 any, …]] type-parameter
    list (constraint [any] — parametric polymorphism imposes no operations on the type), and
    call sites rely on Go's type inference (no explicit type args).  [gid] is the identity;
    [glen] is generic OVER A SLICE (the canonical use — Go's [len] works for any [[]T]),
    instantiated at BOTH [[]int64] and [[]string] (one generic reused at two types); [gfirst]
    shows TWO type parameters.  Dispatch is provable in Rocq directly (parametricity). *)
Definition gid {A : Type} (x : A) : A := x.
Definition glen {A : Type} (xs : GoSlice A) : GoInt := len xs.
Definition gfirst {A B : Type} (x : A) (y : B) : A := x.
Example gid_spec    : forall A (x : A), gid x = x.            Proof. reflexivity. Qed.
Example gfirst_spec : forall A B (x : A) (y : B), gfirst x y = x. Proof. reflexivity. Qed.
(* Faithful instantiation: string literals / typed slices pin the Go type arg.  (A BARE
   untyped-int literal like [gid 7] would have Go infer [int], not our [int64] model — the
   untyped-constant gap (Tier 2 #6); typed operands avoid it.) *)
Definition generics_demo : IO unit :=
  bind (println [any (gid "go"%string)])             (fun _ =>   (* gid @ string → go *)
  bind (println [any (glen (slice_make TI64 3))])    (fun _ =>   (* glen @ []int64 → 3 *)
  bind (println [any (glen (slice_make TString 2))]) (fun _ =>   (* glen @ []string → 2 (same generic) *)
  println [any (gfirst "first"%string true)]))).                 (* gfirst @ (string,bool) → first *)

(** GENERIC STRUCTS / TYPES (Go's [type Box[T any] struct {…}]).  A PARAMETERIZED Rocq
    [Record] maps to a Go generic struct: the type variables in the field types become the
    struct's type-parameter list, and — because Go does NOT infer type args for a composite
    literal — the constructor emits them explicitly ([Box[T1]{…}] inside a generic function,
    [Box[int64]{…}] at a concrete use), taken from the constructed type.  A method's receiver
    carries the params ([func (b Box[T1]) Box_get() T1]); call sites infer.  [Box] needs >= 2
    fields ([btag]) — a 1-field record is unboxed.  One [Box] is reused at [string] AND [bool]. *)
Record Box (A : Type) := MkBox { bval : A ; btag : GoI64 }.
Arguments MkBox {A}. Arguments bval {A}. Arguments btag {A}.
Definition make_box {A : Type} (v : A) : Box A := MkBox v (1)%i64.   (* generic ctor function *)
Definition box_get {A : Type} (b : Box A) : A := bval b.             (* generic-receiver method *)
Definition box_tag {A : Type} (b : Box A) : GoI64 := btag b.         (* reads the non-generic field *)
Example box_get_spec : forall A (v : A), box_get (make_box v) = v. Proof. reflexivity. Qed.
Definition gstruct_demo : IO unit :=
  bind (println [any (box_get (make_box "hi"%string))])  (fun _ =>   (* Box[string] → hi *)
  bind (println [any (box_get (make_box true))])         (fun _ =>   (* Box[bool] → true (same generic) *)
  println [any (box_tag (make_box "x"%string))])).                   (* non-generic field → 1 *)

(** A DEFINED TYPE over a MAP underlying (Go's [type Counts map[string]int64]) — completing
    the composite-underlying axis (primitive/string/func/slice/MAP).  [GoMap] is already
    recognised by name in [pp_type] (unlike [GoSlice]), so no plugin change: the underlying
    renders [map[string]int64], the ctor is the cast [Counts(m)], and the projection cast
    [map[string]int64(c)] (valid Go without parens, like a slice).  [co_size] is an IO-VALUE-
    returning METHOD ([func (c Counts) Co_size() int]); it lowers now that pp_io_body [return]s
    a value-returning IO tail (here the single read [map_len (co_val c)] → [return len(…)]). *)
Record Counts := MkCounts { co_val : GoMap GoString GoI64 ; co_tag : GoTypeTag (GoMap GoString GoI64) }.
Definition mk_counts (m : GoMap GoString GoI64) : Counts := MkCounts m (TMap TString TI64).
Definition co_size (c : Counts) : IO GoInt := map_len (co_val c).   (* IO-value method, single tail → return len(…) *)
(* IO-value method whose tail is a BIND-CHAIN ending in [ret] — exercises the smarter ret case *)
Definition co_sum (c : Counts) : IO GoI64 :=
  bind (map_get_or TString TI64 "a"%string (0)%i64 (co_val c)) (fun a =>
  bind (map_get_or TString TI64 "b"%string (0)%i64 (co_val c)) (fun b =>
  ret (i64_add a b))).
Definition gmap_deftype_demo : IO unit :=
  bind (map_make_typed TString TI64)              (fun m =>
  bind (map_set TString TI64 "a"%string (1)%i64 m) (fun _ =>
  bind (map_set TString TI64 "b"%string (2)%i64 m) (fun _ =>
  bind (co_size (mk_counts m))                    (fun n =>   (* method call → (Mk_counts(m)).Co_size() *)
  bind (println [any n])                          (fun _ =>   (* 2 (size) *)
  bind (co_sum (mk_counts m))                     (fun s =>   (* bind-chain IO-value method *)
  println [any s])))))).   (* 3 (a+b) *)

(** USER RECURSION (a Coq [Fixpoint] → a self-calling Go func).  Structural recursion needs a
    [nat] match ([O] / [S k]) — modeled in STATEMENT position as [if n == 0 { … } else { k :=
    n - 1; … }] (mirroring the list nil/cons case), so the [O] base case and [S k] recursive
    step lower, and the self-call [countdown k …] emits as [Countdown(k, …)].  [n : nat] is the
    decreasing fuel (→ Go [uint]); a [GoI64] accumulator [v] carries the printed value. *)
Fixpoint countdown (n : nat) (v : GoI64) {struct n} : IO unit :=
  match n with
  | O => ret tt
  | S k => bind (println [any v]) (fun _ => countdown k (i64_sub v (1)%i64))
  end.
Definition recursion_demo : IO unit := countdown 3 (3)%i64.   (* 3 / 2 / 1 *)

(** PURE (value-returning) recursion — the nat match in VALUE/tail position.  [pow2] returns
    a [GoI64], so its body's nat match lowers through [pp_pure_tail] (now nat-aware): each arm
    [return]s, and the recursive call [pow2 k] is the self-call [Pow2(k)] in an expression. *)
Fixpoint pow2 (n : nat) : GoI64 :=
  match n with
  | O => (1)%i64
  | S k => i64_mul (2)%i64 (pow2 k)
  end.
Definition pure_rec_demo : IO unit := println [any (pow2 4)].   (* 2^4 = 16 *)

(** MUTUAL RECURSION — two `Fixpoint`s calling each other (a mutual `Dfix`).  No plugin work:
    the `Dfix` arm already emits each function via `pp_function`, and a cross-call is an
    ordinary call; with value-position nat matches now lowering, the bodies emit too. *)
Fixpoint is_even (n : nat) : bool := match n with O => true  | S k => is_odd  k end
with     is_odd  (n : nat) : bool := match n with O => false | S k => is_even k end.
Definition mutual_rec_demo : IO unit :=
  bind (println [any (is_even 4)]) (fun _ => println [any (is_odd 4)]).   (* true / false *)

(** CUSTOM ENUM (a nullary-constructor `Inductive`) → Go's iota-enum idiom: `type Direction
    int` + a `const ( North Direction = iota; … )` block, each constructor a const, and an
    N-arm match → a real Go `switch` (the first `switch` emission).  `bool` is excluded (a
    builtin); nat/list/option are excluded automatically (non-nullary constructors). *)
Inductive Direction := North | South | East | West.
Definition dir_io (d : Direction) : IO unit :=
  match d with
  | North => println [any (0)%i64]
  | South => println [any (1)%i64]
  | East  => println [any (2)%i64]
  | West  => println [any (3)%i64]
  end.
Definition enum_demo : IO unit := dir_io East.   (* switch picks the East case → 2 *)

(* VALUE-position enum match — the [func (d Direction) String() string] idiom: a switch each
   arm of which RETURNs (pp_pure_tail enum arm).  [NoInline] keeps the match in tail position. *)
Definition dir_name (d : Direction) : GoString :=
  match d with
  | North => "N"%string | South => "S"%string | East => "E"%string | West => "W"%string
  end.
Definition enum_value_demo : IO unit := println [any (dir_name West)].   (* W *)

(* ENUM match with a `_` WILDCARD arm: Coq EXPANDS the `_` into the missing constructors
   (South/East/West all get the `0` body), so it lowers to the all-cases switch with no
   plugin change — the wildcard never reaches the plugin as a [Pwild] for a finite enum. *)
Definition dir_sign (d : Direction) : IO unit :=
  match d with
  | North => println [any (1)%i64]
  | _     => println [any (0)%i64]
  end.
Definition enum_default_demo : IO unit :=
  bind (dir_sign North) (fun _ => dir_sign South).   (* 1 (North) / 0 (the expanded South) *)

(** Sequenced with the [>>'] notation ([m >>' k := bind m (fun _ => k)]) — each
    demo's [unit] result is discarded, so this is a flat sequence, not a 45-deep
    nest of [bind … (fun _ => …)] closed by a wall of parens.  ([>>'] is
    left-associative; monad associativity makes the grouping irrelevant, and the
    plugin flattens it to the same straight-line Go.) *)
Definition main_effect : IO unit :=
  println [any (i64_add (1)%i64 (2)%i64)]       >>'   (* prints: 3 *)
  panic_and_recover (i64_add (40)%i64 (2)%i64)  >>'   (* prints: 42 43 *)
  div_demo                      >>'   (* prints: 3 2 *)
  overflow_safe_demo            >>'   (* prints: 3000000000000 1000000 *)
  i64_abs_demo                  >>'   (* prints: 7 7 -9223372036854775808 *)
  neg_op_demo                   >>'   (* prints: -5 7 (unary -x) *)
  conv64_demo                   >>'   (* prints: 18446744073709551615 -1 255 *)
  minmax64_demo                 >>'   (* prints: -2 1 18446744073709551615 *)
  cmp_ops_demo                  >>'   (* prints: true true true true *)
  float_demo                    >>'   (* prints: 3.75 / 0.25 (sci) *)
  float_cmp_demo                >>'   (* prints: true / true / true / false *)
  float_nan_demo 0              >>'   (* prints: false / false (NaN unordered) *)
  float_opp_demo                >>'   (* prints: -1.5 / 2.0 *)
  float_opp_sign_demo 0         >>'   (* prints: true (opp made -0 at runtime) *)
  fminmax_demo                  >>'   (* prints: min/max of 3.0 5.0 *)
  f64_of_int_demo               >>'   (* prints: +5.000000e+000 -3.000000e+000 (float64(i)) *)
  f64_of_i64_demo               >>'   (* prints: +7.000000e+000 -3.000000e+000 (float64(i64)) *)
  fcmp_demo                     >>'   (* prints: true true true *)
  u8_demo                       >>'   (* prints: 44 / 1 / 255 / true *)
  fw_cmp_demo                   >>'   (* prints: true true true (narrow >/>=/!=) *)
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
  const_demo                    >>'   (* prints: 1000000000000 4611686018427387904 (untyped const arithmetic) *)
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
  arr_demo                      >>'   (* prints: 20 true / 0 false ([3]int64 array index) *)
  arr_eq_demo                   >>'   (* prints: true false (array == is field-wise) *)
  arr_copy_demo                 >>'   (* prints: 10 99 (value-copy: a unchanged by arr_set) *)
  assert_safe_demo (7)%i64    >>'   (* prints: 7 true / false false *)
  string_demo                   >>'   (* prints: 2 / 71 true / 0 false / Go! *)
  str_cmp_demo                  >>'   (* prints: true false true false *)
  str_slice_demo                >>'   (* prints: world (s[a:b] string slice) *)
  bytes_demo                    >>'   (* prints: Hi ([]byte / string round-trip) *)
  rune_demo                     >>'   (* prints: Go ([]rune / string round-trip, UTF-8) *)
  rune_to_str_demo              >>'   (* prints: A (string(rune(65))) *)
  str_range_demo                >>'   (* prints: 0 72 / 1 8364 / 4 33 (for i, r := range s) *)
  tsw_demo (any true)           >>'   (* prints: true 1 (bool case) *)
  tsw_demo (any "go"%string)    >>'   (* prints: go 2 (string case) *)
  tsw_demo (any (5)%i64)        >>'   (* prints: 9 (default; int64 matches neither) *)
  tsw3_demo (any true)              >>'   (* prints: true 1 (bool case, 3-case switch) *)
  tsw3_demo (any "hi"%string)       >>'   (* prints: hi 2 (string case) *)
  tsw3_demo (any (i64_abs (5)%i64)) >>'   (* prints: 5 3 (int64 case; typed via func return) *)
  tsw_or_demo (any true)            >>'   (* prints: 1 (bool matches case bool, string) *)
  tsw_or_demo (any "x"%string)      >>'   (* prints: 1 (string also matches the multi-type case) *)
  tsw_or_demo (any (5)%i64)         >>'   (* prints: 0 (default; neither bool nor string) *)
  tsw_or3_demo (any true)           >>'   (* prints: 1 (bool matches case bool, string, int64) *)
  tsw_or3_demo (any "z"%string)     >>'   (* prints: 1 (string also matches) *)
  tsw_or3_demo (any (5)%i64)        >>'   (* prints: 0 (default; int literal boxes as int) *)
  int_sw_demo (1)%i64               >>'   (* prints: 10 (case 1, native expression switch) *)
  int_sw_demo (2)%i64               >>'   (* prints: 20 (case 2) *)
  int_sw_demo (5)%i64               >>'   (* prints: 99 (default) *)
  int_sw3_demo (3)%i64              >>'   (* prints: 30 (case 3, 3-case expression switch) *)
  int_sw3_demo (8)%i64              >>'   (* prints: 99 (default) *)
  str_sw_demo "a"%string            >>'   (* prints: 1 (case "a", string expression switch) *)
  str_sw_demo "b"%string            >>'   (* prints: 2 (case "b") *)
  str_sw_demo "z"%string            >>'   (* prints: 9 (default) *)
  str_sw3_demo "c"%string           >>'   (* prints: 3 (case "c", 3-case string switch) *)
  str_sw3_demo "z"%string           >>'   (* prints: 9 (default) *)
  complex_demo                      >>'   (* prints: the two components of complex(1.5, 2.5) *)
  complex_arith_demo                >>'   (* prints: 4 6 -2 -2 components of the sum/difference *)
  complex_mul_demo                  >>'   (* prints: -5 10 (complex multiply) *)
  complex_div_demo                  >>'   (* prints: 0.44 0.08 (complex divide, Smith's) *)
  complex_neg_demo                  >>'   (* prints: -3 -4 (complex unary negation) *)
  complex_cmp_demo                  >>'   (* prints: true false true (complex ==/!=) *)
  scmp_demo                     >>'   (* prints: true true true *)
  foreach_demo                  >>'   (* prints: 10 / 20 / 30 *)
  variadic_demo                 >>'   (* prints: 7 / 8 / 9 (variadic func f(xs ...int64)) *)
  variadic_mixed_demo           >>'   (* prints: n= 4 / n= 5 (fixed param + variadic) *)
  variadic_lit_demo             >>'   (* prints: 1 / 2 / 3 (multi-value call f(1,2,3)) *)
  foreach_idx_demo              >>'   (* prints: 0 10 / 1 20 / 2 30 (for i, x := range xs) *)
  int_range_demo                >>'   (* prints: 0 / 1 / 2 / 3 (for i := range n) *)
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
  ptr_demo                      >>'   (* prints: 10 / 99 (pointer deref read/write) *)
  new_demo                      >>'   (* prints: 0 (new(int64) → zero) *)
  ptr_safe_demo                 >>'   (* prints: 42 true / 0 false (nil-checked deref) *)
  slice_alias_demo              >>'   (* prints: 99 (sub-slice write seen through parent) *)
  slice_append_demo             >>'   (* prints: 9 (append reallocates a full slice) *)
  slice_makecap_demo            >>'   (* prints: 77 (make-with-cap: in-place append shares backing) *)
  slice_clear_demo              >>'   (* prints: 0 (clear zeros the slice) *)
  slice_copy_demo               >>'   (* prints: 7 (copy src→dst) *)
  count_demo                    >>'   (* prints: 0 / 1 / 2 *)
  defer_demo                    >>'   (* prints: 3 / 2 / 1 *)
  defer_loop_demo               >>'   (* prints: 2 / 1 / 0 *)
  point_demo                    >>'   (* prints: 3 / 4 / 7 *)
  labeled_demo                  >>'   (* prints: true / 5 *)
  method_demo                   >>'   (* prints: 7 / 13 / 14 / 27 *)
  method_value_demo             >>'   (* prints: 11 12 (method value p.Shifted passed to a HOF) *)
  method_expr_demo              >>'   (* prints: 11 (method expression Point.Sum_coords applied to p) *)
  multiret_demo                 >>'   (* prints: 4 3 (multiple return values + destructure) *)
  io_method_demo                >>'   (* prints: 8 / 9 *)
  struct_eq_demo                >>'   (* prints: true false (struct ==, field-wise) *)
  struct_eq_native_demo         >>'   (* prints: true false (native p == q operator) *)
  nested_struct_demo            >>'   (* prints: 5 9 (nested struct fields) *)
  sptr_demo                     >>'   (* prints: 7 4 (mutable *Cell through a pointer) *)
  ptr_method_demo               >>'   (* prints: 11 (pointer-receiver method mutates *Cell) *)
  ptr_method_expr_demo          >>'   (* prints: 6 (pointer-receiver method expression) *)
  nfield_ptr_demo               >>'   (* prints: 31 (pointer-receiver method mutates 3-field *Cell3) *)
  het_ptr_demo                  >>'   (* prints: 11 true (pointer method mutates heterogeneous *Pair) *)
  iface_demo                    >>'   (* prints: 14 / 1007 / 20 / 1010 *)
  single_iface_demo             >>'   (* prints: 15 (single-method interface dispatch) *)
  nullary_iface_demo            >>'   (* prints: fido (nullary method String()) *)
  typestate_demo                >>'   (* prints: 1 / 7 *)
  repinv_demo                   >>'   (* prints: 3 / 7 *)
  deftype_demo                  >>'   (* prints: 42 (defined type with method) *)
  deftype_str_demo              >>'   (* prints: Hi, fido (defined type over string) *)
  deftype_iface_demo            >>'   (* prints: 120 (defined type satisfies an interface) *)
  named_func_demo               >>'   (* prints: 42 (named func type, type Handler func(int64) int64) *)
  deftype_slice_demo            >>'   (* prints: 3 (defined type over a slice, type IntList []int64) *)
  embed_demo                    >>'   (* prints: canine / canine (struct embedding + promotion) *)
  generics_demo                 >>'   (* prints: go / 3 / 2 / first (Go generics, type params) *)
  gstruct_demo                  >>'   (* prints: hi / true / 1 (generic struct Box[T]) *)
  gmap_deftype_demo             >>'   (* prints: 2 (defined type over a map, type Counts map[string]int64) *)
  recursion_demo                >>'   (* prints: 3 / 2 / 1 (user recursion, self-calling func) *)
  pure_rec_demo                 >>'   (* prints: 16 (pure value-returning recursion, pow2 4) *)
  mutual_rec_demo               >>'   (* prints: true / false (mutual recursion is_even/is_odd) *)
  enum_demo                     >>'   (* prints: 2 (custom enum + switch, dir_io East) *)
  enum_value_demo               >>'   (* prints: W (value-position enum switch, dir_name West) *)
  enum_default_demo             >>'   (* prints: 1 / 0 (enum switch with a default arm) *)
  ret tt.

(** The IO ops are now DEFINITIONS (zero-axioms refactor); [Extraction NoInline]
    stops Coq from inlining their proof-only world-threading bodies, so the plugin
    still lowers each BY NAME to its Go primitive (and the abstract state — [ref_sel],
    [chan_buf], … — never reaches the emitted Go).  See ZERO_AXIOMS_PLAN.md. *)
Extraction NoInline
  call_shift10 apply_pt apply_cell swap2 sum_print log_prefixed vararg
  ret bind panic catch run_io
  ref_get ref_set ref_new
  ptr_get ptr_set ptr_new ptr_nil ptr_get_ok go_new
  sptr_new sptr_deref sptr_assign sptr_get_field sptr_set_field cell_incx
  sptr3_new sptr3_get_field sptr3_set_field cell3_inc_z
  sptrh_new sptrh_get_field sptrh_set_field pair_bump
  slice_make_h slice_make_lc slice_idx_get slice_idx_set subslice slice_append
  slice_clear_h slice_copy
  make_chan make_chan_buf send recv close_chan recv_ok select_recv2 select_recv_default go_spawn
  map_empty map_make map_make_typed
  map_get_opt map_len map_get_or map_set map_delete map_clear
  print println defer_call append slice_of_list run_blocks str_range for_each_idx int_range
  len cap slice_get slice_at_ok str_at_ok str_slice str_eqb str_ltb str_to_bytes str_from_bytes str_to_runes runes_to_str rune_to_str
  type_assert type_assert_safe type_switch2 type_switch3 type_switch_or2 type_switch_or3 struct_eqb int_switch2 int_switch3 str_switch2 str_switch3
  go_complex go_real go_imag complex_add complex_sub complex_mul complex_div complex_neg complex_eqb complex_neqb
  arr_lit arr_get_ok arr_eqb arr_set
  str_gtb str_geb str_neqb f64_gtb f64_geb f64_neqb
  i64_lit i64_add i64_sub i64_mul i64_add_nz i64_sub_nz i64_mul_nz i64_eqb i64_ltb i64_leb
  i64_abs i64_neg u64_neg u64_of_i64 i64_of_u64 i64_min i64_max u64_min u64_max f64_min f64_max f64_of_int f64_of_i64
  dir_name
  i64_gtb i64_geb i64_neqb u64_gtb u64_geb u64_neqb
  u8_gtb u8_geb u8_neqb i8_gtb i8_geb i8_neqb
  u16_gtb u16_geb u16_neqb i16_gtb i16_geb i16_neqb
  u32_gtb u32_geb u32_neqb i32_gtb i32_geb i32_neqb
  i64_div i64_mod i64_and i64_or i64_xor i64_andnot i64_not i64_shl i64_shr
  u64_lit u64_add u64_sub u64_mul u64_eqb u64_ltb u64_leb
  u64_div u64_mod u64_and u64_or u64_xor u64_andnot u64_not u64_shl u64_shr
  sret sbind ssend srecv slift run_session.

Go Main Extraction main "main_effect".
