(** Fido entry point.  (Sibling proof theory [concurrency.v] ties happens-before
    to actual execution traces — [hbt_irrefl], and [reachable_wf]/[reachable_hb_strict]
    which earn it from a concurrent operational semantics; it emits no Go.) *)

From Fido Require Import preamble.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.String.   (* string-literal scope for the String-types demo *)
From Stdlib Require Import StrictProp.        (* [squash]: seal the [ComparableW] decidability evidence *)
Require Import Coq.Lists.List.
Import ListNotations.

(* Float literals parse in [go64_scope] (decimal → the binary64 [spec_float]); integer literals are
   type-directed (nat field indices / GoInt via [int_lit] / [%i64] / [%u64]).  No int63 scope — the
   [PrimInt63]/[Sint63]/[PrimFloat] substrate is gone (review #6 #13→zero-axioms). *)
Open Scope go64_scope.

(** [add]/[sub] on the platform [GoInt] (Go's [int]) — index/value arithmetic (loop
    counters, computed slice indices like [sub 0 1]).  [GoInt] is now the FAITHFUL
    [Z]-carried record (review #6 #13), so these wrap at the true [2^63] (via [int_add]/
    [int_sub]) — no longer the bounded [Sint63] carrier.  Full-width int64 VALUE arithmetic
    has its own [GoI64] versions below. *)
Definition add (n m : GoInt) : GoInt := int_add n m.
Definition sub (n m : GoInt) : GoInt := int_sub n m.

(** WHY the plugin REJECTS [Nat.sub] (Coq nat → Go uint): nat subtraction is
    TRUNCATED monus, so [3 - 5 = 0] — lowering it to Go uint's WRAPPING [-]
    ([3 - 5 = 2^64-2]) would be silently wrong.  Machine-checked, so the rejection
    rests on a fact, not a hunch. *)
Example nat_sub_is_truncated : Nat.sub 3 5 = 0%nat.
Proof. reflexivity. Qed.

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
  intros [a] [b]. unfold in_i64, i64_sub, i64wrap, wrap64. cbn. intros H.
  apply andb_prop in H. destruct H as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  rewrite Z.mod_small by lia. lia.
Qed.
Theorem i64_mul_no_overflow_exact : forall a b : GoI64,
  in_i64 (i64raw a * i64raw b)%Z = true -> i64raw (i64_mul a b) = (i64raw a * i64raw b)%Z.
Proof.
  intros [a] [b]. unfold in_i64, i64_mul, i64wrap, wrap64. cbn. intros H.
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
Example i64_abs_pos    : i64_abs (7)%i64 = (7)%i64.   Proof. reflexivity. Qed.
Example i64_abs_neg    : i64_abs (-7)%i64 = (7)%i64.  Proof. reflexivity. Qed.
Example i64_abs_minint :
  i64_abs (-9223372036854775808)%i64 = (-9223372036854775808)%i64.
Proof. reflexivity. Qed.

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
    ruled out the panic.  Underneath they are [int_div]/[int_mod] on the [Z]-carried
    [GoInt] ([Z.quot]/[Z.rem], truncating toward zero exactly like Go's int64, wrapping
    at the true [2^63] — review #6 #13).  (Raw division remains the escape hatch — Go
    panics on a zero divisor.) *)
Definition div_nz (n d : GoInt) (pf : Z.eqb (intraw d) 0%Z = false) : GoInt := int_div n d pf.
Definition mod_nz (n d : GoInt) (pf : Z.eqb (intraw d) 0%Z = false) : GoInt := int_mod n d pf.

(** ===== Go spec conformance: "Integer operators" (go.dev/ref/spec#Integer_operators)
    plus "Integer overflow" (#Integer_overflow) — the SOURCE of div_nz/mod_nz's
    behavior. =====

    Spec: "the integer quotient q = x / y and remainder r = x % y satisfy
    x = q*y + r  and  |r| < |y|, with x / y truncated towards zero".  The spec's
    own example table is reproduced below and machine-checked against our model
    (so this is conformance, not assertion). *)
Example spec_div_5_3    : intraw (div_nz (int_lit 5 eq_refl) (int_lit 3 eq_refl) eq_refl)            = 1%Z.    Proof. now vm_compute. Qed.
Example spec_mod_5_3    : intraw (mod_nz (int_lit 5 eq_refl) (int_lit 3 eq_refl) eq_refl)            = 2%Z.    Proof. now vm_compute. Qed.
Example spec_div_n5_3   : intraw (div_nz (int_lit (-5) eq_refl) (int_lit 3 eq_refl) eq_refl)  = (-1)%Z. Proof. now vm_compute. Qed.
Example spec_mod_n5_3   : intraw (mod_nz (int_lit (-5) eq_refl) (int_lit 3 eq_refl) eq_refl)  = (-2)%Z. Proof. now vm_compute. Qed.
Example spec_div_5_n3   : intraw (div_nz (int_lit 5 eq_refl) (int_lit (-3) eq_refl) eq_refl)  = (-1)%Z. Proof. now vm_compute. Qed.
Example spec_mod_5_n3   : intraw (mod_nz (int_lit 5 eq_refl) (int_lit (-3) eq_refl) eq_refl)  = 2%Z.    Proof. now vm_compute. Qed.
Example spec_div_n5_n3  : intraw (div_nz (int_lit (-5) eq_refl) (int_lit (-3) eq_refl) eq_refl) = 1%Z.    Proof. now vm_compute. Qed.
Example spec_mod_n5_n3  : intraw (mod_nz (int_lit (-5) eq_refl) (int_lit (-3) eq_refl) eq_refl) = (-2)%Z. Proof. now vm_compute. Qed.

(** Spec, the ONE exception: "if the dividend x is the most negative value for the
    int type of x, the quotient q = x / -1 is equal to x (and r = 0) due to
    two's-complement integer overflow".  [GoInt] is now the FAITHFUL [Z]-carried int64
    (review #6 #13), so the most-negative value is the TRUE [int64] minimum [-2^63]
    ([-9223372036854775808]) — no longer the bounded [Sint63] [-2^62].  We honor the
    rule — no panic, [int_div] wraps it to itself (via [wrap64]). *)
Example spec_div_minint_neg1 :
  intraw (div_nz (int_lit (-9223372036854775808) eq_refl) (int_lit (-1) eq_refl) eq_refl) = (-9223372036854775808)%Z.
Proof. now vm_compute. Qed.
Example spec_mod_minint_neg1 :
  intraw (mod_nz (int_lit (-9223372036854775808) eq_refl) (int_lit (-1) eq_refl) eq_refl) = 0%Z.
Proof. now vm_compute. Qed.

(** Division you can only call with a proven-nonzero divisor.  Prints 17/5 = 3
    and 17%5 = 2.  The [eq_refl] discharges [(5 =? 0) = false] at compile time. *)
Definition div_demo : IO unit :=
  println [any (div_nz (int_lit 17 eq_refl) (int_lit 5 eq_refl) eq_refl); any (mod_nz (int_lit 17 eq_refl) (int_lit 5 eq_refl) eq_refl)].   (* prints: 3 2 *)

(** float64 is the AXIOM-FREE [SpecFloat.spec_float] (IEEE 754 double over [Z]; review #6
    #13→zero-axioms), the same binary64 as Go's float64, so arithmetic agrees bit-for-bit
    ([f64_add]/[f64_div]/… are [SF*] definitions; literals like [1.5] are parsed to the
    correctly-rounded [spec_float] and emitted as the exact Go hex-float).  (Go's [println]
    formats float64 in scientific notation — Go's builtin behaviour, captured by the golden.) *)
Definition float_demo : IO unit :=
  println [ any (f64_add 1.5 2.25)%go64     (* 3.75 *)
          ; any (f64_div 1.0 4.0)%go64 ].   (* 0.25 (exact in binary) *)

(** Float COMPARISON lowers to Go's [<]/[<=]/[==] on [float64].  Both [spec_float]'s
    [SFcompare] and Go follow IEEE 754, so the semantics match exactly — including
    NaN (every comparison with NaN is false) and signed zero ([0.0 == -0.0]).
    Comparisons bind looser than arithmetic, so [a + b < c] needs no parens. *)
Definition float_cmp_demo : IO unit :=
  bind (println [any (f64_ltb 1.5 2.5)%go64]) (fun _ =>   (* 1.5 < 2.5  → true  *)
  bind (println [any (f64_leb 2.5 2.5)%go64]) (fun _ =>   (* 2.5 <= 2.5 → true  *)
  bind (println [any (f64_eqb 1.5 1.5)%go64]) (fun _ =>   (* 1.5 == 1.5 → true  *)
  println [any (f64_ltb 3.0 2.0)%go64]))).               (* 3.0 < 2.0  → false *)

(** IEEE NaN faithfulness, MACHINE-CHECKED (Coq side): a NaN ([0.0/0.0]) is
    unordered — [NaN == NaN] and [NaN < x] are both [false].  This is exactly Go's
    float64 behaviour, so lowering [eqb]/[ltb] to [==]/[<] is faithful on the
    corner cases, not merely on ordinary values.  ([float_nan_demo] below shows
    Go agreeing at runtime.) *)
Example nan_eqb_false : f64_eqb (f64_div 0 0) (f64_div 0 0) = false.
Proof. now vm_compute. Qed.
Example nan_ltb_false : f64_ltb (f64_div 0 0) 1 = false.
Proof. now vm_compute. Qed.

(** Runtime witness (Go side) of the same NaN corner cases.  [z] is an opaque
    [float64] parameter (call site passes [0.0]) so [z/z] is a *runtime* NaN —
    a literal [0.0/0.0] would be a Go *compile-time* division-by-zero error. *)
Definition float_nan_demo (z : GoFloat64) : IO unit :=
  bind (println [any (f64_eqb (f64_div z z) (f64_div z z))%go64]) (fun _ =>
  println [any (f64_ltb (f64_div z z) 1)%go64]).   (* NaN==NaN → false ; NaN<1 → false *)

(** Float unary negation [f64_opp] → Go [-x], IEEE-exact (flips the sign
    bit), needing no package import.  Ordinary values: [opp 1.5 = -1.5] and
    [opp (opp 2.0) = 2.0]. *)
Definition float_opp_demo : IO unit :=
  bind (println [any (f64_opp 1.5)%go64]) (fun _ =>               (* -1.5 *)
  println [any (f64_opp (f64_opp 2.0))%go64]).             (* 2.0 *)

(** The IEEE corner case: [opp] yields NEGATIVE zero, distinct in sign from [+0.0]
    (even though [-0.0 == +0.0]).  Witnessed by [1 / -0 = -inf < 0] (whereas
    [1 / +0 = +inf], not [< 0]).  MACHINE-CHECKED on the Coq side; the runtime
    [float_opp_sign_demo] — with an opaque [z := 0.0], so no untyped-constant
    folding of [-0.0] to [+0.0] — shows Go agrees. *)
Example opp_zero_is_neg :
  f64_ltb (f64_div 1 (f64_opp 0)) 0 = true.
Proof. now vm_compute. Qed.
Definition float_opp_sign_demo (z : GoFloat64) : IO unit :=
  println [any (f64_ltb (f64_div 1 (f64_opp z)) 0)%go64].  (* true *)

(** Float [min]/[max] (Go 1.21 builtins, float rules) → Go [min(a,b)]/[max(a,b)].
    Faithful on the two IEEE corners Go's builtin handles: NaN PROPAGATION (a NaN arg
    gives a NaN result — witnessed via [eqb r r = false]) and SIGNED ZERO
    ([min(-0,+0) = -0], [max(-0,+0) = +0] — witnessed via [1/r], which is [-inf < 0]
    iff [r] is [-0]).  Plus the ordinary smaller/larger. *)
Example f64_min_ord     : f64_min 3 5 = 3%go64. Proof. now vm_compute. Qed.
Example f64_max_ord     : f64_max 3 5 = 5%go64. Proof. now vm_compute. Qed.
Example f64_min_nan     : f64_eqb (f64_min (f64_div 0 0) 1) (f64_min (f64_div 0 0) 1) = false.
Proof. now vm_compute. Qed.
Example f64_max_nan_b   : f64_eqb (f64_max 1 (f64_div 0 0)) (f64_max 1 (f64_div 0 0)) = false.
Proof. now vm_compute. Qed.
Example f64_min_negzero : f64_ltb (f64_div 1 (f64_min (f64_opp 0) 0)) 0 = true.
Proof. now vm_compute. Qed.
Example f64_max_poszero : f64_ltb (f64_div 1 (f64_max (f64_opp 0) 0)) 0 = false.
Proof. now vm_compute. Qed.

Definition fminmax_demo : IO unit :=
  println [ any (f64_min 3 5)%go64 ; any (f64_max 3 5)%go64 ].   (* min/max of two floats *)

(** Direct float [>] / [>=] / [!=] (completing the operator set).  Ordinary values
    plus the NaN corners: [NaN >= 1] is FALSE (the reason [f64_geb] is [leb b a], not
    [¬(<)], which would be true), and [NaN != 1] is TRUE. *)
Example f64_gtb_t   : f64_gtb 5 3 = true.   Proof. now vm_compute. Qed.
Example f64_geb_eq  : f64_geb 3 3 = true.   Proof. now vm_compute. Qed.
Example f64_geb_nan : f64_geb (f64_div 0 0) 1 = false. Proof. now vm_compute. Qed.
Example f64_neqb_nan: f64_neqb (f64_div 0 0) 1 = true. Proof. now vm_compute. Qed.

Definition fcmp_demo : IO unit :=
  println [ any (f64_gtb 5 3) ; any (f64_geb 3 3) ; any (f64_neqb 5 3) ]%go64.  (* true true true *)

(** int64 -> float64 conversion ([f64_of_i64], Go [float64(i)]) -- MODELED + machine-checked:
    [7 -> 7.0] and the SIGNED case [-3 -> -3.0].  The [Z]-carried [GoI64] is rounded ONCE to
    binary64 via [SpecFloat.binary_normalize] (axiom-free; >= 2^53 rounds exactly like Go, and
    [MININT = -2^63] is handled directly — no [of_uint63] sign-split, review #6 #13->zero-axioms).
    Recognized by name -> native Go [float64(i)]; the body is suppressed.  The reverse,
    float64 -> int64 TRUNCATION ([i64_of_f64]), also lowers now -- [spec_float] decomposes
    DIRECTLY (no float-primitive needed). *)
Example f64_of_i64_pos : f64_eqb (f64_of_i64 (7)%i64) 7%go64 = true.
Proof. now vm_compute. Qed.
Example f64_of_i64_neg : f64_eqb (f64_of_i64 (-3)%i64) (f64_opp 3%go64) = true.
Proof. now vm_compute. Qed.

(** int → float64 (Go [float64(i)]): recognized by name → native [float64(i)]; the
    [binary_normalize] body (over the [Z]-carried [GoInt], review #6 #13) suppressed.
    Machine-checked across the sign. *)
Example f64_of_int_pos : f64_eqb (f64_of_int (int_lit 5 eq_refl)) 5%go64 = true.
Proof. now vm_compute. Qed.
Example f64_of_int_neg : f64_eqb (f64_of_int (int_lit (-3) eq_refl)) (f64_opp 3%go64) = true.
Proof. now vm_compute. Qed.

(** FLOAT32 faithfulness witnesses (the SpecFloat-based binary32 model).  The decisive one:
    [2^24 + 1] is NOT representable in binary32 (24-bit significand), so [f32_add] rounds it
    back to [2^24] — whereas float64 keeps [16777217].  This proves the model really rounds at
    binary32, not binary64.  Exact cases ([1.5+2.25], [1.5*2.0]) confirm the SpecFloat path
    computes the ordinary results. *)
Example f32_add_rounds : f32_eqb (f32_add (f32_lit 16777216) (f32_lit 1)) (f32_lit 16777216) = true.
Proof. vm_compute. reflexivity. Qed.
Example f32_f64_differ : f64_eqb (16777216 + 1)%go64 16777217 = true.  (* float64 KEEPS the bit *)
Proof. vm_compute. reflexivity. Qed.
Example f32_add_exact  : f32_eqb (f32_add (f32_lit 1.5) (f32_lit 2.25)) (f32_lit 3.75) = true.
Proof. vm_compute. reflexivity. Qed.
Example f32_mul_exact  : f32_eqb (f32_mul (f32_lit 1.5) (f32_lit 2)) (f32_lit 3) = true.
Proof. vm_compute. reflexivity. Qed.

(** float32 LOWERED to native Go [float32].  The SpecFloat model body lowers to nothing — the
    binary32 rounding machinery ([renorm]/[SF*]/[binary_normalize]) is suppressed (proof-only /
    by module), so the plugin emits [f32_add]/… → Go [+]/[-]/[*]/[/] on real [float32] values.
    Demoed through a typed-param function so the call-site constants pin to [float32]. *)
Definition f32_combine (a b c : GoFloat32) : GoFloat32 := f32_mul (f32_add a b) c.
Definition f32_demo : IO unit :=
  println [ any (f32_combine (f32_lit 1.5) (f32_lit 2.25) (f32_lit 2)) ].   (* (1.5+2.25)*2 = 7.5 *)
(** narrow → int64 WIDENING LOWERED: [i64_of_u8]…[i64_of_i32] → IDENTITY (the narrow already
    erases to a Go int64 holding the value; the widen is value-preserving).  The faithful
    [to_Z]-crossing body is suppressed; the op is recognised as identity. *)
Definition i64_of_narrow_demo : IO unit :=
  println [ any (i64_of_u8  (u8_lit 200 eq_refl))         (* 200 *)
          ; any (i64_of_i8  (i8_of_int (int_lit (-5) eq_refl)))      (* -5  (signed widen keeps sign) *)
          ; any (i64_of_u16 (u16_lit 60000 eq_refl)) ].   (* 60000 *)
(** review #4 P1 #4 — the narrow→wide widening through a narrow PARAM (the case the constant-operand
    demos above could NOT see).  The param is a REAL Go [uint8]/[int8], so the widen is NOT identity:
    [i64_of_u8 x] MUST emit [int64(x)] (the reviewer's exact counterexample [func Widen(x uint8) int64
    { return x }] was invalid Go).  These extract to [func …(x uint8) int64 { return int64(x) }] etc.;
    a regression to identity-lowering FAILS [go build] (caught now, not silently shipped). *)
Definition widen_u8_to_i64 (x : GoU8) : GoI64 := i64_of_u8 x.   (* uint8 → int64 (zero-extend) *)
Definition widen_i8_to_i64 (x : GoI8) : GoI64 := i64_of_i8 x.   (* int8  → int64 (sign-extend) *)
Definition widen_u8_to_int (x : GoU8) : GoInt := int_of_u8 x.   (* uint8 → platform int (sibling op) *)
Definition widen_param_demo : IO unit :=
  println [ any (widen_u8_to_i64 (u8_lit 200 eq_refl))     (* int64(uint8 200) = 200 *)
          ; any (widen_i8_to_i64 (i8_of_int (int_lit (-5) eq_refl)))  (* int64(int8 -5)   = -5  (sign kept) *)
          ; any (widen_u8_to_int (u8_lit 100 eq_refl)) ].  (* int(uint8 100)   = 100 *)
(** int64 → narrow TRUNCATION LOWERED: [u8_of_i64]…[i32_of_i64] → the SAME native mask /
    sign-extend as [uN_of_int] ([(x & 0xFF)] for [uN]; [((x & 0xFF) ^ 0x80) - 0x80] for [iN]),
    since [GoI64] and the narrow types share the int64 carrier.  Machine-checked faithful
    (widened back via [i64_of_uN]/[i64_of_iN] so the [Z] is inspectable): unsigned drops the
    high bits, signed sign-extends the low byte, and a NEGATIVE input truncates by its
    two's-complement low byte ([uint8(-1) = 255]). *)
Example i64_to_u8_trunc  : i64raw (i64_of_u8  (u8_of_i64  (i64_lit 4660 eq_refl)))       = 52%Z.        (* uint8(4660) *)
Proof. vm_compute. reflexivity. Qed.
Example i64_to_i8_signed : i64raw (i64_of_i8  (i8_of_i64  (i64_lit 200 eq_refl)))        = (-56)%Z.     (* int8(200) wraps negative *)
Proof. vm_compute. reflexivity. Qed.
Example i64_to_u8_neg    : i64raw (i64_of_u8  (u8_of_i64  (i64_lit (-1) eq_refl)))       = 255%Z.       (* uint8(-1): low byte of 2's-complement *)
Proof. vm_compute. reflexivity. Qed.
Example i64_to_i32_wide  : i64raw (i64_of_i32 (i32_of_i64 (i64_lit 5000000000 eq_refl))) = 705032704%Z. (* int32(5e9) *)
Proof. vm_compute. reflexivity. Qed.
Definition i64_to_narrow_demo : IO unit :=
  println [ any (u8_of_i64  (i64_lit 4660 eq_refl))         (* uint8(4660)   = 52   *)
          ; any (i8_of_i64  (i64_lit 200 eq_refl))          (* int8(200)     = -56  *)
          ; any (u16_of_i64 (i64_lit 70000 eq_refl))        (* uint16(70000) = 4464 *)
          ; any (i32_of_i64 (i64_lit 5000000000 eq_refl)) ]. (* int32(5e9)    = 705032704 *)
(** P0 #2 LOCK (code review): a narrow value through a [let] must box as its REAL Go type, not its
    int64 carrier.  [xu8 : GoU8] is bound via a [let]; [type_assert_safe TU8 (any xu8)] must SUCCEED
    (ok1=true) and [TI64] must FAIL (ok2=false) — the boxed dynamic type is [uint8], DISTINCT from
    [int64], exactly as Go's [v.(uint8)] / [v.(int64)] decide and as the model's [tag_eq] says.
    Regression guard for the let-boundary narrow-box fix (the pre-fix int64-carrier bug boxed [xu8]
    as Go [int], giving [false false]).  Also exercises type_assert_safe on a FRESH box — the backend
    now materialises [any(uint8(xu8))] rather than asserting on the raw (non-interface) payload. *)
Definition narrow_let_assert_demo : IO unit :=
  let xu8 := u8_of_i64 (i64_lit 200 eq_refl) in
  type_assert_safe TU8 (any xu8) (fun v8 ok1 =>
    println [any v8; any ok1]).   (* 200 true *)

(** DIFFERENTIAL TYPE-IDENTITY LOCK (R10 — golden-output ALONE cannot tell
    [uint8]/[int64] apart, which is exactly how the #1/#2/#7 type-identity bugs HID).
    At RUNTIME, assert each scalar against its OWN Go type (→ [true]) AND against a
    sibling it must NOT alias (→ [false]): a uint8 is NOT an int64, an int64 is NOT a
    uint8.  A regression that re-collides them (e.g. boxing [uint8] as [int64] again,
    the #7 cluster bug) FLIPS the assertions, changing the golden ⇒ caught.  This is
    the runtime companion to the model-side [tag_runtime_agrees] lock (break #7d). *)
Definition type_identity_lock_demo : IO unit :=
  let u8v  := u8_of_i64 (i64_lit 7 eq_refl) in
  let i64v := i64_lit 9 eq_refl in
  let u64v := u64_lit 5 eq_refl in
  type_assert_safe TU8  (any u8v)  (fun _ a =>     (* uint8  .(uint8)  → true  *)
  type_assert_safe TI64 (any u8v)  (fun _ b =>     (* uint8  .(int64)  → FALSE *)
  type_assert_safe TI64 (any i64v) (fun _ c =>     (* int64  .(int64)  → true  (locks i64_lit typed int64) *)
  type_assert_safe TU8  (any i64v) (fun _ d =>     (* int64  .(uint8)  → FALSE *)
  type_assert_safe TU64 (any u64v) (fun _ e =>     (* uint64 .(uint64) → true  (locks u64_lit typed uint64) *)
  type_assert_safe TI64 (any u64v) (fun _ f =>     (* uint64 .(int64)  → FALSE *)
  type_assert_safe TInt64 (any i64v) (fun _ g =>   (* int64  .(int)    → FALSE (break #7c: GoI64 is int64, NOT Go's platform int) *)
    println [any a; any b; any c; any d; any e; any f; any g]))))))).
  (* true false true false true false false *)

(** Extends the differential lock (R10) to the FULL #7 narrow cluster: each narrow
    type boxes as its OWN distinct Go type (de-collided from int64 by break #7b).
    Each asserts its own type → [true]; a regression that re-collides any back to
    int64 flips it.  (uint8 is already locked in [type_identity_lock_demo].) *)
Definition narrow_cluster_lock_demo : IO unit :=
  type_assert_safe TI8  (any (i8_of_i64  (i64_lit 5 eq_refl))) (fun _ a =>   (* int8   .(int8)   → true *)
  type_assert_safe TU16 (any (u16_of_i64 (i64_lit 5 eq_refl))) (fun _ b =>   (* uint16 .(uint16) → true *)
  type_assert_safe TI16 (any (i16_of_i64 (i64_lit 5 eq_refl))) (fun _ c =>   (* int16  .(int16)  → true *)
  type_assert_safe TU32 (any (u32_of_i64 (i64_lit 5 eq_refl))) (fun _ d =>   (* uint32 .(uint32) → true *)
  type_assert_safe TI32 (any (i32_of_i64 (i64_lit 5 eq_refl))) (fun _ e =>   (* int32  .(int32)  → true *)
    println [any a; any b; any c; any d; any e]))))).
  (* true true true true true *)

(** review #4 P0 #1 — Go's platform [uint] is now a GENUINELY DISTINCT Rocq type ([GoUint], a
    record), NOT a transparent [int] alias.  TWO defects, both machine-checked closed here:

    (1) TYPE CONFUSION — assigning a [GoInt] where a [GoUint] is expected (or the reverse) no
        longer type-checks, so the plugin can NEVER emit the invalid Go [func(x int) uint { return x }]
        (review #4's exact counterexample).  These [Fail]s are checked at COMPILE time: *)
Fail Definition int_to_uint_confusion (x : GoInt)  : GoUint := x.
Fail Definition uint_to_int_confusion (x : GoUint) : GoInt  := x.
(*  and the retired bare-[int] placeholders no longer exist as types at all (one Rocq type per Go type): *)
Fail Check (GoUint8 : Type).
Fail Check (GoInt32 : Type).

(** (2) TAG INVERSION — a [GoUint] value boxes as Go [uint] (via the now-UNIQUE [Tagged_GoUint = TUint];
    [Tagged_int] no longer applies since [GoUint <> int]), so [.(uint)] SUCCEEDS and [.(int)] FAILS:
    the model ([tag_eq]) and the runtime ([v.(T)]) AGREE.  A regression that re-collapses [GoUint] to
    [int] flips these and moves the golden ⇒ caught.  Runtime companion to the model-side
    [tag_runtime_agrees] lock, now covering the platform-uint tag. *)
Definition uint_lock_demo : IO unit :=
  let uv := uint_lit 5 eq_refl in
  type_assert_safe TUint  (any uv) (fun _ a =>    (* uint .(uint) → true  *)
  type_assert_safe TInt64 (any uv) (fun _ b =>    (* uint .(int)  → FALSE (platform uint <> platform int) *)
    println [any a; any b])).
  (* true false *)
(** P0 #2 — a sub-64 narrow [GoIntN] value now flows correctly through EVERY position: a function RETURN
    (the result is cast to its declared Go type — [func lowbyte(x int64) uint8 { return uint8((x & 0xff)) }]),
    a narrow PARAM ([inc8] below — the param is the declared [uint8], widened to the int carrier inside the
    masked arithmetic), and a narrow result CONSUMED by further (signed) narrow arithmetic ([consume_i8] —
    [i8_add (lowbyte_i8 x) …], where the [int8] result is widened before the `& 0xff` mask).  Each narrow op
    widens its operands to the int carrier, so a narrow-typed operand never overflows the mask; the result is
    re-cast to the narrow Go type only at a boundary (return) or box.  All COMPILE and compute correctly. *)
Definition lowbyte    (x : GoI64) : GoU8 := u8_of_i64 x.
Definition lowbyte_i8 (x : GoI64) : GoI8 := i8_of_i64 x.
Definition inc8       (x : GoU8)  : GoU8 := u8_add x (u8_lit 1 eq_refl).            (* narrow PARAM in arith *)
Definition consume_i8 (x : GoI64) : GoI8 := i8_add (lowbyte_i8 x) (i8_lit 1 eq_refl). (* narrow RESULT consumed *)
Example lowbyte_val    : i64raw (i64_of_u8 (lowbyte    (i64_lit 4660 eq_refl))) = 52%Z.
Proof. vm_compute. reflexivity. Qed.
Example lowbyte_i8_val : i64raw (i64_of_i8 (lowbyte_i8 (i64_lit 200  eq_refl))) = (-56)%Z.
Proof. vm_compute. reflexivity. Qed.
Example inc8_val       : i64raw (i64_of_u8 (inc8       (u8_lit 200 eq_refl)))   = 201%Z.
Proof. vm_compute. reflexivity. Qed.
Example consume_i8_val : i64raw (i64_of_i8 (consume_i8 (i64_lit 200 eq_refl)))  = (-55)%Z.
Proof. vm_compute. reflexivity. Qed.
Definition narrow_ret_demo : IO unit :=
  println [ any (lowbyte    (i64_lit 4660 eq_refl))    (* uint8(4660)        = 52  *)
          ; any (lowbyte_i8 (i64_lit 200  eq_refl))    (* int8(200)          = -56 *)
          ; any (inc8       (u8_lit 200 eq_refl))      (* uint8(200)+1       = 201 *)
          ; any (consume_i8 (i64_lit 200 eq_refl)) ].  (* int8(int8(200)+1)  = -55 *)

(** review #4 P1 #4 (slice 2) — the CONVERSE of the widening: a wide int64-carried value flowing INTO
    a NARROW struct field.  [bb_val : GoU8] renders as Go [uint8], but the constructor value
    [u8_of_i64 …] is computed in the int64 carrier (a masked expr), so a bare [ByteBox{Bb_val: x & 0xff}]
    is INVALID Go (the reviewer's [Box{V: x & 0xff}] with V uint8).  The plugin now casts the value to
    the field's destination type: [ByteBox{Bb_val: uint8(((int64(300)) & 0xff)), …}].  A RUNTIME value
    (not a bare constant) exercises the cast: [u8_of_i64 (i64_lit 300)] truncates to uint8(300)=44, then
    the field read [bb_val b] (a real [uint8]) widens back via [i64_of_u8] (slice 1) to 44. *)
Record ByteBox := MkByteBox { bb_val : GoU8 ; bb_tag : GoI64 }.   (* 2 fields: avoid single-field unboxing *)
Definition narrow_field_demo : IO unit :=
  let b := MkByteBox (u8_of_i64 (i64_lit 300 eq_refl)) (i64_lit 7 eq_refl) in
  println [ any (i64_of_u8 (bb_val b))   (* uint8(300)=44, widened back to int64 *)
          ; any (bb_tag b) ].            (* 7 (the int64 field is untouched) *)
  (* 44 7 *)

(** review #4 P1 #4 (slice 3) — narrow COLLECTION ELEMENTS: a wide int64-carried value flowing into a
    narrow slice/array element.  [[]uint8] / [[N]uint8] literals built from runtime values were emitted
    bare ([[]uint8{x & 0xff}] = invalid Go); the plugin now casts each element to the element type from
    the [GoTypeTag] ([[]uint8{uint8(((int64(300)) & 0xff)), uint8((5 & 0xff))}]).  Exercises the SLICE
    emitter [slice_of_list] ([]T) and the ARRAY emitter [arr_lit] ([N]T); [arr3_lit] ([3]T) shares
    [arr_lit]'s identical element-cast code path ([narrow_go_name go_elem]). *)
Definition narrow_elem_demo : IO unit :=
  let s := slice_of_list TU8 [u8_of_i64 (i64_lit 300 eq_refl); u8_lit 5 eq_refl] in   (* []uint8{44,5} *)
  let a := arr_lit       TU8 [u8_of_i64 (i64_lit 301 eq_refl); u8_lit 6 eq_refl] in   (* [2]uint8{45,6} *)
  bind (slice_get TU8 s (int_lit 0 eq_refl)) (fun s0 =>           (* s[0] = uint8 44 *)
  arr_get_ok TU8 a (int_lit 1 eq_refl) (fun av _ok =>             (* a[1] = uint8 6  *)
    println [ any (i64_of_u8 s0)         (* 44 *)
            ; any (i64_of_u8 av) ])).    (* 6  *)
  (* 44 6 *)

(** review #4 P1 #4 (slice 4) — narrow PAYLOADS at the tag-carrying POINTER & CHANNEL boundaries: a
    wide int64-carried value written into a [*uint8] cell or sent on a [chan uint8].  Both were emitted
    bare (the [ptr_new] IIFE arg / [*p = v] / [ch <- v]) → invalid Go; the plugin now casts the payload
    to the destination narrow type from the op's [GoTypeTag] ([uint8(…)]).  Runtime values exercise it. *)
Definition ptr_chan_narrow_demo : IO unit :=
  bind (ptr_new TU8 (u8_of_i64 (i64_lit 300 eq_refl))) (fun p =>   (* *uint8 ← uint8(44) *)
  bind (ptr_set TU8 p (u8_of_i64 (i64_lit 7 eq_refl)))   (fun _ => (* *p = uint8(7) *)
  bind (ptr_get TU8 p) (fun pv =>                                   (* pv := *p (uint8 7) *)
  bind (make_chan_buf TU8 (int_lit 1 eq_refl)) (fun ch =>
  bind (send TU8 ch (u8_of_i64 (i64_lit 301 eq_refl))) (fun _ =>    (* ch <- uint8(45) *)
  bind (recv TU8 ch) (fun cv =>                                     (* cv := <-ch (uint8 45) *)
  println [ any (i64_of_u8 pv) ; any (i64_of_u8 cv) ])))))).        (* 7 45 *)

(** review #4 P1 #4 (slice 5) — narrow map VALUES: a [map[int64]uint8] written with a wide int64-carried
    value (the map_set RHS) and read with a narrow default (map_get_or's default).  Both were emitted bare
    ([m[k] = x & 0xff] invalid Go; the default boxed as int64 ⇒ [hit] inferred int64, then [hit = _v] from
    the uint8 map = invalid).  The plugin now casts both to the value type from the [GoTypeTag].  (Narrow
    map KEYS are the next slice.) *)
Definition map_narrow_demo : IO unit :=
  bind (map_make_typed TI64 TU8) (fun m =>
  bind (map_set TI64 TU8 (5)%i64 (u8_of_i64 (i64_lit 300 eq_refl)) m) (fun _ =>      (* m[5] = uint8(44) *)
  bind (@map_get_or GoI64 GoU8 TI64 TU8 (5)%i64 (u8_of_i64 (i64_lit 9 eq_refl)) m) (fun hit =>  (* m[5] = 44 *)
  bind (@map_get_or GoI64 GoU8 TI64 TU8 (9)%i64 (u8_of_i64 (i64_lit 9 eq_refl)) m) (fun miss => (* miss → dflt uint8(9) *)
  println [ any (i64_of_u8 hit) ; any (i64_of_u8 miss) ])))).      (* 44 9 *)

(** review #4 P1 #4 (slice 6) — narrow map KEYS: a [map[uint8]int64] keyed by a wide int64-carried value.
    Every key site emitted the key bare ([m[x & 0xff]] = invalid Go: an int64 index into a [map[uint8]]),
    so a narrow-key map was all-or-nothing.  The plugin now casts the key to the key type from the
    [GoTypeTag] at ALL sites: map_set, map_delete, map_get_or, map_get_opt.  This demo exercises set +
    get_or + get_opt(bind/match) + delete + len with a [uint8] key. *)
Definition map_key_narrow_demo : IO unit :=
  bind (map_make_typed TU8 TI64) (fun m =>
  bind (map_set TU8 TI64 (u8_of_i64 (i64_lit 300 eq_refl)) (5)%i64 m) (fun _ =>            (* m[uint8 44] = 5 *)
  bind (@map_get_or GoU8 GoI64 TU8 TI64 (u8_of_i64 (i64_lit 300 eq_refl)) (0)%i64 m) (fun hit =>  (* m[44] = 5 *)
  bind (map_get_opt TU8 TI64 (u8_of_i64 (i64_lit 300 eq_refl)) m) (fun o =>                (* Some 5 *)
  match o with
  | Some v =>
    bind (map_delete TU8 TI64 (u8_of_i64 (i64_lit 300 eq_refl)) m) (fun _ =>               (* delete m[44] *)
    bind (map_len m) (fun n =>                                                              (* len = 0 *)
    println [ any hit ; any v ; any n ]))                                                   (* 5 5 0 *)
  | None => println [ any (0)%i64 ]
  end)))).

(** review #4 P1 #4 (slice 7) — narrow function ARGS: a wide int64-carried value passed to a NARROW
    PARAM of a user function.  The arg [u8_of_i64 …] is the int64-masked carrier, so a bare
    [Takes_u8(x & 0xff)] is invalid Go (int64 into a [uint8] param).  The plugin now casts the arg to
    the callee's param type ([Takes_u8(uint8(…))]) when the params align 1:1 with the visible args
    (monomorphic — no erased tag/witness args).  The existing many-arg int64 calls are unaffected
    (int64 param ⇒ no cast); generic tag-carrying calls (slice_get …) decline (length mismatch). *)
Definition takes_u8 (x : GoU8) : GoI64 := i64_of_u8 x.   (* uint8 param, widened to int64 *)
Definition arg_narrow_demo : IO unit :=
  println [ any (takes_u8 (u8_of_i64 (i64_lit 300 eq_refl))) ].   (* Takes_u8(uint8(44)) = 44 *)

(** P0 R3 — a VALUE-position [let] (nested in an expression, the bound var used twice so extraction keeps
    it) inside int64 arithmetic.  The old backend emitted [(func() any {…})()], i.e. [int64(any)+…], which
    does not compile; now the pure let is inlined so the surrounding [int64] context types it. *)
Definition vlet (x z : GoI64) : GoI64 := i64_add (let y := i64_add x x in i64_add y y) z.
Example vlet_val : i64raw (vlet (5)%i64 (1)%i64) = 21%Z.   Proof. vm_compute. reflexivity. Qed.
Definition vlet_demo : IO unit := println [ any (vlet (5)%i64 (1)%i64) ].   (* (5+5)+(5+5) + 1 = 21 *)
(** narrow ↔ uint64 — CLOSED via the int64 HUB, no new ops.  Every integer conversion factors
    through [GoI64]: narrow→uint64 is [u64_of_i64 ∘ i64_of_narrow] (widen is identity, then the
    [uint64(x)] reinterpret); uint64→narrow is [<narrow>_of_i64 ∘ i64_of_u64] ([int64(x)]
    reinterpret, then mask/sign-extend).  Each leg already lowers, and the NAMED hub functions
    [U64_of_i64]/[I64_of_u64] apply the cast to a VARIABLE — so even the signed corners a bare
    cast would reject (Go forbids [uint64(-1)] on a constant) emit valid Go.  Machine-checked:
    unsigned widen preserves the value; signed widen reinterprets ([uint64(int8 -1) = 2^64-1]);
    truncation drops the high bits ([uint8(uint64 511) = 255]); and a uint64 whose low byte has
    bit 7 set narrows to a NEGATIVE signed ([int8(uint64 255) = -1]). *)
Example u64_of_u8_widen    : u64raw (u64_of_i64 (i64_of_u8 (u8_lit 200 eq_refl)))             = 200%Z.
Proof. vm_compute. reflexivity. Qed.
Example u64_of_i8_reinterp : u64raw (u64_of_i64 (i64_of_i8 (i8_of_int (int_lit (-1) eq_refl))))          = 18446744073709551615%Z.
Proof. vm_compute. reflexivity. Qed.
Example u8_of_u64_trunc    : i64raw (i64_of_u8 (u8_of_i64 (i64_of_u64 (u64_lit 511 eq_refl)))) = 255%Z.
Proof. vm_compute. reflexivity. Qed.
Example i8_of_u64_signed   : i64raw (i64_of_i8 (i8_of_i64 (i64_of_u64 (u64_lit 255 eq_refl)))) = (-1)%Z.
Proof. vm_compute. reflexivity. Qed.
Definition narrow_u64_demo : IO unit :=
  println [ any (u64_of_i64 (i64_of_u8  (u8_lit 200 eq_refl)))     (* uint64(uint8 200) = 200    *)
          ; any (u64_of_i64 (i64_of_i8  (i8_of_int (int_lit (-1) eq_refl))))  (* uint64(int8 -1)   = 2^64-1 *)
          ; any (u8_of_i64  (i64_of_u64 (u64_lit 511 eq_refl)))    (* uint8(uint64 511) = 255    *)
          ; any (i8_of_i64  (i64_of_u64 (u64_lit 255 eq_refl))) ]. (* int8(uint64 255)  = -1     *)

(** float32 ↔ float64 conversions LOWERED.  Widening [f64_of_f32] → [float64(x)] (exact);
    narrowing [f32_of_f64] → [float32(x)] (rounds to binary32).  Machine-checked that the
    narrow really rounds: [2^24 + 1] is unrepresentable in binary32, so it rounds to [2^24]. *)
Example f32_of_f64_rounds : f64_eqb (f64_of_f32 (f32_of_f64 16777217)) 16777216 = true.
Proof. vm_compute. reflexivity. Qed.
Definition narrow32 (x : GoFloat64) : GoFloat32 := f32_of_f64 x.
Definition widen64  (x : GoFloat32) : GoFloat64 := f64_of_f32 x.
(** float32 NEGATION + MIN/MAX (completing float32 to float64 parity, sans abs/sqrt which need
    [math]).  Machine-checked on the IEEE corners: NaN propagation and signed zero.  [f32_neg] →
    Go [-x]; [f32_min]/[f32_max] → Go [min]/[max] on float32. *)
Example f32_neg_ex   : f32_eqb (f32_neg (f32_lit 1.5)) (f32_lit (-1.5)) = true.
Proof. vm_compute. reflexivity. Qed.
Example f32_neg_zero : f64_ltb (f64_div 1 (widen64 (f32_neg (f32_lit 0)))) 0 = true.  (* -0 *)
Proof. vm_compute. reflexivity. Qed.
Example f32_min_ord  : f32_eqb (f32_min (f32_lit 3) (f32_lit 5)) (f32_lit 3) = true.
Proof. vm_compute. reflexivity. Qed.
Example f32_max_ord  : f32_eqb (f32_max (f32_lit 3) (f32_lit 5)) (f32_lit 5) = true.
Proof. vm_compute. reflexivity. Qed.
Example f32_min_nan  : let r := widen64 (f32_min (f32_lit (f64_div 0 0)) (f32_lit 1)) in
                       f64_eqb r r = false.    (* NaN propagates *)
Proof. vm_compute. reflexivity. Qed.
Example f32_min_negzero : f64_ltb (f64_div 1 (widen64 (f32_min (f32_neg (f32_lit 0)) (f32_lit 0)))) 0 = true.   (* min(-0,+0) = -0 *)
Proof. vm_compute. reflexivity. Qed.
Example f32_max_poszero : f64_ltb (f64_div 1 (widen64 (f32_max (f32_neg (f32_lit 0)) (f32_lit 0)))) 0 = false.  (* max(-0,+0) = +0 *)
Proof. vm_compute. reflexivity. Qed.
Definition f32_extra_demo : IO unit :=
  println [ any (f32_neg (f32_lit 1.5))             (* -1.5 *)
          ; any (f32_min (f32_lit 3) (f32_lit 5))   (* 3 *)
          ; any (f32_max (f32_lit 3) (f32_lit 5)) ]. (* 5 *)
(** Differential test — float32 vs float64 DISTINCTNESS under boxing (untested: the f32 demos box+print,
    which can't reveal the boxed Go type).  A boxed [GoFloat32] asserts TO [float32] (true) but NOT TO
    [float64] (false), and a boxed [float64] the reverse — so the model's [tag_eq] agrees with Go's
    runtime [v.(float32)] vs [v.(float64)] (they are genuinely distinct Go types). *)
Definition f32_box_demo : IO unit :=
  type_assert_safe TFloat32 (any (f32_lit 1.5)) (fun _ a =>     (* float32 to float32 → true  *)
  type_assert_safe TFloat64 (any (f32_lit 1.5)) (fun _ b =>     (* float32 to float64 → FALSE *)
  type_assert_safe TFloat64 (any (1.5)%go64)   (fun _ c =>     (* float64 to float64 → true  *)
    println [any a; any b; any c]))).   (* true false true *)
(** float32 RANGE + CONVERSION faithfulness (the float32 trap list).  Every float32↔(int/float64/
    constant) path goes through binary64, which is PROVABLY single-rounding-equivalent: binary64's
    53 bits exceed [2·24 + 2 = 50], so decimal/int → binary64 → binary32 equals a DIRECT round to
    binary32 (the double-rounding-innocuous theorem — no extra error from the intermediate).
    Machine-checked across the corners: *)
Example f32_overflow  : f64_eqb (widen64 (f32_lit 1e40)) (f64_div 1 0) = true.   (* |x|>max → +Inf *)
Proof. vm_compute. reflexivity. Qed.
Example f32_underflow : f64_eqb (widen64 (f32_lit 1e-50)) 0 = true.                     (* below min subnormal → 0 *)
Proof. vm_compute. reflexivity. Qed.
Example f32_of_int_rounds : f32_eqb (f32_of_f64 (f64_of_int (int_lit 16777217 eq_refl))) (f32_lit 16777216) = true. (* float32(2^24+1)=2^24 *)
Proof. vm_compute. reflexivity. Qed.
Example f32_to_int_trunc  : i64raw (i64_of_f64 (f64_of_f32 (f32_lit 3.7))) = 3%Z.             (* int(float32 3.7) trunc → 3 *)
Proof. vm_compute. reflexivity. Qed.
Example f32_const_fold : f32_eqb (f32_of_f64 (f64_of_fconst (fc_add (mkFC 1 10) (mkFC 2 10))))
                                 (f32_of_f64 (f64_of_fconst (mkFC 3 10))) = true.   (* float32(0.1+0.2)=float32(0.3), exact fold *)
Proof. vm_compute. reflexivity. Qed.
Definition f32_conv_demo : IO unit :=
  println [ any (f32_of_f64 (f64_of_int (int_lit 16777217 eq_refl)))                       (* float32(2^24+1) = 1.6777216e7 *)
          ; any (f32_of_f64 (f64_of_fconst (fc_add (mkFC 1 10) (mkFC 2 10)))) ]. (* float32(0.1+0.2) = 0.3 *)
(** narrow ↔ float32 is COMPOSABLE — no DIRECT [f32_of_u8]/[u8_of_f32] op is required: a uint8 reaches
    float32 via [f32_of_i64 ∘ i64_of_u8], and back via [i64_of_f64 ∘ f64_of_f32] — exactly Go's
    [float32(uint8(x))] / [int64(float32(x))], value-correct (a narrow is small, exactly representable).
    Round-tripped through float32 and printed as an int to keep the witness format-free. *)
Definition narrow_f32_demo : IO unit :=
  println [ any (i64_of_f64 (f64_of_f32 (f32_of_i64 (i64_of_u8 (u8_lit 200 eq_refl))))) ].   (* uint8 200 → float32 → int64: 200 *)
(** REGRESSION (code review): a float op on CONSTANTS must extract as a RUNTIME IEEE operation,
    NOT a Go constant expression — Go constants cannot denote -0/±Inf/NaN, and a constant [/0] or
    [float32] overflow are COMPILE ERRORS.  The extractor now forces runtime (typed IIFE) for any
    float op whose operands are not runtime variables.  Model values (machine-checked) and the
    runtime Go now agree on the IEEE results: *)
Example f32_div0_inf  : f64_eqb (widen64 (f32_div (f32_lit 1) (f32_lit 0))) (f64_div 1 0) = true. (* +Inf *)
Proof. vm_compute. reflexivity. Qed.
Example f32_div_negzero : f64_eqb (widen64 (f32_div (f32_lit 1) (f32_neg (f32_lit 0)))) (f64_div 1 (f64_opp 0)) = true. (* -Inf (proves -0) *)
Proof. vm_compute. reflexivity. Qed.
Definition f32_const_runtime_demo : IO unit :=
  println [ any (f32_div (f32_lit 1) (f32_lit 0))             (* +Inf  (pre-fix: Go compile error, constant /0) *)
          ; any (f32_div (f32_lit 1) (f32_neg (f32_lit 0)))   (* -Inf  (proves -0 preserved; pre-fix +0 → +Inf) *)
          ; any (f32_lit 1e40)                                 (* +Inf  (pre-fix: Go compile error, const overflow) *)
          ; any (f64_div 1 0)%go64 ].                   (* float64 +Inf (same class) *)
(** DIRECT int → float32 (code review): [f32_of_i64]/[f32_of_int]/[f32_of_u64] round the integer
    ONCE to binary32, faithfully modelling Go's [float32(x)].  For |x| > 2^53 this DIFFERS from the
    double-rounding [f32_of_f64 (f64_of_int x)] = [float32(float64(x))], DISPROVING the earlier
    "single-rounding-equivalent" claim.  Reviewer's witness, x = 2^61+2^37+1 = 2305843146652647425: *)
Example f32_of_i64_differs :         (* direct ≠ via-float64 — double rounding is REAL *)
  f32_eqb (f32_of_i64 (i64_lit 2305843146652647425 eq_refl))
          (f32_of_f64 (f64_of_i64 (i64_lit 2305843146652647425 eq_refl))) = false.
Proof. vm_compute. reflexivity. Qed.
Example f32_of_i64_direct :          (* direct = 2^61+2^38 (Go float32(x) = 0x5e000001) *)
  f64_eqb (f64_of_f32 (f32_of_i64 (i64_lit 2305843146652647425 eq_refl))) 2305843284091600896 = true.
Proof. vm_compute. reflexivity. Qed.
Example f32_of_i64_viaf64 :          (* via float64 = 2^61 (Go float32(float64(x)) = 0x5e000000) *)
  f64_eqb (f64_of_f32 (f32_of_f64 (f64_of_i64 (i64_lit 2305843146652647425 eq_refl)))) 2305843009213693952 = true.
Proof. vm_compute. reflexivity. Qed.
Definition f32_of_int_demo : IO unit :=
  (* direct float32(x) vs via float64 float32(float64(x)) DIFFER (double rounding); println truncates
     the shared ~6 sig-figs, so print the INEQUALITY (false = they differ) — the observable proof. *)
  println [ any (f32_eqb (f32_of_i64 (i64_lit 2305843146652647425 eq_refl))
                         (f32_of_f64 (f64_of_i64 (i64_lit 2305843146652647425 eq_refl)))) ].  (* false *)
(** EXACT float CONSTANT → float32 (code review's remaining item): [f32_of_fconst] rounds the exact
    rational ONCE to binary32 (correctly-rounded for ALL num/den).  Disproves single-rounding via
    float64 for a large rational, and computes the ordinary small constant exactly. *)
Example f32_of_fconst_direct :   (* exact 2305843146652647425/1 → 2^61+2^38 (Go float32(x) = 0x5e000001) *)
  f64_eqb (f64_of_f32 (f32_of_fconst (mkFC 2305843146652647425 1))) 2305843284091600896 = true.
Proof. vm_compute. reflexivity. Qed.
Example f32_of_fconst_differs :  (* single round ≠ double round (via float64) for the large rational *)
  f32_eqb (f32_of_fconst (mkFC 2305843146652647425 1))
          (f32_of_f64 (f64_of_fconst (mkFC 2305843146652647425 1))) = false.
Proof. vm_compute. reflexivity. Qed.
Example f32_of_fconst_small :    (* 0.1 + 0.2 as an EXACT rational 30/100 → float32(0.3) *)
  f32_eqb (f32_of_fconst (fc_add (mkFC 1 10) (mkFC 2 10))) (f32_lit 0.3) = true.
Proof. vm_compute. reflexivity. Qed.
Definition f32_fconst_demo : IO unit :=
  println [ any (f32_of_fconst (fc_add (mkFC 1 10) (mkFC 2 10))) ].   (* float32(0.1+0.2) = float32(0.3), single round *)
(** f64 exact constant — now correctly-rounded for ALL num/den (the float64 parallel of int→float32):
    [f64_of_fconst] rounds the exact rational ONCE via [SFdiv 53 1024] of the exact spec_floats,
    fixing the latent double-rounding of the old [div (f64_of_i64 num) (f64_of_i64 den)] when BOTH
    endpoints exceed 2^53 (and removing the extraction's 2^53 fail-loud guard — large constants now
    lower as [float64(num.0/den.0)]). *)
Example f64_of_fconst_no_double_round :   (* new (single round) ≠ old (double round) for a both-large rational *)
  f64_eqb (f64_of_fconst (mkFC 9007199254740993 9007199254740995))
                (f64_div (f64_of_i64 (i64_lit 9007199254740993 eq_refl)) (f64_of_i64 (i64_lit 9007199254740995 eq_refl))) = false.
Proof. vm_compute. reflexivity. Qed.
Definition f64_fconst_big_demo : IO unit :=
  println [ any (f64_of_fconst (mkFC 9007199254740993 10)) ].   (* (2^53+1)/10 = 900719925474099.25, single round (was fail-loud) *)
(** SOUNDNESS REGRESSION (closes a code-review hole).  Pre-fix, [GoFloat32 := float] was a
    transparent alias, so a NON-binary32-representable literal could be injected raw and
    [f64_of_f32 16777217 = 16777217] — DISAGREEING with Go (which rounds [float32(16777217)]
    to [16777216]) and licensing unsound proofs.  Now [16777217] cannot enter [GoFloat32]
    except through the rounding boundary [f32_lit], which rounds it to [2^24]; widening that
    yields [16777216], MATCHING Go.  (The raw injection [f64_of_f32 16777217] no longer even
    typechecks — [GoFloat32] is abstract.) *)
Example f32_widen_sound : f64_eqb (widen64 (f32_lit 16777217)) 16777216 = true.
Proof. vm_compute. reflexivity. Qed.
Definition floatconv_demo : IO unit :=
  bind (println [ any (narrow32 16777217) ])        (fun _ =>   (* float64→float32: rounds to 16777216 *)
  println [ any (widen64 (narrow32 7.5)) ]).                    (* round-trip 7.5 (exact) *)
(** UNTYPED FLOAT CONSTANTS (model): a constant float expression is EXACT (rational) until typed,
    then rounded ONCE.  [0.1 + 0.2] as a CONSTANT is [float64(3/10) = 0.3] exactly; the RUNTIME
    add ([f64_add 0.1 0.2]) rounds each operand first → [0.30000000000000004].  Both
    machine-checked, proving the model captures the constant-vs-runtime distinction Go makes.
    (Proof-only: lowering of [f64_of_fconst] to Go is the deferred follow-on.) *)
Example fconst_exact   : f64_eqb (f64_of_fconst (fc_add (mkFC 1 10) (mkFC 2 10))) 0.3 = true.
Proof. vm_compute. reflexivity. Qed.
Example fconst_runtime : f64_eqb (f64_add 0.1 0.2) 0.3 = false.   (* runtime ≠ the constant 0.3 *)
Proof. vm_compute. reflexivity. Qed.
Example fconst_mul     : f64_eqb (f64_of_fconst (fc_mul (mkFC 3 2) (mkFC 1 4))) 0.375 = true.  (* 3/2·1/4 = 3/8 = 0.375 *)
Proof. vm_compute. reflexivity. Qed.
Example fconst_div     : f64_eqb (f64_of_fconst (fc_div (mkFC 1 1) (mkFC 4 1) ltac:(discriminate))) 0.25 = true.   (* 1.0/4.0 = 0.25 *)
Proof. vm_compute. reflexivity. Qed.
(** Review #6 P2 #16 / minimum-suite #12: a constant division by a ZERO constant is
    UNCONSTRUCTABLE.  [fc_div] demands evidence [fc_num b <> 0]; for a zero divisor that
    obligation is [0 <> 0], which is refutable — so no such [fc_div] term can be written.
    (Go rejects constant division by zero at compile time; here it is a TYPE error.) *)
Example fc_div_zero_evidence_absurd : ~ (fc_num (mkFC 0 1) <> 0%Z).
Proof. intro H. exact (H eq_refl). Qed.
(** LOWERED: [f64_of_fconst] folds the exact rational and emits [(float64(num) / float64(den))],
    which Go RE-FOLDS at compile time to the same correctly-rounded constant. *)
Definition fconst_demo : IO unit :=
  println [ any (f64_of_fconst (fc_add (mkFC 1 10) (mkFC 2 10)))    (* (1/10)+(2/10) = 0.3 *)
          ; any (f64_of_fconst (fc_mul (mkFC 3 2) (mkFC 1 4)))      (* (3/2)·(1/4) = 0.375 *)
          ; any (f64_of_fconst (fc_div (mkFC 1 1) (mkFC 4 1) ltac:(discriminate))) ].   (* 1.0/4.0 = 0.25 *)
(** float32 COMPARISON LOWERED to native Go [float32] [<]/[>=]/[!=] (operands are [float32]).
    Machine-checked faithful, NaN corner included: [f32_geb] is the swapped [leb], so [x >= NaN]
    is FALSE (matching Go) — [¬(x < NaN)] would wrongly be true. *)
Notation f32c a b c := (f32_combine (f32_lit a) (f32_lit b) (f32_lit c)) (only parsing).
Example f32_lt_ex   : f32_ltb  (f32c 1.5 0.0 2) (f32c 5.0 0.0 2) = true.   (* 3 < 10  *)
Proof. vm_compute. reflexivity. Qed.
Example f32_ge_ex   : f32_geb  (f32c 5.0 0.0 2) (f32c 1.5 0.0 2) = true.   (* 10 >= 3 *)
Proof. vm_compute. reflexivity. Qed.
Example f32_geb_nan : f32_geb  (f32c 1.0 0.0 1) (f32_lit S754_nan) = false.  (* x >= NaN false *)
Proof. vm_compute. reflexivity. Qed.
Example f32_neq_ex  : f32_neqb (f32c 1.5 0.0 2) (f32c 5.0 0.0 2) = true.   (* 3 != 10 *)
Proof. vm_compute. reflexivity. Qed.
Definition f32_cmp_demo : IO unit :=
  println [ any (f32_ltb  (f32c 1.5 0.0 2) (f32c 5.0 0.0 2))    (* 3 < 10  → true *)
          ; any (f32_geb  (f32c 5.0 0.0 2) (f32c 1.5 0.0 2))    (* 10 >= 3 → true *)
          ; any (f32_neqb (f32c 1.5 0.0 2) (f32c 5.0 0.0 2)) ]. (* 3 != 10 → true *)
(** float64 → int64 TRUNCATION LOWERED: [i64_of_f64] → native Go [int64(f)] (truncates toward
    zero).  The model's [f64_trunc_Z] body (a direct [spec_float] decomposition) is suppressed; demoed through a
    typed-param wrapper so the cast applies to a VARIABLE ([int64(3.7)] on a constant is a Go
    compile error). *)
Definition trunc64 (x : GoFloat64) : GoI64 := i64_of_f64 x.
Definition i64_of_f64_demo : IO unit := println [ any (trunc64 3.7) ; any (trunc64 (f64_opp 2.9)) ].   (* 3 / -2 *)

(** float ↔ uint64 LOWERED — the UNSIGNED counterparts.  [u64_of_f64] → native [uint64(f)]
    (truncate toward zero, parallel to [i64_of_f64]); [f64_of_u64] → native [float64(v)]
    (correctly rounded — the model's single [binary_normalize] over the whole uint64 range is suppressed).
    These cover what [i64↔f64] cannot: a uint64 ABOVE [2^63] is a large POSITIVE double, not the
    negative an int64 reinterpret would give.  Machine-checked: low range exact ([255]); the
    uint64 MAX rounds to [2^64] ([binary_normalize] over the full range rounds correctly); and
    [float64 2^63 → uint64] succeeds where [int64] would overflow. *)
Example f64_of_u64_lo  : f64_eqb (f64_of_u64 (u64_lit 255 eq_refl)) 255 = true.
Proof. vm_compute. reflexivity. Qed.
Example f64_of_u64_max : f64_eqb (f64_of_u64 (u64_lit 18446744073709551615 eq_refl)) 18446744073709551616 = true.  (* → 2^64 *)
Proof. vm_compute. reflexivity. Qed.
Example u64_of_f64_big : u64raw (u64_of_f64 9223372036854775808) = 9223372036854775808%Z.  (* 2^63, beyond int64 *)
Proof. vm_compute. reflexivity. Qed.
Definition u64_trunc  (x : GoFloat64) : GoU64    := u64_of_f64 x.
Definition u64_to_f64 (x : GoU64)     : GoFloat64 := f64_of_u64 x.
Definition u64conv_demo : IO unit :=
  println [ any (u64_to_f64 (u64_lit 18446744073709551615 eq_refl))                    (* uint64 max → +1.844674e+019 (POSITIVE) *)
          ; any (u64_trunc (u64_to_f64 (u64_lit 13835058055282163712 eq_refl))) ].      (* round-trip 1.5·2^63 (exact) *)

Definition f64_of_int_demo : IO unit :=
  println [ any (f64_of_int (int_lit 5 eq_refl)) ; any (f64_of_int (int_lit (-3) eq_refl)) ].
  (* prints: +5.000000e+000 -3.000000e+000 (int → float64 cast) *)

(** GoI64 → float64 (Go [float64(i64)]) — NOW lowers too: same recognize-and-suppress as
    [f64_of_int], plus suppressing the [Z]→int63 helpers [of_Z]/[of_pos] its [Z] carrier
    drags (the [Z]/[positive] arithmetic was already suppressed by module).  It returns
    [float], so it stays a NAMED call — the lowering [f64_of_i64] left deferred is closed. *)
Definition f64_of_i64_demo : IO unit :=
  println [ any (f64_of_i64 (7)%i64) ; any (f64_of_i64 (-3)%i64) ].
  (* prints: +7.000000e+000 -3.000000e+000 (int64 → float64 cast) *)

(** float64 → int64 (Go [int64(f)]): TRUNCATE toward zero, via the direct [spec_float]
    ([S754_finite]) decomposition.  Machine-checked across the sign, the exact case, and zero. *)
Example i64_of_f64_pos   : i64_of_f64 3.7%go64       = (3)%i64.       Proof. vm_compute. reflexivity. Qed.
Example i64_of_f64_neg   : i64_of_f64 (-3.7)%go64    = (-3)%i64.      Proof. vm_compute. reflexivity. Qed.
Example i64_of_f64_exact : i64_of_f64 100%go64       = (100)%i64.     Proof. vm_compute. reflexivity. Qed.
Example i64_of_f64_zero  : i64_of_f64 0%go64         = (0)%i64.       Proof. vm_compute. reflexivity. Qed.
Example i64_of_f64_big   : i64_of_f64 1000000.9%go64 = (1000000)%i64. Proof. vm_compute. reflexivity. Qed.
(** LOWERED to native Go [int64(f)]: [i64_of_f64] is recognized by name; its [f64_trunc_Z]
    body — which decomposes the [spec_float] [S754_finite s m e] DIRECTLY (no [Prim2SF] /
    [normfr_mantissa] primitive, review #6 #13→zero-axioms) — is suppressed.  The MODEL is
    faithful and machine-checked above. *)


(** uint8 (byte): a precise, COMPUTABLE model of Go's 8-bit unsigned arithmetic.
    Each op masks the result back to [0,256), so it wraps mod 256 exactly like Go.
    The wrap is MACHINE-CHECKED (the model is just [Z.land]/[Z.add] on the [Z] carrier, which
    [vm_compute] reduces) — not asserted.  Note the contrast with [Nat.sub]: uint8
    subtraction genuinely WRAPS ([0 - 1 = 255]), which we model faithfully, whereas
    Coq's [Nat.sub] truncates ([0 - 1 = 0]) and is therefore rejected. *)
Example u8_add_wraps : u8_add (u8_lit 200 eq_refl) (u8_lit 100 eq_refl) = u8_lit 44 eq_refl.
Proof. reflexivity. Qed.                                      (* 300 mod 256 = 44 (reflexivity: GoU8's range proof is SProp — the VM can't decide proof-irrelevance, the kernel can) *)
Example u8_mul_wraps : u8_mul (u8_lit 255 eq_refl) (u8_lit 255 eq_refl) = u8_lit 1 eq_refl.
Proof. reflexivity. Qed.                                      (* 65025 mod 256 = 1 *)
Example u8_sub_wraps : u8_sub (u8_lit 0 eq_refl) (u8_lit 1 eq_refl) = u8_lit 255 eq_refl.
Proof. reflexivity. Qed.                                      (* 0 - 1 wraps to 255 *)
Definition u8_demo : IO unit :=
  bind (println [any (u8_add (u8_lit 200 eq_refl) (u8_lit 100 eq_refl))]) (fun _ =>   (* 44  *)
  bind (println [any (u8_mul (u8_lit 255 eq_refl) (u8_lit 255 eq_refl))]) (fun _ =>   (* 1   *)
  bind (println [any (u8_sub (u8_lit 0 eq_refl)   (u8_lit 1 eq_refl))])   (fun _ =>   (* 255 *)
  println [any (u8_ltb (u8_lit 10 eq_refl) (u8_lit 20 eq_refl))]))).                  (* true *)

(** int8 (signed): the SAME template extended to two's-complement.  [int8(150)] is
    [-106] (150 sign-extended from 8 bits), and the wrap is machine-checked.  The
    sign-extension is the harder case the model must get right. *)
Example i8_add_wraps : i8_add (i8_lit 100 eq_refl) (i8_lit 50 eq_refl) = i8_lit (-106) eq_refl.
Proof. reflexivity. Qed.                             (* 100+50=150 → -106 (reflexivity: GoI8 carries an SProp provenance proof) *)
Example i8_sub_wraps : i8_sub (i8_lit (-128) eq_refl) (i8_lit 1 eq_refl) = i8_lit 127 eq_refl.
Proof. reflexivity. Qed.                             (* -128 - 1 wraps to 127 *)
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
Proof. reflexivity. Qed.                        (* 1000000 mod 65536 = 16960 (reflexivity: GoU16 range proof is SProp) *)
Example i16_add_wraps : i16_add (i16_lit 30000 eq_refl) (i16_lit 10000 eq_refl) = i16_lit (-25536) eq_refl.
Proof. reflexivity. Qed.                        (* 40000 wraps to -25536 in int16 (reflexivity: GoI16 SProp provenance) *)
Definition u16_demo : IO unit :=
  bind (println [any (u16_add (u16_lit 60000 eq_refl) (u16_lit 10000 eq_refl))]) (fun _ =>   (* 4464 *)
  bind (println [any (u16_mul (u16_lit 1000 eq_refl)  (u16_lit 1000 eq_refl))])  (fun _ =>   (* 16960 *)
  println [any (i16_add (i16_lit 30000 eq_refl) (i16_lit 10000 eq_refl))])).                 (* -25536 *)

(** Bitwise operators (Go spec "Arithmetic operators": [& | ^ &^] and unary [^]).
    240 = 0b11110000, 60 = 0b00111100: AND=48, OR=252, XOR=204, AND-NOT=192,
    complement(240)=15.  Signed: [^int8(5) = -6], [int8(-1) &^ 5 = -6].  The
    MACHINE-CHECKED proofs below pin the values; this shows Go agreeing at run. *)
Example spec_u8_and    : u8_and    (u8_lit 240 eq_refl) (u8_lit 60 eq_refl) = u8_lit 48  eq_refl. Proof. reflexivity. Qed.
Example spec_u8_or     : u8_or     (u8_lit 240 eq_refl) (u8_lit 60 eq_refl) = u8_lit 252 eq_refl. Proof. reflexivity. Qed.
Example spec_u8_xor    : u8_xor    (u8_lit 240 eq_refl) (u8_lit 60 eq_refl) = u8_lit 204 eq_refl. Proof. reflexivity. Qed.
Example spec_u8_andnot : u8_andnot (u8_lit 240 eq_refl) (u8_lit 60 eq_refl) = u8_lit 192 eq_refl. Proof. reflexivity. Qed.
Example spec_u8_not    : u8_not    (u8_lit 240 eq_refl)                     = u8_lit 15  eq_refl. Proof. reflexivity. Qed.
Example spec_i8_not    : i8_not    (i8_lit 5 eq_refl)                       = i8_lit (-6) eq_refl. Proof. reflexivity. Qed.
Example spec_i8_andnot : i8_andnot (i8_lit (-1) eq_refl) (i8_lit 5 eq_refl) = i8_lit (-6) eq_refl. Proof. reflexivity. Qed.
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
Example spec_u8_shl     : u8_shl (u8_lit 1   eq_refl) (int_lit 3 eq_refl) eq_refl = u8_lit 8    eq_refl. Proof. reflexivity. Qed.
Example spec_u8_shl_ovf : u8_shl (u8_lit 1   eq_refl) (int_lit 8 eq_refl) eq_refl = u8_lit 0    eq_refl. Proof. reflexivity. Qed.
Example spec_u8_shr     : u8_shr (u8_lit 255 eq_refl) (int_lit 4 eq_refl) eq_refl = u8_lit 15   eq_refl. Proof. reflexivity. Qed.
Example spec_i8_shl_wrp : i8_shl (i8_lit 64  eq_refl) (int_lit 1 eq_refl) eq_refl = i8_lit (-128) eq_refl. Proof. reflexivity. Qed.
Example spec_i8_shr_flr : i8_shr (i8_lit (-3) eq_refl) (int_lit 1 eq_refl) eq_refl = i8_lit (-2) eq_refl. Proof. reflexivity. Qed.
Example spec_i8_shr_neg : i8_shr (i8_lit (-1) eq_refl) (int_lit 3 eq_refl) eq_refl = i8_lit (-1) eq_refl. Proof. reflexivity. Qed.
Definition shift_demo : IO unit :=
  bind (println [ any (u8_shl (u8_lit 1   eq_refl) (int_lit 3 eq_refl) eq_refl)      (* 8  *)
                ; any (u8_shl (u8_lit 1   eq_refl) (int_lit 8 eq_refl) eq_refl)      (* 0  (over-width) *)
                ; any (u8_shr (u8_lit 255 eq_refl) (int_lit 4 eq_refl) eq_refl) ])   (* 15 *)
       (fun _ =>
  println [ any (i8_shl (i8_lit 64  eq_refl) (int_lit 1 eq_refl) eq_refl)           (* -128 (wrap) *)
          ; any (i8_shr (i8_lit (-3) eq_refl) (int_lit 1 eq_refl) eq_refl) ]).      (* -2 (arithmetic) *)

(** Numeric conversions (Go spec "Conversions").  Widen ([int_of_*]) preserves the
    value; narrow ([*_of_int]) TRUNCATES to the width — Go's [uint8(x)]/[int8(x)].
    Distinct types mix ONLY through an explicit conversion (the type checker
    rejects implicit mixing — `*_no_implicit`, `u8_of_i16_direct` `Fail`s), so the
    conversions are what make the distinct numeric types usable together.
    MACHINE-CHECKED: [uint8(1000)=232] (mod 256), [uint8(-1)=255], [int8(200)=-56]
    (two's-complement), widen [int(uint8 200)=200], cross-width [int16(uint8 200)]. *)
Example spec_u8_of_int_trunc : u8_of_int (int_lit 1000 eq_refl)  = u8_lit 232 eq_refl. Proof. reflexivity. Qed.
Example spec_u8_of_int_neg   : u8_of_int (int_lit (-1) eq_refl) = u8_lit 255 eq_refl. Proof. reflexivity. Qed.
Example spec_i8_of_int_wrap  : i8_of_int (int_lit 200 eq_refl)  = i8_lit (-56) eq_refl. Proof. reflexivity. Qed.
Example spec_int_of_u8_widen : intraw (int_of_u8 (u8_lit 200 eq_refl)) = 200%Z. Proof. now vm_compute. Qed.
Example spec_i16_of_u8_cross : i16_of_int (int_of_u8 (u8_lit 200 eq_refl)) = i16_lit 200 eq_refl. Proof. reflexivity. Qed.
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
    small/large widths.  Lowering = Go's [int64(x)] widening (review #4 P1 #4; NOT identity — a
    narrow PARAM is a real [uint8]/[int8]/…, so [int64(x)] lands it in the [int64] destination,
    e.g. [func Widen(x uint8) int64 { return int64(x) }]).  The body is now a pure [Z] re-wrap
    ([i64wrap (uNraw a)] — [uNraw]/[iNraw] : narrow → [Z], no [Sint63.to_Z], no match): the
    **narrow-stored-in-Z** refactor that an earlier deep-dive deferred (the single-field records
    used to η-reduce a [to_Z] body into value position) is DONE (review #6 #13→zero-axioms), so
    it extracts cleanly with no banned-decl drag. *)
Example widen_u8  : i64_of_u8  (u8_lit 200 eq_refl)         = (200)%i64.        Proof. vm_compute. reflexivity. Qed.
Example widen_i8  : i64_of_i8  (i8_of_int (int_lit (-5) eq_refl))      = (-5)%i64.         Proof. vm_compute. reflexivity. Qed.
Example widen_u16 : i64_of_u16 (u16_lit 60000 eq_refl)      = (60000)%i64.      Proof. vm_compute. reflexivity. Qed.
Example widen_u32 : i64_of_u32 (u32_lit 4000000000 eq_refl) = (4000000000)%i64. Proof. vm_compute. reflexivity. Qed.
Example widen_i32 : i64_of_i32 (i32_of_int (int_lit (-7) eq_refl))     = (-7)%i64.         Proof. vm_compute. reflexivity. Qed.

(** Fixed-width division / remainder (Go spec "Arithmetic operators": [/ %]).
    Evidence-carrying: the divisor must be proven non-zero (`u8_div_zero` `Fail`).
    Signed division truncates toward zero (`-7/2 = -3`); the most-negative / `-1`
    case wraps two's-complement (`int8(-128)/int8(-1) = -128`). *)
Example spec_u8_div       : u8_div (u8_lit 200 eq_refl) (u8_lit 7 eq_refl) eq_refl = u8_lit 28 eq_refl. Proof. reflexivity. Qed.
Example spec_u8_mod       : u8_mod (u8_lit 200 eq_refl) (u8_lit 7 eq_refl) eq_refl = u8_lit 4  eq_refl. Proof. reflexivity. Qed.
Example spec_i8_div_trunc : i8_div (i8_lit (-7) eq_refl) (i8_lit 2 eq_refl) eq_refl = i8_lit (-3) eq_refl. Proof. reflexivity. Qed.
Example spec_i8_div_ovf   : i8_div (i8_lit (-128) eq_refl) (i8_lit (-1) eq_refl) eq_refl = i8_lit (-128) eq_refl. Proof. reflexivity. Qed.
Definition divmod_demo : IO unit :=
  println [ any (u8_div (u8_lit 200 eq_refl) (u8_lit 7 eq_refl) eq_refl)            (* 28 *)
          ; any (u8_mod (u8_lit 200 eq_refl) (u8_lit 7 eq_refl) eq_refl)            (* 4  *)
          ; any (i8_div (i8_lit (-128) eq_refl) (i8_lit (-1) eq_refl) eq_refl) ].   (* -128 (overflow) *)

(** uint32 / int32: the same template at width 32.  `4e9 + 1e9` wraps mod 2^32 →
    705032704; `2e9 + 2e9` wraps int32 → -294967296.  MULTIPLY is exact too: a
    32-bit product can exceed the 63-bit carrier, but the masked LOW 32 bits survive
    ([2^32 | 2^63]), so no Z model is needed — `100000*100000 = 1e10` wraps mod 2^32
    → 1410065408; `46341^2 = 2147488281 > 2^31` wraps int32 → -2147479015. *)
Example spec_u32_add_wrap : u32_add (u32_lit 4000000000 eq_refl) (u32_lit 1000000000 eq_refl) = u32_lit 705032704 eq_refl. Proof. reflexivity. Qed.
Example spec_i32_add_wrap : i32_add (i32_lit 2000000000 eq_refl) (i32_lit 2000000000 eq_refl) = i32_lit (-294967296) eq_refl. Proof. reflexivity. Qed.
Example spec_u32_mul_wrap : u32_mul (u32_lit 100000 eq_refl) (u32_lit 100000 eq_refl) = u32_lit 1410065408 eq_refl. Proof. reflexivity. Qed.
Example spec_u32_mul_max  : u32_mul (u32_lit 4294967295 eq_refl) (u32_lit 4294967295 eq_refl) = u32_lit 1 eq_refl. Proof. reflexivity. Qed.
Example spec_i32_mul_wrap : i32_mul (i32_lit 46341 eq_refl) (i32_lit 46341 eq_refl) = i32_lit (-2147479015) eq_refl. Proof. reflexivity. Qed.
Definition u32_demo : IO unit :=
  bind (println [ any (u32_add (u32_lit 4000000000 eq_refl) (u32_lit 1000000000 eq_refl))  (* 705032704 *)
                ; any (i32_add (i32_lit 2000000000 eq_refl) (i32_lit 2000000000 eq_refl)) ])  (* -294967296 *)
       (fun _ =>
  bind (println [ any (u32_shl (u32_lit 1 eq_refl) (int_lit 31 eq_refl) eq_refl) ])  (* 2147483648 = 2^31 *)
       (fun _ =>
  println [ any (u32_mul (u32_lit 100000 eq_refl) (u32_lit 100000 eq_refl))   (* 1410065408 *)
          ; any (i32_mul (i32_lit 46341 eq_refl) (i32_lit 46341 eq_refl)) ])).  (* -2147479015 *)

(** int64 — FULL-WIDTH signed 64-bit (Go spec "Numeric types"), the genuine
    Z-carried model.  Faithful across the WHOLE int64 range and wrapping at the TRUE
    2^63 — unlike the [Sint63] [int], which is faithful only within [-2^62, 2^62).
    [2^63-1 + 1] wraps to [-2^63]; [-2^63 - 1] wraps to [2^63-1]; [2^32 * 2^32 = 2^64]
    wraps to 0.  And a sum the OLD 2^62 model could not even represent is now exact. *)
Example spec_i64_add_wrap : i64_add (i64_lit 9223372036854775807 eq_refl) (i64_lit 1 eq_refl) = i64_lit (-9223372036854775808) eq_refl. Proof. reflexivity. Qed.
Example spec_i64_sub_wrap : i64_sub (i64_lit (-9223372036854775808) eq_refl) (i64_lit 1 eq_refl) = i64_lit 9223372036854775807 eq_refl. Proof. reflexivity. Qed.
Example spec_i64_mul_wrap : i64_mul (i64_lit 4294967296 eq_refl) (i64_lit 4294967296 eq_refl) = i64_lit 0 eq_refl. Proof. reflexivity. Qed.
Example spec_i64_beyond62 : i64_add (i64_lit 4611686018427387904 eq_refl) (i64_lit 4611686018427387903 eq_refl) = i64_lit 9223372036854775807 eq_refl. Proof. reflexivity. Qed.
(* No-overflow ⇒ EXACT, at the TRUE int64 width (the canonical overflow theorem;
   the bounded Sint63 version was removed when the int model migrated to GoI64). *)
Theorem i64_add_no_overflow_exact : forall a b : GoI64,
  in_i64 (i64raw a + i64raw b)%Z = true -> i64raw (i64_add a b) = (i64raw a + i64raw b)%Z.
Proof.
  intros [a] [b]. unfold in_i64, i64_add, i64wrap, wrap64. cbn. intros H.
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
Example spec_i64_div_trunc : i64_div (i64_lit (-7) eq_refl) (i64_lit 2 eq_refl) eq_refl = i64_lit (-3) eq_refl. Proof. reflexivity. Qed.
Example spec_i64_mod_sign  : i64_mod (i64_lit (-7) eq_refl) (i64_lit 2 eq_refl) eq_refl = i64_lit (-1) eq_refl. Proof. reflexivity. Qed.
Example spec_i64_div_ovf   : i64_div (i64_lit (-9223372036854775808) eq_refl) (i64_lit (-1) eq_refl) eq_refl = i64_lit (-9223372036854775808) eq_refl. Proof. reflexivity. Qed.
Example spec_i64_shl_wrap  : i64_shl (i64_lit 1 eq_refl) 63 eq_refl = i64_lit (-9223372036854775808) eq_refl. Proof. reflexivity. Qed.
Example spec_i64_shr_arith : i64_shr (i64_lit (-8) eq_refl) 1 eq_refl = i64_lit (-4) eq_refl. Proof. reflexivity. Qed.
Example spec_i64_and       : i64_and (i64_lit (-1) eq_refl) (i64_lit 255 eq_refl) = i64_lit 255 eq_refl. Proof. reflexivity. Qed.
Example spec_i64_not       : i64_not (i64_lit 5 eq_refl) = i64_lit (-6) eq_refl. Proof. reflexivity. Qed.
Definition i64_ops_demo : IO unit :=
  bind (println [ any (i64_div (i64_lit 9000000000000000000 eq_refl) (i64_lit 7 eq_refl) eq_refl)  (* 1285714285714285714 *)
                ; any (i64_shl (i64_lit 1 eq_refl) 40 eq_refl) ])  (* 1099511627776 = 2^40 *)
       (fun _ =>
  println [ any (i64_and (i64_lit (-1) eq_refl) (i64_lit 4294967295 eq_refl))   (* 4294967295 *)
          ; any (i64_not (i64_lit 5 eq_refl)) ]).  (* -6 *)

(** UNTYPED CONSTANTS (Go: a literal/constant EXPRESSION is ARBITRARY-PRECISION and untyped until
    it lands in a typed context, where it must be REPRESENTABLE there — else a COMPILE ERROR).
    Fido models this: a constant's argument is an exact [Z] expression and the constructor's
    FIT-PROOF *is* Go's representability check.  (1) CONSTANT EXPRESSIONS fold — [(1<<40)+5],
    [(1<<20)-1], [10^6 * 10^6] extract to their values (plugin [z_eval], checked-int64 with
    OVERFLOW = fail-loud, so an intermediate exceeding int64 never silently wraps — matching Go's
    arbitrary-precision constant fold); (2) ONE constant, MANY types — [100] at [int64] AND
    [uint8]; (3) overflow REJECTED at "compile time" — [2^63] has no [in_i64] proof, [300] no
    [<256] proof, so the literal can't be built and unsafe Go never extracts.  *(Scope: untyped
    INTEGER constants; default types and untyped float/rune constants remain.)* *)
Definition uc_bignum  : GoI64 := i64_lit (Z.shiftl 1 40 + 5) eq_refl.   (* (1<<40)+5 = 1099511627781 *)
Definition uc_mask    : GoI64 := i64_lit (Z.shiftl 1 20 - 1) eq_refl.   (* (1<<20)-1 = 1048575 (0xFFFFF) *)
Definition uc_product : GoI64 := i64_lit (1000000 * 1000000) eq_refl.   (* 10^12 = 1000000000000 *)
Definition uc_100_i64 : GoI64 := i64_lit 100 eq_refl.
Definition uc_100_u8  : GoU8  := u8_lit 100 eq_refl.              (* the SAME 100, typed uint8 *)
Definition uc_u64_hi  : GoU64 := u64_lit (Z.shiftl 1 63) eq_refl.     (* 2^63: a uint64 CONSTANT EXPRESSION beyond int64 max *)
Definition uc_u64_msk : GoU64 := u64_lit (Z.shiftl 1 32 - 1) eq_refl. (* (1<<32)-1 = 4294967295 *)
Example uc_i64_overflow : in_i64 9223372036854775808 = false. Proof. now vm_compute. Qed.  (* 2^63 ∉ int64 *)
Example uc_u8_overflow  : (300 <? 256)%Z = false.             Proof. now vm_compute. Qed.  (* 300 ∉ uint8 *)
Example uc_u64_hi_val   : u64raw uc_u64_hi = 9223372036854775808%Z. Proof. now vm_compute. Qed.
Definition uconst_demo : IO unit :=
  println [ any uc_bignum ; any uc_mask ; any uc_product ; any uc_100_i64 ; any uc_100_u8
          ; any uc_u64_hi ; any uc_u64_msk ].
  (* 1099511627781 1048575 1000000000000 100 100 9223372036854775808 4294967295 *)

(** ===== GoU64: FULL-WIDTH unsigned 64-bit integer =====
    Machine-checked witnesses:
    - [spec_u64_add_wrap]: 2^63 + 2^63 = 0 (mod 2^64) — the true unsigned wrap boundary.
    - [spec_u64_sub_wrap]: 0 - 1 = 2^64-1 — unsigned underflow wraps to max.
    - [spec_u64_not]:      ~0 = 2^64-1 (all 64 bits set).
    - [spec_u64_shr]:      8 >> 1 = 4 (logical right shift, not arithmetic).
    - [spec_u64_beyond63]: value > 2^62 unrepresentable in the old Sint63 model.
    All axiom-free (Print Assumptions = Closed under the global context). *)
Example spec_u64_add_wrap : u64_add (u64_lit 9223372036854775808%Z eq_refl) (u64_lit 9223372036854775808%Z eq_refl)
                            = u64_lit 0%Z eq_refl. Proof. reflexivity. Qed.
Example spec_u64_sub_wrap : u64_sub (u64_lit 0%Z eq_refl) (u64_lit 1%Z eq_refl)
                            = u64_lit 18446744073709551615%Z eq_refl. Proof. reflexivity. Qed.
Example spec_u64_not      : u64_not (u64_lit 0%Z eq_refl) = u64_lit 18446744073709551615%Z eq_refl. Proof. reflexivity. Qed.
Example spec_u64_shr      : u64_shr (u64_lit 8%Z eq_refl) 1 eq_refl = u64_lit 4%Z eq_refl. Proof. reflexivity. Qed.
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
  ch <-' make_chan_buf TI64 (int_lit 1 eq_refl) ;;
  send TI64 ch (77)%i64 >>'
  recv_ok TI64 ch (fun x _ => println [ any x ]).   (* prints: 77 *)

Definition i64_pipeline_demo : IO unit :=
  ch <-' make_chan_buf TI64 (int_lit 1 eq_refl) ;;
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
  ch <-' make_chan_buf TU64 (int_lit 1 eq_refl) ;;
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
Example spec_go_min       : intraw (go_min (int_lit 3 eq_refl) (int_lit 5 eq_refl)) = 3%Z. Proof. now vm_compute. Qed.
Example spec_go_max       : intraw (go_max (int_lit 3 eq_refl) (int_lit 5 eq_refl)) = 5%Z. Proof. now vm_compute. Qed.
Example spec_go_min_neg   : intraw (go_min (int_lit (-2) eq_refl) (int_lit 1 eq_refl)) = (-2)%Z. Proof. now vm_compute. Qed.
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
  bind (println [ any (go_min (int_lit 3 eq_refl) (int_lit 5 eq_refl)); any (go_max (int_lit 3 eq_refl) (int_lit 5 eq_refl)) ]) (fun _ =>  (* 3 5 — go_min/max BUILTIN demo on GoInt *)
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
Example spec_str_len_Go    : intraw (str_len "Go"%string)  = 2%Z. Proof. reflexivity. Qed.
Example spec_str_len_empty : intraw (str_len ""%string)    = 0%Z. Proof. reflexivity. Qed.
Example spec_str_concat    : str_concat "Go"%string "!"%string = "Go!"%string.
Proof. reflexivity. Qed.
(* Build-checked: a string does not implicitly accept an [int] (distinct types). *)
Fail Definition str_no_implicit : GoString := str_concat "x"%string (int_lit 5 eq_refl).

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

(** MAP REFERENCE SEMANTICS (aliasing): a [GoMap] passed to a function and mutated THERE is
    observed by the caller — Go maps are reference types (the heap model threads the write
    through the [World], so a callee's [map_set] persists).  [map_put] writes [m[7]=77]; the
    caller then reads [77].  A struct param would instead copy.  This exhibits at the FUNCTION
    BOUNDARY what [map_get_set_same] (builtins.v) proves about the heap; parallels
    [slice_alias_demo] / [ptr_alias_demo]. *)
Definition map_put (m : GoMap GoI64 GoI64) : IO unit := map_set TI64 TI64 (7)%i64 (77)%i64 m.
Definition map_alias_demo : IO unit :=
  bind (map_make_typed TI64 TI64) (fun m =>
  bind (map_put m) (fun _ =>                                              (* mutate via a function call *)
  bind (@map_get_or GoI64 GoI64 TI64 TI64 (7)%i64 (0)%i64 m) (fun v =>    (* caller observes the write *)
  println [any v]))).                                                     (* 77 *)

Definition slice_demo : IO unit :=
  let xs := slice_of_list TI64 [(1)%i64; (2)%i64; (3)%i64; (4)%i64; (5)%i64] in
  let n  := len xs in
  bind (slice_get TI64 xs (int_lit 2 eq_refl)) (fun v =>   (* xs[2] = 3, valid (index is Go int) *)
  println [any n; any v] >>'                      (* prints: 5 3 *)
  catch
    (bind (@slice_get GoI64 TI64 xs (int_lit 9 eq_refl)) (fun _ =>  (* xs[9] panics — OOB *)
     ret tt))
    (fun _ => println [any false])).              (* caught: prints false *)

(** Differential test — a SLICE boxed as [any] (via explicit [anyt], since [GoSlice] has no [Tagged]
    instance) then type-asserted.  Exercises the RECURSIVE [go_type_of_tag] for [TSlice TI64] → Go
    [ []int64 ] (previously UNEXERCISED): a []int64 interface value asserted TO []int64 SUCCEEDS and TO
    int64 FAILS — the composite tag rendering AGREES with Go's runtime type identity. *)
Definition slice_box_demo : IO unit :=
  let s := slice_of_list TI64 [(7)%i64; (8)%i64] in
  type_assert_safe (TSlice TI64) (anyt (TSlice TI64) s) (fun _ a =>   (* []int64 to []int64 → true  *)
  type_assert_safe TI64 (anyt (TSlice TI64) s) (fun _ b =>           (* []int64 to int64   → FALSE *)
    println [any a; any b])).   (* true false *)

(** Buffered channel: send 42, close, then recv_ok twice.
    First recv: value=42, ok=true  (buffered value still present after close).
    Second recv: value=0,  ok=false (channel drained and closed). *)
Definition chan_demo : IO unit :=
  ch <-' make_chan_buf TI64 (int_lit 1 eq_refl) ;;
  send TI64 ch (42)%i64 >>'
  close_chan TI64 ch >>'
  recv_ok TI64 ch (fun x ok =>                   (* prints: 42 true *)
  println [any x; any ok] >>'
  recv_ok TI64 ch (fun x2 ok2 =>
  println [any x2; any ok2])).

(** Differential test — channel-close PANICS at RUNTIME (the closed-world tenet's DEFENSE, for the
    open-world boundary).  Go panics on send-to-closed and on double-close; the model OPanics
    ([run_send_closed] / [run_close_closed]), and [catch] (Go defer/recover) catches BOTH — so the
    modeled panic and Go's runtime panic AGREE, and the defense is catchable.  (recv-from-closed is
    [chan_demo] above; this covers the two PANICKING close interactions.) *)
Definition closed_panic_demo : IO unit :=
  ch <-' make_chan_buf TI64 (int_lit 1 eq_refl) ;;
  close_chan TI64 ch >>'
  catch (send TI64 ch (5)%i64 >>' ret tt) (fun _ => println [any (1)%i64]) >>'  (* send-on-closed → panic → 1 *)
  catch (close_chan TI64 ch) (fun _ => println [any (2)%i64]).                   (* double-close → panic → 2 *)

(** select (Go spec "Select statements"): choose among ready channel ops.  [ch1]
    is buffered with 42 (ready), [ch2] is empty — so select picks [ch1].  (The
    choice is Go's at runtime; the demo makes exactly ONE case ready so the golden
    is stable.)  The lowering is a faithful Go [select { case … }]; the choice /
    blocking semantics is the tracked frontier (like [recv]'s blocking). *)
Definition select_demo : IO unit :=
  ch1 <-' make_chan_buf TI64 (int_lit 1 eq_refl) ;;
  ch2 <-' make_chan_buf TI64 (int_lit 1 eq_refl) ;;
  send TI64 ch1 (42)%i64 >>'
  select_recv2 TI64 ch1 (fun x => println [any x])     (* ch1 ready → 42 *)
               TI64 ch2 (fun y => println [any y]).

(** select with a default (the NON-BLOCKING form): [ch] is empty, so no case is
    ready and the [default] runs. *)
Definition select_default_demo : IO unit :=
  ch <-' make_chan_buf TI64 (int_lit 1 eq_refl) ;;
  select_recv_default TI64 ch (fun x => println [any x])   (* ch empty → default *)
                      (println [any (99)%i64]).            (* prints: 99 *)

(** Differential test — select over a CLOSED channel.  A closed-and-DRAINED channel's recv is READY in
    Go (it yields the zero value immediately), so the recv case fires and [default] is NOT taken — the
    select_recv_default code-review fix (2026-06-20; examining only the buffer mispredicted default for a
    closed channel).  Here [ch] is closed+empty: the recv case runs with the zero value (0), printing 0,
    NOT 99.  A regression to the pre-fix behaviour would print 99. *)
Definition select_closed_demo : IO unit :=
  ch <-' make_chan_buf TI64 (int_lit 1 eq_refl) ;;
  close_chan TI64 ch >>'                                   (* ch closed + empty *)
  select_recv_default TI64 ch (fun x => println [any x])   (* closed+drained ⇒ recv READY ⇒ 0 (not default) *)
                      (println [any (99)%i64]).

(** select as a NON-FINAL statement — `select … >>' rest`.  Same routing class as the type-switch
    fix: select is a pp_stmts-only form, so without a bind-action case it would fall to value position
    and the tag constructors fail.  Here a ready channel takes the recv case (3), then execution
    CONTINUES after the select (5). *)
Definition select_nonfinal_demo : IO unit :=
  ch <-' make_chan_buf TI64 (int_lit 1 eq_refl) ;;
  send TI64 ch (3)%i64 >>'
  select_recv_default TI64 ch (fun x => println [any x]) (println [any (99)%i64]) >>'  (* ch ready → 3 *)
  println [any (5)%i64].                                                                (* continues → 5 *)

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

(* R9 (review #3): the OLD record's PUBLIC [MkSess] could FORGE any protocol with a
   no-op body — [MkSess (ret tt) : Sess PingPong PEnd unit] claims a send-then-recv
   yet communicates nothing.  [Sess] is now a forge-proof INDUCTIVE: [MkSess] no
   longer exists, so the forgery is UNTYPABLE (the index cannot be detached from the
   operations).  This is the regression lock for the R9 deeper-fix migration. *)
Fail Definition bad_forge : Sess PingPong PEnd unit := MkSess (ret tt).

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
  bind (if int_ltb (int_lit 3 eq_refl) (int_lit 10 eq_refl)  then println [any (int_lit 1 eq_refl)] else println [any (int_lit 0 eq_refl)]) (fun _ =>
  bind (if int_ltb (int_lit 30 eq_refl) (int_lit 10 eq_refl) then println [any (int_lit 1 eq_refl)] else println [any (int_lit 0 eq_refl)]) (fun _ =>
  if int_ltb (int_lit 5 eq_refl) (int_lit 10 eq_refl)        then println [any (int_lit 1 eq_refl)] else println [any (int_lit 0 eq_refl)])).

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
  slice_at_ok TI64 xs (int_lit 1 eq_refl) (fun v ok =>      (* in bounds → 20 true *)
  println [any v; any ok] >>'
  slice_at_ok TI64 xs (int_lit 9 eq_refl) (fun v2 ok2 =>    (* above range → 0 false *)
  println [any v2; any ok2] >>'
  (* runtime-NEGATIVE index (sub 0 1 = -1) — a *constant* negative index is a Go
     compile error, so use a computed one; the lower-bound check must reject it.
     The index is a Go [int], so [sub] (Sint63) is kept for index arithmetic. *)
  slice_at_ok TI64 xs (sub (int_lit 0 eq_refl) (int_lit 1 eq_refl)) (fun v3 ok3 =>    (* negative (signed) → 0 false *)
  println [any v3; any ok3]))).

(** Array (Go spec "Array types"): a FIXED-SIZE [3]int64 VALUE.  [arr_lit] lowers to
    the [[3]int64{…}] literal (the size from the list length, not the Coq type), bound
    to a local whose Go type is INFERRED.  [arr_get_ok] is the bounds-checked read (Go
    arrays panic on OOB), identical lowering to [slice_at_ok].  Distinct from a slice:
    a fixed-size [N]T value (value-copy + comparability are later B4 pieces). *)
Definition arr_demo : IO unit :=
  let a := arr_lit TI64 [(10)%i64; (20)%i64; (30)%i64] in   (* [3]int64{10,20,30} *)
  arr_get_ok TI64 a (int_lit 1 eq_refl) (fun v ok =>        (* a[1] in bounds → 20 true *)
  println [any v; any ok] >>'
  (* a CONSTANT out-of-range index on an array is a Go COMPILE error (arrays are
     statically bounds-checked, unlike slices), so use a COMPUTED index [sub 10 5 = 5]
     (lowers to a runtime [Sub(10,5)]); [arr_get_ok]'s guard then rejects it at runtime *)
  arr_get_ok TI64 a (sub (int_lit 10 eq_refl) (int_lit 5 eq_refl)) (fun v2 ok2 =>     (* a[5] out of range → 0 false *)
  println [any v2; any ok2])).

(** Array in a TYPED POSITION (the previously fail-loud case): [GoArr3 GoI64] = Go [[3]int64], the
    size carried in the TYPE.  [vecN_a]/[vecN_b] emit [var … [3]int64 = [3]int64{…}]; [vec3_eqb]'s
    PARAMETERS are [[3]int64] — a typed position that previously ABORTED extraction — and the
    comparison lowers to field-wise [==].  The constructor takes exactly 3 elements, so length 3
    is guaranteed (no wrong-length literal). *)
Definition vecN_a : GoArr3 GoI64 := arr3_lit TI64 (10)%i64 (20)%i64 (30)%i64.
Definition vecN_b : GoArr3 GoI64 := arr3_lit TI64 (10)%i64 (20)%i64 (99)%i64.
Definition vec3_eqb (a b : GoArr3 GoI64) : bool := arr3_eqb a b.  (* params lower to [3]int64 *)
Definition pairN  : GoArr2 GoI64 := arr2_lit TI64 (7)%i64 (8)%i64.  (* GoArr2 → [2]int64 (any N works) *)
Definition vec2_eqb (a b : GoArr2 GoI64) : bool := arr2_eqb a b.
Definition arrN_demo : IO unit :=
  println [ any (vec3_eqb vecN_a vecN_a) ; any (vec3_eqb vecN_a vecN_b) ; any (vec2_eqb pairN pairN) ].   (* true false true *)

(** Array RETURN + array FIELD positions — completing the typed-position coverage beyond [arrN_demo]'s
    typed-VAR + PARAM.  [vec3_id]'s RETURN type is [[3]int64]; [Triple] has an array FIELD
    [t_vec : [3]int64] (emitted [type Triple struct { T_vec [3]int64; T_label int64 }]).  Both ride the
    same [GoArr<N>]→[[N]T] [pp_type] rendering — no new plugin support, any concrete N. *)
Definition vec3_id (a : GoArr3 GoI64) : GoArr3 GoI64 := a.
Record Triple := MkTriple { t_vec : GoArr3 GoI64 ; t_label : GoI64 }.
Definition arr_field_ret_demo : IO unit :=
  let tr := MkTriple (arr3_lit TI64 (4)%i64 (5)%i64 (6)%i64) (77)%i64 in
  bind (println [any (vec3_eqb (vec3_id (t_vec tr)) (t_vec tr))]) (fun _ =>   (* field → return-id → compare: true *)
  println [any (t_label tr)]).                                                (* the struct's int64 field: 77 *)

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
  arr_data (arr_set 3 TI64 (arr_lit TI64 [(10)%i64;(20)%i64;(30)%i64]) (int_lit 0 eq_refl) (99)%i64 eq_refl)
  = [(99)%i64;(20)%i64;(30)%i64].
Proof. reflexivity. Qed.
(** Review #6 P1 #11 / minimum-suite #7: [mkArr3 []] is UNCONSTRUCTABLE (its length proof
    [length [] = 3] is unprovable) — every GoArr3 genuinely has length 3; and an out-of-range
    [arr_set] is rejected (its bounds proof [0 <= 5 < 3] is unprovable). *)
Example arr3_has_length_3 : forall {A} (a : GoArr3 A), List.length (arr3_data a) = 3%nat.
Proof. intros A a. exact (arr3_len a). Qed.
Fail Definition mkArr3_wrong_length : GoArr3 GoI64 := mkArr3 nil eq_refl.
Fail Definition arr_set_oob : GoArray GoI64 :=
  arr_set 3 TI64 (arr_lit TI64 [(10)%i64;(20)%i64;(30)%i64]) (int_lit 5 eq_refl) (99)%i64 eq_refl.
Definition arr_copy_demo : IO unit :=
  let a := arr_lit TI64 [(10)%i64; (20)%i64; (30)%i64] in
  let b := arr_set 3 TI64 a (int_lit 0 eq_refl) (99)%i64 eq_refl in   (* b = a with [0]=99; a UNCHANGED (value-copy) *)
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
  str_at_ok s (int_lit 0 eq_refl) (fun b ok =>                (* 71 ('G') true *)
  println [any b; any ok] >>'
  str_at_ok s (int_lit 5 eq_refl) (fun b2 ok2 =>              (* out of range → 0 false *)
  println [any b2; any ok2] >>'
  println [any (str_concat s "!"%string)])).        (* Go! *)

(** String COMPARISON (Go [==] / [<]): byte-sequence equality and lexicographic
    byte ordering.  Lowers to the bare Go operators on string operands. *)
Definition str_cmp_demo : IO unit :=
  println [ any (str_eqb "Go"%string "Go"%string)    (* true  *)
          ; any (str_eqb "Go"%string "No"%string)    (* false *)
          ; any (str_ltb "abc"%string "abd"%string)  (* true  *)
          ; any (str_ltb "b"%string "a"%string) ].   (* false *)

(** Differential test — string comparison is UNSIGNED byte-wise (the classic signed/unsigned trap).
    A string whose first byte is 200 (0xC8, ≥ 128): Go compares bytes as uint8, so "z" (0x7A=122) <
    that string.  A naive SIGNED byte compare would read 200 as -56 and FLIP it.  [str_ltb] uses
    [PrimInt63.ltb] on the 0–255 byte (unsigned), agreeing with Go's native [<].  (Bytes ≥ 128 were
    only covered for ASCII by [spec_str_lt_*].) *)
Definition str_highbyte_demo : IO unit :=
  let hi := str_from_bytes (slice_of_list TU8 [u8_lit 200 eq_refl]) in   (* 1-byte string, byte 0xC8 *)
  println [ any (str_ltb "z"%string hi)        (* 0x7A < 0xC8 → true  (unsigned) *)
          ; any (str_ltb hi "z"%string) ].     (* 0xC8 < 0x7A → false *)

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

(** Differential test — type SWITCH respects the break-#7 DISTINCTNESS (uint8 vs int64 are different
    Go cases).  A boxed uint8 hits `case uint8:` (not `case int64:`), and a boxed int64 hits
    `case int64:`.  This is a DIFFERENT dispatch from type-assert (a multi-case switch), so it checks
    the same distinctness through the switch path. *)
Definition tsw_narrow (a : GoAny) : IO unit :=
  type_switch2 a
    TU8  (fun u => println [any (i64_of_u8 u)])     (* case uint8 → widen → print *)
    TI64 (fun i => println [any i])                  (* case int64 → print *)
    (println [any (9)%i64]).                          (* default *)
Definition tsw_distinct_demo : IO unit :=
  bind (tsw_narrow (any (u8_of_i64 (i64_lit 200 eq_refl)))) (fun _ =>   (* uint8 → 200 *)
        tsw_narrow (any (i64_lit 7 eq_refl))).                          (* int64 → 7  *)

(** The fail-closed gap from the previous tick — a type-switch on an INLINE boxed scrutinee, and as a
    NON-FINAL statement — now lowers correctly (two coordinated go.ml fixes): the inline `any x` is
    RE-BOXED so `.(type)` is on an interface, and a `type_switch … >>' rest` action is routed to
    statement position (it previously fell to value position and the tag constructors failed). *)
Definition tsw_inline_demo : IO unit :=
  type_switch2 (any (u8_of_i64 (i64_lit 200 eq_refl)))   (* INLINE boxed scrutinee, NON-FINAL switch *)
    TU8  (fun u => println [any (i64_of_u8 u)])          (* uint8 → 200 *)
    TI64 (fun i => println [any i])
    (println [any (9)%i64]) >>'
  println [any (5)%i64].                                  (* continues AFTER the switch → 5 *)

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
  let c := go_complex (1.5)%go64 (2.5)%go64 in
  println [any (go_real c); any (go_imag c)].   (* the two components (Go float format) *)

(** Complex [+] / [-] (component-wise, native Go operators): (1+2i)+(3+4i) = 4+6i,
    (1+2i)-(3+4i) = -2-2i.  Extract each component to print. *)
Definition complex_arith_demo : IO unit :=
  let a := go_complex (1.0)%go64 (2.0)%go64 in
  let b := go_complex (3.0)%go64 (4.0)%go64 in
  let s := complex_add a b in
  let d := complex_sub a b in
  println [any (go_real s); any (go_imag s); any (go_real d); any (go_imag d)].

(** Complex unary [-] (component-wise sign-flip, native operator): -(3+4i) = -3-4i. *)
Definition complex_neg_demo : IO unit :=
  let c := go_complex (3.0)%go64 (4.0)%go64 in
  let n := complex_neg c in
  println [any (go_real n); any (go_imag n)].   (* -3 -4 *)
(** REGRESSION (code review): complex ops on CONSTANTS must extract as RUNTIME IEEE — Go constants
    cannot denote a complex -0/±Inf/NaN, and constant /0 fails to compile (the complex parallel of the
    float constant-vs-runtime fix).  [complex_neg] / [complex_add/sub/mul/div] are now forced to
    runtime via typed IIFEs unless an operand is a runtime variable. *)
Example complex_neg_negzero :   (* real(-complex(0,0)) = -0, so 1/that = -Inf (was +Inf: const -0 → +0) *)
  f64_eqb (f64_div 1 (go_real (complex_neg (go_complex 0 0))))
                (f64_div 1 (f64_opp 0)) = true.
Proof. vm_compute. reflexivity. Qed.
Definition complex_const_runtime_demo : IO unit :=
  println [ any (f64_div 1 (go_real (complex_neg (go_complex 0 0)))) ].   (* -Inf (complex -0 preserved at runtime) *)

(** Complex [*] (gc's naive cross-product, native operator): (1+2i)*(3+4i) = -5+10i. *)
Definition complex_mul_demo : IO unit :=
  let a := go_complex (1.0)%go64 (2.0)%go64 in
  let b := go_complex (3.0)%go64 (4.0)%go64 in
  let p := complex_mul a b in
  println [any (go_real p); any (go_imag p)].   (* -5 10 *)

(** Complex [/] (Smith's algorithm = gc's runtime.complex128div, native operator):
    (1+2i)/(3+4i) = 0.44 + 0.08i. *)
Definition complex_div_demo : IO unit :=
  let a := go_complex (1.0)%go64 (2.0)%go64 in
  let b := go_complex (3.0)%go64 (4.0)%go64 in
  let q := complex_div a b in
  println [any (go_real q); any (go_imag q)].   (* 0.44 0.08 *)

(** Complex [==] / [!=] (component-wise, native operators): equal complexes compare equal,
    a differing imaginary part makes them unequal. *)
Definition complex_cmp_demo : IO unit :=
  let a := go_complex (1.0)%go64 (2.0)%go64 in
  let b := go_complex (1.0)%go64 (2.0)%go64 in
  let c := go_complex (1.0)%go64 (3.0)%go64 in
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
  println [any (rune_to_str (i32wrap 65))].   (* string(rune(65)) → "A" *)

(** Go [for i, r := range s]: [i] the BYTE offset of each code point, [r] the rune.
    Byte offsets are faithful to UTF-8 widths — for [A 中 B] (1/3/1 bytes) the offsets are
    [0 1 4], machine-checked here on the model; [str_range] lowers to the native two-variable
    range loop.  The decode round-trips ([str_to_runes ∘ runes_to_str = id], [rune_roundtrip_*]). *)
Example str_range_offsets :
  List.map (fun p => (intraw (fst p), snd p))
    (runes_with_offsets (int_lit 0 eq_refl)
      (str_to_runes_w (runes_to_str (i32wrap 65 :: i32wrap 20013 :: i32wrap 66 :: nil))))
  = (0%Z, i32wrap 65) :: (1%Z, i32wrap 20013) :: (4%Z, i32wrap 66) :: nil.
Proof. vm_compute. reflexivity. Qed.
(** Review #6 P1 #9 / minimum-suite #3: INVALID UTF-8 byte offsets.  Source bytes [0x80 'A'] —
    a lone continuation, then 'A'.  Go's range yields [(0,U+FFFD) (1,'A')]: the bad byte consumed
    exactly ONE source byte, so 'A' is at offset 1 — NOT 3, which re-encoding U+FFFD (3 bytes)
    would have wrongly given.  This is the offset bug the consumed-width decoder fixes. *)
Example str_range_invalid_offsets :
  List.map (fun p => (intraw (fst p), snd p))
    (runes_with_offsets (int_lit 0 eq_refl)
      (str_to_runes_w (String (byte_chr 128) (String (byte_chr 65) EmptyString))))
  = (0%Z, i32wrap 65533) :: (1%Z, i32wrap 65) :: nil.
Proof. vm_compute. reflexivity. Qed.
Definition str_range_demo : IO unit :=
  str_range (str_concat (rune_to_str (i32wrap 72))
            (str_concat (rune_to_str (i32wrap 8364))
                        (rune_to_str (i32wrap 33))))   (* "H€!" — H(1 byte) €(3) !(1) *)
    (fun i r => println [any i; any r]).   (* 0 72 / 1 8364 / 4 33 (byte offset, rune) *)

(** Capture in a goto loop: each iteration defers [println iv].  The loop-temp
    [iv] is captured BY VALUE per iteration, so the deferred calls (LIFO at
    return) print 2, 1, 0 — not 2, 2, 2 (which a shared cell would give). *)
Definition defer_loop_demo : IO unit :=
  bind (ref_new TInt64 (int_lit 0 eq_refl)) (fun i =>
  run_blocks 0%nat [
    bind (ref_get TInt64 i) (fun iv =>
      if int_ltb iv (int_lit 3 eq_refl) then
        bind (defer_call (println [any iv]))  (fun _ =>
        bind (ref_set i (add iv (int_lit 1 eq_refl)))           (fun _ =>
        ret (Jump 0%nat)))
      else ret (Jump 1%nat)) ;
    ret Done
  ]).

(** Function-scoped defer: [defer_call] runs at function return, LIFO across all
    defers — distinct from block-scoped [with_defer].  Prints 3, then 2, then 1. *)
Definition defer_demo : IO unit :=
  bind (defer_call (println [any (int_lit 1 eq_refl)])) (fun _ =>   (* runs 3rd (LIFO) *)
  bind (defer_call (println [any (int_lit 2 eq_refl)])) (fun _ =>   (* runs 2nd *)
  println [any (int_lit 3 eq_refl)])).                               (* runs now *)

(** Mutable local variable: declare, read, reassign, read again — straight-line
    (no control flow, so trivially scope-correct). *)
Definition mut_demo : IO unit :=
  bind (ref_new TInt64 (int_lit 10 eq_refl))        (fun r =>  (* r := 10        *)
  bind (ref_get TInt64 r)          (fun a =>  (* a := r  (= 10) *)
  bind (ref_set r (add a (int_lit 5 eq_refl)))       (fun _ =>  (* r = a + 5 (= 15) *)
  bind (ref_get TInt64 r)          (fun b =>  (* b := r  (= 15) *)
  println [any b])))).                         (* prints 15 *)

(** Narrow [Ref] type-IDENTITY (P1 #4 narrow-Ref residual): a [Ref GoU8] now lowers to a Go [uint8]
    cell, not the [int64] carrier — so a value read back, boxed, and asserted resolves to [uint8] (true)
    NOT [int64] (false), agreeing with the model's [TU8] tag.  [ref_new TU8] casts the init via its tag;
    [ref_set] casts via the value's own narrow type.  Without the fix the cell was [int64] (`false true`).
    The numeric value (7) was always right — this locks the previously-latent type identity. *)
Definition narrow_ref_demo : IO unit :=
  bind (ref_new TU8 (u8_of_i64 (i64_lit 200 eq_refl))) (fun r =>   (* r := uint8(200) *)
  bind (ref_set r (u8_of_i64 (i64_lit 7 eq_refl)))      (fun _ =>   (* r = uint8(7) *)
  bind (ref_get TU8 r)                                  (fun v =>   (* v := r  (uint8 7) *)
  type_assert_safe TU8 (any v)  (fun _ okU =>                        (* assert uint8 → true  *)
  type_assert_safe TI64 (any v) (fun _ okI =>                        (* assert int64 → false *)
  println [any okU; any okI]))))).                                   (* true false *)

(** Phase B1: POINTERS (Go spec "Pointer types").  [ptr_new] allocates a fresh
    [*int64] holding 10; [*p] reads it; [*p = v] writes through it.  Distinct from a
    [Ref] (a local var): a [Ptr] lowers to Go [*T], so a COPY of the pointer aliases
    the SAME cell — the [ptr_alias] THEOREM (builtins.v) proves a write through one
    handle is seen through another.  Read-after-write is [ptr_get_set_same]. *)
Definition ptr_demo : IO unit :=
  bind (ptr_new TI64 (10)%i64) (fun p =>      (* p := new(int64) ← 10 *)
  bind (ptr_get TI64 p)        (fun a =>      (* a := *p  (= 10) *)
  bind (println [any a])       (fun _ =>      (* prints 10 *)
  bind (ptr_set TI64 p (99)%i64) (fun _ =>    (* *p = 99 *)
  bind (ptr_get TI64 p)        (fun b =>      (* b := *p  (= 99) *)
  println [any b]))))).                        (* prints 99 *)

(** Phase B1d: [&x] — the ADDRESS-OF operator (Go's `&`).  [&x] takes the address of a LOCAL
    variable [x] (a [Ref], which lowers to an addressable Go var), yielding a [*int64] that ALIASES
    x's cell.  Passing [&x] to a mutator ([write_thru]) and writing THROUGH the pointer changes [x]
    itself — the defining reason `&` exists in Go (a callee mutating a caller's variable).  [&x] is
    provably NEVER nil ([ref_as_ptr_not_nil], builtins.v), so the deref is safe; that the write is
    visible at [x] is [ptr_set_ref_as_ptr_aliases].  Lowers to Go [write_thru(&x)]. *)
Definition write_thru (p : Ptr GoI64) : IO unit :=
  ptr_set TI64 p (99)%i64.                     (* *p = int64(99) *)
Definition addr_of_demo : IO unit :=
  bind (ref_new TI64 (10)%i64) (fun x =>       (* x := int64(10) *)
  bind (ref_get TI64 x)        (fun a =>       (* a := x  (= 10) *)
  bind (println [any a])       (fun _ =>       (* prints 10 *)
  bind (write_thru (ref_as_ptr x)) (fun _ =>   (* write_thru(&x) — mutate x through its address *)
  bind (ref_get TI64 x)        (fun b =>       (* b := x  (= 99, aliased through &x!) *)
  println [any b]))))).                         (* prints 99 *)

(** Differential test — a POINTER boxed as [any] then type-asserted.  Exercises the RECURSIVE
    [go_type_of_tag] ([TPtr TI64] → Go [*int64], the pointer-as-interface case, previously
    UNEXERCISED): a [*int64] interface value asserted TO [*int64] SUCCEEDS and TO [int64] FAILS, so the
    composite tag rendering AGREES with Go's runtime type identity (model [tag_eq] vs runtime assert). *)
Definition ptr_box_demo : IO unit :=
  bind (ptr_new TI64 (10)%i64) (fun p =>
  type_assert_safe (TPtr TI64) (any p) (fun _ a =>    (* assert *int64 to *int64 → true  *)
  type_assert_safe TI64 (any p) (fun _ b =>           (* assert *int64 to int64  → FALSE *)
    println [any a; any b]))).   (* true false *)

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

(** Phase B1c: a POINTER over a CHANNEL ([chan *int64]) — unlocked by [TPtr] (the pointer
    [GoTypeTag], 2026-06-21).  [p := new(int64) ← 7]; send [p] over [ch]; receive [q] (an ALIAS of
    [p], same cell); [*q = 7].  A [*T] is now a first-class channel payload / [any] box / map element
    (it rides the same tag machinery as scalars — [Tagged_ptr] infers [TPtr (the_tag T)]). *)
Definition ptr_chan_demo : IO unit :=
  bind (ptr_new TI64 (7)%i64)        (fun p =>      (* p := new(int64) ← 7 *)
  bind (make_chan_buf (TPtr TI64) (int_lit 1 eq_refl)) (fun ch =>     (* ch := make(chan *int64, 1) *)
  bind (send (TPtr TI64) ch p)       (fun _ =>      (* ch <- p *)
  bind (recv (TPtr TI64) ch)         (fun q =>      (* q := <-ch  (aliases p) *)
  bind (ptr_get TI64 q)              (fun v =>      (* v := *q  (= 7) *)
  println [any v]))))).                              (* prints 7 *)

(** A CHANNEL nested in a STRUCT (Go's worker/inbox pattern: [type Inbox struct { ch chan int64;
    name string }]).  The struct holds the channel HANDLE — a reference type, so copying the struct
    SHARES the channel — and send/recv flow through the field [box.Ib_ch].  A first step toward the
    north-star nesting (channels inside structs / slices). *)
Record Inbox := MkInbox { ib_ch : GoChan GoI64 ; ib_name : GoString }.
Definition inbox_demo : IO unit :=
  bind (make_chan_buf TI64 (int_lit 1 eq_refl))            (fun ch =>   (* ch := make(chan int64, 1) *)
  let box := MkInbox ch "fido"%string in              (* box := Inbox{Ib_ch: ch, Ib_name: "fido"} *)
  bind (send TI64 (ib_ch box) (42)%i64)  (fun _ =>    (* box.Ib_ch <- 42 *)
  recv_ok TI64 (ib_ch box) (fun v _ =>                (* v := <-box.Ib_ch *)
  println [any (ib_name box); any v]))).               (* prints: fido 42 *)

(** Deeper north-star nesting: a SLICE of CHANNELS inside a STRUCT (Go's [type Hub struct {
    chans []chan int64; id int64 }]) — channels in a slice in a struct.  Build the slice with the
    channel element tag [TChan TI64], index it to a channel ([hub.Hub_chans[1]], bounds-checked),
    then send/recv on that channel.  (A slice of STRUCTS would need a named-type tag — deferred;
    a slice of CHANNELS works because [TChan TI64] is a real tag.) *)
Record Hub := MkHub { hub_chans : GoSlice (GoChan GoI64) ; hub_id : GoI64 }.
Definition hub_demo : IO unit :=
  bind (make_chan_buf TI64 (int_lit 1 eq_refl)) (fun ch0 =>
  bind (make_chan_buf TI64 (int_lit 1 eq_refl)) (fun ch1 =>
  let hub := MkHub (slice_of_list (TChan TI64) [ch0; ch1]) (7)%i64 in   (* Hub{[]chan int64{ch0,ch1}, 7} *)
  bind (slice_get (TChan TI64) (hub_chans hub) (int_lit 1 eq_refl)) (fun c =>       (* c := hub.Hub_chans[1] (= ch1) *)
  bind (send TI64 c (99)%i64) (fun _ =>                                  (* c <- 99 *)
  recv_ok TI64 c (fun v _ =>                                             (* v := <-c *)
  println [any (hub_id hub); any v]))))).                                (* prints: 7 99 *)

(** Concurrency OVER the nesting: a GOROUTINE sends through a channel that lives in a STRUCT field
    ([go func(){ box.Ib_ch <- 123 }(); v := <-box.Ib_ch]) — the worker pattern (a goroutine feeding a
    struct's channel), combining [go_spawn] with the channel-in-struct nesting.  Unbuffered, so the
    send/recv RENDEZVOUS makes the result deterministic. *)
Definition hub_worker_demo : IO unit :=
  bind (make_chan TI64) (fun ch =>
  let box := MkInbox ch "worker"%string in
  bind (go_spawn (send TI64 (ib_ch box) (123)%i64)) (fun _ =>   (* go func(){ box.Ib_ch <- 123 }() *)
  bind (recv TI64 (ib_ch box)) (fun v =>                        (* v := <-box.Ib_ch (rendezvous) *)
  println [any (ib_name box); any v]))).                        (* prints: worker 123 *)

(** "Channels that send themselves" (the user's north-star phrasing): a CHANNEL OF CHANNELS
    ([chan chan int64]) — the request/reply pattern.  The main sends a [reply] channel OVER the
    [reqs] channel; a worker goroutine receives that reply-channel and sends a result back through
    it — a channel VALUE flows over a channel.  Buffered + the data dependency ⇒ deterministic. *)
Definition chan_of_chan_demo : IO unit :=
  bind (make_chan_buf (TChan TI64) (int_lit 1 eq_refl)) (fun reqs =>            (* reqs : chan chan int64 *)
  bind (make_chan_buf TI64 (int_lit 1 eq_refl))         (fun reply =>           (* reply : chan int64 *)
  bind (go_spawn (bind (recv (TChan TI64) reqs) (fun r => send TI64 r (77)%i64))) (fun _ =>
  bind (send (TChan TI64) reqs reply) (fun _ =>              (* reqs <- reply (a channel over a channel) *)
  recv_ok TI64 reply (fun v _ =>                             (* v := <-reply *)
  println [any v]))))).                                       (* prints: 77 *)

(** CAPSTONE — ONE program nesting the lot: a STRUCT [Pool] holding a SLICE of CHANNELS, a GOROUTINE
    per channel feeding it, the struct's slice INDEXED to recover each channel, the results collected
    concurrently and summed.  Buffered + the data dependency ⇒ deterministic.  "Horrifying-but-correct":
    [struct { []chan int64 ; int64 }] + 2 goroutines + slice-index + recv + arithmetic, all from the
    shipped features composing as Go nests them — and the whole thing is a single extracted Go func. *)
Record Pool := MkPool { pool_chans : GoSlice (GoChan GoI64) ; pool_base : GoI64 }.
Definition pool_demo : IO unit :=
  c0 <-' make_chan_buf TI64 (int_lit 1 eq_refl) ;;
  c1 <-' make_chan_buf TI64 (int_lit 1 eq_refl) ;;
  go_spawn (send TI64 c0 (5)%i64) >>'                         (* worker 0: c0 <- 5 *)
  go_spawn (send TI64 c1 (7)%i64) >>'                         (* worker 1: c1 <- 7 *)
  let pool := MkPool (slice_of_list (TChan TI64) [c0; c1]) (10)%i64 in
  ch0 <-' slice_get (TChan TI64) (pool_chans pool) (int_lit 0 eq_refl) ;; (* ch0 := pool.Pool_chans[0] *)
  ch1 <-' slice_get (TChan TI64) (pool_chans pool) (int_lit 1 eq_refl) ;; (* ch1 := pool.Pool_chans[1] *)
  v0 <-' recv TI64 ch0 ;;                                     (* v0 := <-ch0 (= 5) *)
  v1 <-' recv TI64 ch1 ;;                                     (* v1 := <-ch1 (= 7) *)
  println [any (i64_add (pool_base pool) (i64_add v0 v1))].   (* 10 + (5+7) = 22 *)

(** RECURSIVE / self-referential type — the north-star FRONTIER, now OPERATED on, not just declared.
    [ListNode] (builtins.v) is [type ListNode struct { Val int64 ; Next *ListNode }] — a struct that
    points to ITSELF.  The previous tick DECLARED the type (a single nil-[next] node, no tag); this tick
    CRACKS the recursive type TAG: [TListNode] is a NULLARY nominal tag — FINITE, not the feared cyclic
    [tag = TPtr tag] (the field's tag is the finite [TPtr TListNode]).  With the tag, a [*ListNode] cell
    lives in the typed heap, so a genuine 3-node singly-linked list is heap-ALLOCATED ([ptr_new TListNode],
    tail-first), pointer-CHAINED, then TRAVERSED head→tail via [ptr_get]/[ln_next] — a real linked list,
    allocated + linked + walked, axiom-free, extracted to ordinary Go. *)
Definition linked_list_demo : IO unit :=
  p3 <-' ptr_new TListNode (MkListNode (3)%i64 (ptr_nil_tf tt)) ;;   (* tail: ListNode{3, nil}       *)
  p2 <-' ptr_new TListNode (MkListNode (2)%i64 p3) ;;                (* mid : ListNode{2, &tail}     *)
  p1 <-' ptr_new TListNode (MkListNode (1)%i64 p2) ;;               (* head: ListNode{1, &mid}      *)
  n1 <-' ptr_get TListNode p1 ;;                                    (* *p1                          *)
  n2 <-' ptr_get TListNode (ln_next n1) ;;                          (* *(p1.Next) — follow the link *)
  n3 <-' ptr_get TListNode (ln_next n2) ;;                          (* *(p2.Next) — follow again    *)
  println [any (ln_val n1) ; any (ln_val n2) ; any (ln_val n3)].    (* prints: 1 2 3 *)

(** "A CHANNEL THAT SENDS ITSELF" — the north-star horror, realized.  [ChanBox] (builtins.v) is
    [type ChanBox struct { Id int64 ; Ch chan ChanBox }]; a [chan ChanBox] carries a [ChanBox] whose
    [Ch] field IS that very channel, so the channel transmits a value containing ITSELF.  (Stronger than
    [chan_of_chan_demo]'s [chan chan int64], where the element is a DIFFERENT type — here the element type
    contains the channel's own type.)  Recursion through the tag-free phantom [GoChan] + the NULLARY
    nominal tag [TChanBox] (finite; the channel-of-itself tag is the finite [TChan TChanBox]).  A goroutine
    sends the self-box; main receives it and reads the id — built from safe channel APIs (no [close], so
    send-on-closed is unexpressible) and structurally race-free (one sender, one receiver, no shared
    writes), yet self-sending.  (As with [cursed_demo], a per-program formal race-freedom proof is the
    limit-#2 frontier; the feature safety is machine-checked.) *)
Definition chanbox_demo : IO unit :=
  c <-' make_chan TChanBox ;;                            (* c : chan ChanBox                                    *)
  go_spawn (send TChanBox c (MkChanBox (42)%i64 c)) >>' (* goroutine: c <- ChanBox{42, c} — the channel sends ITSELF *)
  ( v <-' recv TChanBox c ;;                             (* v : ChanBox = {42, c} (its [Ch] field is c again)  *)
    println [any (cb_id v)] ).                           (* prints: 42  (parens: [>>'] is level 50, the [<-'] tail level 80) *)

(** THE NORTH-STAR "CURSED" DEMO (v2) — assorted Go horror in ONE struct, safe BY CONSTRUCTION (see the
    HONEST SCOPE note at the end: per-program formal race-freedom is the limit-#2 frontier).  A struct
    [Cursed] holds a SLICE of channels that SEND THEMSELVES ([]chan ChanBox) AND a pointer into a
    RECURSIVE linked list (a *ListNode).  TWO goroutines each pull their channel OUT of the slice-in-the-
    struct and make it transmit a [ChanBox] whose [Ch] field IS that very channel — channels-in-a-slice-
    in-a-struct sending THEMSELVES, concurrently — while main receives BOTH and TRAVERSES the 3-node
    recursive list head→tail.  It looks unsafe to a Go expert (a slice of self-sending channels nested in
    a struct, concurrent goroutines, a recursive heap type), yet it is built EXCLUSIVELY from
    safe-by-construction APIs: out-of-bounds is UNEXPRESSIBLE ([slice_get] demands an in-range proof),
    every deref is the fail-loud [ptr_get], every channel op a safe form, and the program contains no
    [close] — so OOB / nil-deref / send-on-closed cannot silently occur — and it is STRUCTURALLY
    race-free (each goroutine owns its own channel; no shared writes).  Assembled entirely from the
    shipped features (ChanBox self-send + ListNode recursion + channels-in-slices-in-structs +
    goroutines).  Prints: 99 1 2 3.  (HONEST SCOPE: the FEATURE-level safety and the GENERAL race-freedom
    theory are machine-checked; a per-program, end-to-end formal safety proof of THIS typed program —
    Denoting it into the [rstep] calculus to transfer its race-freedom — is the limit-#2 frontier, NOT
    yet discharged.  Per CLAUDE.md, this is not "verified race-free Go".) *)
Record Cursed := MkCursed {
  cu_chans : GoSlice (GoChan ChanBox) ;   (* []chan ChanBox — self-sending channels, IN A SLICE *)
  cu_list  : Ptr ListNode                 (* *ListNode      — a RECURSIVE linked list             *)
}.
Definition cursed_demo : IO unit :=
  c0 <-' make_chan TChanBox ;;                                     (* two self-sending channels...           *)
  c1 <-' make_chan TChanBox ;;
  t3 <-' ptr_new TListNode (MkListNode (3)%i64 (ptr_nil_tf tt)) ;; (* ...and a 3-node recursive list (tail)  *)
  t2 <-' ptr_new TListNode (MkListNode (2)%i64 t3) ;;
  t1 <-' ptr_new TListNode (MkListNode (1)%i64 t2) ;;
  let cu := MkCursed (slice_of_list (TChan TChanBox) [c0; c1]) t1 in (* struct{ []chan ChanBox ; *ListNode } *)
  ch0 <-' slice_get (TChan TChanBox) (cu_chans cu) (int_lit 0 eq_refl) ;;      (* pull each channel OUT of the slice-in-struct *)
  ch1 <-' slice_get (TChan TChanBox) (cu_chans cu) (int_lit 1 eq_refl) ;;
  go_spawn (send TChanBox ch0 (MkChanBox (90)%i64 ch0)) >>'        (* goroutine 0: ch0 <- ChanBox{90, ch0} — SENDS ITSELF *)
  go_spawn (send TChanBox ch1 (MkChanBox (9)%i64 ch1)) >>'         (* goroutine 1: ch1 <- ChanBox{9, ch1}  — SENDS ITSELF *)
  ( v0 <-' recv TChanBox ch0 ;;                                    (* receive both self-boxes...             *)
    v1 <-' recv TChanBox ch1 ;;
    n1 <-' ptr_get TListNode (cu_list cu) ;;                       (* ...and TRAVERSE the recursive list head→tail *)
    n2 <-' ptr_get TListNode (ln_next n1) ;;
    n3 <-' ptr_get TListNode (ln_next n2) ;;
    println [any (i64_add (cb_id v0) (cb_id v1)) ; any (ln_val n1) ; any (ln_val n2) ; any (ln_val n3)] ).
    (* prints: 99 1 2 3  (90+9, then the 3-node list) *)

(** Phase B3a: SLICE ALIASING.  A [SliceH] is an aliasing handle into a backing array;
    a SUB-SLICE [s[1:3]] SHARES that backing, so a write through the sub-slice is seen
    through the parent — the [subslice_alias] THEOREM.  Here [s[1:3][0] = 99] writes
    [s[1]], read back as 99 — impossible for the value (list-based) slice model. *)
Definition slice_alias_demo : IO unit :=
  bind (slice_make_h TI64 (int_lit 3 eq_refl)) (fun s =>                                  (* s := make([]int64, 3) *)
  bind (slice_idx_set s (int_lit 0 eq_refl) (10)%i64) (fun _ =>                           (* s[0] = 10 *)
  bind (slice_idx_set s (int_lit 1 eq_refl) (20)%i64) (fun _ =>                           (* s[1] = 20 *)
  bind (subslice s (int_lit 1 eq_refl) (int_lit 3 eq_refl)) (fun ss =>                                (* ss := s[1:3] (bounds-checked) *)
  bind (slice_idx_set ss (int_lit 0 eq_refl) (99)%i64) (fun _ =>                          (* ss[0] = 99 (= s[1]) *)
  bind (slice_idx_get TI64 s (int_lit 1 eq_refl)) (fun v =>                               (* v := s[1] — sees 99 (aliasing) *)
  println [any v])))))).                                                       (* prints 99 *)

(** Review #6 P0 #4 / minimum-suite #6: an out-of-range subslice PANICS rather than producing
    a bogus descriptor.  s has cap 2; [s[0:3]] requests b=3 > cap, which Go rejects — so the
    wrapped-descriptor path that would defeat the index bounds check is unconstructable. *)
Example subslice_past_cap_panics : forall (w : World),
  run_io (subslice (mkSliceH 100 0 2 2 TI64) (int_lit 0 eq_refl) (int_lit 3 eq_refl)) w
    = OPanic rt_slice_bounds w.
Proof. intros w. unfold subslice, run_io. now vm_compute. Qed.

(** Phase B3b: APPEND.  Go's [append] extends in place when [len < cap] (aliasing the
    backing — the [slice_append_incap_aliases] THEOREM) and REALLOCATES a fresh backing
    when [len = cap] (no aliasing).  Here [s] is full ([len = cap = 2]), so [append]
    reallocates; [s2 = [5, 0, 9]] (len 3) and the appended element [s2[2] = 9]. *)
Definition slice_append_demo : IO unit :=
  bind (slice_make_h TI64 (int_lit 2 eq_refl)) (fun s =>             (* make([]int64, 2), len=cap=2 *)
  bind (slice_idx_set s (int_lit 0 eq_refl) (5)%i64) (fun _ =>       (* s[0] = 5 *)
  bind (slice_append TI64 s (9)%i64) (fun s2 =>          (* s2 := append(s, 9) — reallocates, appends at index len=2 *)
  bind (slice_idx_get TI64 s2 (int_lit 2 eq_refl)) (fun v =>         (* v := s2[2] = 9 (the appended element) *)
  println [any v])))).                                    (* prints 9 *)

(** Phase B3c: [make([]T, len, cap)] gives a slice SPARE capacity, so [append] is
    IN PLACE and KEEPS the backing shared — the in-place-append aliasing of B3b, shown
    at runtime.  [s] has len 1, cap 3; [append] writes index 1 in place (no realloc), so
    [s2] shares [s]'s backing — writing [s2[0]] is seen through [s[0]]. *)
Definition slice_makecap_demo : IO unit :=
  bind (slice_make_lc TI64 (int_lit 1 eq_refl) (int_lit 3 eq_refl)) (fun s =>    (* make([]int64, 1, 3): len=1, cap=3 *)
  bind (slice_idx_set s (int_lit 0 eq_refl) (5)%i64) (fun _ =>        (* s[0] = 5 *)
  bind (slice_append TI64 s (8)%i64) (fun s2 =>           (* s2 := append(s, 8) — IN PLACE (len<cap), shares backing *)
  bind (slice_idx_set s2 (int_lit 0 eq_refl) (77)%i64) (fun _ =>      (* s2[0] = 77 *)
  bind (slice_idx_get TI64 s (int_lit 0 eq_refl)) (fun v =>           (* v := s[0] — sees 77 (shared backing!) *)
  println [any v]))))).                                    (* prints 77 *)

(** Review #6 P0 #4 / minimum-suite #5: a slice with len=1, cap=2 — writing index 1 (in the
    spare CAPACITY but past LENGTH) PANICS, exactly as Go bounds-checks against LEN not cap.
    Pre-fix the model silently wrote the spare backing cell and returned normally. *)
Example slice_write_past_len_panics : forall (v : GoI64) (w : World),
  run_io (slice_idx_set (mkSliceH 100 0 1 2 TI64) (int_lit 1 eq_refl) v) w
    = OPanic rt_index_oob w.
Proof. intros v w. apply run_slice_idx_set_oob. now vm_compute. Qed.

(** review R5 follow-up: the model REALLOCATES to cap = len+1 (NO spare), so a SECOND append after a
    realloc reallocates again → disjoint backing.  The plugin now FORCES Go's realloc capacity to len+1
    (a manual `make([]T, len+1, len+1)` copy) to match — if it left Go's native `append` to over-allocate,
    the 2nd append would go IN PLACE into Go's spare and ALIAS where the model says disjoint.  Here:
    s=[0,0] (full) → s2=[0,0,1] (len=cap=3) → s3=[0,0,1,2] (2nd realloc, DISJOINT from s2); writing s3[0]
    must NOT be seen through s2[0] (prints 0, the model's disjoint value; pre-fix Go would print 99). *)
Definition slice_realloc_alias_demo : IO unit :=
  bind (slice_make_h TI64 (int_lit 2 eq_refl)) (fun s =>             (* len=cap=2, [0,0] *)
  bind (slice_append TI64 s (1)%i64) (fun s2 =>          (* realloc → s2=[0,0,1], len=cap=3 (forced) *)
  bind (slice_append TI64 s2 (2)%i64) (fun s3 =>         (* s2 full → realloc → s3=[0,0,1,2], DISJOINT *)
  bind (slice_idx_set s3 (int_lit 0 eq_refl) (99)%i64) (fun _ =>     (* s3[0] = 99 *)
  bind (slice_idx_get TI64 s2 (int_lit 0 eq_refl)) (fun v =>         (* v := s2[0] — disjoint, unaffected → 0 *)
  println [any v]))))).                                   (* prints 0 *)

(** Phase B3c: [clear] zeros a slice's elements; [copy] copies elements src→dst. *)
Definition slice_clear_demo : IO unit :=
  bind (slice_make_h TI64 (int_lit 2 eq_refl)) (fun s =>
  bind (slice_idx_set s (int_lit 0 eq_refl) (5)%i64) (fun _ =>        (* s[0] = 5 *)
  bind (slice_clear_h TI64 s) (fun _ =>                   (* clear(s) → all zero *)
  bind (slice_idx_get TI64 s (int_lit 0 eq_refl)) (fun v =>           (* v := s[0] = 0 *)
  println [any v])))).                                     (* prints 0 *)
Definition slice_copy_demo : IO unit :=
  bind (slice_make_h TI64 (int_lit 2 eq_refl)) (fun dst =>
  bind (slice_make_h TI64 (int_lit 2 eq_refl)) (fun src =>
  bind (slice_idx_set src (int_lit 0 eq_refl) (7)%i64) (fun _ =>       (* src[0] = 7 *)
  bind (slice_copy TI64 dst src) (fun _n =>               (* copy(dst, src) *)
  bind (slice_idx_get TI64 dst (int_lit 0 eq_refl)) (fun v =>          (* v := dst[0] = 7 *)
  println [any v]))))).                                    (* prints 7 *)

(** Backward-goto counting loop: a [Ref] counter + [goto] back to the header.
    The read [iv := ref_get i] cannot use [:=] (it re-runs each iteration), so
    its declaration is hoisted to [var iv int64] (dominating the loop) and
    assigned with [=].  [ref_set] also assigns with [=].  Prints 0,1,2. *)
Definition count_demo : IO unit :=
  bind (ref_new TInt64 (int_lit 0 eq_refl)) (fun i =>
  run_blocks 0%nat [
    bind (ref_get TInt64 i) (fun iv =>            (* block 0: loop header *)
      if int_ltb iv (int_lit 3 eq_refl) then
        bind (println [any iv])      (fun _ =>
        bind (ref_set i (add iv (int_lit 1 eq_refl)))  (fun _ =>
        ret (Jump 0%nat)))                        (* goto block0 (backward) *)
      else ret (Jump 1%nat)) ;                    (* exit *)
    ret Done                                       (* block 1 *)
  ]).

(** review #4 P1 3: a run_blocks with a NONZERO entry (block 1) now emits its own `block1:`
    label — the raw fallback used to emit `goto block1` with NO such label (undefined Go).  Entry
    block 1 prints 5 then jumps to block 0 (so block 0 is reachable, not dead); block 0 prints 7. *)
Definition cfg_nonzero_entry_demo : IO unit :=
  run_blocks 1%nat [
    bind (println [any (int_lit 7 eq_refl)]) (fun _ => ret Done) ;           (* block 0 — reached via block 1's jump *)
    bind (println [any (int_lit 5 eq_refl)]) (fun _ => ret (Jump 0%nat))     (* block 1 — the ENTRY, then → block 0 *)
  ].

(** Control flow as a goto-CFG.  Three blocks; block 0 conditionally jumps to
    the merge (block 2), skipping block 1.  The structurer lifts this to a clean
    one-armed [if !early { println(2) }] — block 1 runs only when not early.
    early ⇒ 1,3 ; else ⇒ 1,2,3. *)
Definition cond_goto_demo (early : bool) : IO unit :=
  run_blocks 0%nat [
    bind (println [any (int_lit 1 eq_refl)]) (fun _ =>
      if early then ret (Jump 2%nat) else ret (Jump 1%nat)) ;
    bind (println [any (int_lit 2 eq_refl)]) (fun _ => ret (Jump 2%nat)) ;
    bind (println [any (int_lit 3 eq_refl)]) (fun _ => ret Done)
  ].

(** Diamond: block 0 branches to two non-empty arms (blocks 1 and 2) that
    reconverge at the merge (block 3).  The structurer finds the merge (the
    immediate post-dominator) and lifts this to [if b { 10 } else { 20 }; 99],
    emitting the merge once.  b ⇒ 1,10,99 ; else ⇒ 1,20,99. *)
Definition diamond_demo (b : bool) : IO unit :=
  run_blocks 0%nat [
    bind (println [any (int_lit 1 eq_refl)]) (fun _ =>
      if b then ret (Jump 1%nat) else ret (Jump 2%nat)) ;
    bind (println [any (int_lit 10 eq_refl)]) (fun _ => ret (Jump 3%nat)) ;
    bind (println [any (int_lit 20 eq_refl)]) (fun _ => ret (Jump 3%nat)) ;
    bind (println [any (int_lit 99 eq_refl)]) (fun _ => ret Done)
  ].

(** Loop containing a branch: a counting loop (block 0 header, block 3 the
    increment/loop tail) whose body has an in-loop one-armed [if] (block 1 → 2).
    Exercises the relooper nesting a conditional inside a [for]: the header
    becomes [for { … if iv < 3 { … } else { break } }], and block 1's branch a
    nested [if … < 1 { println(100) }].  Counter is a [Ref], re-read per block
    (separate goto-blocks don't share Rocq scope).  Prints 100, 0, 1, 2. *)
Definition loopif_demo : IO unit :=
  bind (ref_new TInt64 (int_lit 0 eq_refl)) (fun i =>
  run_blocks 0%nat [
    bind (ref_get TInt64 i) (fun iv =>                              (* block 0: header *)
      if int_ltb iv (int_lit 3 eq_refl) then ret (Jump 1%nat) else ret (Jump 4%nat)) ;
    bind (ref_get TInt64 i) (fun iv =>                              (* block 1: in-loop branch *)
      if int_ltb iv (int_lit 1 eq_refl) then ret (Jump 2%nat) else ret (Jump 3%nat)) ;
    bind (println [any (int_lit 100 eq_refl)]) (fun _ => ret (Jump 3%nat)) ;  (* block 2: first-iter marker *)
    bind (ref_get TInt64 i) (fun iv =>                              (* block 3: body, incr, loop *)
    bind (println [any iv]) (fun _ =>
    bind (ref_set i (add iv (int_lit 1 eq_refl))) (fun _ => ret (Jump 0%nat)))) ;
    ret Done                                                        (* block 4: exit *)
  ]).

(** Nested loops: an outer counter [i] (header block 0, tail block 4) wrapping an
    inner counter [j] (header block 2, tail block 3).  Exercises the relooper
    nesting one [for] inside another — [loopctx] stacks, so the inner [jv >= 2]
    exit becomes the inner [break] (to block 4) and the outer [iv >= 2] exit the
    outer [break] (to block 5).  Two [Ref]s; [j] is reset each outer pass.
    Prints 0,1 (inner, i=0) then 0,1 (inner, i=1). *)
Definition nested_loop_demo : IO unit :=
  bind (ref_new TInt64 (int_lit 0 eq_refl)) (fun i =>
  bind (ref_new TInt64 (int_lit 0 eq_refl)) (fun j =>
  run_blocks 0%nat [
    bind (ref_get TInt64 i) (fun iv =>                              (* block 0: outer header *)
      if int_ltb iv (int_lit 2 eq_refl) then ret (Jump 1%nat) else ret (Jump 5%nat)) ;
    bind (ref_set j (int_lit 0 eq_refl)) (fun _ => ret (Jump 2%nat)) ;        (* block 1: reset j *)
    bind (ref_get TInt64 j) (fun jv =>                              (* block 2: inner header *)
      if int_ltb jv (int_lit 2 eq_refl) then ret (Jump 3%nat) else ret (Jump 4%nat)) ;
    bind (ref_get TInt64 j) (fun jv =>                              (* block 3: inner body *)
    bind (println [any jv]) (fun _ =>
    bind (ref_set j (add jv (int_lit 1 eq_refl))) (fun _ => ret (Jump 2%nat)))) ;
    bind (ref_get TInt64 i) (fun iv =>                              (* block 4: outer tail *)
    bind (ref_set i (add iv (int_lit 1 eq_refl))) (fun _ => ret (Jump 0%nat))) ;
    ret Done                                                        (* block 5: exit *)
  ])).

(** Early return from inside a loop: block 1 returns ([Done]) when [iv] reaches 2,
    mid-loop — distinct from the loop's normal [break] (block 0 → block 3) and the
    post-loop code.  The relooper emits [return] for the in-loop [Done], [break]
    for the exit edge, and the block-3 tail after the [for].  Prints 0, 1, then
    returns (so block 3's 999 is never reached). *)
Definition early_return_demo : IO unit :=
  bind (ref_new TInt64 (int_lit 0 eq_refl)) (fun i =>
  run_blocks 0%nat [
    bind (ref_get TInt64 i) (fun iv =>                              (* block 0: header *)
      if int_ltb iv (int_lit 9 eq_refl) then ret (Jump 1%nat) else ret (Jump 3%nat)) ;
    bind (ref_get TInt64 i) (fun iv =>                              (* block 1: early return *)
      if int_ltb iv (int_lit 2 eq_refl) then ret (Jump 2%nat) else ret Done) ;
    bind (ref_get TInt64 i) (fun iv =>                              (* block 2: body, incr, loop *)
    bind (println [any iv]) (fun _ =>
    bind (ref_set i (add iv (int_lit 1 eq_refl))) (fun _ => ret (Jump 0%nat)))) ;
    bind (println [any (int_lit 999 eq_refl)]) (fun _ => ret Done)           (* block 3: normal exit *)
  ]).

(** Labeled break: from inside the inner loop, block 3 jumps to the *outer*
    loop's exit (block 6) when [jv] reaches 2 — escaping both loops at once.
    That is more than the innermost loop can [break], so the relooper labels the
    outer [for] [L0:] and emits [break L0].  The inner loop is multi-exit (its
    normal exit is block 5, plus the labeled escape to block 6), which the
    primary-exit analysis accepts.  Prints 0, 1, 2 then stops entirely. *)
Definition labeled_break_demo : IO unit :=
  bind (ref_new TInt64 (int_lit 0 eq_refl)) (fun i =>
  bind (ref_new TInt64 (int_lit 0 eq_refl)) (fun j =>
  run_blocks 0%nat [
    bind (ref_get TInt64 i) (fun iv =>                              (* block 0: outer header *)
      if int_ltb iv (int_lit 3 eq_refl) then ret (Jump 1%nat) else ret (Jump 6%nat)) ;
    bind (ref_set j (int_lit 0 eq_refl)) (fun _ => ret (Jump 2%nat)) ;        (* block 1: reset j *)
    bind (ref_get TInt64 j) (fun jv =>                              (* block 2: inner header *)
      if int_ltb jv (int_lit 3 eq_refl) then ret (Jump 3%nat) else ret (Jump 5%nat)) ;
    bind (ref_get TInt64 j) (fun jv =>                              (* block 3: print; break L0 at 2 *)
    bind (println [any jv]) (fun _ =>
      if int_ltb jv (int_lit 2 eq_refl) then ret (Jump 4%nat) else ret (Jump 6%nat))) ;
    bind (ref_get TInt64 j) (fun jv =>                              (* block 4: inner tail, j++ *)
    bind (ref_set j (add jv (int_lit 1 eq_refl))) (fun _ => ret (Jump 2%nat))) ;
    bind (ref_get TInt64 i) (fun iv =>                              (* block 5: outer tail, i++ *)
    bind (ref_set i (add iv (int_lit 1 eq_refl))) (fun _ => ret (Jump 0%nat))) ;
    ret Done                                                        (* block 6: exit *)
  ])).

(** Labeled continue: from inside the inner loop, block 3 jumps to the *outer*
    header (block 0) once [jv] reaches 1 — abandoning the inner loop to restart
    the outer one.  That escapes the innermost loop, so it lowers to
    [continue L0] (the outer [for] is labeled).  The outer header increments [i]
    so it still terminates.  Prints 0, 1 (inner, i=0) then 0, 1 (i=1). *)
Definition labeled_continue_demo : IO unit :=
  bind (ref_new TInt64 (int_lit 0 eq_refl)) (fun i =>
  bind (ref_new TInt64 (int_lit 0 eq_refl)) (fun j =>
  run_blocks 0%nat [
    bind (ref_get TInt64 i) (fun iv =>                              (* block 0: outer header, i++ *)
    bind (ref_set i (add iv (int_lit 1 eq_refl))) (fun _ =>
      if int_ltb iv (int_lit 2 eq_refl) then ret (Jump 1%nat) else ret (Jump 5%nat))) ;
    bind (ref_set j (int_lit 0 eq_refl)) (fun _ => ret (Jump 2%nat)) ;        (* block 1: reset j *)
    bind (ref_get TInt64 j) (fun jv =>                              (* block 2: inner header *)
      if int_ltb jv (int_lit 3 eq_refl) then ret (Jump 3%nat) else ret (Jump 4%nat)) ;
    bind (ref_get TInt64 j) (fun jv =>                              (* block 3: print; continue L0 *)
    bind (println [any jv]) (fun _ =>
    bind (ref_set j (add jv (int_lit 1 eq_refl))) (fun _ =>
      if int_ltb jv (int_lit 1 eq_refl) then ret (Jump 2%nat) else ret (Jump 0%nat)))) ;
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
  bind (ref_new TInt64 (int_lit 0 eq_refl)) (fun n =>
  run_blocks 0%nat [
    (if enter_high then ret (Jump 2%nat) else ret (Jump 1%nat)) ;  (* block 0: two-entry *)
    bind (ref_get TInt64 n) (fun nv =>                             (* block 1 *)
    bind (println [any (int_lit 1 eq_refl)]) (fun _ =>
    bind (ref_set n (add nv (int_lit 1 eq_refl))) (fun _ => ret (Jump 2%nat)))) ;
    bind (ref_get TInt64 n) (fun nv =>                             (* block 2 *)
    bind (println [any (int_lit 2 eq_refl)]) (fun _ =>
    bind (ref_set n (add nv (int_lit 1 eq_refl))) (fun _ =>
      if int_ltb nv (int_lit 3 eq_refl) then ret (Jump 1%nat) else ret (Jump 3%nat)))) ;
    ret Done                                                       (* block 3: exit *)
  ]).

(** Bounded loop: [for_each] over a slice lowers to a Go [for ... range]. *)
Definition foreach_demo : IO unit :=
  let xs := slice_of_list TInt64 [int_lit 10 eq_refl; int_lit 20 eq_refl; int_lit 30 eq_refl] in
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
(** review #4 P1 #4 — a method with a NARROW param: `func (p Point) Px_plus(b uint8) int64`.  The
    receiver is param 0, so the cast machinery uses the param-type TAIL aligned with the non-receiver
    args; a wide value at the narrow `b` is cast (`p.Px_plus(uint8(…))`) — the method residual the
    function-arg slice left open, now closed (else `p.Px_plus(int64-expr)` = invalid Go). *)
Definition px_plus (p : Point) (b : GoU8) : GoI64 := i64_add (px p) (i64_of_u8 b).

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
  bind (println [any (sum_coords q)])   (fun _ =>   (* 27 *)
  println [any (px_plus p (u8_of_i64 (i64_lit 300 eq_refl)))])))).   (* 3 + uint8(44) = 47 (narrow method arg) *)

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

(** N-ARY (3+) multiple return (Go `func(…) (A, B, C)`).  Coq's `A * B * C` is the LEFT-NESTED
    `(A * B) * C` with value `(a, b, c)` = `((a, b), c)`; the plugin flattens the left spine to a
    FLAT Go `func(…) (int64, int64, int64)` / `return a, b, c`, and the nested destructure
    `let '(x, y, z) := …` to a single `x, y, z := Triple3(…)`. *)
Definition triple3 (a b c : GoI64) : GoI64 * GoI64 * GoI64 := (a, b, c).
Definition triple_demo : IO unit :=
  let '(x, y, z) := triple3 (1)%i64 (2)%i64 (3)%i64 in   (* (1, 2, 3) *)
  println [any x; any y; any z].                          (* 1 2 3 *)

(** PURE-value-position multiple-return destructure — a value-returning (NON-IO) function that
    destructures a multi-return and uses the components, e.g. Go `func f() int64 { x, y := g();
    return x + y }`.  Covers 2-ary (`sum_pair` over `swap2`) and N-ary (`sum3` over `triple3`).  Was
    a fail-closed gap: the destructure only lowered in IO/statement position; now `pp_pure_tail`
    handles it too (`x, y[, z] := f(); return …`). *)
Definition sum_pair (a b : GoI64) : GoI64 := let '(x, y) := swap2 a b in i64_add x y.
Definition sum3 (a b c : GoI64) : GoI64 :=
  let '(x, y, z) := triple3 a b c in i64_add (i64_add x y) z.
(* A BLANK binder [_] in a destructure → Go [_], NOT the unused gensym Coq extracts it as (which,
   left as a real `:=` binder, is `declared and not used` — invalid Go). *)
Definition snd_of (a b : GoI64) : GoI64 := let '(_, y) := swap2 a b in y.
Definition pure_destr_demo : IO unit :=
  println [any (sum_pair (3)%i64 (4)%i64); any (sum3 (1)%i64 (2)%i64 (3)%i64); any (snd_of (5)%i64 (6)%i64)].   (* 7 6 5 *)
(* same, but the blank-binder destructure is in IO/STATEMENT position. *)
Definition stmt_blank_demo : IO unit :=
  let '(_, y) := swap2 (7)%i64 (8)%i64 in println [any y].   (* 7 *)
(* NARROW multiple-return `func(…) (uint8, uint8)`: each component is an int64-carrier op result that
   must be CAST to its narrow return slot — `return uint8(…), uint8(…)`.  Was a fail-OPEN (int64 into a
   uint8 return slot fails `go build`). *)
Definition narrow_pair (x y : GoI64) : GoU8 * GoU8 := (u8_of_i64 x, u8_of_i64 y).
Definition narrow_pair_demo : IO unit :=
  let '(p, q) := narrow_pair (300)%i64 (7)%i64 in   (* u8_of_i64 300 = 44, u8_of_i64 7 = 7 *)
  println [any p; any q].                            (* 44 7 *)

(** An IO-returning method (a method with effects) — the receiver threads through
    the [pp_io_body] path just like a pure one: [func (p Point) Describe() { … }],
    and the statement-position call [describe p] lowers to [p.Describe()]. *)
Definition describe (p : Point) : IO unit :=
  bind (println [any (px p)]) (fun _ => println [any (py p)]).

Definition io_method_demo : IO unit :=
  let p := MkPoint (8)%i64 (9)%i64 in
  describe p.   (* prints: 8 / 9 *)

(** A VALUE-returning IO method whose body is a BIND-CHAIN (an effect, then [ret v]) — not just
    a single-expression tail.  [func (p Point) Px_then_sum() int64 { println(p.Px); return p.Px+p.Py }]:
    the leading [println] becomes a STATEMENT, the [ret] tail becomes [return …]. *)
Definition px_then_sum (p : Point) : IO GoI64 :=
  bind (println [any (px p)]) (fun _ => ret (i64_add (px p) (py p))).
Definition io_val_method_demo : IO unit :=
  let p := MkPoint (8)%i64 (9)%i64 in
  bind (px_then_sum p) (fun s => println [any s]).   (* px_then_sum prints 8, returns 17; then prints 17 *)

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
    [struct_eqb] is evidence-carrying: it demands the SEALED comparability witness
    [squash point_eqb_spec] (a proof that [point_eqb] DECIDES Point equality, which Go's
    comparability requires) and lowers to the bare Go [p == q].  [struct_eqb_native_spec]
    proves the native form STILL decides Point equality — same guarantee as [point_eqb],
    now via the actual operator. *)
Lemma struct_eqb_native_spec :
  forall a b, struct_eqb point_eqb (squash point_eqb_spec) a b = true <-> a = b.
Proof. intros. unfold struct_eqb. apply point_eqb_spec. Qed.
Definition struct_eq_native_demo : IO unit :=
  let p := MkPoint (3)%i64 (4)%i64 in
  let q := MkPoint (3)%i64 (4)%i64 in
  let r := MkPoint (3)%i64 (5)%i64 in
  println [any (struct_eqb point_eqb (squash point_eqb_spec) p q);
           any (struct_eqb point_eqb (squash point_eqb_spec) p r)].   (* true false *)

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
(* The CANONICAL rep for [Cell] (review #6 #10(b)): bound once to the type, so every [*Cell] handle
   reconstructs the same way.  [cell_f0]/[cell_f1] are the field-COHERENCE evidence (#10(c)) — they
   tie [cx]↔cell 0 and [cy]↔cell 1 to that rep, so a field access cannot name the wrong cell. *)
#[local] Instance StructRep2Of_Cell : StructRep2Of Cell := mkSR2 cx cy MkCell cell_eta.
Definition cell_f0 : field_at2 (the_rep2 Cell) 0 cx := or_introl (conj eq_refl eq_refl).
Definition cell_f1 : field_at2 (the_rep2 Cell) 1 cy := or_intror (conj eq_refl eq_refl).
Definition sptr_demo : IO unit :=
  bind (sptr_new (MkCell (3)%i64 (4)%i64)) (fun p =>  (* p := &Cell{3,4} *)
  bind (sptr_set_field p 0 cx TI64 cell_f0 (7)%i64) (fun _ =>     (* p.Cx = 7 (mutate through *p) *)
  bind (sptr_get_field p 0 cx TI64 cell_f0) (fun a =>            (* a := p.Cx → 7 *)
  bind (sptr_get_field p 1 cy TI64 cell_f1) (fun b =>            (* b := p.Cy → 4 *)
  println [any a; any b])))).                                   (* prints: 7 4 *)

(** POINTER-RECEIVER method (Phase B2): a method whose first param is [SPtr Cell] (a
    [*Cell]) and MUTATES the receiver.  The plugin detects the [SPtr (record)] first
    param → [func (p *Cell) Cell_incx() { … }] (and a call [cell_incx p] → [p.Cell_incx()]),
    exactly the value-receiver path but through a pointer.  The mutation is observed by
    the CALLER (the defining pointer-receiver behaviour), backed by [sptr_field_get_set]. *)
Definition cell_incx (p : SPtr Cell) : IO unit :=
  bind (sptr_get_field p 0 cx TI64 cell_f0) (fun a =>          (* read p.Cx *)
        sptr_set_field p 0 cx TI64 cell_f0 (i64_add a (1)%i64)).  (* p.Cx = p.Cx + 1 *)

Definition ptr_method_demo : IO unit :=
  bind (sptr_new (MkCell (10)%i64 (20)%i64)) (fun p =>
  bind (cell_incx p) (fun _ =>                                (* p.Cell_incx() — mutates p.Cx *)
  bind (sptr_get_field p 0 cx TI64 cell_f0) (fun a =>          (* a := p.Cx → 11 *)
  println [any a]))).                                          (* prints: 11 *)

(** POINTER-receiver method EXPRESSION (the parenthesized-star-Cell dot Cell_incx form) — the
    pointer-receiver method referenced UNBOUND is Go's [func] taking a [*Cell] receiver.
    Passed to a HOF [apply_cell] taking that func; the plugin records the receiver type as the
    PARENTHESIZED pointer form (vs the value-receiver [Point.Sum_coords]). *)
Definition apply_cell (f : SPtr Cell -> IO unit) (p : SPtr Cell) : IO unit := f p.
Definition ptr_method_expr_demo : IO unit :=
  bind (sptr_new (MkCell (5)%i64 (6)%i64)) (fun p =>
  bind (apply_cell cell_incx p) (fun _ =>                     (* pointer-receiver method expr via the HOF — mutates p.Cx *)
  bind (sptr_get_field p 0 cx TI64 cell_f0) (fun a =>          (* a := p.Cx → 6 *)
  println [any a]))).                                          (* prints: 6 *)

(** EMBEDDING a POINTER-to-struct ([*Cell]) in a struct (Go's [type Node struct { *Cell; tag int64 }]):
    Go promotes the embedded [*T]'s method set THROUGH the pointer.  Detected by the SAME "field name =
    base type name" rule, now for an [SPtr Cell] field → an anonymous [*Cell] field.  The pointer-receiver
    method [cell_incx] is PROMOTED: [cell_incx (cell nd)] → [nd.Cell_incx()] (peeling the embedded
    projection, exactly like struct-in-struct, but through the pointer); the struct's own [ntag] coexists. *)
Record Node := MkNode { cell : SPtr Cell ; ntag : GoI64 }.
Definition node_embed_demo : IO unit :=
  bind (sptr_new (MkCell (10)%i64 (20)%i64)) (fun p =>
  let nd := MkNode p (99)%i64 in
  bind (cell_incx (cell nd)) (fun _ =>                         (* PROMOTED: nd.Cell_incx() mutates the embedded *Cell *)
  bind (sptr_get_field (cell nd) 0 cx TI64 cell_f0) (fun a =>   (* read through the embed: nd.Cell.Cx → 11 *)
  println [any a; any (ntag nd)]))).                           (* prints: 11 99 *)

(** N-FIELD struct pointer: a 3-field [*Cell3] with a pointer-receiver method that mutates
    a field.  Same generic field-cell substrate as the 2-field case ([sptr3_field_get_set]
    backs the mutation); shows the pointer story is not limited to 2 fields. *)
Record Cell3 := MkCell3 { c3x : GoI64 ; c3y : GoI64 ; c3z : GoI64 }.
Lemma cell3_eta : forall v, MkCell3 (c3x v) (c3y v) (c3z v) = v.
Proof. intros [a b c]; reflexivity. Qed.
#[local] Instance StructRep3Of_Cell3 : StructRep3Of Cell3 := mkSR3 c3x c3y c3z MkCell3 cell3_eta.
Definition cell3_f2 : field_at3 (the_rep3 Cell3) 2 c3z := or_intror (or_intror (conj eq_refl eq_refl)).
Definition cell3_inc_z (p : SPtr3 Cell3) : IO unit :=
  bind (sptr3_get_field p 2 c3z TI64 cell3_f2) (fun z =>          (* read p.C3z *)
        sptr3_set_field p 2 c3z TI64 cell3_f2 (i64_add z (1)%i64)).  (* p.C3z = p.C3z + 1 *)
Definition nfield_ptr_demo : IO unit :=
  bind (sptr3_new (MkCell3 (10)%i64 (20)%i64 (30)%i64)) (fun p =>
  bind (cell3_inc_z p) (fun _ =>                                (* p.Cell3_inc_z() — mutates p.C3z *)
  bind (sptr3_get_field p 2 c3z TI64 cell3_f2) (fun z =>          (* z := p.C3z → 31 *)
  println [any z]))).                                           (* prints: 31 *)

(** HETEROGENEOUS struct pointer: a [*Pair] whose two fields have DIFFERENT types
    ([N int64], [B bool]) — the common real-Go case.  Same generic field-cell substrate
    ([sptrh_field_get_set] backs the mutation); the rep just carries the per-field types
    and tags.  The pointer-receiver method bumps the int64 field, leaving the bool. *)
Record Pair := MkPair { p_n : GoI64 ; p_b : bool }.
Lemma pair_eta : forall v, MkPair (p_n v) (p_b v) = v.
Proof. intros [a b]; reflexivity. Qed.
#[local] Instance StructRep2HOf_Pair : StructRep2HOf Pair GoI64 bool := mkSR2H p_n p_b TI64 TBool MkPair pair_eta.
Definition pair_f0 : field_atH (the_repH Pair GoI64 bool) 0 p_n TI64 := or_introl (conj eq_refl eq_refl).
Definition pair_f1 : field_atH (the_repH Pair GoI64 bool) 1 p_b TBool := or_intror (conj eq_refl eq_refl).
Definition pair_bump (p : SPtrH Pair GoI64 bool) : IO unit :=
  bind (sptrh_get_field p 0 p_n TI64 pair_f0) (fun n =>          (* read p.P_n *)
        sptrh_set_field p 0 p_n TI64 pair_f0 (i64_add n (1)%i64)).  (* p.P_n = p.P_n + 1 *)
Definition het_ptr_demo : IO unit :=
  bind (sptrh_new (MkPair (10)%i64 true)) (fun p =>
  bind (pair_bump p) (fun _ =>                                  (* p.Pair_bump() — mutates p.P_n *)
  bind (sptrh_get_field p 0 p_n TI64 pair_f0) (fun n =>          (* n := p.P_n → 11 *)
  bind (sptrh_get_field p 1 p_b TBool pair_f1) (fun b =>         (* b := p.P_b → true *)
  println [any n; any b])))).                                  (* prints: 11 true *)

(** review #6 #10(c) — the field COHERENCE is ENFORCED, not decorative: a [field_at…] witness for a
    MISMATCHED (idx, proj) or (proj, tag) pairing does NOT typecheck, so a struct-pointer access can
    never name one field while addressing another cell (the exact defect the review flagged). *)
Fail Definition cell_bad_coh   (* cy is field 1, not field 0 *)
  : field_at2 (the_rep2 Cell) 0 cy := or_introl (conj eq_refl eq_refl).
Fail Definition pair_bad_type  (* field 1 is bool — cannot be read as the int64 p_n with tag TI64 *)
  : field_atH (the_repH Pair GoI64 bool) 1 p_n TI64 := or_intror (conj eq_refl eq_refl).

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

(** INTERFACE EMBEDDING (Go's [type ReadWriter interface { Reader; Writer }]).  An interface
    that EMBEDS others has the UNION of their method sets, and a value of it may be used wherever
    any embedded interface is wanted.  In the dictionary model the embedding interface is the FLAT
    UNION dictionary (all methods + the captured value), and the "is-a" relation is an explicit
    UPCAST that PROJECTS the embedded interface's methods (and the same hidden value) into its
    smaller dictionary — Go's implicit embedded-interface assignment, made explicit (consistent
    with our explicit-dictionary deviation).  [mk_file] is ONE concrete carrier satisfying both
    [Reader] and [Writer]; the upcasts never see it (existential), exactly like a flat interface. *)
Record Reader     := MkReader     { rd_read  : GoI64 -> GoI64 ; rd_self : GoAny }.
Record Writer     := MkWriter     { wr_write : GoI64 -> GoI64 ; wr_self : GoAny }.
Record ReadWriter := MkReadWriter { rw_read  : GoI64 -> GoI64 ; rw_write : GoI64 -> GoI64 ; rw_self : GoAny }.
Definition mk_file (base : GoI64) : ReadWriter :=
  MkReadWriter (fun x => i64_add x base) (fun x => i64_sub x base) (any base).
(* The embedding upcasts: a [ReadWriter] IS-A [Reader] and IS-A [Writer]. *)
Definition rw_as_reader (rw : ReadWriter) : Reader := MkReader  (rw_read rw)  (rw_self rw).
Definition rw_as_writer (rw : ReadWriter) : Writer := MkWriter  (rw_write rw) (rw_self rw).
(* Dispatch through an upcast is exactly the method the concrete carrier supplied — provable,
   and the method-set union means [rw_read]/[rw_write] both dispatch directly too. *)
Example embed_read  : forall base x, rd_read  (rw_as_reader (mk_file base)) x = i64_add x base.
Proof. reflexivity. Qed.
Example embed_write : forall base x, wr_write (rw_as_writer (mk_file base)) x = i64_sub x base.
Proof. reflexivity. Qed.
Definition embed_iface_demo : IO unit :=
  let f := mk_file (10)%i64 in
  bind (println [any (rw_read f (3)%i64)])                (fun _ =>   (* direct (union): 3+10 = 13 *)
  bind (println [any (rd_read (rw_as_reader f) (5)%i64)]) (fun _ =>   (* via Reader upcast: 5+10 = 15 *)
  println [any (wr_write (rw_as_writer f) (40)%i64)])).               (* via Writer upcast: 40-10 = 30 *)

(** Embedding an INTERFACE in a STRUCT (Go's [type LoggedGreeter struct { Greeter; calls int64 }]):
    the embedded interface's method set is PROMOTED to the outer struct.  In the dictionary model
    an interface IS a struct (its vtable), so this rides the SAME anonymous-field embedding as
    struct-in-struct — the embedded [Greeter]'s [greet] is promoted (emitted [lg.Greet(x)], not
    [lg.Greeter.Greet(x)]), coexisting with the struct's own [lg_calls] field.  A common Go pattern:
    wrap an interface value with extra state while still satisfying its method set. *)
Record LoggedGreeter := MkLoggedGreeter { greeter : Greeter ; lg_calls : GoI64 }.
Definition mk_logged (base calls : GoI64) : LoggedGreeter := MkLoggedGreeter (mk_adder base) calls.
Example promoted_greet : forall base calls x, greet (greeter (mk_logged base calls)) x = i64_add base x.
Proof. reflexivity. Qed.
Definition embed_iface_in_struct_demo : IO unit :=
  let lg := mk_logged (100)%i64 (7)%i64 in
  bind (println [any (greet (greeter lg) (5)%i64)])  (fun _ =>   (* PROMOTED Greet: 100+5 = 105 *)
  println [any (lg_calls lg)]).                                  (* the struct's own field: 7 *)

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
(* [Celsius]'s unboxing-blocker phantom is [unit] (not the [GoTypeTag GoI64] the other deftypes use):
   a 2-field record is still not unboxed (so [Celsius] stays a distinct method-receiver and extracts
   [type Celsius int64], the phantom dropped), AND [unit] is AXIOM-FREE COMPARABLE ([tt = tt] is
   trivial) — so [Celsius] can be compared / be a map KEY, which a [GoTypeTag GoI64] phantom blocks
   (its uniqueness is unprovable without an axiom — a Type-indexed family).  See PROGRESS.md. *)
Record Celsius := MkCelsius { c_val : GoI64 ; c_tag : unit }.
Definition mk_celsius (v : GoI64) : Celsius := MkCelsius v tt.
(* The payoff: [Celsius] IS comparable AXIOM-FREE (two are equal iff their [c_val] carriers are; the
   [unit] phantom is trivially equal) — the comparability a defined-type map key needs. *)
Lemma comparable_celsius : forall a b : Celsius, i64_eqb (c_val a) (c_val b) = true <-> a = b.
Proof.
  intros [av []] [bv []]. cbn. split.
  - intro H. apply i64_eqb_spec in H. subst. reflexivity.
  - intro H. injection H as ->. apply i64_eqb_spec. reflexivity.
Qed.
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
Record Handler := MkHandler { h_fn : GoFunc GoI64 GoI64 ; h_tag : GoTypeTag (GoFunc GoI64 GoI64) }.
Definition mk_handler (f : GoI64 -> GoI64) : Handler := MkHandler (gofunc_of f) (TArrow TI64 TI64).
(* [h_fn h] is a NULLABLE func value (review #8); CALLING it is the effectful [gofunc_call] — a real
   handler runs, a nil one panics (Go's nil-func call).  The plugin erases the [Some]/[gofunc_call]
   down to the bare Go call [(func(int64) int64)(h)(x)]. *)
Definition handler_run (h : Handler) (x : GoI64) : IO GoI64 := gofunc_call (h_fn h) x.
Definition hinc (n : GoI64) : GoI64 := i64_add n (1)%i64.
(* dispatch is provable: the wrapped (non-nil) func IS what [handler_run] calls *)
Example handler_run_spec : forall f x w,
  run_io (handler_run (mk_handler f) x) w = ORet (f x) w.
Proof. reflexivity. Qed.
(* review #8 — the ZERO func is a genuine nil ([NilFunc]), and CALLING it PANICS (Go's nil-func
   call = nil-pointer dereference); it is NOT a silently-callable codomain-zero placeholder. *)
Example zero_func_is_nil : zero_val (TArrow TI64 TI64) = NilFunc.
Proof. reflexivity. Qed.
Example zero_func_call_panics : forall w,
  run_io (gofunc_call (zero_val (TArrow TI64 TI64)) (5)%i64) w = OPanic rt_nil_deref w.
Proof. reflexivity. Qed.
Definition named_func_demo : IO unit :=
  r <-' handler_run (mk_handler hinc) (41)%i64 ;; println [any r].   (* 42 *)

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

(** GENERIC [comparable] CONSTRAINT (Go's [func F[K comparable](…)]).  Beyond [any]: [ceqb] is
    generic over a comparable [K], dispatching to native [==].  Its [ComparableW K] witness is
    computational in Rocq (so the witnesses below reduce) but ERASED by the plugin — [ceqb] lowers
    to [func Ceqb[K comparable](a, b K) bool { return a == b }], and each call drops the witness.
    Instantiated at [int64] AND [string] (one generic, two comparable types). *)
(** ONE generic [ceqb] over EVERY Go-comparable type kind — scalar ([int64], [uint64]), [string],
    and STRUCT (field-wise [==]).  Each carries its own [ComparableW] witness (computational in
    Rocq, erased by the plugin); all lower to the same [func Ceqb[K comparable]] with native [==].
    The witness instances ([cw_i64]/[cw_u64]/[cw_str]/[cw_point]) are auto-suppressed (any
    [ComparableW]-typed def). *)
Definition ceq_i64   (a b : GoI64)   : bool := ceqb cw_i64   a b.
Definition ceq_u64   (a b : GoU64)   : bool := ceqb cw_u64   a b.
Definition ceq_str   (a b : GoString): bool := ceqb cw_str   a b.
Definition cw_point  : ComparableW Point := MkComparableW point_eqb (squash point_eqb_spec).  (* struct comparable via field-wise [==], with sealed evidence *)
Definition ceq_point (a b : Point)   : bool := ceqb cw_point a b.
(* A DEFINED TYPE is comparable too: [cw_celsius] is the SEALED witness over [Celsius]'s axiom-free
   comparability ([comparable_celsius]), made possible by the unit-phantom rep; [ceqb] over it lowers
   to [Ceqb[Celsius comparable]] / native [Celsius == Celsius]. *)
Definition cw_celsius : ComparableW Celsius := MkComparableW (fun a b => i64_eqb (c_val a) (c_val b)) (squash comparable_celsius).
Definition ceq_celsius (a b : Celsius) : bool := ceqb cw_celsius a b.
Example ceq_i64_t   : ceq_i64 (5)%i64 (5)%i64         = true.  Proof. now vm_compute. Qed.
Example ceq_i64_f   : ceq_i64 (5)%i64 (6)%i64         = false. Proof. now vm_compute. Qed.
Example ceq_str_t   : ceq_str "go"%string "go"%string = true.  Proof. now vm_compute. Qed.
Example ceq_u64_t   : ceq_u64 (9)%u64 (9)%u64         = true.  Proof. now vm_compute. Qed.
Example ceq_point_t : ceq_point (MkPoint (1)%i64 (2)%i64) (MkPoint (1)%i64 (2)%i64) = true.  Proof. now vm_compute. Qed.
Example ceq_point_f : ceq_point (MkPoint (1)%i64 (2)%i64) (MkPoint (1)%i64 (9)%i64) = false. Proof. now vm_compute. Qed.
Example ceq_celsius_t : ceq_celsius (mk_celsius (20)%i64) (mk_celsius (20)%i64) = true.  Proof. now vm_compute. Qed.
Example ceq_celsius_f : ceq_celsius (mk_celsius (20)%i64) (mk_celsius (37)%i64) = false. Proof. now vm_compute. Qed.
Definition comparable_demo : IO unit :=
  println [ any (ceq_i64   (5)%i64 (5)%i64)                                          (* int64  → true  *)
          ; any (ceq_u64   (9)%u64 (9)%u64)                                          (* uint64 → true  *)
          ; any (ceq_str   "go"%string "hi"%string)                                  (* string → false *)
          ; any (ceq_point (MkPoint (1)%i64 (2)%i64) (MkPoint (1)%i64 (2)%i64))       (* struct → true  *)
          ; any (ceq_celsius (mk_celsius (20)%i64) (mk_celsius (20)%i64)) ].           (* DEFINED TYPE → true *)

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

(** review-driven: a generic struct instantiated at a NARROW type ([Box GoU8] = [Box[uint8]]).  The
    P1 #4 struct-field / function-arg casts key off the DECLARED type, which here is a type VARIABLE
    [A] ⇒ [narrow_dest_conv] is None ⇒ no cast.  The value [u8_of_i64 …] is an int64-masked carrier, so
    `Make_box[uint8](x & 0xff)` would pass an int64 to a [uint8] type-param = invalid Go (the generics×
    narrow fail-open).  Reading back widens via [i64_of_u8]. *)
Definition gbox_narrow_demo : IO unit :=
  let b := make_box (u8_of_i64 (i64_lit 300 eq_refl)) in   (* Box[uint8] in the model, bval = uint8(44) *)
  type_assert_safe TU8 (any (box_get b)) (fun _ ok =>       (* model: box_get : GoU8 ⇒ .(uint8) is TRUE *)
    println [ any (i64_of_u8 (box_get b)) ; any ok ]).      (* 44 true — runtime must AGREE (Box[uint8], not Box[int64]) *)

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
  uconst_demo                   >>'   (* prints: 1099511627781 100 100 (untyped constants: arbitrary precision, typed-at-use) *)
  u64_demo                      >>'   (* prints: 8000000000000000000 9000000000000000000 *)
  i64_pipeline_demo             >>'   (* prints: 9000000000000000001 (int64 through chan + map) *)
  u64_pipeline_demo             >>'   (* prints: 18000000000000000000 (uint64 >= 2^63 through chan + map) *)
  const_demo                    >>'   (* prints: 1000000000000 4611686018427387904 (untyped const arithmetic) *)
  recv_unused_ok_demo           >>'   (* prints: 77 (recv_ok with unused ok-flag) *)
  builtins_demo                 >>'   (* prints: 3 5 / 3 / 0 *)
  prec_demo                     >>'   (* prints: 10 20 *)
  neglit_demo                   >>'   (* prints: -7 -1 -2147483648 *)
  map_demo                      >>'   (* prints: 3 999 0 *)
  map_alias_demo                >>'   (* prints: 77 (map reference semantics: callee's write seen by caller) *)
  slice_demo                    >>'   (* prints: 5 3 / false *)
  slice_box_demo                >>'   (* prints: true false (a []int64 boxed as any: asserts to []int64 not int64 — recursive TSlice tag) *)
  chan_demo                     >>'   (* prints: 42 true / 0 false *)
  closed_panic_demo             >>'   (* prints: 1 / 2 (send-on-closed + double-close panics caught) *)
  select_demo                   >>'   (* prints: 42 (ch1 ready) *)
  select_default_demo           >>'   (* prints: 99 (default, ch empty) *)
  select_closed_demo            >>'   (* prints: 0 (select over CLOSED chan: recv ready with zero, NOT default) *)
  select_nonfinal_demo          >>'   (* prints: 3 / 5 (select as a NON-FINAL statement, then continues) *)
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
  arrN_demo                     >>'   (* prints: true false (array in a TYPED position: [3]int64 param) *)
  arr_field_ret_demo            >>'   (* prints: true 77 (array RETURN + array FIELD positions) *)
  arr_eq_demo                   >>'   (* prints: true false (array == is field-wise) *)
  arr_copy_demo                 >>'   (* prints: 10 99 (value-copy: a unchanged by arr_set) *)
  assert_safe_demo (7)%i64    >>'   (* prints: 7 true / false false *)
  string_demo                   >>'   (* prints: 2 / 71 true / 0 false / Go! *)
  str_cmp_demo                  >>'   (* prints: true false true false *)
  str_highbyte_demo             >>'   (* prints: true false (string comparison is UNSIGNED byte-wise, byte 0xC8) *)
  str_slice_demo                >>'   (* prints: world (s[a:b] string slice) *)
  bytes_demo                    >>'   (* prints: Hi ([]byte / string round-trip) *)
  rune_demo                     >>'   (* prints: Go ([]rune / string round-trip, UTF-8) *)
  rune_to_str_demo              >>'   (* prints: A (string(rune(65))) *)
  str_range_demo                >>'   (* prints: 0 72 / 1 8364 / 4 33 (for i, r := range s) *)
  tsw_demo (any true)           >>'   (* prints: true 1 (bool case) *)
  tsw_distinct_demo             >>'   (* prints: 200 / 7 (type switch respects uint8 vs int64 distinctness) *)
  tsw_inline_demo               >>'   (* prints: 200 / 5 (inline boxed scrutinee + non-final type-switch — gap closed) *)
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
  complex_const_runtime_demo        >>'   (* prints: -Inf (complex const ops forced to runtime; -0 preserved) *)
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
  narrow_ref_demo               >>'   (* prints: true false (a Ref GoU8 lowers to a uint8 cell, not int64) *)
  ptr_demo                      >>'   (* prints: 10 / 99 (pointer deref read/write) *)
  addr_of_demo                  >>'   (* prints: 10 / 99 (&x: writing through a local's address aliases it) *)
  ptr_box_demo                  >>'   (* prints: true false (a *int64 boxed as any: asserts to *int64 not int64 — recursive TPtr tag) *)
  new_demo                      >>'   (* prints: 0 (new(int64) → zero) *)
  ptr_safe_demo                 >>'   (* prints: 42 true / 0 false (nil-checked deref) *)
  ptr_chan_demo                 >>'   (* prints: 7 (a *int64 sent over a chan, deref'd) *)
  inbox_demo                    >>'   (* prints: fido 42 (a channel nested in a struct field) *)
  hub_demo                      >>'   (* prints: 7 99 (a SLICE of channels in a struct: channels-in-slice-in-struct) *)
  hub_worker_demo               >>'   (* prints: worker 123 (a GOROUTINE feeding a channel nested in a struct) *)
  chan_of_chan_demo             >>'   (* prints: 77 (a CHANNEL OF CHANNELS: a reply-chan sent over a chan, request/reply) *)
  pool_demo                     >>'   (* prints: 22 (CAPSTONE: struct + []chan + 2 goroutines + index + concurrent sum) *)
  linked_list_demo              >>'   (* prints: 1 2 3 (a RECURSIVE struct heap-traversed: type ListNode struct { Val int64; Next *ListNode }) *)
  chanbox_demo                  >>'   (* prints: 42 (a channel that SENDS ITSELF: type ChanBox struct { Id int64; Ch chan ChanBox }) *)
  cursed_demo                   >>'   (* prints: 99 1 2 3 (NORTH-STAR v2: a SLICE of 2 self-sending channels + a 3-node recursive list traversed, in one struct, safe by construction — per-program race-freedom is the limit-#2 frontier) *)
  slice_alias_demo              >>'   (* prints: 99 (sub-slice write seen through parent) *)
  slice_append_demo             >>'   (* prints: 9 (append reallocates a full slice) *)
  slice_makecap_demo            >>'   (* prints: 77 (make-with-cap: in-place append shares backing) *)
  slice_realloc_alias_demo      >>'   (* prints: 0 (forced realloc cap=len+1: 2nd append disjoint, not aliased) *)
  slice_clear_demo              >>'   (* prints: 0 (clear zeros the slice) *)
  slice_copy_demo               >>'   (* prints: 7 (copy src→dst) *)
  count_demo                    >>'   (* prints: 0 / 1 / 2 *)
  cfg_nonzero_entry_demo        >>'   (* prints: 5 / 7 (nonzero run_blocks entry now labelled, R#4 P1 3) *)
  defer_demo                    >>'   (* prints: 3 / 2 / 1 *)
  defer_loop_demo               >>'   (* prints: 2 / 1 / 0 *)
  point_demo                    >>'   (* prints: 3 / 4 / 7 *)
  labeled_demo                  >>'   (* prints: true / 5 *)
  method_demo                   >>'   (* prints: 7 / 13 / 14 / 27 *)
  method_value_demo             >>'   (* prints: 11 12 (method value p.Shifted passed to a HOF) *)
  method_expr_demo              >>'   (* prints: 11 (method expression Point.Sum_coords applied to p) *)
  multiret_demo                 >>'   (* prints: 4 3 (multiple return values + destructure) *)
  triple_demo                   >>'   (* prints: 1 2 3 (N-ary 3-return + nested destructure) *)
  pure_destr_demo               >>'   (* prints: 7 6 5 (destructure in a PURE value fn; last = blank binder) *)
  stmt_blank_demo               >>'   (* prints: 7 (blank-binder destructure, IO/statement position) *)
  narrow_pair_demo              >>'   (* prints: 44 7 (narrow `(uint8, uint8)` multi-return, components cast) *)
  io_method_demo                >>'   (* prints: 8 / 9 *)
  io_val_method_demo            >>'   (* prints: 8 17 (value-returning IO method, bind-chain tail) *)
  struct_eq_demo                >>'   (* prints: true false (struct ==, field-wise) *)
  struct_eq_native_demo         >>'   (* prints: true false (native p == q operator) *)
  nested_struct_demo            >>'   (* prints: 5 9 (nested struct fields) *)
  sptr_demo                     >>'   (* prints: 7 4 (mutable *Cell through a pointer) *)
  ptr_method_demo               >>'   (* prints: 11 (pointer-receiver method mutates *Cell) *)
  ptr_method_expr_demo          >>'   (* prints: 6 (pointer-receiver method expression) *)
  node_embed_demo               >>'   (* prints: 11 99 (embedded *Cell: promoted pointer-method through the pointer) *)
  nfield_ptr_demo               >>'   (* prints: 31 (pointer-receiver method mutates 3-field *Cell3) *)
  het_ptr_demo                  >>'   (* prints: 11 true (pointer method mutates heterogeneous *Pair) *)
  iface_demo                    >>'   (* prints: 14 / 1007 / 20 / 1010 *)
  single_iface_demo             >>'   (* prints: 15 (single-method interface dispatch) *)
  nullary_iface_demo            >>'   (* prints: fido (nullary method String()) *)
  embed_iface_demo              >>'   (* prints: 13 / 15 / 30 (interface embedding: union + upcasts) *)
  embed_iface_in_struct_demo    >>'   (* prints: 105 / 7 (interface embedded in a struct, method promoted) *)
  typestate_demo                >>'   (* prints: 1 / 7 *)
  repinv_demo                   >>'   (* prints: 3 / 7 *)
  deftype_demo                  >>'   (* prints: 42 (defined type with method) *)
  deftype_str_demo              >>'   (* prints: Hi, fido (defined type over string) *)
  deftype_iface_demo            >>'   (* prints: 120 (defined type satisfies an interface) *)
  named_func_demo               >>'   (* prints: 42 (named func type, type Handler func(int64) int64) *)
  deftype_slice_demo            >>'   (* prints: 3 (defined type over a slice, type IntList []int64) *)
  embed_demo                    >>'   (* prints: canine / canine (struct embedding + promotion) *)
  generics_demo                 >>'   (* prints: go / 3 / 2 / first (Go generics, type params) *)
  comparable_demo               >>'   (* prints: true true false true true (generic [K comparable]: int64/uint64/string/struct/DEFINED-TYPE → native ==) *)
  gstruct_demo                  >>'   (* prints: hi / true / 1 (generic struct Box[T]) *)
  gbox_narrow_demo              >>'   (* prints: 44 true (generic struct Box[uint8] — generics×narrow type inference) *)
  gmap_deftype_demo             >>'   (* prints: 2 (defined type over a map, type Counts map[string]int64) *)
  recursion_demo                >>'   (* prints: 3 / 2 / 1 (user recursion, self-calling func) *)
  pure_rec_demo                 >>'   (* prints: 16 (pure value-returning recursion, pow2 4) *)
  mutual_rec_demo               >>'   (* prints: true / false (mutual recursion is_even/is_odd) *)
  f32_demo                      >>'   (* prints: 7.5 (native float32 arithmetic) *)
  i64_of_narrow_demo            >>'   (* prints: 200 -5 60000 (narrow→int64 widening) *)
  widen_param_demo              >>'   (* prints: 200 -5 100 (narrow PARAM widen: int64(uint8)/int64(int8)/int(uint8) — review #4 P1 #4) *)
  i64_to_narrow_demo            >>'   (* prints: 52 -56 4464 705032704 (int64→narrow truncation) *)
  narrow_let_assert_demo        >>'   (* prints: 200 true (let-bound GoU8 boxes+asserts as uint8) *)
  type_identity_lock_demo       >>'   (* prints: true false true false true false false (uint8≠int64, GoI64=int64≠Go-int, R10 differential) *)
  narrow_cluster_lock_demo      >>'   (* prints: true true true true true (full #7 narrow cluster boxes as own Go type) *)
  uint_lock_demo                >>'   (* prints: true false (platform uint boxes as Go uint, distinct from int — review #4 P0 #1) *)
  narrow_ret_demo               >>'   (* prints: 52 -56 (narrow RETURN boundary: func returns uint8/int8) *)
  narrow_field_demo             >>'   (* prints: 44 7 (narrow struct FIELD boundary: ByteBox{uint8(…)} — review #4 P1 #4 slice 2) *)
  narrow_elem_demo              >>'   (* prints: 44 6 (narrow slice/array ELEMENT boundary: []uint8{uint8(…)} — review #4 P1 #4 slice 3) *)
  ptr_chan_narrow_demo          >>'   (* prints: 7 45 (narrow POINTER/CHANNEL payload: *uint8 / chan uint8 — review #4 P1 #4 slice 4) *)
  map_narrow_demo               >>'   (* prints: 44 9 (narrow map VALUE: map[int64]uint8 value+default — review #4 P1 #4 slice 5) *)
  map_key_narrow_demo           >>'   (* prints: 5 5 0 (narrow map KEY: map[uint8]int64 set/get/del — review #4 P1 #4 slice 6) *)
  arg_narrow_demo               >>'   (* prints: 44 (narrow function ARG: takes_u8(uint8(…)) — review #4 P1 #4 slice 7) *)
  vlet_demo                     >>'   (* prints: 21 (value-position let in int64 arithmetic) *)
  narrow_u64_demo               >>'   (* prints: 200 18446744073709551615 255 -1 (narrow↔uint64 via hub) *)
  floatconv_demo                >>'   (* prints: 16777216 / 7.5 (float32↔float64 convert) *)
  fconst_demo                   >>'   (* prints: 0.3 0.375 (untyped float CONSTANTS, exact-rational fold) *)
  f32_cmp_demo                  >>'   (* prints: true true true (native float32 comparison) *)
  f32_extra_demo                >>'   (* prints: -1.5 / 3 / 5 (float32 neg, min, max) *)
  f32_box_demo                  >>'   (* prints: true false true (float32 vs float64 boxing distinctness) *)
  f32_conv_demo                 >>'   (* prints: 1.6777216e7 / 0.3 (float32(int), float32 const) *)
  narrow_f32_demo               >>'   (* prints: 200 (narrow↔float32 composable via int64/float64) *)
  f32_const_runtime_demo        >>'   (* prints: +Inf / -Inf / +Inf / +Inf (const float ops forced to runtime IEEE) *)
  f32_of_int_demo               >>'   (* prints: false (direct float32(x) ≠ float32(float64(x)) — double rounding) *)
  f32_fconst_demo               >>'   (* prints: 0.3 (exact FConst → float32, single round) *)
  f64_fconst_big_demo           >>'   (* prints: 900719925474099.25 (large exact FConst → float64, single round) *)
  i64_of_f64_demo               >>'   (* prints: 3 / -2 (float64→int64 truncation) *)
  u64conv_demo                  >>'   (* prints: +1.844674e+019 13835058055282163712 (float↔uint64) *)
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
  ptr_get ptr_set ptr_new ptr_nil ptr_get_ok go_new ref_as_ptr
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
  dir_name f32_combine trunc64 narrow32 widen64
  i64_gtb i64_geb i64_neqb u64_gtb u64_geb u64_neqb
  u8_gtb u8_geb u8_neqb i8_gtb i8_geb i8_neqb
  u16_gtb u16_geb u16_neqb i16_gtb i16_geb i16_neqb
  u32_gtb u32_geb u32_neqb i32_gtb i32_geb i32_neqb
  i64_div i64_mod i64_and i64_or i64_xor i64_andnot i64_not i64_shl i64_shr
  u64_lit uint_lit u64_add u64_sub u64_mul u64_eqb u64_ltb u64_leb
  u64_div u64_mod u64_and u64_or u64_xor u64_andnot u64_not u64_shl u64_shr
  sret sbind ssend srecv slift run_session
  ceqb ceq_i64 ceq_u64 ceq_str ceq_point map_put vec3_eqb vec2_eqb
  fc_add fc_sub fc_mul fc_div f64_of_fconst.

Print Assumptions main_effect.

Go Main Extraction main "main_effect".
