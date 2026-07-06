(** builtins — the OP LAYER of the modelled Go: the IO-typed operations over the split-out
    foundations (the import block below; plans/builtins-split.md).  ★FROZEN
    raw ore (CLAUDE.md): never grows; being mined into final-purpose modules, then deleted. *)

Require Import Coq.Init.Specif.
Require Import Coq.Classes.Morphisms.   (* Proper / setoid rewriting for [io_eq] — replaces funext *)
Require Import Coq.Setoids.Setoid.
Require Import Coq.Lists.List.   (* app / tl for the channel FIFO buffer model *)
From Stdlib Require Import Lia.   (* happens-before timestamp arithmetic *)
From Stdlib Require Import ZArith.   (* Z.to_nat for the slice index *)
From Stdlib Require Import StrictProp.   (* Squash: carry a range invariant in SProp (proof-irrelevant ⇒ wrapper equality decided by the carrier alone, no axiom) *)
From Fido Require Import GoNumeric.   (* the numeric model (split wave 1) — ints + spec_float floats *)
From Fido Require Import GoRuntimeTypes.   (* the runtime type layer (split wave 2) — carriers + GoTypeTag + GoAny + zero_val *)
From Fido Require Import GoEffects.   (* the effect model (split wave 3) — World/Outcome/IO/io_eq/Hoare *)
From Fido Require Import GoPanic.     (* the runtime panic payloads (split wave 4) *)
From Fido Require Import GoSlice.     (* the pure-list slice/array model (split wave 5) *)
From Fido Require Import GoMap.       (* Go maps over the world heap (split wave 6) *)
From Fido Require Import GoChan.      (* Go channels + the go-mem story (split wave 7) *)
From Fido Require Import GoHeap.      (* the ref heap — locals/pointers/SliceH/struct heap (split wave 8) *)
Require Import Coq.Strings.String Coq.Strings.Ascii.
(* No [PrimInt63] / [PrimFloat] imports: the numeric model is AXIOM-FREE — integers are [Z]-carried
   records, heap locations [nat], floats [SpecFloat.spec_float]. *)




(** Function VALUES.  [gofunc_of] wraps a real closure as a non-nil [GoFunc]; the
    [zero_val (TArrow ..) = None] nil func is the ONLY other inhabitant.  [gofunc_call] is the
    EFFECTFUL invocation: a real closure runs, but a [nil] ([None]) func PANICS with Go's exact
    nil-dereference message ([rt_nil_deref]).  So a nil func is never a silently-callable
    placeholder — extraction emits the bare Go call [f(x)], whose runtime nil-panic MATCHES. *)
Definition gofunc_of {A B} (f : A -> B) : GoFunc A B := SomeFunc f.
Definition gofunc_call {A B} (f : GoFunc A B) (x : A) : IO B :=
  match f with
  | SomeFunc g => ret (g x)
  | NilFunc    => panic rt_nil_deref
  end.
Lemma gofunc_call_of : forall {A B} (f : A -> B) (x : A) (w : World),
  run_io (gofunc_call (gofunc_of f) x) w = ORet (f x) w.
Proof. reflexivity. Qed.
Lemma gofunc_call_nil : forall {A B} (x : A) (w : World),
  run_io (gofunc_call (@NilFunc A B) x) w = OPanic rt_nil_deref w.
Proof. reflexivity. Qed.

(** ---- Types ---- *)


(** ---- Fixed-width unsigned integers (precise, computable models) ----

    A [uintN] value is [Z]-carried, kept reduced mod 2^N after EVERY operation —
    exactly Go's uintN arithmetic.  DEFINITIONS, not axioms: computable
    ([vm_compute] discharges concrete wrap facts), nothing added to the trust base.

    TYPE DISTINCTNESS (Go spec "Numeric types": numeric types are DISTINCT;
    explicit conversions required).  [GoU8] is its OWN record type, so Rocq
    REJECTS mixing a [uint8] with another integer type; the only way in is
    [u8_lit] (the untyped-constant conversion).  The plugin ERASES the wrapper at
    extraction ([MkU8]/[u8raw] → identity), and each op lowers to int64 + the
    explicit mask ([u8_add a b] → [(a + b) & 0xff]) — compilable BY CONSTRUCTION.
    [u8_no_implicit] (a [Fail]) is the build-checked proof that mixing is
    unrepresentable. *)
(* Go spec "Constants": a constant is typed at use with a REPRESENTABILITY check —
   "it is an error if the constant value cannot be represented as a value of the
   respective type".  So an out-of-range constant is a COMPILE ERROR, NOT a silent
   wrap.  [u8_lit] demands a proof the constant fits ([x < 256], discharged by
   [eq_refl] for a literal in range); there is no masking, so [u8_lit 300] is
   unrepresentable — exactly Go's "constant overflows uint8". *)
(** [Z.modulo z 256] is always in [0, 256) — the range invariant every [uint8] op preserves.
    [u8wrap] is the ONLY internal constructor of a computed [GoU8]: it reduces mod 256 and
    carries the (SProp-erased) proof, so the forged [MkU8 300 _] is UNCONSTRUCTABLE.  SProp ⇒
    proof irrelevance ⇒ two [GoU8] with equal [u8raw] are definitionally equal. *)
Lemma in_u8_mod256 : forall z, in_u8 (Z.modulo z 256) = true.
Proof.
  intro z. unfold in_u8.
  pose proof (Z.mod_pos_bound z 256 ltac:(lia)) as [Hlo Hhi].
  apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Definition u8wrap (z : Z) : GoU8 := MkU8 (Z.modulo z 256) (squash (in_u8_mod256 z)).
Definition u8_lit (z : Z) (pf : in_u8 z = true) : GoU8 := MkU8 z (squash pf).
Definition u8_add (a b : GoU8) : GoU8 := u8wrap (u8raw a + u8raw b).
Definition u8_sub (a b : GoU8) : GoU8 := u8wrap (u8raw a - u8raw b).
Definition u8_mul (a b : GoU8) : GoU8 := u8wrap (u8raw a * u8raw b).
Definition u8_eqb (a b : GoU8) : bool := Z.eqb (u8raw a) (u8raw b).
Definition u8_ltb (a b : GoU8) : bool := Z.ltb (u8raw a) (u8raw b).
Definition u8_leb (a b : GoU8) : bool := Z.leb (u8raw a) (u8raw b).

(* Build-checked: [uint8] and [int] do NOT mix — no implicit conversion. *)
Fail Definition u8_no_implicit (x : GoU8) : GoU8 := u8_add x (5 : nat).
(* Build-checked: an out-of-range constant is UNREPRESENTABLE (Go: "overflows uint8"). *)
Fail Definition u8_const_oob : GoU8 := u8_lit 300 eq_refl.
(* Build-checked: even the RAW constructor cannot forge an out-of-range uint8 — [MkU8] demands a
   proof [u8raw < 256]. *)
Fail Definition u8_forged : GoU8 := MkU8 300 (squash eq_refl).

(* Go's [byte] is a predeclared alias for [uint8] — the faithful [GoU8] record.
   So [s[i]] (a string byte) and a [uint8] are the SAME type, as in Go. *)
Notation GoByte := GoU8.

(** ---- Signed fixed-width integers ----

    [int8] in [-128, 128).  Go's int8 arithmetic wraps two's-complement.  Model:
    reduce mod 256 then SIGN-EXTEND onto [[-128,128)] — exactly Go's [int8(x)]
    conversion.  Comparison is SIGNED ([Z.ltb] on the sign-extended value → Go's
    signed int64 [<]).  The plugin emits the explicit int64 mask + sign-extend,
    e.g. [i8_add a b] → [((((a + b) & 0xff) ^ 0x80) - 0x80)].  Each width is a
    DISTINCT record (like [GoU8]); the wrapper erases at extraction. *)
(* [i8_norm_z] is hoisted up to the wrapper-record block (the GoI8 provenance invariant needs it).
   [i8wrap] is the internal constructor: normalize to 8-bit signed + carry the (trivial) provenance
   proof, so a forged [MkI8 200 _] is unconstructable (200 is not in [i8_norm_z]'s image). *)
Definition i8wrap (z : Z) : GoI8 := MkI8 (i8_norm_z z) (squash (in_i8_norm z)).
Definition i8_lit (z : Z) (pf : in_i8 z = true) : GoI8 := MkI8 z (squash pf).
Definition i8_add (a b : GoI8) : GoI8 := i8wrap (i8raw a + i8raw b).
Definition i8_sub (a b : GoI8) : GoI8 := i8wrap (i8raw a - i8raw b).
Definition i8_mul (a b : GoI8) : GoI8 := i8wrap (i8raw a * i8raw b).
Definition i8_eqb (a b : GoI8) : bool := Z.eqb (i8raw a) (i8raw b).
Definition i8_ltb (a b : GoI8) : bool := Z.ltb (i8raw a) (i8raw b).   (* SIGNED comparison *)
Definition i8_leb (a b : GoI8) : bool := Z.leb (i8raw a) (i8raw b).

(** Direct [>] / [>=] / [!=] for the fixed-width types, completing Go's six comparison
    operators (here for [uint8]/[int8] — representative; the plugin's [fw_is] recognizes
    the same op on EVERY width, so [u16]/[i16]/[u32]/[i32] are identical one-liners).
    Defined as the swapped [</<=] and [negb (==)] but recognized by name and lowered to
    the DIRECT Go operator. *)
Definition u8_gtb  (a b : GoU8) : bool := u8_ltb b a.
Definition u8_geb  (a b : GoU8) : bool := u8_leb b a.
Definition u8_neqb (a b : GoU8) : bool := negb (u8_eqb a b).
Definition i8_gtb  (a b : GoI8) : bool := i8_ltb b a.
Definition i8_geb  (a b : GoI8) : bool := i8_leb b a.
Definition i8_neqb (a b : GoI8) : bool := negb (i8_eqb a b).

(** [uint16] / [int16] — the same template at width 16 (mask [0xffff]; sign bit
    [0x8000]).  Still fully faithful on the 63-bit carrier: a 16-bit product is
    [< 2^32], far below the [2^62] boundary, so [mul] is exact too. *)
(** [land x 65535] is always [< 65536] — the [uint16] range invariant (parallel to [land255_lt256]).
    [u16wrap] masks + carries the SProp proof, so a forged [MkU16 70000 _] is unconstructable. *)
Lemma in_u16_mod65536 : forall z, in_u16 (Z.modulo z 65536) = true.
Proof.
  intro z. unfold in_u16.
  pose proof (Z.mod_pos_bound z 65536 ltac:(lia)) as [Hlo Hhi].
  apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Definition u16wrap (z : Z) : GoU16 := MkU16 (Z.modulo z 65536) (squash (in_u16_mod65536 z)).
Definition u16_lit (z : Z) (pf : in_u16 z = true) : GoU16 := MkU16 z (squash pf).
Definition u16_add (a b : GoU16) : GoU16 := u16wrap (u16raw a + u16raw b).
Definition u16_sub (a b : GoU16) : GoU16 := u16wrap (u16raw a - u16raw b).
Definition u16_mul (a b : GoU16) : GoU16 := u16wrap (u16raw a * u16raw b).
Definition u16_eqb (a b : GoU16) : bool := Z.eqb (u16raw a) (u16raw b).
Definition u16_ltb (a b : GoU16) : bool := Z.ltb (u16raw a) (u16raw b).
Definition u16_leb (a b : GoU16) : bool := Z.leb (u16raw a) (u16raw b).

(* [i16_norm_z] hoisted to the wrapper-record block (the GoI16 provenance invariant needs it).
   [i16wrap] = normalize + carry the trivial provenance proof, so [MkI16 40000 _] is unconstructable. *)
Definition i16wrap (z : Z) : GoI16 := MkI16 (i16_norm_z z) (squash (in_i16_norm z)).
Definition i16_lit (z : Z) (pf : in_i16 z = true) : GoI16 := MkI16 z (squash pf).
Definition i16_add (a b : GoI16) : GoI16 := i16wrap (i16raw a + i16raw b).
Definition i16_sub (a b : GoI16) : GoI16 := i16wrap (i16raw a - i16raw b).
Definition i16_mul (a b : GoI16) : GoI16 := i16wrap (i16raw a * i16raw b).
Definition i16_eqb (a b : GoI16) : bool := Z.eqb (i16raw a) (i16raw b).
Definition i16_ltb (a b : GoI16) : bool := Z.ltb (i16raw a) (i16raw b).
Definition i16_leb (a b : GoI16) : bool := Z.leb (i16raw a) (i16raw b).

(* Build-checked (Go spec "Numeric types": distinct types, no implicit mixing):
   neither a typed value of another numeric type nor an [int] may be passed. *)
Fail Definition i8_no_implicit  (x : GoI8)  : GoI8  := i8_add  x (5 : nat).
Fail Definition u16_no_implicit (x : GoU16) : GoU16 := u16_add x (5 : nat).
Fail Definition i16_no_implicit (x : GoI16) : GoI16 := i16_add x (5 : nat).
(* Cross-WIDTH too: [uint8] and [uint16] are distinct types — no implicit widen. *)
Fail Definition u8_u16_no_mix (x : GoU8) (y : GoU16) : GoU16 := u16_add y x.

(* Build-checked (Go spec "Constants"): out-of-range constants are UNREPRESENTABLE
   (a compile error), per width — no silent wrap. *)
Fail Definition i8_const_oob  : GoI8  := i8_lit  200    eq_refl.   (* > 127 *)
(* Build-checked: the RAW constructor cannot forge an out-of-range int8 — the provenance proof
   [in_i8 200 = true] is false (200 is not in the int8 range [-128,128)). *)
Fail Definition i8_forged : GoI8 := MkI8 200 (squash (ex_intro _ 200 eq_refl)).
Fail Definition u16_const_oob : GoU16 := u16_lit 70000  eq_refl.   (* >= 2^16 *)
(* Build-checked: the RAW constructor cannot forge an out-of-range uint16 (SProp range proof). *)
Fail Definition u16_forged : GoU16 := MkU16 70000 (squash eq_refl).
Fail Definition i16_const_oob : GoI16 := i16_lit 40000  eq_refl.   (* > 32767 *)
(* Build-checked: the RAW constructor cannot forge an out-of-range int16 (provenance proof false). *)
Fail Definition i16_forged : GoI16 := MkI16 40000 (squash (ex_intro _ 40000 eq_refl)).

(** ---- Fixed-width bitwise operators (Go spec "Arithmetic operators": [& | ^ &^],
    and unary [^] complement) ----

    Bitwise AND / OR / XOR / AND-NOT and unary complement on the fixed-width
    types.  TOTAL and panic-free (unlike shifts, whose count can panic).
    Faithful by construction:
    - [uintN]: AND/OR/XOR of two in-range values stay in [0,2^N), so no mask is
      needed; AND-NOT and complement flip within the width via [lxor _ (2^N-1)].
    - [intN]: the sign-extended carrier already makes the raw bitwise op correct,
      but we re-[norm] (idempotent) so every result is manifestly a valid [intN].
    Go's [&^] (AND-NOT) and unary [^] (complement) are single operators.  The
    plugin emits the bare Go infix [& | ^ &^] / unary [^] (no wrap) — faithful
    because the operands are in range / sign-extended (verified on int64). *)
Definition u8_and     (a b : GoU8)  : GoU8  := u8wrap (Z.land (u8raw a) (u8raw b)).
Definition u8_or      (a b : GoU8)  : GoU8  := u8wrap (Z.lor  (u8raw a) (u8raw b)).
Definition u8_xor     (a b : GoU8)  : GoU8  := u8wrap (Z.lxor (u8raw a) (u8raw b)).
Definition u8_andnot  (a b : GoU8)  : GoU8  := u8wrap (Z.land (u8raw a) (Z.lxor (u8raw b) 255)).
Definition u8_not     (a   : GoU8)  : GoU8  := u8wrap (Z.lxor (u8raw a) 255).
Definition i8_and     (a b : GoI8)  : GoI8  := i8wrap (Z.land (i8raw a) (i8raw b)).
Definition i8_or      (a b : GoI8)  : GoI8  := i8wrap (Z.lor  (i8raw a) (i8raw b)).
Definition i8_xor     (a b : GoI8)  : GoI8  := i8wrap (Z.lxor (i8raw a) (i8raw b)).
Definition i8_andnot  (a b : GoI8)  : GoI8  := i8wrap (Z.land (i8raw a) (Z.lxor (i8raw b) 255)).
Definition i8_not     (a   : GoI8)  : GoI8  := i8wrap (Z.lxor (i8raw a) 255).
Definition u16_and    (a b : GoU16) : GoU16 := u16wrap (Z.land (u16raw a) (u16raw b)).
Definition u16_or     (a b : GoU16) : GoU16 := u16wrap (Z.lor  (u16raw a) (u16raw b)).
Definition u16_xor    (a b : GoU16) : GoU16 := u16wrap (Z.lxor (u16raw a) (u16raw b)).
Definition u16_andnot (a b : GoU16) : GoU16 := u16wrap (Z.land (u16raw a) (Z.lxor (u16raw b) 65535)).
Definition u16_not    (a   : GoU16) : GoU16 := u16wrap (Z.lxor (u16raw a) 65535).
Definition i16_and    (a b : GoI16) : GoI16 := i16wrap (Z.land (i16raw a) (i16raw b)).
Definition i16_or     (a b : GoI16) : GoI16 := i16wrap (Z.lor  (i16raw a) (i16raw b)).
Definition i16_xor    (a b : GoI16) : GoI16 := i16wrap (Z.lxor (i16raw a) (i16raw b)).
Definition i16_andnot (a b : GoI16) : GoI16 := i16wrap (Z.land (i16raw a) (Z.lxor (i16raw b) 65535)).
Definition i16_not    (a   : GoI16) : GoI16 := i16wrap (Z.lxor (i16raw a) 65535).

(* Build-checked: bitwise ops respect type distinctness too (no implicit mix). *)
Fail Definition u8_and_no_implicit (x : GoU8) : GoU8 := u8_and x (5 : nat).

(** ---- Fixed-width shifts (Go spec "Arithmetic operators": [<< >>]) ----

    Left / right shift on the fixed-width types.  Unlike the bitwise ops, a shift
    can PANIC: Go panics if the count is negative.  So — exactly like [div_nz] —
    the shift is EVIDENCE-CARRYING: it demands a proof the count is non-negative
    ([0 <= k], discharged by [eq_refl] for a literal), making the panic
    unreachable (safe-by-construction).  There is NO upper limit on the count
    (Go: an over-width shift gives 0 / sign-fill, not UB); the primitives agree —
    [lsl]/[lsr] give 0 for [k >= width], [asr] fills with the sign bit.
    - [<<]: [uintN] truncates to the width ([(x<<k) mod 2^N], via [land]); [intN]
      is two's-complement (sign-extend via [norm]).
    - [>>]: [uintN] is LOGICAL ([lsr]); [intN] is ARITHMETIC ([asr]) — sign-
      preserving, truncating toward −∞, NOT toward zero like [/] ([-3>>1 = -2],
      whereas [-3/2 = -1]).
    The plugin emits Go [x << k] / [x >> k]: for [>>], the int64 carrier is
    non-negative for [uintN] (so Go's [>>] is logical) and sign-extended for
    [intN] (so Go's [>>] is arithmetic) — both correct with no mask. *)
Definition u8_shl  (x : GoU8)  (k : GoInt) (_ : (Z.leb 0 (intraw k)) = true) : GoU8  := u8wrap (Z.shiftl (u8raw x) (intraw k)).
Definition u8_shr  (x : GoU8)  (k : GoInt) (_ : (Z.leb 0 (intraw k)) = true) : GoU8  := u8wrap (Z.shiftr (u8raw x) (intraw k)).
Definition i8_shl  (x : GoI8)  (k : GoInt) (_ : (Z.leb 0 (intraw k)) = true) : GoI8  := i8wrap (Z.shiftl (i8raw x) (intraw k)).
Definition i8_shr  (x : GoI8)  (k : GoInt) (_ : (Z.leb 0 (intraw k)) = true) : GoI8  := i8wrap (Z.shiftr (i8raw x) (intraw k)).
Definition u16_shl (x : GoU16) (k : GoInt) (_ : (Z.leb 0 (intraw k)) = true) : GoU16 := u16wrap (Z.shiftl (u16raw x) (intraw k)).
Definition u16_shr (x : GoU16) (k : GoInt) (_ : (Z.leb 0 (intraw k)) = true) : GoU16 := u16wrap (Z.shiftr (u16raw x) (intraw k)).
Definition i16_shl (x : GoI16) (k : GoInt) (_ : (Z.leb 0 (intraw k)) = true) : GoI16 := i16wrap (Z.shiftl (i16raw x) (intraw k)).
Definition i16_shr (x : GoI16) (k : GoInt) (_ : (Z.leb 0 (intraw k)) = true) : GoI16 := i16wrap (Z.shiftr (i16raw x) (intraw k)).

(* Build-checked: a NEGATIVE shift count is UNREPRESENTABLE (Go panics on it). *)
Fail Definition u8_shl_neg : GoU8 := u8_shl (u8_lit 1 eq_refl) (MkGoInt (-1)%Z (squash eq_refl)) eq_refl.

(** ---- Numeric conversions (Go spec "Conversions") ----

    "When converting between integer types, if the value is a signed integer, it
    is sign extended to implicit infinite precision ... It is then truncated to
    fit in the result type's size."  These are the EXPLICIT conversions the
    "Numeric types" rule requires to mix distinct types — the type checker rejects
    implicit mixing (the [*_no_implicit] [Fail]s), so a value crosses types only
    through one of these.

    Every conversion routes through the [int] carrier, which already holds each
    fixed-width value's exact mathematical value (sign-extended for [intN],
    zero-extended for [uintN]):
    - [int_of_FW] WIDENS to [int] — value preserved in the model (every [uintN]/[intN]
      fits in [int]), but EMITTED as a real cast [int(x)], NOT identity (a narrow Go value
      at an [int] boundary needs it).
    - [FW_of_int] NARROWS [int] to the width — TRUNCATE ([land] to [uintN], or
      mask+sign-extend [norm] to [intN]) — exactly Go's [uint8(x)]/[int8(x)].  No
      representability proof (unlike [*_lit]): a conversion truncates, it does not
      reject.  Composition handles cross-width ([uint8(int16val)] =
      [u8_of_int (int_of_i16 x)] = low 8 bits, faithful). *)
Definition int_of_u8  (x : GoU8)  : GoInt := intwrap (u8raw  x).
Definition int_of_i8  (x : GoI8)  : GoInt := intwrap (i8raw  x).
Definition int_of_u16 (x : GoU16) : GoInt := intwrap (u16raw x).
Definition int_of_i16 (x : GoI16) : GoInt := intwrap (i16raw x).
Definition u8_of_int  (x : GoInt) : GoU8  := u8wrap (intraw x).
Definition i8_of_int  (x : GoInt) : GoI8  := i8wrap (intraw x).
Definition u16_of_int (x : GoInt) : GoU16 := u16wrap (intraw x).
Definition i16_of_int (x : GoInt) : GoI16 := i16wrap (intraw x).

(* Build-checked: a conversion takes an [int], NOT another fixed-width type — so a
   cross-type conversion MUST go through [int] (e.g. [u8_of_int (int_of_i16 y)]),
   never [u8_of_int y] directly. *)
Fail Definition u8_of_i16_direct (y : GoI16) : GoU8 := u8_of_int y.

(** ---- Narrow -> full-width int64 WIDENING (Go [int64(x)]) ----
    Widen a fixed-width [uintN]/[intN] to the CANONICAL [int64] ([GoI64]).  The
    value is PRESERVED: an unsigned narrow ([0..2^N-1]) and a signed narrow
    ([-2^(N-1)..2^(N-1)-1]) both fit int64 exactly, so the carrier's [Z] reading
    ([uNraw]/[iNraw] — the value's SIGNED reading, correct for both: unsigned narrows
    are [< 2^32] and signed narrows hold their sign-extended value) is in
    range and lands unchanged in [GoI64].  Distinct from the narrow [int_of_FW]
    (which targets the index-[int]); these target the value-[int64].
    The body is a PURE [Z] re-wrap ([i64wrap] of the narrow's [Z] reading), but the
    EMITTED Go is a real widening cast [int64(x)], NOT identity — a narrow Go value
    at an int64 boundary needs the cast.  Machine-checked in main.v. *)
Definition i64_of_u8  (a : GoU8)  : GoI64 := i64wrap (u8raw  a).
Definition i64_of_i8  (a : GoI8)  : GoI64 := i64wrap (i8raw  a).
Definition i64_of_u16 (a : GoU16) : GoI64 := i64wrap (u16raw a).
Definition i64_of_i16 (a : GoI16) : GoI64 := i64wrap (i16raw a).
Definition i64_of_u32 (a : GoU32) : GoI64 := i64wrap (u32raw a).
Definition i64_of_i32 (a : GoI32) : GoI64 := i64wrap (i32raw a).

(** ---- Fixed-width division / remainder (Go spec "Arithmetic operators": [/ %]) ----
    EVIDENCE-CARRYING like [div_nz]: demand the divisor be non-zero (Go panics on a
    zero divisor), so the panic is unreachable (safe-by-construction).
    - [uintN]: the carrier is non-negative, so the SIGNED primitives [divs]/[mods]
      compute the UNSIGNED quotient/remainder; the result is in range (quotient
      <= dividend, |remainder| < divisor), no mask.
    - [intN]: SIGNED div/mod (truncate toward zero), wrapped to the width ([norm]) —
      this is where the most-negative / [-1] overflow lands: Go [int8(-128)/int8(-1)
      = -128] (two's-complement wrap), and [norm] gives exactly that. *)
Definition u8_div  (a b : GoU8)  (_ : (Z.eqb (u8raw b)  0) = false) : GoU8  := u8wrap (Z.quot (u8raw a) (u8raw b)).
Definition u8_mod  (a b : GoU8)  (_ : (Z.eqb (u8raw b)  0) = false) : GoU8  := u8wrap (Z.rem (u8raw a) (u8raw b)).
Definition i8_div  (a b : GoI8)  (_ : (Z.eqb (i8raw b)  0) = false) : GoI8  := i8wrap (Z.quot (i8raw a) (i8raw b)).
Definition i8_mod  (a b : GoI8)  (_ : (Z.eqb (i8raw b)  0) = false) : GoI8  := i8wrap (Z.rem (i8raw a) (i8raw b)).
Definition u16_div (a b : GoU16) (_ : (Z.eqb (u16raw b) 0) = false) : GoU16 := u16wrap (Z.quot (u16raw a) (u16raw b)).
Definition u16_mod (a b : GoU16) (_ : (Z.eqb (u16raw b) 0) = false) : GoU16 := u16wrap (Z.rem (u16raw a) (u16raw b)).
Definition i16_div (a b : GoI16) (_ : (Z.eqb (i16raw b) 0) = false) : GoI16 := i16wrap (Z.quot (i16raw a) (i16raw b)).
Definition i16_mod (a b : GoI16) (_ : (Z.eqb (i16raw b) 0) = false) : GoI16 := i16wrap (Z.rem (i16raw a) (i16raw b)).

(* Build-checked: a ZERO divisor is UNREPRESENTABLE (Go panics on it). *)
Fail Definition u8_div_zero : GoU8 := u8_div (u8_lit 1 eq_refl) (u8_lit 0 eq_refl) eq_refl.

(** ---- uint32 / int32 — the SAME template at width 32 ----

    Distinct [Z]-carried records, same as the narrower widths: every op
    (add/sub/mul, comparison, bitwise, shift, div/mod, conversions) reduces mod
    [2^32] (sign-extending for [int32]) — exact by construction on [Z].
    Machine-checked: [spec_u32_mul_wrap]/[spec_i32_mul_wrap] in main.v. *)
(** [land x (2^32-1)] is always [< 2^32] — the [uint32] range invariant (parallel to
    [land255_lt256]).  [u32wrap] masks + carries the SProp proof; forged [MkU32 5000000000 _] is
    unconstructable. *)
Lemma in_u32_mod : forall z, in_u32 (Z.modulo z 4294967296) = true.
Proof.
  intro z. unfold in_u32.
  pose proof (Z.mod_pos_bound z 4294967296 ltac:(lia)) as [Hlo Hhi].
  apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Definition u32wrap (z : Z) : GoU32 := MkU32 (Z.modulo z 4294967296) (squash (in_u32_mod z)).
Definition u32_lit (z : Z) (pf : in_u32 z = true) : GoU32 := MkU32 z (squash pf).
Definition u32_add (a b : GoU32) : GoU32 := u32wrap (u32raw a + u32raw b).
Definition u32_sub (a b : GoU32) : GoU32 := u32wrap (u32raw a - u32raw b).
Definition u32_mul (a b : GoU32) : GoU32 := u32wrap (u32raw a * u32raw b).
Definition u32_eqb (a b : GoU32) : bool := Z.eqb (u32raw a) (u32raw b).
Definition u32_ltb (a b : GoU32) : bool := Z.ltb (u32raw a) (u32raw b).
Definition u32_leb (a b : GoU32) : bool := Z.leb (u32raw a) (u32raw b).
Definition u32_and    (a b : GoU32) : GoU32 := u32wrap (Z.land (u32raw a) (u32raw b)).
Definition u32_or     (a b : GoU32) : GoU32 := u32wrap (Z.lor  (u32raw a) (u32raw b)).
Definition u32_xor    (a b : GoU32) : GoU32 := u32wrap (Z.lxor (u32raw a) (u32raw b)).
Definition u32_andnot (a b : GoU32) : GoU32 := u32wrap (Z.land (u32raw a) (Z.lxor (u32raw b) 4294967295)).
Definition u32_not    (a   : GoU32) : GoU32 := u32wrap (Z.lxor (u32raw a) 4294967295).
Definition u32_shl (x : GoU32) (k : GoInt) (_ : (Z.leb 0 (intraw k)) = true) : GoU32 := u32wrap (Z.shiftl (u32raw x) (intraw k)).
Definition u32_shr (x : GoU32) (k : GoInt) (_ : (Z.leb 0 (intraw k)) = true) : GoU32 := u32wrap (Z.shiftr (u32raw x) (intraw k)).
Definition u32_div (a b : GoU32) (_ : (Z.eqb (u32raw b) 0) = false) : GoU32 := u32wrap (Z.quot (u32raw a) (u32raw b)).
Definition u32_mod (a b : GoU32) (_ : (Z.eqb (u32raw b) 0) = false) : GoU32 := u32wrap (Z.rem (u32raw a) (u32raw b)).
Definition int_of_u32 (x : GoU32) : GoInt := intwrap (u32raw x).
Definition u32_of_int (x : GoInt) : GoU32 := u32wrap (intraw x).

(* [i32_norm_z] hoisted to the wrapper-record block (the GoI32 provenance invariant needs it).
   [i32wrap] = normalize + carry the trivial provenance proof, so [MkI32 5000000000 _] is
   unconstructable. *)
Definition i32wrap (z : Z) : GoI32 := MkI32 (i32_norm_z z) (squash (in_i32_norm z)).
Definition i32_lit (z : Z) (pf : in_i32 z = true) : GoI32 := MkI32 z (squash pf).
Definition i32_add (a b : GoI32) : GoI32 := i32wrap (i32raw a + i32raw b).
Definition i32_sub (a b : GoI32) : GoI32 := i32wrap (i32raw a - i32raw b).
Definition i32_mul (a b : GoI32) : GoI32 := i32wrap (i32raw a * i32raw b).
Definition i32_eqb (a b : GoI32) : bool := Z.eqb (i32raw a) (i32raw b).
Definition i32_ltb (a b : GoI32) : bool := Z.ltb (i32raw a) (i32raw b).
Definition i32_leb (a b : GoI32) : bool := Z.leb (i32raw a) (i32raw b).

(** Direct [>] / [>=] / [!=] for the remaining fixed widths (u16/i16/u32/i32),
    completing Go's six comparison operators for EVERY integer type.  Same trivial
    pattern as u8/i8 (swapped [</<=], [negb (==)]) recognized by the generic [fw_is]. *)
Definition u16_gtb  (a b : GoU16) : bool := u16_ltb b a.
Definition u16_geb  (a b : GoU16) : bool := u16_leb b a.
Definition u16_neqb (a b : GoU16) : bool := negb (u16_eqb a b).
Definition i16_gtb  (a b : GoI16) : bool := i16_ltb b a.
Definition i16_geb  (a b : GoI16) : bool := i16_leb b a.
Definition i16_neqb (a b : GoI16) : bool := negb (i16_eqb a b).
Definition u32_gtb  (a b : GoU32) : bool := u32_ltb b a.
Definition u32_geb  (a b : GoU32) : bool := u32_leb b a.
Definition u32_neqb (a b : GoU32) : bool := negb (u32_eqb a b).
Definition i32_gtb  (a b : GoI32) : bool := i32_ltb b a.
Definition i32_geb  (a b : GoI32) : bool := i32_leb b a.
Definition i32_neqb (a b : GoI32) : bool := negb (i32_eqb a b).
Definition i32_and    (a b : GoI32) : GoI32 := i32wrap (Z.land (i32raw a) (i32raw b)).
Definition i32_or     (a b : GoI32) : GoI32 := i32wrap (Z.lor  (i32raw a) (i32raw b)).
Definition i32_xor    (a b : GoI32) : GoI32 := i32wrap (Z.lxor (i32raw a) (i32raw b)).
Definition i32_andnot (a b : GoI32) : GoI32 := i32wrap (Z.land (i32raw a) (Z.lxor (i32raw b) 4294967295)).
Definition i32_not    (a   : GoI32) : GoI32 := i32wrap (Z.lxor (i32raw a) 4294967295).
Definition i32_shl (x : GoI32) (k : GoInt) (_ : (Z.leb 0 (intraw k)) = true) : GoI32 := i32wrap (Z.shiftl (i32raw x) (intraw k)).
Definition i32_shr (x : GoI32) (k : GoInt) (_ : (Z.leb 0 (intraw k)) = true) : GoI32 := i32wrap (Z.shiftr (i32raw x) (intraw k)).
Definition i32_div (a b : GoI32) (_ : (Z.eqb (i32raw b) 0) = false) : GoI32 := i32wrap (Z.quot (i32raw a) (i32raw b)).
Definition i32_mod (a b : GoI32) (_ : (Z.eqb (i32raw b) 0) = false) : GoI32 := i32wrap (Z.rem (i32raw a) (i32raw b)).
Definition int_of_i32 (x : GoI32) : GoInt := intwrap (i32raw x).
Definition i32_of_int (x : GoInt) : GoI32 := i32wrap (intraw x).

(* Build-checked: u32/i32 are distinct, out-of-range constants unrepresentable. *)
Fail Definition u32_no_implicit (x : GoU32) : GoU32 := u32_add x (5 : nat).
Fail Definition u32_const_oob   : GoU32 := u32_lit 5000000000 eq_refl.   (* >= 2^32 *)
(* Build-checked: the RAW constructor cannot forge an out-of-range uint32 (SProp range proof). *)
Fail Definition u32_forged : GoU32 := MkU32 5000000000 (squash eq_refl).
(* Build-checked: the RAW int32 constructor cannot forge an out-of-range value (provenance proof false). *)
Fail Definition i32_forged : GoI32 := MkI32 5000000000 (squash (ex_intro _ 5000000000 eq_refl)).

(** ---- int64 — FULL-WIDTH signed 64-bit (Go spec "Numeric types") ----

    The faithful model of Go's [int64] / (64-bit) [int]: carried by [Z] and
    normalised mod [2^64] into the signed range after every op.
    [wrap64] is the two's-complement wrap; it is the IDENTITY
    on in-range values (so a no-overflow op equals the exact mathematical result —
    [i64_add_no_overflow_exact] in main.v), and at the boundary [2^63-1 + 1] wraps to
    [-2^63] exactly like Go ([spec_i64_add_wrap]).  Extraction erases the wrapper and
    emits BARE Go int64 ops ([a + b], …): Go's int64 wraps natively at [2^64], so the
    mask the narrow widths need is here unnecessary.  Comparison is signed [Z]
    comparison — valid because every stored value is normalised into [-2^63, 2^63). *)
(* [wrap64]/[in_i64]/[i64wrap] are hoisted to the wrapper-record block. *)
(* Smart literal: DEMANDS the constant fit int64 (Go's compile-time representability
   check); an out-of-range literal is unrepresentable ([i64_const_oob] Fail). *)
Definition i64_lit (z : Z) (pf : in_i64 z = true) : GoI64 := MkI64 z (squash pf).
Definition i64_add (a b : GoI64) : GoI64 := i64wrap (i64raw a + i64raw b).
Definition i64_sub (a b : GoI64) : GoI64 := i64wrap (i64raw a - i64raw b).
Definition i64_mul (a b : GoI64) : GoI64 := i64wrap (i64raw a * i64raw b).
(* Unary negation (Go's unary [-]): [-x] = [0 - x] with the same two's-complement wrap
   (so [-MININT = MININT]).  Lowers to the DIRECT prefix [-x], not the encoded [0 - x]. *)
Definition i64_neg (a : GoI64) : GoI64 := i64wrap (wrap64 (Z.opp (i64raw a))).
Definition i64_eqb (a b : GoI64) : bool := Z.eqb (i64raw a) (i64raw b).
Definition i64_ltb (a b : GoI64) : bool := Z.ltb (i64raw a) (i64raw b).
Definition i64_leb (a b : GoI64) : bool := Z.leb (i64raw a) (i64raw b).

(* Platform-int [GoInt] ops — the EXACT [GoI64] shape, rendered with Go [int] operators
   instead of [int64].  [int_lit] is the proof-carrying literal (NoInline'd, plugin-folded — bare
   decimal in expression position, [int(N)] when a Go type must be pinned); arithmetic wraps at the
   true [2^63] via [wrap64].  [int_div]/[int_mod] are evidence-gated (nonzero divisor) — Go's truncated
   [/]/[%] ([Z.quot]/[Z.rem]); [MININT/-1] overflows and wraps to MININT, the TRUE int64 [-2^63]. *)
Definition int_lit (z : Z) (pf : in_i64 z = true) : GoInt := MkGoInt z (squash pf).
Definition int_add (a b : GoInt) : GoInt := intwrap (intraw a + intraw b).
Definition int_sub (a b : GoInt) : GoInt := intwrap (intraw a - intraw b).
Definition int_mul (a b : GoInt) : GoInt := intwrap (intraw a * intraw b).
Definition int_neg (a : GoInt) : GoInt := intwrap (wrap64 (Z.opp (intraw a))).
(* Go's unary [^x] on [int] — the two's-complement BITWISE COMPLEMENT, = [-x-1] = [Z.lnot] exactly
   (verified `go run`: ^3 = -4, ^-1 = 0, ^minint = maxint); a bijection on the int64 window, so the
   wrap is the identity here — [intwrap] kept for the carrier's range invariant. *)
Definition int_not (a : GoInt) : GoInt := intwrap (Z.lnot (intraw a)).
(* Go's BITWISE binops on [int] — total on the carrier (the two's-complement window is closed
   under [land]/[lor]/[lxor]; [&^] = AND NOT, [Z.land a (Z.lnot b)]); [intwrap] kept for the
   carrier's range invariant (verified `go run`: 3&1=1, 3|4=7, 3^1=2, 3&^1=2, 3&^2=1). *)
Definition int_and    (a b : GoInt) : GoInt := intwrap (Z.land (intraw a) (intraw b)).
Definition int_or     (a b : GoInt) : GoInt := intwrap (Z.lor  (intraw a) (intraw b)).
Definition int_xor    (a b : GoInt) : GoInt := intwrap (Z.lxor (intraw a) (intraw b)).
Definition int_andnot (a b : GoInt) : GoInt := intwrap (Z.land (intraw a) (Z.lnot (intraw b))).
(* Go's SHIFTS on [int] — the EXACT [i64_shl]/[i64_shr] shape: evidence-gated NONNEGATIVE count
   ([<<] wraps at [2^63] via [intwrap]'s [wrap64]; [>>] is the ARITHMETIC shift — [Z.shiftr] on a
   negative is floor division, Go's sign fill; verified `go run`: 3<<62 wraps negative, -3>>1 = -2,
   -3>>64 = -1).  The consumer saturates counts >= 64 BEFORE the op (GoSem's [int_shift_checked]),
   so the shift amount stays small. *)
Definition int_shl (x : GoInt) (k : Z) (_ : (0 <=? k)%Z = true) : GoInt := intwrap (Z.shiftl (intraw x) k).
Definition int_shr (x : GoInt) (k : Z) (_ : (0 <=? k)%Z = true) : GoInt := intwrap (Z.shiftr (intraw x) k).
Fail Definition int_shl_neg : GoInt := int_shl (intwrap 1%Z) (-1)%Z eq_refl.
Definition int_eqb (a b : GoInt) : bool := Z.eqb (intraw a) (intraw b).
Definition int_ltb (a b : GoInt) : bool := Z.ltb (intraw a) (intraw b).
Definition int_leb (a b : GoInt) : bool := Z.leb (intraw a) (intraw b).
Definition int_div (a b : GoInt) (_ : Z.eqb (intraw b) 0%Z = false) : GoInt := intwrap (wrap64 (Z.quot (intraw a) (intraw b))).
Definition int_mod (a b : GoInt) (_ : Z.eqb (intraw b) 0%Z = false) : GoInt := intwrap (wrap64 (Z.rem (intraw a) (intraw b))).

(** ── GoI64 ARITHMETIC has the commutative-semiring CORE mod 2^64 (signed two's-complement) — the
    signed analogue of the GoU64 laws.  Key: the SIGNED [wrap64] preserves the residue mod 2^64
    ([wrap64_residue]: [wrap64 z ≡ z]), so it is a ring homomorphism — an inner [wrap64] is absorbed
    across `+` / `*` ([wrap64_idem_*]); the rest mirrors GoU64. ── *)
Lemma wrap64_residue : forall z,
  (wrap64 z mod 18446744073709551616 = z mod 18446744073709551616)%Z.
Proof.
  intro z. unfold wrap64. rewrite Zminus_mod, Zmod_mod, <- Zminus_mod. f_equal. ring.
Qed.
Lemma wrap64_eq_of_mod : forall a b,
  (a mod 18446744073709551616 = b mod 18446744073709551616)%Z -> wrap64 a = wrap64 b.
Proof.
  intros a b H. unfold wrap64. f_equal.
  rewrite Zplus_mod, H, <- Zplus_mod. reflexivity.
Qed.
Lemma wrap64_idem_add_r : forall a b, wrap64 (a + wrap64 b) = wrap64 (a + b).
Proof. intros. apply wrap64_eq_of_mod. rewrite Zplus_mod, wrap64_residue, <- Zplus_mod. reflexivity. Qed.
Lemma wrap64_idem_add_l : forall a b, wrap64 (wrap64 a + b) = wrap64 (a + b).
Proof. intros. apply wrap64_eq_of_mod. rewrite Zplus_mod, wrap64_residue, <- Zplus_mod. reflexivity. Qed.
Lemma wrap64_idem_mul_r : forall a b, wrap64 (a * wrap64 b) = wrap64 (a * b).
Proof. intros. apply wrap64_eq_of_mod. rewrite Zmult_mod, wrap64_residue, <- Zmult_mod. reflexivity. Qed.
Lemma wrap64_idem_mul_l : forall a b, wrap64 (wrap64 a * b) = wrap64 (a * b).
Proof. intros. apply wrap64_eq_of_mod. rewrite Zmult_mod, wrap64_residue, <- Zmult_mod. reflexivity. Qed.

Lemma i64_ext : forall x y : GoI64, i64raw x = i64raw y -> x = y.
Proof. intros [rx px] [ry py] H. cbn in H. subst ry. reflexivity. Qed.
Lemma i64raw_add : forall a b, i64raw (i64_add a b) = wrap64 (i64raw a + i64raw b).
Proof. intros. reflexivity. Qed.
Lemma i64raw_mul : forall a b, i64raw (i64_mul a b) = wrap64 (i64raw a * i64raw b).
Proof. intros. reflexivity. Qed.

(** Keystone coding: a CONCRETE [nat] ↦ Go int64 ([GoI64]) coding with an HONEST round-trip.
    An injection [nat ↪ GoI64] with a left inverse is IMPOSSIBLE ([GoI64] is finite), so
    [keystone_prj (keystone_inj n) = n] holds ONLY for REPRESENTABLE [n] ([Z.of_nat n < 2^63]) —
    [keystone_roundtrip].  The concurrency Keystone bridge must rest on THIS bounded fact. *)
Definition keystone_inj (n : nat) : GoI64 := i64wrap (Z.of_nat n).
Definition keystone_prj (g : GoI64) : nat := Z.to_nat (i64raw g).
Lemma keystone_roundtrip : forall n,
  (Z.of_nat n < 9223372036854775808)%Z -> keystone_prj (keystone_inj n) = n.
Proof.
  intros n Hn. pose proof (Nat2Z.is_nonneg n) as Hpos.
  unfold keystone_prj, keystone_inj, i64wrap. cbn [i64raw]. unfold wrap64.
  rewrite Z.mod_small by lia.
  replace (Z.of_nat n + 9223372036854775808 - 9223372036854775808)%Z with (Z.of_nat n) by lia.
  apply Nat2Z.id.
Qed.
(** Representability predicate for the Keystone bridge: a value the [keystone] coding round-trips
    (fits a signed int64).  Defined here so the [Z]-scope stays in [builtins.v] (concurrency.v has no ZArith). *)
Definition Vrep64 (n : nat) : Prop := (Z.of_nat n < 9223372036854775808)%Z.
Lemma Vrep64_0 : Vrep64 0.
Proof. unfold Vrep64. cbn. lia. Qed.

Lemma i64_add_comm : forall a b, i64_add a b = i64_add b a.
Proof. intros. apply i64_ext. rewrite !i64raw_add, (Z.add_comm (i64raw a)). reflexivity. Qed.
Lemma i64_mul_comm : forall a b, i64_mul a b = i64_mul b a.
Proof. intros. apply i64_ext. rewrite !i64raw_mul, (Z.mul_comm (i64raw a)). reflexivity. Qed.
Lemma i64_add_assoc : forall a b c, i64_add a (i64_add b c) = i64_add (i64_add a b) c.
Proof.
  intros. apply i64_ext. rewrite !i64raw_add.
  rewrite wrap64_idem_add_r, wrap64_idem_add_l. f_equal. ring.
Qed.
Lemma i64_mul_assoc : forall a b c, i64_mul a (i64_mul b c) = i64_mul (i64_mul a b) c.
Proof.
  intros. apply i64_ext. rewrite !i64raw_mul.
  rewrite wrap64_idem_mul_r, wrap64_idem_mul_l. f_equal. ring.
Qed.
Lemma i64_mul_add_distr_l : forall a b c,
  i64_mul a (i64_add b c) = i64_add (i64_mul a b) (i64_mul a c).
Proof.
  intros. apply i64_ext. rewrite !i64raw_add, !i64raw_mul, !i64raw_add.
  rewrite wrap64_idem_mul_r, wrap64_idem_add_l, wrap64_idem_add_r. f_equal. ring.
Qed.

(** [<] is a STRICT TOTAL ORDER on (signed) GoI64 and [<=] is antisymmetric — the int64 analogue of
    the GoU64 order laws (pure [Z]-order + [i64_ext]). *)
Lemma i64_ltb_irrefl : forall a, i64_ltb a a = false.
Proof. intros. unfold i64_ltb. apply Z.ltb_irrefl. Qed.
Lemma i64_ltb_trans : forall a b c, i64_ltb a b = true -> i64_ltb b c = true -> i64_ltb a c = true.
Proof. intros a b c Hab Hbc. unfold i64_ltb in *. apply Z.ltb_lt in Hab, Hbc. apply Z.ltb_lt. lia. Qed.
Lemma i64_lt_trichotomy : forall a b, i64_ltb a b = true \/ a = b \/ i64_ltb b a = true.
Proof.
  intros a b. unfold i64_ltb. destruct (Z.lt_trichotomy (i64raw a) (i64raw b)) as [H|[H|H]].
  - left. apply Z.ltb_lt. exact H.
  - right; left. apply i64_ext. exact H.
  - right; right. apply Z.ltb_lt. exact H.
Qed.
Lemma i64_leb_antisym : forall a b, i64_leb a b = true -> i64_leb b a = true -> a = b.
Proof.
  intros a b Hab Hba. unfold i64_leb in *. apply i64_ext.
  apply Z.le_antisymm; apply Z.leb_le; assumption.
Qed.

(* Integer absolute value.  Go has NO abs builtin for ints (only [math.Abs] for
   floats — and that needs an import), so it is written by hand with an [if] in
   VALUE position: [|a| = if a < 0 then -a else a].  Faithful across the WHOLE
   int64 range INCLUDING the [MININT] corner: [0 - MININT] is the exact [2^63],
   which [wrap64] lands back at [MININT] — exactly Go's two's-complement
   [0 - a] (the classic [abs(math.MinInt64) = math.MinInt64] overflow).  This is
   the canonical demo of the pure-function tail-match lowering: the
   body's [if] is a value-position match, lowered to an [if]/[else] whose arms
   each [return]. *)
Definition i64_abs (a : GoI64) : GoI64 :=
  if i64_ltb a (i64wrap 0) then i64_sub (i64wrap 0) a else a.
(* DIV/MOD: Go truncates toward ZERO ([Z.quot]/[Z.rem]) — NOT Coq's flooring
   [Z.div]/[Z.modulo] (which give [-7/2 = -4]).  Evidence-carrying non-zero divisor
   (Go panics on /0).  [wrap64] lands the lone overflow case [MININT / -1 = MININT]
   (the exact quotient [2^63] wraps to [-2^63], Go's two's-complement behaviour). *)
Definition i64_div (a b : GoI64) (_ : Z.eqb (i64raw b) 0%Z = false) : GoI64 := i64wrap (wrap64 (Z.quot (i64raw a) (i64raw b))).
Definition i64_mod (a b : GoI64) (_ : Z.eqb (i64raw b) 0%Z = false) : GoI64 := i64wrap (wrap64 (Z.rem (i64raw a) (i64raw b))).
(* BITWISE: Go int64 [& | ^ &^] and unary [^] on the 64-bit two's-complement value.
   [Z.land]/[lor]/[lxor]/[lnot] use infinite two's complement, which agrees on the
   low 64 bits; the result of in-range operands stays in range, so [wrap64] is the
   identity here (kept for uniformity).  Unary [^x = -x-1]. *)
Definition i64_and    (a b : GoI64) : GoI64 := i64wrap (wrap64 (Z.land (i64raw a) (i64raw b))).
Definition i64_or     (a b : GoI64) : GoI64 := i64wrap (wrap64 (Z.lor  (i64raw a) (i64raw b))).
Definition i64_xor    (a b : GoI64) : GoI64 := i64wrap (wrap64 (Z.lxor (i64raw a) (i64raw b))).
Definition i64_andnot (a b : GoI64) : GoI64 := i64wrap (wrap64 (Z.land (i64raw a) (Z.lnot (i64raw b)))).
Definition i64_not    (a   : GoI64) : GoI64 := i64wrap (wrap64 (Z.lnot (i64raw a))).
(* SHIFTS: [<<] wraps mod 2^64 ([wrap64 . Z.shiftl]); [>>] is ARITHMETIC (sign-
   filling) for signed = [Z.shiftr] (floor toward -inf, in range).  Evidence-
   carrying non-negative count (Go panics on a negative shift). *)
Definition i64_shl (x : GoI64) (k : Z) (_ : (0 <=? k)%Z = true) : GoI64 := i64wrap (wrap64 (Z.shiftl (i64raw x) k)).
Definition i64_shr (x : GoI64) (k : Z) (_ : (0 <=? k)%Z = true) : GoI64 := i64wrap (Z.shiftr (i64raw x) k).

(* Build-checked: a constant that does not fit int64 is UNREPRESENTABLE (Go's
   constant-overflow compile error), and int64 does not implicitly mix with [int]. *)
Fail Definition i64_const_oob : GoI64 := i64_lit 9223372036854775808%Z eq_refl.  (* = 2^63 *)
(* Build-checked: the RAW constructor cannot forge an out-of-range int64 (in_i64 proof false). *)
Fail Definition i64_forged : GoI64 := MkI64 9223372036854775808%Z (squash eq_refl).
Fail Definition i64_no_implicit (x : GoI64) : GoI64 := i64_add x (5 : nat).
(* Build-checked: a ZERO divisor / NEGATIVE shift count is UNREPRESENTABLE (Go panics). *)
Fail Definition i64_div_zero : GoI64 := i64_div (i64_lit 1%Z eq_refl) (i64_lit 0%Z eq_refl) eq_refl.
Fail Definition i64_shl_neg  : GoI64 := i64_shl (i64_lit 1%Z eq_refl) (-1)%Z eq_refl.

(** ---- GoU64: FULL-WIDTH unsigned 64-bit integer (Go spec "Numeric types") ----

    Carried by [Z], normalised into [[0, 2^64)] after every op by [wrapU64]
    (always non-negative — Z.modulo of a positive modulus is non-negative).
    Extraction erases the wrapper; a [GoU64] value is a Go [uint64], which wraps
    unsigned-natively at [2^64], so the emitted ops need no mask.

    Comparison uses [Z.ltb]/[Z.leb] on non-negative operands, which gives the
    unsigned order (Z order agrees with unsigned order for non-negative values).

    Division: [Z.div]/[Z.modulo] (floored) agree with Go's truncating uint64
    division since both dividend and divisor are non-negative (floor = truncate
    for non-negative).

    Bitwise: [Z.land]/[Z.lor]/[Z.lxor] on non-negative operands stay in
    [[0, 2^64)] — no mask needed.  [Z.lnot n = -(n+1)] is negative, so
    [wrapU64] brings it back to [2^64-1-n] (the 64-bit bitwise complement).
    [Z.land n (Z.lnot m)] for n ≥ 0 stays ≥ 0 (and < 2^64) — no wrap needed.

    Shifts: [<<] wraps mod [2^64] via [wrapU64 . Z.shiftl]; [>>] is LOGICAL
    (for unsigned, arithmetic = logical), so [Z.shiftr n k] is exact for n ≥ 0. *)
(* [in_u64]/[wrapU64] are hoisted to the wrapper-record block (the GoU64 range invariant needs them).
   [wrapU64 z = z mod 2^64] is always in range, so [u64wrap] carries the proof from one lemma; a forged
   [u64wrap (2^64) _] is unconstructable ([in_u64 (2^64)] is false). *)
Lemma in_u64_wrapU64 : forall z, in_u64 (wrapU64 z) = true.
Proof.
  intro z. unfold in_u64, wrapU64.
  pose proof (Z.mod_pos_bound z 18446744073709551616%Z ltac:(lia)) as [Hlo Hhi].
  apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Definition u64wrap (z : Z) : GoU64 := MkU64 (wrapU64 z) (squash (in_u64_wrapU64 z)).
(* [u64_lit z _]: a uint64 constant; the proof is a representability check
   (must be in [0, 2^64)); an out-of-range literal is unrepresentable. *)
Definition u64_lit (z : Z) (pf : in_u64 z = true) : GoU64 := MkU64 z (squash pf).
(* Platform-uint [GoUint] literal — the EXACT [GoU64] shape: a proof-carrying smart
   constructor demanding [in_u64 z] (so [z] is in [[0, 2^64)]).  Like [u64_lit] it is [NoInline]'d and
   the plugin folds [uint_lit z _] → Go [uint(<decimal>)] — the wrapper unboxes to its [Z] carrier
   (SProp proof erased), so the [uint(…)] cast MUST come from this op (a raw [MkUint] would render the
   bare carrier, which Go infers as [int]).  An out-of-range constant is unrepresentable: [eq_refl]
   cannot prove [in_u64 z = true] when [z] ∉ [[0, 2^64)]. *)
Definition uint_lit (z : Z) (pf : in_u64 z = true) : GoUint := MkUint z (squash pf).
(* [uintwrap] — the TOTAL wrap into the platform-[uint] range (mod 2^64, [wrapU64] — Go's runtime
   [uint(x)] conversion semantics; [uint] is 64-bit here).  The proof-carrying [uint_lit] stays the
   fail-closed CONSTANT builder; this is the RUNTIME-conversion authority (GoSem tier R3). *)
Definition uintwrap (z : Z) : GoUint := MkUint (wrapU64 z) (squash (in_u64_wrapU64 z)).
Definition u64_add (a b : GoU64) : GoU64 := u64wrap (wrapU64 (u64raw a + u64raw b)).
Definition u64_sub (a b : GoU64) : GoU64 := u64wrap (wrapU64 (u64raw a - u64raw b)).
(* Unary negation: [-x] mod 2^64 (so [-1 = 2^64-1]).  Lowers to the prefix [-x]. *)
Definition u64_neg (a : GoU64) : GoU64 := u64wrap (wrapU64 (Z.opp (u64raw a))).
Definition u64_mul (a b : GoU64) : GoU64 := u64wrap (wrapU64 (u64raw a * u64raw b)).
Definition u64_eqb (a b : GoU64) : bool := Z.eqb (u64raw a) (u64raw b).
Definition u64_ltb (a b : GoU64) : bool := Z.ltb (u64raw a) (u64raw b).
Definition u64_leb (a b : GoU64) : bool := Z.leb (u64raw a) (u64raw b).

(** ── GoU64 ARITHMETIC has the commutative-semiring CORE mod 2^64 — `+` and `*` are commutative,
    associative, and distributive — an algebraic-faithfulness check that the modelled uint64
    arithmetic has the expected structure (wraparound is a ring homomorphism Z → Z/2^64, so it
    preserves these).  Two [GoU64] with equal raw [Z] are EQUAL — the second (SProp range) field is
    proof-irrelevant ([u64_ext]) — so every law reduces to a [Z]-mod identity. ── *)
Lemma u64_ext : forall x y : GoU64, u64raw x = u64raw y -> x = y.
Proof. intros [rx px] [ry py] H. cbn in H. subst ry. reflexivity. Qed.

Lemma u64raw_add : forall a b, u64raw (u64_add a b) = wrapU64 (u64raw a + u64raw b).
Proof. intros. unfold u64_add, u64wrap. cbn. unfold wrapU64. apply Zmod_mod. Qed.
Lemma u64raw_mul : forall a b, u64raw (u64_mul a b) = wrapU64 (u64raw a * u64raw b).
Proof. intros. unfold u64_mul, u64wrap. cbn. unfold wrapU64. apply Zmod_mod. Qed.

Lemma u64_add_comm : forall a b, u64_add a b = u64_add b a.
Proof. intros. apply u64_ext. rewrite !u64raw_add, (Z.add_comm (u64raw a)). reflexivity. Qed.
Lemma u64_mul_comm : forall a b, u64_mul a b = u64_mul b a.
Proof. intros. apply u64_ext. rewrite !u64raw_mul, (Z.mul_comm (u64raw a)). reflexivity. Qed.

Lemma u64_add_assoc : forall a b c, u64_add a (u64_add b c) = u64_add (u64_add a b) c.
Proof.
  intros. apply u64_ext. rewrite !u64raw_add. unfold wrapU64.
  rewrite Z.add_mod_idemp_r, Z.add_mod_idemp_l by (intro H; discriminate H).
  f_equal. ring.
Qed.
Lemma u64_mul_assoc : forall a b c, u64_mul a (u64_mul b c) = u64_mul (u64_mul a b) c.
Proof.
  intros. apply u64_ext. rewrite !u64raw_mul. unfold wrapU64.
  rewrite Z.mul_mod_idemp_r, Z.mul_mod_idemp_l by (intro H; discriminate H).
  f_equal. ring.
Qed.
Lemma u64_mul_add_distr_l : forall a b c,
  u64_mul a (u64_add b c) = u64_add (u64_mul a b) (u64_mul a c).
Proof.
  intros. apply u64_ext. rewrite !u64raw_add, !u64raw_mul, !u64raw_add. unfold wrapU64.
  rewrite Z.mul_mod_idemp_r, Z.add_mod_idemp_l, Z.add_mod_idemp_r by (intro H; discriminate H).
  f_equal. ring.
Qed.

(** [<] is a STRICT TOTAL ORDER on GoU64 (irreflexive, transitive, trichotomous) and [<=] is
    antisymmetric — Go's comparison operators on uint64 are a well-behaved total order, a
    completeness check the value-witnesses don't give.  (Pure [Z]-order + [u64_ext]; the SProp range
    field is never needed.) *)
Lemma u64_ltb_irrefl : forall a, u64_ltb a a = false.
Proof. intros. unfold u64_ltb. apply Z.ltb_irrefl. Qed.
Lemma u64_ltb_trans : forall a b c, u64_ltb a b = true -> u64_ltb b c = true -> u64_ltb a c = true.
Proof. intros a b c Hab Hbc. unfold u64_ltb in *. apply Z.ltb_lt in Hab, Hbc. apply Z.ltb_lt. lia. Qed.
Lemma u64_lt_trichotomy : forall a b, u64_ltb a b = true \/ a = b \/ u64_ltb b a = true.
Proof.
  intros a b. unfold u64_ltb. destruct (Z.lt_trichotomy (u64raw a) (u64raw b)) as [H|[H|H]].
  - left. apply Z.ltb_lt. exact H.
  - right; left. apply u64_ext. exact H.
  - right; right. apply Z.ltb_lt. exact H.
Qed.
Lemma u64_leb_antisym : forall a b, u64_leb a b = true -> u64_leb b a = true -> a = b.
Proof.
  intros a b Hab Hba. unfold u64_leb in *. apply u64_ext.
  apply Z.le_antisymm; apply Z.leb_le; assumption.
Qed.

(** Direct [>] / [>=] / [!=] completing Go's six comparison operators for the
    canonical [int64]/[uint64].  We already emit [== < <=] directly; [>]/[>=] are the
    swapped [</<=] and [!=] is [negb (==)] — SEMANTICALLY identical to the encodings a
    program would otherwise write, but each is recognized by name and lowered to the
    DIRECT Go operator ([a > b], not [b < a]), so the emitted Go matches the source
    operator.  (The [int64] order is signed, the [uint64] order unsigned, inherited
    from [i64_ltb]/[u64_ltb].) *)
Definition i64_gtb  (a b : GoI64) : bool := i64_ltb b a.
Definition i64_geb  (a b : GoI64) : bool := i64_leb b a.
Definition i64_neqb (a b : GoI64) : bool := negb (i64_eqb a b).
Definition u64_gtb  (a b : GoU64) : bool := u64_ltb b a.
Definition u64_geb  (a b : GoU64) : bool := u64_leb b a.
Definition u64_neqb (a b : GoU64) : bool := negb (u64_eqb a b).
(* DIVISION: evidence-carrying non-zero divisor (Go panics on /0).  [Z.div] and
   [Z.modulo] are used here (floored) — for non-negative values they agree with
   Go's truncating division, so the result is exact.  No wrap needed: both
   results stay in [[0, 2^64)]. *)
Definition u64_div (a b : GoU64) (_ : Z.eqb (u64raw b) 0%Z = false) : GoU64 := u64wrap (Z.div    (u64raw a) (u64raw b)).
Definition u64_mod (a b : GoU64) (_ : Z.eqb (u64raw b) 0%Z = false) : GoU64 := u64wrap (Z.modulo (u64raw a) (u64raw b)).
Definition u64_and    (a b : GoU64) : GoU64 := u64wrap (Z.land (u64raw a) (u64raw b)).
Definition u64_or     (a b : GoU64) : GoU64 := u64wrap (Z.lor  (u64raw a) (u64raw b)).
Definition u64_xor    (a b : GoU64) : GoU64 := u64wrap (Z.lxor (u64raw a) (u64raw b)).
Definition u64_andnot (a b : GoU64) : GoU64 := u64wrap (Z.land (u64raw a) (Z.lnot (u64raw b))).
Definition u64_not    (a   : GoU64) : GoU64 := u64wrap (wrapU64 (Z.lnot (u64raw a))).
Definition u64_shl (x : GoU64) (k : Z) (_ : (0 <=? k)%Z = true) : GoU64 := u64wrap (wrapU64 (Z.shiftl (u64raw x) k)).
Definition u64_shr (x : GoU64) (k : Z) (_ : (0 <=? k)%Z = true) : GoU64 := u64wrap (Z.shiftr (u64raw x) k).

(* Build-checked: a constant >= 2^64 is UNREPRESENTABLE; uint64 does not
   implicitly mix with [int], [GoI64], or other types. *)
Fail Definition u64_const_oob : GoU64 := u64_lit 18446744073709551616%Z eq_refl.  (* = 2^64 *)
(* Build-checked: the RAW constructor cannot forge an out-of-range uint64 (in_u64 proof false). *)
Fail Definition u64_forged : GoU64 := MkU64 18446744073709551616%Z (squash eq_refl).
Fail Definition u64_no_implicit (x : GoU64) : GoU64 := u64_add x (5 : nat).
(* Build-checked: a ZERO divisor / NEGATIVE shift count is UNREPRESENTABLE. *)
Fail Definition u64_div_zero : GoU64 := u64_div (u64_lit 1%Z eq_refl) (u64_lit 0%Z eq_refl) eq_refl.
Fail Definition u64_shl_neg  : GoU64 := u64_shl (u64_lit 1%Z eq_refl) (-1)%Z eq_refl.

(** ---- Bitwise BOOLEAN-ALGEBRA laws for GoU64 (the bitwise counterpart of the proven arithmetic
    semiring + total-order laws).  COMMUTATIVITY holds directly; ASSOCIATIVITY needs that [wrapU64]
    (mod 2⁶⁴) depends only on the LOW 64 bits — so an inner [wrapU64] under a bit-op can be pulled out
    ([wrapU64_bit_r]/[_l], one [Z.bits_inj'] each).  (Idempotence [a & a = a] is SProp-BLOCKED: it
    needs [u64raw a] in range, which the [Squash] seal hides from [Prop] — documented, not skipped.) *)
Lemma wrapU64_bit_r : forall (op : Z -> Z -> Z) (bf : bool -> bool -> bool),
  (forall x y n, Z.testbit (op x y) n = bf (Z.testbit x n) (Z.testbit y n)) ->
  forall a b, wrapU64 (op a (wrapU64 b)) = wrapU64 (op a b).
Proof.
  intros op bf Hspec a b. unfold wrapU64. change 18446744073709551616%Z with (2 ^ 64)%Z.
  apply Z.bits_inj'. intros n Hn. destruct (Z.lt_ge_cases n 64) as [Hlt | Hge].
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite !Hspec.
    rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma wrapU64_bit_l : forall (op : Z -> Z -> Z) (bf : bool -> bool -> bool),
  (forall x y n, Z.testbit (op x y) n = bf (Z.testbit x n) (Z.testbit y n)) ->
  forall a b, wrapU64 (op (wrapU64 a) b) = wrapU64 (op a b).
Proof.
  intros op bf Hspec a b. unfold wrapU64. change 18446744073709551616%Z with (2 ^ 64)%Z.
  apply Z.bits_inj'. intros n Hn. destruct (Z.lt_ge_cases n 64) as [Hlt | Hge].
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite !Hspec.
    rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma u64_and_comm : forall a b, u64_and a b = u64_and b a.
Proof. intros a b. apply u64_ext. unfold u64_and, u64wrap; cbn. f_equal. apply Z.land_comm. Qed.
Lemma u64_or_comm  : forall a b, u64_or a b = u64_or b a.
Proof. intros a b. apply u64_ext. unfold u64_or, u64wrap; cbn. f_equal. apply Z.lor_comm. Qed.
Lemma u64_xor_comm : forall a b, u64_xor a b = u64_xor b a.
Proof. intros a b. apply u64_ext. unfold u64_xor, u64wrap; cbn. f_equal. apply Z.lxor_comm. Qed.

Lemma u64_and_assoc : forall a b c, u64_and a (u64_and b c) = u64_and (u64_and a b) c.
Proof.
  intros a b c. apply u64_ext. unfold u64_and, u64wrap; cbn.
  rewrite (wrapU64_bit_r Z.land andb Z.land_spec), (wrapU64_bit_l Z.land andb Z.land_spec).
  f_equal. apply Z.land_assoc.
Qed.
Lemma u64_or_assoc : forall a b c, u64_or a (u64_or b c) = u64_or (u64_or a b) c.
Proof.
  intros a b c. apply u64_ext. unfold u64_or, u64wrap; cbn.
  rewrite (wrapU64_bit_r Z.lor orb Z.lor_spec), (wrapU64_bit_l Z.lor orb Z.lor_spec).
  f_equal. apply Z.lor_assoc.
Qed.
Lemma u64_xor_assoc : forall a b c, u64_xor a (u64_xor b c) = u64_xor (u64_xor a b) c.
Proof.
  intros a b c. apply u64_ext. unfold u64_xor, u64wrap; cbn.
  rewrite (wrapU64_bit_r Z.lxor xorb Z.lxor_spec), (wrapU64_bit_l Z.lxor xorb Z.lxor_spec).
  f_equal. symmetry. apply Z.lxor_assoc.
Qed.

(** ---- GoI64 / GoU64 are THE canonical Go int64 / uint64 ----

    [GoI64]/[GoU64] (the [Z]-carried full-width types) are the faithful models of
    Go's [int64]/[uint64].  These abbreviations + scopes make them as ERGONOMIC as
    a primitive: [42%i64] is a range-checked int64 literal, [(a + b)%i64] is
    full-width addition.

    The literal parser ([i64_of_Z]/[u64_of_Z]) RANGE-CHECKS at PARSE TIME,
    returning [None] for an out-of-range numeral — an over-wide literal is
    REJECTED, exactly Go's untyped-constant overflow compile error.  The parser's
    range check is the proof, so the literal builds the raw [MkI64]/[MkU64] with
    no separate [_lit] obligation. *)
Notation int64  := GoI64.
Notation uint64 := GoU64.

Definition i64_of_Z (z : Z) : option GoI64 := if in_i64 z then Some (i64wrap z) else None.  (* wrap64 z = z under the guard *)
Definition Z_of_i64 (x : GoI64) : Z := i64raw x.
Definition u64_of_Z (z : Z) : option GoU64 := if in_u64 z then Some (u64wrap z) else None.  (* wrapU64 z = z under the guard *)
Definition Z_of_u64 (x : GoU64) : Z := u64raw x.

Declare Scope i64_scope.
Delimit Scope i64_scope with i64.
Bind Scope i64_scope with GoI64.
Number Notation GoI64 i64_of_Z Z_of_i64 : i64_scope.
Infix "+"  := i64_add : i64_scope.
Infix "-"  := i64_sub : i64_scope.
Infix "*"  := i64_mul : i64_scope.
Infix "=?" := i64_eqb : i64_scope.
Infix "<?" := i64_ltb : i64_scope.
Infix "<=?" := i64_leb : i64_scope.

Declare Scope u64_scope.
Delimit Scope u64_scope with u64.
Bind Scope u64_scope with GoU64.
Number Notation GoU64 u64_of_Z Z_of_u64 : u64_scope.
Infix "+"  := u64_add : u64_scope.
Infix "-"  := u64_sub : u64_scope.
Infix "*"  := u64_mul : u64_scope.
Infix "=?" := u64_eqb : u64_scope.
Infix "<?" := u64_ltb : u64_scope.
Infix "<=?" := u64_leb : u64_scope.

(* Build-checked: an out-of-range literal is REJECTED AT PARSE (Go untyped-constant
   overflow).  [2^63] overflows int64 (max [2^63-1]); [2^64] overflows uint64. *)
Fail Definition i64_lit_oob : GoI64 := (9223372036854775808)%i64.   (* = 2^63 *)
Fail Definition u64_lit_oob : GoU64 := (18446744073709551616)%u64.  (* = 2^64 *)
(* Platform-uint: the proof-carrying [uint_lit] range-checks too — [eq_refl] cannot prove
   [in_u64 (2^64) = true], so an out-of-range platform-uint constant is unrepresentable. *)
Fail Definition uint_lit_oob : GoUint := uint_lit 18446744073709551616 eq_refl.  (* = 2^64 *)

(** ---- Full-width int64 <-> uint64 CONVERSIONS (Go spec "Conversions") ----
    Go's [uint64(x)] / [int64(x)] between the two 64-bit integer types REINTERPRET
    the same 64-bit two's-complement pattern: the value is unchanged when it fits
    the target, otherwise it is the mod-2^64 representative (a negative int64 maps to
    its 2^64-complement uint64; a uint64 >= 2^63 maps to a negative int64).  The
    Z-carried model makes this EXACT — re-normalise the raw [Z] into the target's
    range — with NO rounding or loss (unlike int<->float).  [int_of_FW]/[FW_of_int]
    cover the NARROW widths; these are the full-width pair (distinct because [GoU64]
    lowers to a real Go [uint64], not [int64]). *)
Definition u64_of_i64 (a : GoI64) : GoU64 := u64wrap (wrapU64 (i64raw a)).
Definition i64_of_u64 (a : GoU64) : GoI64 := i64wrap (wrap64  (u64raw a)).

(* Reinterpret is mod-2^64 on both sides, so the two normalisers AGREE after a
   round-trip: [wrap64 (wrapU64 z) = wrap64 z] (both reduce mod 2^64 first). *)
Lemma wrap64_wrapU64 : forall z, wrap64 (wrapU64 z) = wrap64 z.
Proof.
  intro z. unfold wrap64, wrapU64.
  rewrite Zplus_mod_idemp_l.   (* (z mod 2^64 + 2^63) mod 2^64 = (z + 2^63) mod 2^64 *)
  reflexivity.
Qed.

(** SIGNED↔UNSIGNED bitwise FAITHFULNESS — Go: [a & b == int64(uint64(a) & uint64(b))].
    The signed bitwise op equals the SIGNED REINTERPRETATION of the UNSIGNED op on the two's-complement
    bit patterns, so [i64_and]/[_or]/[_xor] are FAITHFUL to Go's int64/uint64 bitwise agreement.  Proof:
    cancel the double mod-2⁶⁴ ([wrapU64_idem]), pull each [wrapU64] out through the bit-op
    ([wrapU64_bit_l]/[_r]), then collapse [wrap64 ∘ wrapU64 = wrap64]. *)
Lemma wrapU64_idem : forall z, wrapU64 (wrapU64 z) = wrapU64 z.
Proof. intro z. unfold wrapU64. rewrite Z.mod_mod by lia. reflexivity. Qed.

Lemma i64_and_via_u64 : forall a b,
  i64_and a b = i64_of_u64 (u64_and (u64_of_i64 a) (u64_of_i64 b)).
Proof.
  intros a b. apply i64_ext.
  cbn [i64_and i64_of_u64 u64_and u64_of_i64 i64wrap u64wrap i64raw u64raw].
  rewrite !wrapU64_idem,
          (wrapU64_bit_l Z.land andb Z.land_spec), (wrapU64_bit_r Z.land andb Z.land_spec),
          wrap64_wrapU64.
  reflexivity.
Qed.
Lemma i64_or_via_u64 : forall a b,
  i64_or a b = i64_of_u64 (u64_or (u64_of_i64 a) (u64_of_i64 b)).
Proof.
  intros a b. apply i64_ext.
  cbn [i64_or i64_of_u64 u64_or u64_of_i64 i64wrap u64wrap i64raw u64raw].
  rewrite !wrapU64_idem,
          (wrapU64_bit_l Z.lor orb Z.lor_spec), (wrapU64_bit_r Z.lor orb Z.lor_spec),
          wrap64_wrapU64.
  reflexivity.
Qed.
Lemma i64_xor_via_u64 : forall a b,
  i64_xor a b = i64_of_u64 (u64_xor (u64_of_i64 a) (u64_of_i64 b)).
Proof.
  intros a b. apply i64_ext.
  cbn [i64_xor i64_of_u64 u64_xor u64_of_i64 i64wrap u64wrap i64raw u64raw].
  rewrite !wrapU64_idem,
          (wrapU64_bit_l Z.lxor xorb Z.lxor_spec), (wrapU64_bit_r Z.lxor xorb Z.lxor_spec),
          wrap64_wrapU64.
  reflexivity.
Qed.

(** ---- Untyped INTEGER constants (Go spec "Constants") ----

    A Go untyped constant is ARBITRARY-PRECISION: constant arithmetic is exact (no
    width, no wrap), and the constant acquires a fixed-width TYPE only at the point of
    USE, where a representability check fires — a constant that does not fit is a
    COMPILE ERROR, not a runtime wrap.  We model an untyped int constant as [Z], its
    arithmetic as [Z] arithmetic (exact), and the type-at-use conversion as
    [i64c]/[u64c]: each EVALUATES the closed [Z] expression with [vm_compute] (real
    bignums, so an INTERMEDIATE may exceed the target width — e.g. [1 << 70] — as long
    as the final value fits) to a literal, then converts demanding [in_i64]/[in_u64].
    An out-of-range constant FAILS to elaborate (the [now vm_compute] proof of
    representability cannot be built) — the analog of Go's untyped-constant overflow.
    The literal the notation produces lowers via the existing [i64_lit]/[u64_lit] fold;
    no plugin change — the arbitrary precision lives entirely in [vm_compute]. *)
Notation i64c e :=
  (i64_lit ltac:(let v := eval vm_compute in (e : Z) in exact v) ltac:(now vm_compute))
  (only parsing).
Notation u64c e :=
  (u64_lit ltac:(let v := eval vm_compute in (e : Z) in exact v) ltac:(now vm_compute))
  (only parsing).

(** ---- int64 → float64 conversion (Go spec "Conversions") ----

    Go [float64(i)] converts an [int64] to an IEEE double; values past 2^53 ROUND (the
    double's mantissa), exactly as Go does.  We round the EXACT signed [Z] mantissa ONCE to
    binary64 via [SpecFloat.binary_normalize] at format (53, 1024) — axiom-free, round-to-
    nearest-even, spanning the whole int64 range.  Recognised BY NAME → native Go [float64(i)]
    (machine-checked by [f64_of_i64_pos]/[f64_of_i64_neg] in main.v); the [binary_normalize]
    body is suppressed.  The reverse — float64→int64 TRUNCATION ([i64_of_f64]) — is modelled
    DIRECTLY on the [spec_float] representation below (no truncation primitive needed). *)
Definition f64_of_i64 (a : GoI64) : GoFloat64 := binary_normalize 53 1024 (i64raw a) 0 false.

(** int64 → narrow (Go [uint8(x)] / [int8(x)] / … / [int32(x)]): TRUNCATE to the low W bits.
    A [GoU8]/[GoI8]/… erases to the same int64 carrier as a [GoI64], so the conversion is
    EXACTLY the narrow-from-int truncation ([fw_wrap]: mask to W bits, sign-extend for [iN]) —
    lowered to Go's native [(x & 0xFF)] / sign-extended form, identical to [uN_of_int].  The model
    masks the [Z] carrier directly ([uNwrap]/[iNwrap] on [i64raw a]): for [W < 64] the low W bits
    of [i64raw a] are [(i64raw a) mod 2^W].
    The [wrap] body never reaches the emitted Go — the op is recognized by name (`fw_is r "of_i64"`)
    and its decl suppressed (`fixed_width_op`), exactly as the [of_int] narrows are. *)
Definition u8_of_i64  (a : GoI64) : GoU8  := u8wrap (i64raw a).
Definition i8_of_i64  (a : GoI64) : GoI8  := i8wrap (i64raw a).
Definition u16_of_i64 (a : GoI64) : GoU16 := u16wrap (i64raw a).
Definition i16_of_i64 (a : GoI64) : GoI16 := i16wrap (i64raw a).
Definition u32_of_i64 (a : GoI64) : GoU32 := u32wrap (i64raw a).
Definition i32_of_i64 (a : GoI64) : GoI32 := i32wrap (i64raw a).

(** int → float64 (Go [float64(i)]): the IEEE double NEAREST the integer (EXACT for |i| < 2^53,
    rounds beyond — exactly Go's rule).  Rounds the EXACT [Z] mantissa ONCE via [binary_normalize] at
    (53, 1024) — the SAME axiom-free Z→float path as [f64_of_i64] / [f32_of_int].  Recognized by name
    → native [float64(i)]; the [spec_float] body is suppressed.  Machine-checked by [f64_of_int_pos]/
    [f64_of_int_neg] (main.v). *)
Definition f64_of_int (i : GoInt) : GoFloat64 := binary_normalize 53 1024 (intraw i) 0 false.

(** float64 → int64 (Go [int64(f)]): TRUNCATE toward zero.  [GoFloat64] is [spec_float], so
    the decomposition is DIRECT — a finite [f = S754_finite s m e] is [(-1)^s * m * 2^e] ([m]
    positive, [e : Z]), no float-decomposition primitive.  The truncated MAGNITUDE is
    [m * 2^e] when [e >= 0] (an exact integer) or [m / 2^(-e)] when [e < 0] (the FLOOR of the
    positive magnitude = truncation toward zero); the sign is applied AFTER, so it rounds toward
    zero — exactly Go's rule.  [i64_of_f64] is recognised BY NAME → native [int64(f)] (the
    [f64_trunc_Z] body suppressed); machine-checked (witnesses in main.v).  *Bounded deviation:*
    NaN / ±Inf / out-of-int64-range inputs are IMPLEMENTATION-DEFINED in Go (spec "Conversions");
    the model gives [0] (and [wrap64] folds overflow) — a documented model gap on those corners;
    the FINITE in-range case (the common use) is faithful and machine-checked. *)
Definition f64_trunc_Z (f : GoFloat64) : Z :=
  match f with
  | S754_finite s m e =>
      let mag := if Z.leb 0 e then (Zpos m * 2 ^ e)%Z else (Zpos m / 2 ^ (- e))%Z in
      if s then (- mag)%Z else mag
  | _ => 0%Z
  end.
Definition i64_of_f64 (f : GoFloat64) : GoI64 := i64wrap (wrap64 (f64_trunc_Z f)).

(** float64 → uint64 (Go [uint64(f)]): TRUNCATE toward zero — the exact parallel of [i64_of_f64],
    only wrapping into the unsigned range.  In-range ([0 <= trunc f < 2^64]) it is faithful (the
    verified [f64_trunc_Z]); out of range is Go-implementation-defined, where the defined wrap is
    an acceptable choice.  Lowered to native [uint64(f)]; the [spec_float]-match body suppressed. *)
Definition u64_of_f64 (f : GoFloat64) : GoU64 := u64wrap (wrapU64 (f64_trunc_Z f)).

(** uint64 → float64 (Go [float64(v)]): the CORRECTLY-ROUNDED double.  Rounds the EXACT [Z] mantissa
    (in [[0, 2^64)]) ONCE via [binary_normalize] at (53, 1024) — the SAME Z→float path as the int64/
    int conversions, spanning the WHOLE uint64 range in one shot.  Lowered to native [float64(v)];
    the body suppressed. *)
Definition f64_of_u64 (a : GoU64) : GoFloat64 := binary_normalize 53 1024 (u64raw a) 0 false.

(** UNTYPED FLOAT CONSTANTS — exact rationals, rounded ONCE at the typed boundary.  Go folds
    constant float arithmetic at ARBITRARY precision, rounding only when the constant acquires a
    type: [const x float64 = 0.1 + 0.2] is [float64(3/10) = 0.3] EXACTLY, NOT the runtime
    [0.1+0.2 = 0.30000000000000004] (which rounds each operand THEN adds).  Fido's runtime floats
    ([spec_float] arithmetic) give the runtime answer; this models the CONSTANT one.  An [FConst] is an exact
    rational [num/den]; [fc_add]/[fc_sub]/[fc_mul] are EXACT ([Q]-style cross-multiply, no
    rounding); [f64_of_fconst] rounds exactly ONCE (its own contract below is the rounding
    authority).  MODEL + machine-checked; the plugin's FConst-fold lowers a CONSTANT
    expression whose int64-CHECKED endpoints fold — beyond int64 the fold declines and
    extraction fails loud. *)
(** The denominator is a [positive] — exactly the shape of Coq's [QArith.Q] — so a Go
    float CONSTANT is an EXACT *nonzero-denominator* rational and can NEVER denote ±Inf
    or NaN.  A malformed [den = 0] constant is UNCONSTRUCTABLE by
    type, so the extractor's [den = 0] fold guard is a dead defensive boundary rather than
    a reachable path.  [Bind Scope] keeps [mkFC n d] literals parsing [d] as a positive. *)
Record FConst := mkFC { fc_num : Z ; fc_den : positive }.
Bind Scope positive_scope with positive.
Definition fc_add (a b : FConst) : FConst :=
  mkFC (fc_num a * Zpos (fc_den b) + fc_num b * Zpos (fc_den a)) (Pos.mul (fc_den a) (fc_den b)).
Definition fc_sub (a b : FConst) : FConst :=
  mkFC (fc_num a * Zpos (fc_den b) - fc_num b * Zpos (fc_den a)) (Pos.mul (fc_den a) (fc_den b)).
Definition fc_mul (a b : FConst) : FConst := mkFC (fc_num a * fc_num b) (Pos.mul (fc_den a) (fc_den b)).
(** Constant DIVISION is EVIDENCE-CARRYING: Go constant division by zero is a COMPILE error,
    so [fc_div] DEMANDS a proof the divisor's numerator is nonzero — a constant [/0] cannot be
    written.  The denominator stays strictly positive by
    folding the divisor's SIGN into the numerator:
      (na/da)/(nb/db) = (na·db)/(da·nb) = (sgn(nb)·na·db)/(da·|nb|). *)
Definition fc_div (a b : FConst) (hb : fc_num b <> 0%Z) : FConst :=
  mkFC (Z.sgn (fc_num b) * fc_num a * Zpos (fc_den b))
       (Pos.mul (fc_den a) (Z.to_pos (Z.abs (fc_num b)))).  (* (a/b)/(c/d) = ad/bc, den kept > 0 *)
(** ([sf_of_Z] — exact [Z] → [spec_float] — is defined up with the float64 ops.) *)
(** Exact float CONSTANT → float64 — round the EXACT rational [num/den] ONCE to binary64 via [SFdiv]
    of the EXACT-integer spec_floats (no intermediate binary64), so correctly-rounded for ALL num/den,
    not just [< 2^53].  Lowered to Go [float64(num.0 / den.0)] (untyped-constant division, single
    round). *)
Definition f64_of_fconst (a : FConst) : GoFloat64 :=
  SFdiv 53 1024 (sf_of_Z (fc_num a)) (sf_of_Z (Zpos (fc_den a))).

(** FLOAT32 arithmetic — faithful binary32 (prec 24, emax 128) via [SpecFloat], then routed
    back through [f32_of_f64] so the result re-enters the abstract type WITH its provenance
    proof ([eq_refl]).  The extra round is the IDENTITY in reality (an [SFadd]/… result is
    already in binary32 format), so this stays faithful — exactly Go's [float32] arithmetic
    (single round-to-nearest-even at binary32).  Lowered BY NAME to native Go [float32]
    [+]/[-]/[*]/[/]; the SpecFloat body (and the [f32val]/[mkF32] wrapping) is suppressed. *)
Definition f32_add (x y : GoFloat32) : GoFloat32 :=
  f32_of_f64 (SFadd 24 128 (f32val x) (f32val y)).
Definition f32_sub (x y : GoFloat32) : GoFloat32 :=
  f32_of_f64 (SFsub 24 128 (f32val x) (f32val y)).
Definition f32_mul (x y : GoFloat32) : GoFloat32 :=
  f32_of_f64 (SFmul 24 128 (f32val x) (f32val y)).
Definition f32_div (x y : GoFloat32) : GoFloat32 :=
  f32_of_f64 (SFdiv 24 128 (f32val x) (f32val y)).

(** float32 COMPARISON.  The carrier holds a binary32-CANONICAL value and a comparison performs
    NO rounding, so [SFltb]/[SFleb]/[SFeqb] on [f32val] ARE the float32 comparisons (both operands
    are binary32-canonical, so [SFcompare]'s representation-sensitivity is satisfied).  Lowered to
    native Go [float32] [<]/[<=]/[==]/[>]/[>=]/[!=].  Same NaN subtlety as float64: [f32_geb]/
    [f32_gtb] are the SWAPPED [leb]/[ltb] (so a NaN operand makes [>=]/[>] FALSE), [f32_neqb] is
    [negb (eqb)]. *)
Definition f32_ltb  (x y : GoFloat32) : bool := SFltb (f32val x) (f32val y).
Definition f32_leb  (x y : GoFloat32) : bool := SFleb (f32val x) (f32val y).
Definition f32_eqb  (x y : GoFloat32) : bool := SFeqb (f32val x) (f32val y).
Definition f32_gtb  (x y : GoFloat32) : bool := SFltb (f32val y) (f32val x).
Definition f32_geb  (x y : GoFloat32) : bool := SFleb (f32val y) (f32val x).
Definition f32_neqb (x y : GoFloat32) : bool := negb (SFeqb (f32val x) (f32val y)).

(** float32 → float64 WIDENING is EXACT (a binary32 value is exactly a binary64): the carrier
    re-canonicalised to binary64 ([renorm 53 1024] — exact, no rounding, since binary32 ⊂ binary64),
    SOUND because [f32ok] guarantees the carrier is binary32-representable.  Lowered to Go
    [float64(x)].  (Narrowing [f32_of_f64] / [f32_lit] is defined up top, with the type.) *)
Definition f64_of_f32 (x : GoFloat32) : GoFloat64 := renorm 53 1024 (f32val x).

(** DIRECT integer → float32 (Go [float32(x)]) — round the EXACT integer ONCE to binary32 via
    [binary_normalize] at format (24, 128).  This is NOT [f32_of_f64 (f64_of_int x)] (= Go
    [float32(float64(x))]): for |x| > 2^53 the int→float64 step ALREADY rounds, and the second
    round to binary32 can DISAGREE — double rounding.  (E.g. [x = 2^61 + 2^37 + 1]: direct rounds
    UP to [2^61 + 2^38]; via float64 the low bit is lost onto the float32 midpoint and ties-to-even
    rounds DOWN to [2^61].)  Lowered to Go's direct [float32(x)] cast (single round). *)
Definition f32_of_i64 (a : GoI64) : GoFloat32 :=
  f32_of_f64 (binary_normalize 24 128 (i64raw a) 0 false).
Definition f32_of_u64 (a : GoU64) : GoFloat32 :=
  f32_of_f64 (binary_normalize 24 128 (u64raw a) 0 false).
Definition f32_of_int (i : GoInt) : GoFloat32 :=
  f32_of_f64 (binary_normalize 24 128 (intraw i) 0 false).

(** DIRECT exact float CONSTANT → float32 (Go [float32(num.0 / den.0)]): round the EXACT rational
    [num/den] ONCE to binary32 via [SFdiv] of the EXACT-integer spec_floats (no intermediate binary64
    — so correct for ALL [num], [den], unlike [f32_of_f64 (f64_of_fconst …)] which double-rounds when
    [|num| > 2^53]: e.g. [2305843146652647425/1] rounds to [2^61+2^38] here but [2^61] via float64).
    [SFdiv] handles arbitrary mantissas, so this is the correctly-rounded rational→binary32. *)
Definition f32_of_fconst (a : FConst) : GoFloat32 :=
  f32_of_f64 (SFdiv 24 128 (sf_of_Z (fc_num a)) (sf_of_Z (Zpos (fc_den a)))).

(** float32 unary NEGATION — EXACT (IEEE sign-flip, makes [-0.0]); re-enter the abstract type
    (the round is the identity on the sign-flipped, still-representable value).  Lowered to Go
    [-x].  Same role as [f64_opp] for float64. *)
Definition f32_neg (x : GoFloat32) : GoFloat32 := f32_of_f64 (SFopp (f32val x)).

(** [min]/[max] on float32 (Go "min and max") — the SAME two IEEE corners as float64, decided on
    the binary32 carriers: NaN propagation ([eqb v v = false]) and signed zero ([min(-0,+0) = -0],
    [max(-0,+0) = +0], via [1/v]).  Each returns the chosen OPERAND, already a valid [GoFloat32],
    so there is no re-rounding.  Lowered to Go [min]/[max] on float32. *)
Definition f32_min (x y : GoFloat32) : GoFloat32 :=
  if negb (SFeqb (f32val x) (f32val x)) then x            (* x is NaN → NaN *)
  else if negb (SFeqb (f32val y) (f32val y)) then y       (* y is NaN → NaN *)
  else if SFltb (f32val x) (f32val y) then x
  else if SFltb (f32val y) (f32val x) then y
  else if SFeqb (f32val x) (S754_zero false)
       then (if SFltb (SFdiv 24 128 (sf_of_Z 1) (f32val x)) (S754_zero false) then x else y)   (* min wants -0 *)
       else x.
Definition f32_max (x y : GoFloat32) : GoFloat32 :=
  if negb (SFeqb (f32val x) (f32val x)) then x
  else if negb (SFeqb (f32val y) (f32val y)) then y
  else if SFltb (f32val x) (f32val y) then y
  else if SFltb (f32val y) (f32val x) then x
  else if SFeqb (f32val x) (S754_zero false)
       then (if SFltb (SFdiv 24 128 (sf_of_Z 1) (f32val x)) (S754_zero false) then y else x)   (* max wants +0 *)
       else x.

(** ---- Builtins ---- *)

(** [print]/[println] write to stdout — a RECORDED effect: each call appends an event
    [(is_println, args)] to the world's [w_output] trace, so programs that print different
    things are not [run_io]-equal.  Lowered BY NAME to native Go [print]/[println]; the
    trace is proof-only and never extracted. *)
Definition w_log (b : bool) (xs : list GoAny) (w : World) : World :=
  mkWorld (w_refs w) (w_chans w) (w_maps w) (w_next w) (w_output w ++ ((b, xs) :: nil)).
Definition print   (xs : list GoAny) : IO unit := fun w => ORet tt (w_log false xs w).
Definition println (xs : list GoAny) : IO unit := fun w => ORet tt (w_log true xs w).

(** [run_io] RESPECTS output — a program that prints TWICE is not provably equal to
    one that prints ONCE.  The result worlds differ in their [w_output] trace length. *)
Example output_distinguishes_programs :
  run_io (bind (println nil) (fun _ => println nil)) w_init
  <> run_io (println nil) w_init.
Proof. vm_compute. discriminate. Qed.

(** [panic], [bind_panic_l], and the PANIC-SENSITIVE Hoare logic ([hoare_panic_unreachable] /
    [hoare_no_panic]) are defined up top with the panic-aware semantics; all are proved lemmas. *)

(** ---- panic / recover semantics ----

    [catch m h] is the semantic of [defer func() { if r := recover(); r != nil { h(r) } }()].
    [recover()] in Go is just the panic value bound by [h] — it needs no separate axiom.

    Compound panics: if [h] itself panics with [w], [catch (panic v) h = h v = panic w],
    so the new panic [w] replaces [v].  This is correct Go semantics and falls out from
    [catch_panic] alone — no extra law needed.

    [with_defer] models [defer cleanup()] (without recover): runs [cleanup] on both
    normal exit and panic exit.  If [cleanup] panics mid-panic, the new panic wins —
    also correct Go semantics, again from [catch_panic] + [bind_panic_l]. *)

(** [catch] is declared up top; [catch_ret] and [catch_panic] are proved
    lemmas (from [run_catch]), not axioms. *)

(** [with_defer cleanup m]: run [m], then run [cleanup] EXACTLY ONCE regardless
    of outcome (Go runs one deferred call once).  If [cleanup] panics, its panic
    replaces any in-flight panic.
    Invariant: cleanup does NOT live inside the [catch] that distinguishes the
    body outcome — [m]'s outcome is reified into a [GoAny + A] sum WITHOUT running
    cleanup, then cleanup runs exactly once on the single post-[catch] path and
    the captured body panic is re-raised. *)
Definition with_defer {A : Type} (cleanup : IO unit) (m : IO A) : IO A :=
  r <-' catch (x <-' m ;; ret (@inr GoAny A x)) (fun v => ret (@inl GoAny A v)) ;;
  cleanup >>' match r with
              | inl v => panic v
              | inr x => ret x
              end.

(** When the guarded body panics, the deferred [cleanup] still runs and the
    original panic propagates afterwards.  Follows from [bind_panic_l] (panic
    short-circuits the body, reifying nothing) and [catch_panic] (the handler
    captures the panic as [inl v]); cleanup then runs once and re-raises it. *)
Lemma with_defer_panic : forall {A} (cleanup : IO unit) (v : GoAny),
  @with_defer A cleanup (panic v) =io= cleanup >>' panic v.
Proof.
  intros A cleanup v. unfold with_defer.
  rewrite bind_panic_l, catch_panic, bind_ret_l. reflexivity.
Qed.

(** Companion lemma for the NORMAL path: when the body returns [x], cleanup runs
    and [x] propagates.  Crucially this holds UNCONDITIONALLY in [cleanup] — even
    a [cleanup] that panics is run exactly once (the RHS mentions [cleanup] once);
    together with [with_defer_panic] it certifies a single cleanup execution on
    both exits. *)
Lemma with_defer_ret : forall {A} (cleanup : IO unit) (x : A),
  @with_defer A cleanup (ret x) =io= cleanup >>' ret x.
Proof.
  intros A cleanup x. unfold with_defer.
  rewrite bind_ret_l, catch_ret, bind_ret_l. reflexivity.
Qed.

(** [defer_call f] (Go spec "Defer statements"): Go's [defer] keyword — schedule [f] to run when the
    enclosing *function* returns (LIFO across all defers, on both normal and panic exit).  FUNCTION-scoped,
    unlike block-scoped [with_defer].  Lowers to [defer func(){ f }()] (Go provides the function-scoping,
    LIFO ordering, run-at-return).

    FAILS LOUD in the sequential [run_io] semantics: shallow [World -> Outcome] cannot run a
    func-scoped defer (it cannot reify the deferred command to run it at return), so the sequential
    meaning is a LOUD panic rather than a silent drop of an observable effect.  The FAITHFUL defer
    is [run_cmd] over a [CDfr] node (cmd.v), which runs defers LIFO at func-scope return, on panic
    too.  Extraction is unaffected: the plugin lowers [defer_call] BY NAME to a real
    [defer func(){…}()] (this body is suppressed). *)
Definition defer_call (_ : IO unit) : IO unit :=
  fun w => OPanic (anyt TString "fido: defer_call has no shallow run_io meaning — a func-scoped defer needs the deep command model; the faithful semantics is run_cmd's CDfr (cmd.v); run_io fails loud rather than silently dropping the deferred effect"%string) w.


(** [type_assert tag v] (Go spec "Type assertions") asserts that [v : GoAny] holds
    a value of Go type [T].  Panics (like Go's [v.(T)]) if the runtime type does not
    match.

    ESCAPE HATCH: the raw panicking form, safe only inside [catch] or when the
    runtime type is already known.  Prefer [type_assert_safe] (below), the
    safe-by-construction default.

    The tagged [GoAny] carries the value's runtime [GoTypeTag], so [tag_coerce]
    checks it against the target [tag] and recovers the value when they agree; a
    mismatch PANICS, exactly Go's [v.(T)].  Lowered by NAME to [v.(T)] (body
    suppressed). *)
Definition type_assert {T : Type} (tag : GoTypeTag T) (a : GoAny) : IO T :=
  match a with
  | existT _ _ (x, atag) =>
      match tag_coerce tag atag x with
      | Some t => ret t
      | None   => panic rt_assert_fail   (* runtime-type mismatch: Go panics *)
      end
  end.

(** Read-after-assert: asserting [anyt tag x] to its OWN tag returns [x] — a THEOREM,
    from [tag_coerce_refl]. *)
Theorem type_assert_ok : forall {T} (tag : GoTypeTag T) (x : T),
  type_assert tag (anyt tag x) = ret x.
Proof. intros T tag x. unfold type_assert. rewrite tag_coerce_refl. reflexivity. Qed.

(** Safe checked assertion (the safe-by-construction default for [GoAny]).
    [type_assert_safe tag a (fun v ok => body)] lowers to Go's native
    two-value form [v, ok := a.(T); body]: when the runtime tag matches [T], [ok =
    true] and [v] is the value; otherwise [ok = false] and [v = zero_val tag].
    Because the caller must handle [ok = false], it cannot panic.  CPS like [recv_ok]. *)
Definition type_assert_safe {T B : Type}
  (tag : GoTypeTag T) (a : GoAny) (k : T -> bool -> IO B) : IO B :=
  match a with
  | existT _ _ (x, atag) =>
      match tag_coerce tag atag x with
      | Some t => k t true
      | None   => k (zero_val tag) false
      end
  end.

(** Build-checked: a WRONG-type assertion does NOT silently return the value — the
    coercion is [None], so the result is a panic / [ok = false], never [ret x]. *)
Example type_assert_safe_ok : forall {B} (x : GoInt) (k : GoInt -> bool -> IO B),
  type_assert_safe TInt64 (anyt TInt64 x) k = k x true.
Proof. intros B x k. unfold type_assert_safe. rewrite tag_coerce_refl. reflexivity. Qed.
Example type_assert_safe_mismatch : forall {B} (x : GoInt) (k : bool -> bool -> IO B),
  type_assert_safe TBool (anyt TInt64 x) k = k false false.
Proof. intros B x k. reflexivity. Qed.

(** ---- Type switch ----  (Go spec: "Type switches")

    Go's [switch v := x.(type) { case T1: …; case T2: …; default: … }] dispatches on
    the RUNTIME type of an interface value [x].  We model it on the SAME [tag_coerce]
    machinery as [type_assert_safe] (so it is axiom-free): try each case's tag against
    the value's tag; the first match runs that case's continuation with the recovered,
    correctly-typed value, otherwise the default runs.  Lowers to Go's native type
    switch.  N-ary (>2 cases) is the same shape with more arms. *)
Definition type_switch2 {A1 A2 B : Type} (a : GoAny)
  (t1 : GoTypeTag A1) (k1 : A1 -> IO B)
  (t2 : GoTypeTag A2) (k2 : A2 -> IO B)
  (d : IO B) : IO B :=
  match a with
  | existT _ _ (x, atag) =>
      match tag_coerce t1 atag x with
      | Some v1 => k1 v1
      | None =>
          match tag_coerce t2 atag x with
          | Some v2 => k2 v2
          | None => d
          end
      end
  end.

(** Build-checked dispatch: a value tagged [t1] runs the first arm with the recovered
    value (never a wrong arm or the default)… *)
Example type_switch2_first : forall {A1 A2 B} (t1 : GoTypeTag A1) (t2 : GoTypeTag A2)
    (x : A1) (k1 : A1 -> IO B) k2 d,
  type_switch2 (anyt t1 x) t1 k1 t2 k2 d = k1 x.
Proof. intros. unfold type_switch2. rewrite tag_coerce_refl. reflexivity. Qed.

(** …and a value whose type matches NEITHER case falls through to the default — the
    coercions are both [None], so no arm can fire on a type mismatch. *)
Example type_switch2_default : forall {B} (x : GoInt) k1 k2 (d : IO B),
  type_switch2 (anyt TInt64 x) TBool k1 TString k2 d = d.
Proof. intros. reflexivity. Qed.

(** N-ary type switch is the same shape with more arms — here three cases.  (The plugin
    lowers any arity through one generalised arm, so [type_switch4]… would work the same.) *)
Definition type_switch3 {A1 A2 A3 B : Type} (a : GoAny)
  (t1 : GoTypeTag A1) (k1 : A1 -> IO B)
  (t2 : GoTypeTag A2) (k2 : A2 -> IO B)
  (t3 : GoTypeTag A3) (k3 : A3 -> IO B)
  (d : IO B) : IO B :=
  match a with
  | existT _ _ (x, atag) =>
      match tag_coerce t1 atag x with
      | Some v1 => k1 v1
      | None =>
          match tag_coerce t2 atag x with
          | Some v2 => k2 v2
          | None =>
              match tag_coerce t3 atag x with
              | Some v3 => k3 v3
              | None => d
              end
          end
      end
  end.

(** Build-checked: the THIRD case fires for an [int64]-tagged value — the first two
    coercions miss (different tags), the third matches and runs [k3] with the value. *)
Example type_switch3_third : forall {B} (x : GoI64) k1 k2 (k3 : GoI64 -> IO B) d,
  type_switch3 (anyt TI64 x) TBool k1 TString k2 TI64 k3 d = k3 x.
Proof. intros. unfold type_switch3. rewrite tag_coerce_refl. reflexivity. Qed.

(** Multi-type case — Go's [case T1, T2:].  A single case matching EITHER of two types;
    in Go the bound value is NOT narrowed (it keeps the interface type), so the body
    commonly ignores it — we model it as a thunk [k : IO B] (no value binder), run when
    the value's type is [t1] OR [t2].  Same [tag_coerce] basis (axiom-free); lowers to
    Go's [case T1, T2:]. *)
Definition type_switch_or2 {A1 A2 B : Type} (a : GoAny)
  (t1 : GoTypeTag A1) (t2 : GoTypeTag A2) (k : IO B) (d : IO B) : IO B :=
  match a with
  | existT _ _ (x, atag) =>
      match tag_coerce t1 atag x with
      | Some _ => k
      | None => match tag_coerce t2 atag x with Some _ => k | None => d end
      end
  end.

(** Build-checked: the multi-type case fires for EITHER tag (here the first and the
    second), and a value matching neither falls through to the default. *)
Example type_switch_or2_first : forall {A1 A2 B} (t1 : GoTypeTag A1) (t2 : GoTypeTag A2)
    (x : A1) (k d : IO B), type_switch_or2 (anyt t1 x) t1 t2 k d = k.
Proof. intros. unfold type_switch_or2. rewrite tag_coerce_refl. reflexivity. Qed.
Example type_switch_or2_second : forall {B} (x : GoString) (k d : IO B),
  type_switch_or2 (anyt TString x) TBool TString k d = k.
Proof. intros. unfold type_switch_or2. rewrite tag_coerce_refl. reflexivity. Qed.
Example type_switch_or2_default : forall {B} (x : GoInt) (k d : IO B),
  type_switch_or2 (anyt TInt64 x) TBool TString k d = d.
Proof. intros. reflexivity. Qed.

(** N-type multi-case — three types here (Go's [case T1, T2, T3:]); same shape as
    [type_switch_or2], one more tag.  The plugin lowers any arity through one generalised
    arm. *)
Definition type_switch_or3 {A1 A2 A3 B : Type} (a : GoAny)
  (t1 : GoTypeTag A1) (t2 : GoTypeTag A2) (t3 : GoTypeTag A3) (k : IO B) (d : IO B) : IO B :=
  match a with
  | existT _ _ (x, atag) =>
      match tag_coerce t1 atag x with
      | Some _ => k
      | None => match tag_coerce t2 atag x with
                | Some _ => k
                | None => match tag_coerce t3 atag x with Some _ => k | None => d end
                end
      end
  end.
Example type_switch_or3_third : forall {B} (x : GoI64) (k d : IO B),
  type_switch_or3 (anyt TI64 x) TBool TString TI64 k d = k.
Proof. intros. unfold type_switch_or3. rewrite tag_coerce_refl. reflexivity. Qed.
Example type_switch_or3_default : forall {B} (x : GoInt) (k d : IO B),
  type_switch_or3 (anyt TInt64 x) TBool TString TFloat64 k d = d.
Proof. intros. reflexivity. Qed.

(** Native EXPRESSION switch — Go's [switch x { case v1: …; case v2: …; default: … }]
    on an int64 scrutinee.  Semantically an equality if-chain (faithful: Go's expression
    switch compares the scrutinee to each case value with [==], first match wins) but
    lowered to the native Go [switch].  Axiom-free (built on [i64_eqb]); N-ary is the same
    shape (the plugin arm is generalised over the (value, body) pairs). *)
Definition int_switch2 {B : Type} (x : GoI64)
  (v1 : GoI64) (k1 : IO B)
  (v2 : GoI64) (k2 : IO B)
  (d : IO B) : IO B :=
  if i64_eqb x v1 then k1
  else if i64_eqb x v2 then k2
  else d.

(** Build-checked dispatch: the scrutinee selects the first matching case, else default. *)
Example int_switch2_first : forall {B} (k1 k2 d : IO B),
  int_switch2 (1)%i64 (1)%i64 k1 (2)%i64 k2 d = k1.
Proof. reflexivity. Qed.
Example int_switch2_second : forall {B} (k1 k2 d : IO B),
  int_switch2 (2)%i64 (1)%i64 k1 (2)%i64 k2 d = k2.
Proof. reflexivity. Qed.
Example int_switch2_default : forall {B} (k1 k2 d : IO B),
  int_switch2 (9)%i64 (1)%i64 k1 (2)%i64 k2 d = d.
Proof. reflexivity. Qed.

(** N-ary expression switch — three cases here; same generalised plugin arm as
    [int_switch2] (it takes any number of (value, body) pairs). *)
Definition int_switch3 {B : Type} (x : GoI64)
  (v1 : GoI64) (k1 : IO B)
  (v2 : GoI64) (k2 : IO B)
  (v3 : GoI64) (k3 : IO B)
  (d : IO B) : IO B :=
  if i64_eqb x v1 then k1
  else if i64_eqb x v2 then k2
  else if i64_eqb x v3 then k3
  else d.
Example int_switch3_third : forall {B} (k1 k2 k3 d : IO B),
  int_switch3 (3)%i64 (1)%i64 k1 (2)%i64 k2 (3)%i64 k3 d = k3.
Proof. reflexivity. Qed.
Example int_switch3_default : forall {B} (k1 k2 k3 d : IO B),
  int_switch3 (9)%i64 (1)%i64 k1 (2)%i64 k2 (3)%i64 k3 d = d.
Proof. reflexivity. Qed.

(** [min]/[max] (Go 1.21 predeclared builtins) on [int] — the smaller / larger of
    two values, by the SIGNED ordering (Go's int [<]), so [go_min] = Go [min(a,b)]
    and [go_max] = Go [max(a,b)] for the [int] type.  Computable (so [go_min 3 5 =
    3] is a THEOREM); the plugin lowers the call to Go's builtin.  (Go's [min]/[max]
    also apply to floats — with NaN/`-0` corner cases — and strings; those follow
    once those orderings are settled.) *)
Definition go_min (a b : GoInt) : GoInt := if int_ltb a b then a else b.
Definition go_max (a b : GoInt) : GoInt := if int_ltb a b then b else a.

(** [min]/[max] on the CANONICAL full-width types: [int64] ([GoI64], SIGNED order via
    [i64_ltb]) and [uint64] ([GoU64], UNSIGNED order via [u64_ltb]) — each exactly Go's
    [min(a,b)]/[max(a,b)] for that type.  Computable theorems; the plugin lowers each
    call to the Go builtin.  No carrier bridge (the comparison is the type's own [<]). *)
Definition i64_min (a b : GoI64) : GoI64 := if i64_ltb a b then a else b.
Definition i64_max (a b : GoI64) : GoI64 := if i64_ltb a b then b else a.
Definition u64_min (a b : GoU64) : GoU64 := if u64_ltb a b then a else b.
Definition u64_max (a b : GoU64) : GoU64 := if u64_ltb a b then b else a.

(** [min]/[max] on FLOAT (Go spec "min and max" — the float rules).  A naive
    [if a < b] is WRONG on two IEEE corners that Go's builtin handles, so we model
    them faithfully (the body is suppressed; each call lowers to Go's [min]/[max],
    which does the same):
    - NaN PROPAGATION: if either argument is a NaN, the result is a NaN.  Detected by
      [eqb x x = false] (only NaN is unequal to itself).
    - SIGNED ZERO: when the two are numerically EQUAL and are [±0], [max] yields [+0]
      and [min] yields [-0] (Go treats [+0 > -0]).  Detected by [eqb a 0] (both are
      [±0]) and [1/a < 0] (a is the negative zero, since [1 / -0 = -inf]).
    Otherwise the smaller / larger by [ltb].  Machine-checked on all these corners. *)
Definition f64_min (a b : GoFloat64) : GoFloat64 :=
  if negb (SFeqb a a) then a            (* a is NaN → NaN *)
  else if negb (SFeqb b b) then b       (* b is NaN → NaN *)
  else if SFltb a b then a
  else if SFltb b a then b
  else (* numerically equal (incl. ±0) *)
    if SFeqb a (S754_zero false)
    then (if SFltb (SFdiv 53 1024 (sf_of_Z 1) a) (S754_zero false) then a else b)   (* min wants -0 *)
    else a.
Definition f64_max (a b : GoFloat64) : GoFloat64 :=
  if negb (SFeqb a a) then a            (* a is NaN → NaN *)
  else if negb (SFeqb b b) then b       (* b is NaN → NaN *)
  else if SFltb a b then b
  else if SFltb b a then a
  else (* numerically equal (incl. ±0) *)
    if SFeqb a (S754_zero false)
    then (if SFltb (SFdiv 53 1024 (sf_of_Z 1) a) (S754_zero false) then b else a)   (* max wants +0 *)
    else a.

(** Direct [>] / [>=] / [!=] for float64.  CRUCIAL NaN subtlety: [>=] is NOT
    [¬(<)] — with a NaN operand, [a >= b] is FALSE (Go/IEEE), whereas [¬(a < b)]
    would be TRUE.  So [f64_geb] is the SWAPPED [leb] ([b <= a]), and [f64_gtb] the
    swapped [ltb] — both correctly false on NaN.  [f64_neqb] IS [negb (eqb)] (a NaN
    compares UNEQUAL to everything, so [a != b] is true — matching [negb false]). *)
Definition f64_gtb  (a b : GoFloat64) : bool := SFltb b a.
Definition f64_geb  (a b : GoFloat64) : bool := SFleb b a.
Definition f64_neqb (a b : GoFloat64) : bool := negb (SFeqb a b).


(** Variadic parameter (Go [func f(xs ...T)]): inside [f] the param is a SLICE, but Go's call
    syntax SPREADS — [f(slice...)].  [Variadic T] is a 2-FIELD record (the [bool] phantom stops
    Coq from unboxing the single slice field, so the PARAM TYPE stays distinguishable from a
    plain [[]T] — the plugin renders it [...T], not [[]T]; no [Comparable] is needed for a
    variadic param so the phantom-breaks-equality issue that ruled this out for [GoI64] does
    not apply here).  [vararg xs] marks a call argument for spreading ([xs...]); inside [f],
    [va_slice] recovers the slice (it IS the param itself — the projection is erased, no Go emitted). *)
Record Variadic (T : Type) := MkVariadic { va_slice : GoSlice T ; va_ph : bool }.
Arguments MkVariadic {T} _ _.
Arguments va_slice {T} _.  Arguments va_ph {T} _.
Definition vararg {T} (xs : GoSlice T) : Variadic T := MkVariadic xs true.


(** Array COMPARABILITY (Go spec "Comparison operators": arrays are comparable iff the
    element type is — unlike SLICES, which are NOT comparable).  Go's array [==] is
    FIELD-WISE; [arr_eqb] decides it element-by-element (here for [int64] arrays), so it
    is a THEOREM that it decides array equality.  Lowers to the bare Go [a == b].  Go
    requires the two arrays be the SAME type (same length) for [==] — different lengths
    are a Go COMPILE error, so only same-length arrays are compared. *)
Fixpoint goi64_list_eqb (xs ys : list GoI64) : bool :=
  match xs, ys with
  | nil, nil => true
  | x :: xs', y :: ys' => andb (i64_eqb x y) (goi64_list_eqb xs' ys')
  | _, _ => false
  end.
Definition arr_eqb (a b : GoArray GoI64) : bool := goi64_list_eqb (arr_data a) (arr_data b).
Definition arr3_eqb (a b : GoArr3 GoI64) : bool := goi64_list_eqb (arr3_data a) (arr3_data b).
Definition arr2_eqb (a b : GoArr2 GoI64) : bool := goi64_list_eqb (arr2_data a) (arr2_data b).

(** ---- String operations (Go spec "String types") ----

    [str_len s] is the BYTE length (Go [len(s)]): a computable [int] that counts
    the [string]'s bytes, so [str_len "Go" = 2] is a THEOREM.  The plugin lowers
    it to Go [int64(len(s))] — the byte count in the [Z]-carried [GoInt] (int64) model.

    [str_at_ok] is the SAFE byte index (spec: "a string's bytes can be accessed
    by integer indices [0 <= i < len(s)]"; [s[i]] is of type [byte]).  CPS /
    comma-ok like [slice_at_ok]: it FORCES handling the out-of-range case, so it
    cannot panic.  In range ⇒ [b = s[i]] (the byte, a [GoByte] = [uint8]) and
    [ok = true]; else [b = 0], [ok = false].  [i : int] is SIGNED, so the bounds
    check covers BOTH ends.  Lowers to a bounds-checked [int64(s[i])] (the byte
    in the int64 carrier), mirroring [slice_at_ok].

    [str_concat] is Go's string [+] (spec "Operators": string concatenation) — a
    pure, total operation on immutable byte sequences, so [str_concat "ab" "cd" =
    "abcd"] is a THEOREM.  Defined by its OWN recursion (no [String.append]
    dependency to drag into extraction); suppressed in the plugin, lowered to Go
    [a + b]. *)
Fixpoint str_len (s : GoString) : GoInt :=
  match s with
  | EmptyString   => intwrap 0
  | String _ rest => intwrap (1 + intraw (str_len rest))
  end.

(** DEFINITION: the i'th BYTE of the string at the signed index,
    as a [GoByte] (= [GoU8]); out of range ⇒ [k 0 false].  Like the slice forms,
    the body must pull in NO external stdlib function, so it uses SELF-CONTAINED,
    suppressed helpers: [ascii_byte] decodes the 8 bits of an [ascii] to its 0–255
    [GoU8] carrier INLINE (no [nat_of_ascii], which drags in [N_of_digits]), and
    [go_str_byte] walks to the i'th byte ([int]-indexed, structural on the string,
    no [String.get]+[Z.to_nat]).  Lowered BY NAME to a bounds-checked [int64(s[i])]
    (body suppressed + NoInline), so this affects only proofs. *)
Definition ascii_byte (c : ascii) : GoByte :=
  match c with
  | Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
      let v (b : bool) (k : Z) : Z := if b then k else 0%Z in
      u8wrap (v b0 1 + (v b1 2 + (v b2 4 + (v b3 8 +
             (v b4 16 + (v b5 32 + (v b6 64 + v b7 128)))))))%Z
  end.
Fixpoint go_str_byte (s : GoString) (i : nat) : GoByte :=
  match s with
  | EmptyString  => u8wrap 0
  | String c rest => if Nat.eqb i 0 then ascii_byte c
                     else go_str_byte rest (Nat.pred i)
  end.

(** ---- [[]byte] / [string] conversions (Go spec "Conversions to and from a string
    type") ----  [[]byte(s)] is the BYTE sequence of [s] (no UTF-8 decoding); [string(b)]
    reconstructs it.  [GoString] IS a byte sequence ([list ascii]), so these are faithful
    byte-for-byte.  [str_to_bytes] maps each char to its [GoByte] via the suppressed
    [ascii_byte]; [byte_ascii] is its inverse (reconstruct the 8 bits, again no
    [nat_of_ascii]).  Both lower BY NAME to the native [[]byte(s)] / [string(b)] (bodies
    suppressed + NoInline, so they affect only proofs).  [str_to_bytes_length] proves the
    byte count is preserved ([len([]byte(s)) == len(s)]); the value round-trip is golden. *)
Definition byte_ascii (b : GoByte) : ascii :=
  let n := u8raw b in
  let bit (k : Z) : bool := Z.testbit n k in
  Ascii (bit 0%Z) (bit 1%Z) (bit 2%Z) (bit 3%Z)
        (bit 4%Z) (bit 5%Z) (bit 6%Z) (bit 7%Z).
Fixpoint str_to_bytes (s : GoString) : list GoByte :=
  match s with
  | EmptyString   => nil
  | String c rest => ascii_byte c :: str_to_bytes rest
  end.
Fixpoint str_from_bytes (b : list GoByte) : GoString :=
  match b with
  | nil       => EmptyString
  | x :: rest => String (byte_ascii x) (str_from_bytes rest)
  end.
Lemma str_to_bytes_length : forall s, Datatypes.length (str_to_bytes s) = String.length s.
Proof. induction s as [|c rest IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.
Definition str_at_ok {B : Type}
  (s : GoString) (i : GoInt) (k : GoByte -> bool -> IO B) : IO B :=
  if (Z.leb 0 (intraw i) && Z.ltb (intraw i) (intraw (str_len s)))%bool
  then k (go_str_byte s (Z.to_nat (intraw i))) true
  else k (u8wrap 0) false.

Fixpoint str_concat (a b : GoString) : GoString :=
  match a with
  | EmptyString   => b
  | String c rest => String c (str_concat rest b)
  end.

(** String slicing [s[a:b]] (Go spec "Slice expressions": for a string, the result is the
    BYTE-substring [a, b)).  EVIDENCE-CARRYING / safe-by-construction: it DEMANDS a proof
    that [a <= b <= len(s)] (in bytes), so the emitted [s[a:b]] cannot panic — the bounds
    proof discharged Go's slice-bounds check (same discipline as [div_nz]).  Indices are
    [nat] (a string length/offset is non-negative).  The body [String.substring a (b-a) s] is recognized
    away to the native [s[a:b]] (decl + [substring] suppressed).  [eq_refl] discharges the
    proof for literal bounds. *)
Definition str_slice (s : GoString) (a b : nat)
  (_ : (Nat.leb a b && Nat.leb b (String.length s))%bool = true) : GoString :=
  String.substring a (b - a) s.

(** ---- Rune view: [[]rune(s)] / [string([]rune)] (Go spec "Conversions to and from a
    string type") ----  A [rune] is an int32 code point.  [[]rune(s)] UTF-8-DECODES the
    byte sequence to code points; [string(rs)] UTF-8-ENCODES them back.  Both lower BY NAME
    to the native Go [[]rune(s)] / [string(rs)] (the runtime does the real UTF-8, faithful);
    the Coq bodies below are the proof-side model (suppressed + NoInline), a full 1–4 byte
    UTF-8 codec.  [byte_chr] is a byte value → [ascii]; the codec is verified by the
    round-trip examples (ASCII and a 3-byte CJK code point). *)
Definition byte_chr (v : Z) : ascii := byte_ascii (u8wrap v).

(** [str_to_runes] is a FAITHFUL UTF-8 decoder — exactly Go's [utf8.DecodeRune] /
    range-over-string.  An invalid sequence yields [RuneError] (U+FFFD) and advances by exactly ONE byte
    (NOT the would-be width), rejecting: continuation bytes used as leads (0x80–0xBF), overlong 2-byte
    (0xC0/0xC1), missing/bad continuation bytes, overlong 3/4-byte (0xE0 with c1<0xA0; 0xF0 with c1<0x90),
    UTF-16 surrogates (0xED with c1≥0xA0), >MaxRune (0xF4 with c1≥0x90), and invalid leads ≥0xF5.  The body
    is proof-only (lowered by name to native [[]rune(s)], which does the same). *)
(** [str_to_runes_w] decodes AND records, per rune, the number of SOURCE bytes consumed (1 for an
    invalid byte — Go's [utf8.DecodeRune] advances exactly one — or the 2/3/4 of a valid multibyte).
    That CONSUMED width, not the decoded rune's would-be re-encoded width, is what [str_range]
    accumulates into byte offsets: for source [0x80 'A'] Go yields
    [(0,U+FFFD) (1,'A')], and so does the model (the FFFD consumed ONE byte, not
    [rune_width U+FFFD] = 3).  [str_to_runes] (rune-only) is [map fst] of this — one decoder. *)
Fixpoint str_to_runes_w (s : GoString) : list (GoI32 * Z) :=
  match s with
  | EmptyString => nil
  | String c0 r0 =>
      (* [rerr]/[isc] are LOCAL (not top-level Definitions): the whole body is suppressed and lowered by
         name to native [[]rune(s)], so the unsigned [ltb]/[leb] here are proof-only and never extracted. *)
      let rerr := i32wrap 65533%Z in              (* U+FFFD *)
      let isc  := fun v => andb (Z.leb 128%Z v) (Z.ltb v 192%Z) in  (* cont byte 0x80–0xBF *)
      let v0 := u8raw (ascii_byte c0) in
      if Z.ltb v0 128%Z then              (* 1-byte: ASCII 0x00–0x7F *)
        (i32wrap v0, 1%Z) :: str_to_runes_w r0
      else if Z.ltb v0 194%Z then         (* 0x80–0xC1: cont-as-lead OR overlong-2 → error *)
        (rerr, 1%Z) :: str_to_runes_w r0
      else if Z.ltb v0 224%Z then         (* 0xC2–0xDF: 2-byte (result ≥ 0x80, non-overlong) *)
        match r0 with
        | String c1 r1 =>
            let v1 := u8raw (ascii_byte c1) in
            if isc v1 then
              (i32wrap (Z.lor (Z.shiftl (Z.land v0 31%Z) 6%Z)
                                     (Z.land v1 63%Z)), 2%Z) :: str_to_runes_w r1
            else (rerr, 1%Z) :: str_to_runes_w r0   (* bad continuation → error, advance 1 *)
        | EmptyString => (rerr, 1%Z) :: nil         (* truncated → advance 1 (the lead) *)
        end
      else if Z.ltb v0 240%Z then         (* 0xE0–0xEF: 3-byte *)
        match r0 with
        | String c1 r1' =>
            let v1 := u8raw (ascii_byte c1) in
            let v1ok :=                                 (* accept-range: 0xE0→[0xA0,0xBF] (overlong); 0xED→[0x80,0x9F] (surrogate) *)
              if Z.eqb v0 224%Z then andb (Z.leb 160%Z v1) (Z.ltb v1 192%Z)
              else if Z.eqb v0 237%Z then andb (Z.leb 128%Z v1) (Z.ltb v1 160%Z)
              else isc v1 in
            match r1' with
            | String c2 r2 =>
                let v2 := u8raw (ascii_byte c2) in
                if andb v1ok (isc v2) then
                  (i32wrap (Z.lor (Z.lor
                           (Z.shiftl (Z.land v0 15%Z) 12%Z)
                           (Z.shiftl (Z.land v1 63%Z) 6%Z))
                           (Z.land v2 63%Z)), 3%Z) :: str_to_runes_w r2
                else (rerr, 1%Z) :: str_to_runes_w r0
            | EmptyString => (rerr, 1%Z) :: str_to_runes_w r0
            end
        | EmptyString => (rerr, 1%Z) :: nil
        end
      else if Z.ltb v0 245%Z then         (* 0xF0–0xF4: 4-byte *)
        match r0 with
        | String c1 r1' =>
            let v1 := u8raw (ascii_byte c1) in
            let v1ok :=                                 (* accept-range: 0xF0→[0x90,0xBF] (overlong); 0xF4→[0x80,0x8F] (>MaxRune) *)
              if Z.eqb v0 240%Z then andb (Z.leb 144%Z v1) (Z.ltb v1 192%Z)
              else if Z.eqb v0 244%Z then andb (Z.leb 128%Z v1) (Z.ltb v1 144%Z)
              else isc v1 in
            match r1' with
            | String c2 r2' =>
                let v2 := u8raw (ascii_byte c2) in
                match r2' with
                | String c3 r3 =>
                    let v3 := u8raw (ascii_byte c3) in
                    if andb v1ok (andb (isc v2) (isc v3)) then
                      (i32wrap (Z.lor (Z.lor (Z.lor
                               (Z.shiftl (Z.land v0 7%Z) 18%Z)
                               (Z.shiftl (Z.land v1 63%Z) 12%Z))
                               (Z.shiftl (Z.land v2 63%Z) 6%Z))
                               (Z.land v3 63%Z)), 4%Z) :: str_to_runes_w r3
                    else (rerr, 1%Z) :: str_to_runes_w r0
                | EmptyString => (rerr, 1%Z) :: str_to_runes_w r0
                end
            | EmptyString => (rerr, 1%Z) :: str_to_runes_w r0
            end
        | EmptyString => (rerr, 1%Z) :: nil
        end
      else                                             (* 0xF5–0xFF: invalid lead → error *)
        (rerr, 1%Z) :: str_to_runes_w r0
  end.
(* rune-only view = drop the consumed-width tags.  A manual fixpoint (not [List.map]) so the
   suppressed body pulls no generic [map] into the extraction closure. *)
Fixpoint str_runes_fst (rs : list (GoI32 * Z)) : list GoI32 :=
  match rs with
  | nil              => nil
  | cons (r, _) rest => cons r (str_runes_fst rest)
  end.
Definition str_to_runes (s : GoString) : list GoI32 := str_runes_fst (str_to_runes_w s).
Definition rune_bytes (r : GoI32) : GoString :=
  (* Go's [string(rune)] / [utf8.EncodeRune] replaces an out-of-range or surrogate rune with
     U+FFFD: Go tests [uint32(r) > MaxRune], so a NEGATIVE int32 is out of range —
     on our [Z] carrier that is simply [c0 < 0] (we guard [0 <= c0] below) — as is [r] in the
     UTF-16 surrogate range [0xD800,0xDFFF]. *)
  let c0 := i32raw r in
  (* out-of-range (incl. NEGATIVE — on the [Z] carrier that is [c0 < 0]) or UTF-16
     surrogate → U+FFFD. *)
  let c := if andb (andb (Z.leb 0 c0) (Z.leb c0 1114111))
                   (negb (andb (Z.leb 55296 c0) (Z.leb c0 57343)))
           then c0 else 65533%Z in
  if Z.ltb c 128 then
    String (byte_chr c) EmptyString
  else if Z.ltb c 2048 then
    String (byte_chr (Z.lor 192 (Z.shiftr c 6)))
   (String (byte_chr (Z.lor 128 (Z.land c 63))) EmptyString)
  else if Z.ltb c 65536 then
    String (byte_chr (Z.lor 224 (Z.shiftr c 12)))
   (String (byte_chr (Z.lor 128 (Z.land (Z.shiftr c 6) 63)))
   (String (byte_chr (Z.lor 128 (Z.land c 63))) EmptyString))
  else
    String (byte_chr (Z.lor 240 (Z.shiftr c 18)))
   (String (byte_chr (Z.lor 128 (Z.land (Z.shiftr c 12) 63)))
   (String (byte_chr (Z.lor 128 (Z.land (Z.shiftr c 6) 63)))
   (String (byte_chr (Z.lor 128 (Z.land c 63))) EmptyString))).
Fixpoint runes_to_str (rs : list GoI32) : GoString :=
  match rs with
  | nil => EmptyString
  | r :: rest => str_concat (rune_bytes r) (runes_to_str rest)
  end.

(** Codec verified by ROUND-TRIP: encode→decode is the identity for ASCII and for a 3-byte
    CJK code point (中 = U+4E2D = 20013, UTF-8 E4 B8 AD). *)
Example rune_roundtrip_ascii :
  str_to_runes (runes_to_str (i32wrap 65 :: i32wrap 66 :: nil))
    = i32wrap 65 :: i32wrap 66 :: nil.
Proof. vm_compute. reflexivity. Qed.
Example rune_roundtrip_cjk :
  str_to_runes (runes_to_str (i32wrap 20013 :: nil)) = i32wrap 20013 :: nil.
Proof. vm_compute. reflexivity. Qed.

(** Witnesses (machine-checked): INVALID UTF-8 decodes to U+FFFD (65533) per offending
    byte, advancing ONE byte — exactly Go's [utf8.DecodeRune].  [byte_chr v] is the byte
    with value [v]. *)
Example utf8_cont_as_lead :                  (* lone continuation 0x80 — not a valid lead → one U+FFFD *)
  str_to_runes (String (byte_chr 128) EmptyString) = i32wrap 65533 :: nil.
Proof. vm_compute. reflexivity. Qed.
Example utf8_overlong_2 :                     (* 0xC0 0x80 (overlong NUL): 0xC0 bad lead, 0x80 cont → two U+FFFD *)
  str_to_runes (String (byte_chr 192) (String (byte_chr 128) EmptyString))
    = i32wrap 65533 :: i32wrap 65533 :: nil.
Proof. vm_compute. reflexivity. Qed.
Example utf8_surrogate :                      (* 0xED 0xA0 0x80 (would be U+D800, a UTF-16 surrogate) → three U+FFFD *)
  str_to_runes (String (byte_chr 237) (String (byte_chr 160) (String (byte_chr 128) EmptyString)))
    = i32wrap 65533 :: i32wrap 65533 :: i32wrap 65533 :: nil.
Proof. vm_compute. reflexivity. Qed.
Example utf8_truncated_2 :                     (* 0xC2 with no continuation → one U+FFFD *)
  str_to_runes (String (byte_chr 194) EmptyString) = i32wrap 65533 :: nil.
Proof. vm_compute. reflexivity. Qed.
Example utf8_valid_2byte :                     (* 0xC2 0xA9 = U+00A9 (©) still decodes correctly *)
  str_to_runes (String (byte_chr 194) (String (byte_chr 169) EmptyString)) = i32wrap 169 :: nil.
Proof. vm_compute. reflexivity. Qed.

(** Single rune → string (Go's [string(rune)]): the 1-code-point UTF-8 string.  Reuses the
    [rune_bytes] encoder; lowers to the native [string(rune(r))] (the explicit [rune] cast
    keeps it out of the deprecated [string(int)] form). *)
Definition rune_to_str (r : GoI32) : GoString := rune_bytes r.
Example rune_to_str_ascii : rune_to_str (i32wrap 65) = "A"%string.
Proof. vm_compute. reflexivity. Qed.
(** An out-of-range or surrogate rune encodes to U+FFFD,
    exactly Go's [string(rune)].  Witnessed against the explicit FFFD encoding [EF BF BD]: a
    UTF-16 surrogate (0xD800), a code point past MaxRune (0x110000), and a NEGATIVE rune (-1,
    built by [i32_sub] so it is a genuine negative int32) all collapse to U+FFFD. *)
Example rune_to_str_surrogate : rune_to_str (i32wrap 55296) = rune_to_str (i32wrap 65533).
Proof. vm_compute. reflexivity. Qed.
Example rune_to_str_above_max : rune_to_str (i32wrap 1114112) = rune_to_str (i32wrap 65533).
Proof. vm_compute. reflexivity. Qed.
Example rune_to_str_negative :
  rune_to_str (i32_sub (i32wrap 0) (i32wrap 1)) = rune_to_str (i32wrap 65533).
Proof. vm_compute. reflexivity. Qed.

(** String COMPARISON (Go spec "Comparison operators": strings are comparable AND
    ordered).  [str_eqb] is Go [==] — byte-sequence equality (a THEOREM via
    [String.eqb]).  [str_ltb] is Go [<] — LEXICOGRAPHIC by BYTE VALUE, exactly Go's
    string ordering: compare byte-by-byte (unsigned 0..255), the first differing byte
    decides, and a proper prefix is [<] the longer string.  Both are pure, total
    operations on immutable byte sequences; the bodies are suppressed and each lowers
    to the bare Go operator ([a == b] / [a < b]).  [str_ltb] reuses the already-
    suppressed [ascii_byte] decoder (so it drags in no [nat_of_ascii]). *)
Definition str_eqb (a b : GoString) : bool := String.eqb a b.

(** Generic [comparable] CONSTRAINT (Go's [func F[K comparable](…)]).  A comparable type's
    equality is carried as a [ComparableW K] WITNESS — computational in Rocq (so [vm_compute] /
    proofs reduce), but the plugin ERASES it: a function with a [ComparableW (Tvar)] parameter
    drops that parameter at its declaration AND every call site, emits the corresponding type
    variable as [K comparable] (not [any]), and lowers the witness equality [cw_eqb] to native
    Go [==].  Faithful: on a Go-comparable type, [cw_eqb] decides the SAME equality [==] does, so
    erasing the dictionary to the native operator preserves meaning (the witness exists only so
    Rocq can compute/prove; Go's [comparable] supplies [==] structurally with no runtime dict). *)
(** Each comparison function DECIDES its type's equality — the evidence a sealed witness must carry. *)
Lemma i64_eqb_spec : forall x y, i64_eqb x y = true <-> x = y.
Proof.
  intros x y. unfold i64_eqb. split.
  - intro H. apply Z.eqb_eq in H. apply i64_ext; exact H.
  - intro H; subst; apply Z.eqb_refl.
Qed.
Lemma u64_eqb_spec : forall x y, u64_eqb x y = true <-> x = y.
Proof.
  intros x y. unfold u64_eqb. split.
  - intro H. apply Z.eqb_eq in H. apply u64_ext; exact H.
  - intro H; subst; apply Z.eqb_refl.
Qed.
Lemma str_eqb_spec : forall x y, str_eqb x y = true <-> x = y.
Proof. intros x y. unfold str_eqb. apply String.eqb_eq. Qed.

(** SEALED: [ComparableW] CARRIES the decidability proof
    [cw_ok] (SProp-erased, proof-irrelevant), so a bogus witness like [MkComparableW (fun _ _ => false) _]
    is UNCONSTRUCTABLE — its spec [forall x y, false = true <-> x = y] is false.  Hence erasing [cw_eqb] to
    native Go [==] is sound, not a forgeable claim.  The proof field erases (SProp), so extraction is
    unchanged: the whole witness is dropped by the plugin regardless of arity. *)
Record ComparableW (K : Type) : Type := MkComparableW {
  cw_eqb : K -> K -> bool ;
  cw_ok  : Squash (forall x y, cw_eqb x y = true <-> x = y) }.
Arguments MkComparableW {K} _ _.
Arguments cw_eqb {K} _.
Arguments cw_ok {K} _.
Definition ceqb {K} (w : ComparableW K) (a b : K) : bool := cw_eqb w a b.
(** Each instance is a [ComparableW]-typed Definition, suppressed by the plugin (the witness erases to
    native [==]); the [squash]ed spec is the seal that makes a bogus witness unconstructable. *)
Definition cw_i64 : ComparableW GoI64    := MkComparableW i64_eqb (squash i64_eqb_spec).
Definition cw_u64 : ComparableW GoU64    := MkComparableW u64_eqb (squash u64_eqb_spec).
Definition cw_str : ComparableW GoString := MkComparableW str_eqb (squash str_eqb_spec).

(** The seal is real (machine-checked): the always-[false] equality does NOT decide [GoI64] equality, so
    no [ComparableW GoI64] can wrap it — the forged witness [MkComparableW (fun _ _ => false) _] is
    unconstructable (its [cw_ok] obligation is the unprovable proposition below).  This is the safe-by-
    construction guarantee the erasure [cw_eqb w → Go ==] needs: a witness exists only when [cw_eqb]
    genuinely decides [=], hence agrees with Go's [==]. *)
Lemma bogus_eqb_undecidable :
  ~ (forall x y : GoI64, (fun _ _ : GoI64 => false) x y = true <-> x = y).
Proof. intro H. destruct (H (i64wrap 0%Z) (i64wrap 0%Z)) as [_ Hb]. discriminate (Hb eq_refl). Qed.

Fixpoint str_ltb (a b : GoString) : bool :=
  match a, b with
  | EmptyString,  EmptyString  => false   (* equal — not [<] *)
  | EmptyString,  String _ _   => true    (* "" < non-empty (prefix) *)
  | String _ _,   EmptyString  => false   (* non-empty not < "" *)
  | String ca ra, String cb rb =>
      let na := u8raw (ascii_byte ca) in  (* byte value 0..255 *)
      let nb := u8raw (ascii_byte cb) in
      if Z.ltb na nb then true
      else if Z.ltb nb na then false
      else str_ltb ra rb
  end.

(** Direct [>] / [>=] / [!=] for strings (total lexicographic order, no NaN, so
    [>=] is [¬(<)]).  Recognized by name and lowered to the direct Go operator. *)
Definition str_gtb  (a b : GoString) : bool := str_ltb b a.
Definition str_geb  (a b : GoString) : bool := negb (str_ltb a b).
Definition str_neqb (a b : GoString) : bool := negb (str_eqb a b).

(** Expression switch on a STRING scrutinee — Go's [switch s { case "a": …; default: … }].
    Same shape as [int_switch2] but the equality is [str_eqb] (byte equality); the plugin
    arm is SHARED (it emits the scrutinee and each case value verbatim, Go doing the [==]),
    so int64 and string scrutinees lower identically. *)
Definition str_switch2 {B : Type} (x : GoString)
  (v1 : GoString) (k1 : IO B)
  (v2 : GoString) (k2 : IO B)
  (d : IO B) : IO B :=
  if str_eqb x v1 then k1
  else if str_eqb x v2 then k2
  else d.

Example str_switch2_first : forall {B} (k1 k2 d : IO B),
  str_switch2 "a"%string "a"%string k1 "b"%string k2 d = k1.
Proof. reflexivity. Qed.
Example str_switch2_second : forall {B} (k1 k2 d : IO B),
  str_switch2 "b"%string "a"%string k1 "b"%string k2 d = k2.
Proof. reflexivity. Qed.
Example str_switch2_default : forall {B} (k1 k2 d : IO B),
  str_switch2 "z"%string "a"%string k1 "b"%string k2 d = d.
Proof. reflexivity. Qed.

(** N-ary string expression switch (3 cases) — same generalised plugin arm as
    [str_switch2]/[int_switch2]; completes the >2-case coverage for both scrutinee types. *)
Definition str_switch3 {B : Type} (x : GoString)
  (v1 : GoString) (k1 : IO B)
  (v2 : GoString) (k2 : IO B)
  (v3 : GoString) (k3 : IO B)
  (d : IO B) : IO B :=
  if str_eqb x v1 then k1
  else if str_eqb x v2 then k2
  else if str_eqb x v3 then k3
  else d.
Example str_switch3_third : forall {B} (k1 k2 k3 d : IO B),
  str_switch3 "c"%string "a"%string k1 "b"%string k2 "c"%string k3 d = k3.
Proof. reflexivity. Qed.
Example str_switch3_default : forall {B} (k1 k2 k3 d : IO B),
  str_switch3 "z"%string "a"%string k1 "b"%string k2 "c"%string k3 d = d.
Proof. reflexivity. Qed.

(** ---- Complex numbers (Go spec "Complex numbers"; the predeclared [complex]/[real]/
    [imag] builtins) ----  A [complex128] is a pair of [float64] components.  We model it
    as a 2-field record over [float]; the plugin renders the type as Go's native
    [complex128] and lowers [go_complex]/[go_real]/[go_imag] to the predeclared builtins
    [complex(re, im)] / [real(c)] / [imag(c)] (the record's struct decl, constructor, and
    projections are all suppressed — recognised by operation name, like the numint
    wrappers).  Construction/extraction are PROVABLE ([go_real (go_complex re im) = re]). *)
Record GoComplex128 : Type := MkComplex128 { c_re : GoFloat64 ; c_im : GoFloat64 }.
Definition go_complex (re im : GoFloat64) : GoComplex128 := MkComplex128 re im.
Definition go_real (c : GoComplex128) : GoFloat64 := c_re c.
Definition go_imag (c : GoComplex128) : GoFloat64 := c_im c.

Example go_real_complex : forall re im, go_real (go_complex re im) = re.
Proof. reflexivity. Qed.
Example go_imag_complex : forall re im, go_imag (go_complex re im) = im.
Proof. reflexivity. Qed.

(** Complex ARITHMETIC — Go's [+] / [-] on complex128.  These are COMPONENT-WISE (each
    component is a single IEEE float add/sub), so the model is faithful including the
    Inf/NaN corners, and it lowers to the native Go [+] / [-].  *([*] and [/] are DEFERRED:
    Go's complex multiply/divide carry rounding-order subtleties — naive cross-products for
    [*], Smith's scaling algorithm for [/] in the runtime — that a faithful model must match
    exactly; a careful follow-up, not approximated here.)* *)
Definition complex_add (a b : GoComplex128) : GoComplex128 :=
  MkComplex128 (f64_add (c_re a) (c_re b)) (f64_add (c_im a) (c_im b)).
Definition complex_sub (a b : GoComplex128) : GoComplex128 :=
  MkComplex128 (f64_sub (c_re a) (c_re b)) (f64_sub (c_im a) (c_im b)).

(** Build-checked: each component of the sum/difference is the float add/sub of the
    corresponding components (so the native [a + b] computes exactly what Go does). *)
Example complex_add_components : forall a b,
  go_real (complex_add a b) = f64_add (go_real a) (go_real b)
  /\ go_imag (complex_add a b) = f64_add (go_imag a) (go_imag b).
Proof. intros. split; reflexivity. Qed.
Example complex_sub_components : forall a b,
  go_real (complex_sub a b) = f64_sub (go_real a) (go_real b)
  /\ go_imag (complex_sub a b) = f64_sub (go_imag a) (go_imag b).
Proof. intros. split; reflexivity. Qed.

(** Complex COMPARISON — Go's [==] / [!=] on complex128.  Two complex values are equal iff
    BOTH components are equal (Go spec "Comparison operators"); float [==] is EXACT, so this
    is faithful including the NaN corner ([NaN != NaN] ⇒ a complex with a NaN component is
    never [==] itself).  Lowers to the native Go [==] / [!=]. *)
Definition complex_eqb (a b : GoComplex128) : bool :=
  andb (f64_eqb (c_re a) (c_re b)) (f64_eqb (c_im a) (c_im b)).
Definition complex_neqb (a b : GoComplex128) : bool := negb (complex_eqb a b).

(** Build-checked: equality is the component-wise float-[==] conjunction (so the native
    [a == b] decides exactly what Go's complex [==] does). *)
Example complex_eqb_components : forall a b,
  complex_eqb a b = andb (f64_eqb (go_real a) (go_real b)) (f64_eqb (go_imag a) (go_imag b)).
Proof. reflexivity. Qed.

(** Complex MULTIPLY — Go's [*] on complex128.  The Go spec underspecifies the rounding of
    complex multiply, and the gc compiler inlines the NAIVE cross-product formula
    [(ac − bd) + (ad + bc)i] (it does NOT implement C99 Annex G's Inf/NaN recovery — only
    DIVISION calls a runtime helper).  This model uses exactly that naive formula, so it
    matches gc bit-for-bit including the Inf/NaN corners (both are naive IEEE), and lowers
    to the native Go [*].  *([/] is still DEFERRED: gc's [runtime.complex128div] uses
    Smith's scaling algorithm — a different computation a faithful model must port exactly.)* *)
Definition complex_mul (a b : GoComplex128) : GoComplex128 :=
  MkComplex128
    (f64_sub (f64_mul (c_re a) (c_re b)) (f64_mul (c_im a) (c_im b)))
    (f64_add (f64_mul (c_re a) (c_im b)) (f64_mul (c_im a) (c_re b))).

(** Build-checked: the real/imag parts are exactly gc's naive cross products. *)
Example complex_mul_components : forall a b,
  go_real (complex_mul a b)
    = f64_sub (f64_mul (go_real a) (go_real b)) (f64_mul (go_imag a) (go_imag b))
  /\ go_imag (complex_mul a b)
    = f64_add (f64_mul (go_real a) (go_imag b)) (f64_mul (go_imag a) (go_real b)).
Proof. intros. split; reflexivity. Qed.

(** Complex unary NEGATION — Go's [-c] on complex128.  Negates BOTH components, each a
    single IEEE float sign-flip [f64_opp], so faithful including signed zero — note
    [-c] (sign-flip) differs from [(0+0i) - c] on a zero component ([opp (+0) = -0] but
    [0 - (+0) = +0]); we use the sign-flip, matching Go's unary [-].  Lowers to native [-c]. *)
Definition complex_neg (c : GoComplex128) : GoComplex128 :=
  MkComplex128 (f64_opp (c_re c)) (f64_opp (c_im c)).

Example complex_neg_components : forall c,
  go_real (complex_neg c) = f64_opp (go_real c)
  /\ go_imag (complex_neg c) = f64_opp (go_imag c).
Proof. intros. split; reflexivity. Qed.

(** Complex DIVIDE — Go's [/] on complex128.  Unlike [*] (a naive inline), gc lowers [/]
    to [runtime.complex128div], which uses SMITH'S scaling algorithm (divide through by the
    larger-magnitude denominator component, for numerical stability).  This model is exactly
    that algorithm — operand-for-operand the gc source — and it lowers to the native Go [/].
    (The Annex-G-style Inf/NaN recovery postamble for DEGENERATE divisors is modelled too —
    see the branch comment below.) *)
Definition complex_div (n m : GoComplex128) : GoComplex128 :=
  let nr := c_re n in let ni := c_im n in
  let mr := c_re m in let mi := c_im m in
  (* branch on which denominator component is larger in magnitude — Go uses [|mr| >= |mi|], i.e.
     [|mi| <= |mr|].  We compare ABSOLUTE VALUES via [f64_abs] (= [SpecFloat.SFabs], axiom-free):
     abs never overflows, so the branch matches Go even for huge components (a squared-magnitude
     compare would collapse to [Inf <= Inf] and pick the wrong branch).  Sound even though
     [math.Abs] would need an import: [complex_div] lowers to the NATIVE Go [/] (body PROOF-ONLY,
     suppressed by name), so the [abs] is never extracted.
    The DEGENERATE-divisor postamble (C99 Annex G.5.1 step 3 — zero / Inf / NaN denominators) is
    PORTED operand-for-operand from gc's [runtime.complex128div], so the model matches Go on ALL
    inputs, not just finite ones.  NaN/Inf are detected with [spec_float] primitives ([eqb x x] /
    [|x| = +Inf]); [copysign_inf]/[inf2one] reproduce gc's [math.Copysign] (sign of a zero via
    [1.0 / c = -Inf]).  All proof-only — [complex_div] still lowers to native Go [/], whose
    runtime applies exactly this recovery. *)
  let isnan := fun x => negb (f64_eqb x x) in
  let isinf := fun x => f64_eqb (f64_abs x) (S754_infinity false) in
  let isfin := fun x => negb (orb (isnan x) (isinf x)) in
  (* sign bit set (x < 0, or x = -0 detected via 1.0/-0 = -Inf) *)
  let negs  := fun x => orb (f64_ltb x (0%go64))
                            (f64_eqb (f64_div (1%go64) x) (S754_infinity true)) in
  let copysign_inf := fun c => if negs c then (S754_infinity true) else (S754_infinity false) in (* Copysign(+Inf, c) *)
  let inf2one := fun x => let g := if isinf x then (1%go64) else (0%go64) in
                          if negs x then f64_opp g else g in       (* Copysign(isInf?1:0, x) *)
  let res :=
    if f64_leb (f64_abs mi) (f64_abs mr) then
      let ratio := f64_div mi mr in
      let denom := f64_add mr (f64_mul ratio mi) in
      MkComplex128 (f64_div (f64_add nr (f64_mul ni ratio)) denom)
                   (f64_div (f64_sub ni (f64_mul nr ratio)) denom)
    else
      let ratio := f64_div mr mi in
      let denom := f64_add mi (f64_mul ratio mr) in
      MkComplex128 (f64_div (f64_add (f64_mul nr ratio) ni) denom)
                   (f64_div (f64_sub (f64_mul ni ratio) nr) denom) in
  (* Annex-G recovery: only when BOTH components came out NaN (a degenerate divisor) *)
  if andb (isnan (c_re res)) (isnan (c_im res)) then
    let a := nr in let b := ni in let c := mr in let d := mi in
    if andb (andb (f64_eqb c (0%go64)) (f64_eqb d (0%go64)))
            (orb (negb (isnan a)) (negb (isnan b)))                          (* m == 0, n not all-NaN *)
    then MkComplex128 (f64_mul (copysign_inf c) a) (f64_mul (copysign_inf c) b)
    else if andb (orb (isinf a) (isinf b)) (andb (isfin c) (isfin d))        (* Inf numerator / finite denom *)
    then let a' := inf2one a in let b' := inf2one b in
         MkComplex128 (f64_mul (S754_infinity false) (f64_add (f64_mul a' c) (f64_mul b' d)))
                      (f64_mul (S754_infinity false) (f64_sub (f64_mul b' c) (f64_mul a' d)))
    else if andb (orb (isinf c) (isinf d)) (andb (isfin a) (isfin b))        (* finite numerator / Inf denom *)
    then let c' := inf2one c in let d' := inf2one d in
         MkComplex128 (f64_mul (0%go64) (f64_add (f64_mul a c') (f64_mul b d')))
                      (f64_mul (0%go64) (f64_sub (f64_mul b c') (f64_mul a d')))
    else res
  else res.

(** Witness (machine-checked): on a large divisor where BOTH components square to [+Inf]
    (|mi|, |mr| ≳ 1e154) but |mi| > |mr|, a squared-magnitude branch [mi² <= mr²] wrongly reduces
    to [Inf <= Inf = true] (picks the |mr|-branch), while [|mi| <= |mr|] correctly yields [false]
    (the |mi|-branch) — exactly Go's [|mr| >= |mi|].  ([0x1p550] = 2^550, [0x1p600] = 2^600.) *)
Example complex_div_branch_overflow_fixed :
  let mr := binary_normalize 53 1024 1 550 false in let mi := binary_normalize 53 1024 1 600 false in  (* 2^550, 2^600 *)
     f64_leb (f64_mul mi mi) (f64_mul mr mr) = true    (* squared: WRONG branch *)
  /\ f64_leb (f64_abs mi)    (f64_abs mr)    = false.  (* abs:     RIGHT branch *)
Proof. vm_compute. split; reflexivity. Qed.
(** DEGENERATE divisors recover per Annex G (not the bare-Smith NaN).  Finite
    nonzero / ZERO yields infinities; finite / Inf yields zero — matching gc's runtime.complex128div. *)
Example complex_div_by_zero_is_inf :   (* (1+2i)/(0+0i) = (+Inf, +Inf) *)
  f64_eqb (c_re (complex_div (go_complex (1%go64) (2%go64)) (go_complex (0%go64) (0%go64)))) (S754_infinity false) = true
  /\ f64_eqb (c_im (complex_div (go_complex (1%go64) (2%go64)) (go_complex (0%go64) (0%go64)))) (S754_infinity false) = true.
Proof. vm_compute. split; reflexivity. Qed.
Example complex_div_by_inf_is_zero :   (* (1+1i)/(Inf+Inf i) = (0, 0) *)
  f64_eqb (c_re (complex_div (go_complex (1%go64) (1%go64)) (go_complex (S754_infinity false) (S754_infinity false)))) (0%go64) = true
  /\ f64_eqb (c_im (complex_div (go_complex (1%go64) (1%go64)) (go_complex (S754_infinity false) (S754_infinity false)))) (0%go64) = true.
Proof. vm_compute. split; reflexivity. Qed.

(** ---- STRUCT CHANNELS (a 2-field [int64 x int64] struct over a channel) ----

    A struct channel is a [GoChan (GoI64 * GoI64)]: the CELL stores the field TUPLE, tagged by the
    DECIDABLE [TProd TI64 TI64] (a product is canonical, so [tag_eq] recovers it — a nominal
    [GoTypeTag] for a NAMED struct is impossible, [tag_eq] cannot decide it).  The value sent IS the
    tuple, so the channel marshals it by the IDENTITY.

    COHERENCE — there is NO [StructRep] to choose, so a send and a receive CANNOT disagree on
    field order: marshalling by the identity makes a swapped-rep corruption UNREPRESENTABLE
    (the non-overridable behaviour of a Go [chan (int64,int64)]).  A named 2-field struct over
    a channel would need a nominal struct tag (unavailable) — out of scope, not approximated.

    *(Extraction of the idiomatic native [chan R] / [ch <- p] / [<-ch] is a separate slice: Coq's
    [prod] is the multi-return tuple, so emitting it as a Go struct needs dedicated plugin work;
    this lands the MODEL + the correctness theorem.)* *)
Definition struct_make2 (n : GoInt) : IO (GoChan (GoI64 * GoI64)) :=
  bind (make_chan_buf (TProd TI64 TI64) n) (fun ch => ret (MkChan (ch_loc ch))).
Definition struct_send2 (ch : GoChan (GoI64 * GoI64)) (v : GoI64 * GoI64) : IO unit :=
  send (TProd TI64 TI64) (MkChan (ch_loc ch)) v.
Definition struct_recv2 (ch : GoChan (GoI64 * GoI64)) : IO (GoI64 * GoI64) :=
  recv (TProd TI64 TI64) (MkChan (ch_loc ch)).

(** CORRECTNESS — round-trip faithfulness.  On an OPEN, EMPTY channel, [struct_send2] then
    [struct_recv2] recovers the struct EXACTLY: the field-tuple marshalling is lossless, by
    [sr2_eta] of the channel's CANONICAL rep (send and recv share it — no rep to mismatch).  This
    is the acceptance test at the model level (a struct survives a channel round-trip intact). *)
Theorem struct_chan_roundtrip2 :
  forall (ch : GoChan (GoI64 * GoI64)) (v : GoI64 * GoI64) (w : World),
    @chan_closed (GoI64 * GoI64)%type (MkChan (ch_loc ch)) w = false ->
    chan_buf (TProd TI64 TI64) (MkChan (ch_loc ch)) w = nil ->
    chan_room (TProd TI64 TI64) (MkChan (ch_loc ch)) w = true ->
    exists w', run_io (bind (struct_send2 ch v)
                            (fun _ => struct_recv2 ch)) w = ORet v w'.
Proof.
  intros ch v w Hopen Hempty Hroom.
  unfold struct_send2, struct_recv2.
  rewrite run_bind.
  rewrite (run_send (TProd TI64 TI64) (MkChan (ch_loc ch)) v w Hopen Hroom).
  assert (Hbuf1 : chan_buf (TProd TI64 TI64) (MkChan (ch_loc ch))
            (chan_send_upd (TProd TI64 TI64) (MkChan (ch_loc ch)) v w) = v :: nil)
    by (rewrite chan_buf_send, Hempty; reflexivity).
  rewrite (run_recv (TProd TI64 TI64) (MkChan (ch_loc ch)) v nil _ Hbuf1).
  eexists; reflexivity.
Qed.

(** ---- [range] over a string (Go spec "For statements: For range"): [for i, r := range s] ----
    Go ranges a STRING by UTF-8 code point: [i] is the BYTE offset of each code point's first
    byte, [r] the decoded rune.  Modeled faithfully on the rune view: [str_to_runes_w] decodes
    each rune WITH the number of source bytes it consumed, and the byte offsets are the running
    prefix sums of those CONSUMED widths — exactly Go's string-range index, even for invalid
    UTF-8 (machine-checked by [str_range_offsets] / [str_range_invalid_offsets] in main.v).
    ([rune_width] — utf8.RuneLen, a rune's ENCODED length — is a separate utility.)  [str_range] lowers
    to the NATIVE two-variable [for i, r := range s]; the [for_each_pairs]/[runes_with_offsets]
    model is proof-only (recognized by name, decl suppressed), so the emitted Go is the
    idiomatic range loop — never a [[]rune] materialisation.  The index is the Go [int]
    index type. *)
Definition rune_width (r : GoI32) : Z :=
  let c := i32raw r in
  if Z.ltb c 128   then 1    (* 1-byte (ASCII) *)
  else if Z.ltb c 2048  then 2    (* 2-byte *)
  else if Z.ltb c 65536 then 3    (* 3-byte *)
  else 4.                          (* 4-byte *)
(** Byte offsets are the running prefix sums of the CONSUMED SOURCE widths (the [int] tag from
    [str_to_runes_w]), so an invalid byte advances the offset by ONE — matching Go's range even
    for invalid UTF-8.  Re-encoding the decoded rune (via [rune_width]) would
    OVER-count: U+FFFD is 3 bytes encoded but a malformed byte consumes only 1. *)
Fixpoint runes_with_offsets (off : GoInt) (rs : list (GoI32 * Z)) : list (GoInt * GoI32) :=
  match rs with
  | nil              => nil
  | cons (r, w) rest => cons (off, r) (runes_with_offsets (int_add off (intwrap w)) rest)
  end.
Fixpoint for_each_pairs {A B : Type} (xs : list (A * B)) (body : A -> B -> IO unit) : IO unit :=
  match xs with
  | nil              => ret tt
  | cons (a, b) rest => bind (body a b) (fun _ => for_each_pairs rest body)
  end.
Definition str_range (s : GoString) (body : GoInt -> GoI32 -> IO unit) : IO unit :=
  for_each_pairs (runes_with_offsets (intwrap 0) (str_to_runes_w s)) body.

(** ---- Indexed [range] over a slice (Go spec "For statements: For range"): [for i, x := range xs] ----
    [i] is the element INDEX (0, 1, 2, …), [x] the element — the indexed counterpart of
    [for_each] (which discards the index).  The index is the Go [int] index type (the [Z]-carried [GoInt]).
    Lowers to the native two-variable [for i, x := range xs]; the accumulator model below is
    proof-only (recognized by name, decl suppressed). *)
Fixpoint for_each_idx_from {A : Type} (i : GoInt) (xs : GoSlice A) (body : GoInt -> A -> IO unit) : IO unit :=
  match xs with
  | nil         => ret tt
  | cons x rest => bind (body i x) (fun _ => for_each_idx_from (int_add i (intwrap 1)) rest body)
  end.
Definition for_each_idx {A : Type} (xs : GoSlice A) (body : GoInt -> A -> IO unit) : IO unit :=
  for_each_idx_from (intwrap 0) xs body.

(** ---- Integer [range] (Go 1.22, spec "For statements: For range" over an integer): [for i := range n] ----
    Produces [i = 0, 1, …, n-1] (and runs zero times when [n = 0], exactly Go's rule).
    The bound [n] is the iteration COUNT (a [nat] — non-negative, and the structurally
    DECREASING argument, so termination is by construction with no carrier conversion); the produced index
    [i] is the Go [int] index type (the [Z]-carried [GoInt]).  Recognized by name + decl suppressed, so the
    lowering is the native [for i := range n] (the [nat] count renders as the bound). *)
Fixpoint int_range_aux (i : GoInt) (n : nat) (body : GoInt -> IO unit) : IO unit :=
  match n with
  | O    => ret tt
  | S f  => bind (body i) (fun _ => int_range_aux (int_add i (intwrap 1)) f body)
  end.
Definition int_range (n : nat) (body : GoInt -> IO unit) : IO unit :=
  int_range_aux (intwrap 0) n body.
