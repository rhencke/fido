# Go spec conformance ledger

Tracks our model against the **Go language spec** (go.dev/ref/spec) and the **Go
memory model** (go.dev/ref/mem), **in spec document order** — top to bottom, one
section at a time.  Our Rocq is meant to follow this order too, so each spec
section maps to a region of the model.  Each entry: the spec rule (the SOURCE of
our behavior, cited), our model, status, and the machine-checked witness.

Status legend:
- **✓ conforms** — verified, ideally a machine-checked witness (an `Example`/
  `Theorem` whose proof IS the conformance check).
- **⚠ bounded deviation** — conforms within a principled, documented limit; the
  deviation is known and tracked, never silent.
- **✗ not modeled (fails loud)** — unmodeled; any use aborts extraction
  (`unsupported`) or fails `go build` — never silently wrong (the fail-loud
  policy).  An honest gap, not a conformance violation.

Discipline: a primitive is "done" only when its section is honored here; when
code implements a rule, it cites the section in a comment.

---

## Lexical elements

### [Integer literals](https://go.dev/ref/spec#Integer_literals) / [Floating-point literals](https://go.dev/ref/spec#Floating-point_literals) — ⚠ (typed/fixed-width view)
Spec: literals are *untyped constants* (see Constants).  Ours: written as Rocq
`PrimInt63` / `PrimFloat` values — i.e. the already-*typed*, fixed-width runtime
view.  The lexical shapes (decimal, sign) round-trip (`neglit_demo`:
`-7 / -1 / -2147483648`), but the untyped/arbitrary-precision layer is not
modeled here — see **Constants** below.

## Constants

### [Constants](https://go.dev/ref/spec#Constants) / [Constant expressions](https://go.dev/ref/spec#Constant_expressions) — ✓ representability (fixed-width); ⚠ arbitrary precision
Spec: "Numeric constants represent **exact values of arbitrary precision and do
not overflow**."  A constant acquires a type only at use, where "**it is an error
if the constant value cannot be represented as a value of the respective type**"
(a compile-time representability check); constant overflow is a *compile error*
(NOT a runtime wrap), and constant float arithmetic rounds once at the typed
boundary (`const 0.1+0.2` = `0.3`).
Ours: **REPRESENTABILITY now airtight for the fixed-width types** — `u8_lit`/
`i8_lit`/`u16_lit`/`i16_lit` DEMAND a proof the constant fits the type's range
(`u8_lit : forall x, (x <? 256) = true -> GoU8`), discharged by `eq_refl` for an
in-range literal.  So an out-of-range constant is **unrepresentable** — a compile
error, exactly Go's "constant overflows uint8", NOT a silent wrap — build-checked
by `u8_const_oob`/`i8_const_oob`/`u16_const_oob`/`i16_const_oob` (`Fail` tests).
The Go output is unchanged (the proof erases; in-range mask is a no-op).  ✓
*Remaining for full airtightness (the rest of this section):* `int` (Sint63)
literals aren't yet representability-checked (ties to wrapping `int` as a distinct
record + the Z-width model, Tier 2 #4); **arbitrary-precision** constant
arithmetic (large intermediates like `1<<40 * 1<<40`) needs untyped int constants
as `Z`; **float constants** need exact rationals (`Q`) rounding once at the typed
boundary.  ⚠ tracked.

## Types

### [Boolean types](https://go.dev/ref/spec#Boolean_types) — ✓
Spec: `bool`; comparable; values `true`/`false`.  Ours: Coq `bool` → Go `bool`.
(Comparison: see Comparison operators.)  ✓

### [Numeric types](https://go.dev/ref/spec#Numeric_types) — ✓ ranges/two's-complement/**distinctness**; ⚠ `int` width
Spec: `uint8…uint64`, `int8…int64` with exact ranges; "**the value of an n-bit
integer is n bits wide and represented using two's complement arithmetic**";
`byte`=`uint8`, `rune`=`int32`; `int`/`uint` are 32-or-64-bit.  And: "**all
numeric types are defined types and thus distinct… Explicit conversions are
required when different numeric types are mixed**."
Ours: `uint8`/`int8`/`uint16`/`int16` are each their OWN Rocq type (a record over
the `int` carrier, wrapper erased in extraction) — fully modeled (mask +
two's-complement sign-extend).  Two's-complement: ✓ (`i8_add_wraps`,
`i16_add_wraps`).  **DISTINCTNESS now airtight, BY CONSTRUCTION**: Rocq rejects
mixing types, build-checked by `u8_no_implicit`, `i8_no_implicit`,
`u16_no_implicit`, `i16_no_implicit`, and the cross-width `u8_u16_no_mix` — exactly
the spec's "no implicit conversion; the only implicit path is an untyped constant"
(`u8_lit : int -> GoU8`).  ✓  *Remaining:* `int`=Sint63 (⚠ faithful to int64 only
within ±2⁶², Tier 2 #4) is not yet wrapped as a distinct record; `uint32`/`int32`
add/sub/cmp (mul **✗ fails loud** — exceeds carrier), 64-bit **✗ fails loud**
(needs Z-model); `float32` **✗** (no native Rocq f32).  Note: distinctness makes
explicit CONVERSIONS (next section) load-bearing — without them you can't use a
`uint8` where an `int` is wanted (which is correct: it fails loud, not silently).

### [String types](https://go.dev/ref/spec#String_types) — ✓ byte sequence (rune view deferred)
Spec: "A string value is a (possibly empty) sequence of **bytes**… The number of
bytes is called the **length**… A string's **bytes** can be accessed by integer
indices `0` through `len(s)-1`" (`s[i]` is a byte); strings are **immutable**;
`range s` decodes UTF-8 to runes.
Ours: `GoString := string` (Coq's `Strings.String`, *itself* a sequence of
`Ascii.ascii` = bytes) → Go `string`.  This is the faithful byte model, replacing
the earlier `list GoRune` (the rune view, which mismodelled `len`/`s[i]`).
- **`len`** (`str_len`): a computable `int` counting **bytes** → Go `int64(len(s))`;
  `str_len "Go" = 2` is a **theorem** (`spec_str_len_Go`). ✓
- **index** (`str_at_ok`): the **safe** byte accessor — CPS/comma-ok like
  `slice_at_ok`, so it *forces* handling out-of-range (cannot panic).  In range ⇒
  `b = s[i]` (a `byte` = `GoU8`, widened to the int64 carrier) and `ok = true`;
  else `0`/`false`.  `i : int` is signed → both ends checked.  Demo: `s[5]` of
  `"Go"` (len 2) → `0 false`, no panic. ✓
- **concat** (`str_concat`, spec "Operators"): pure byte append → Go `+`;
  `str_concat "Go" "!" = "Go!"` is a **theorem** (`spec_str_concat`). ✓
- **immutability**: free (Coq `string` is a value). ✓
- **distinctness**: a `string` is its own type — `str_no_implicit` (a `Fail`) is
  the build-checked proof that an `int` does not implicitly convert in. ✓
- **literals**: the plugin decodes a Coq `String`/`Ascii`/`EmptyString` literal to
  a byte-faithful Go string literal (printable ASCII verbatim; other bytes via Go's
  `\xNN`), so the emitted literal denotes EXACTLY the modelled bytes. ✓
**Deferred (not silently wrong — unmodeled, fails loud):** the **rune view**
(`range s` UTF-8 decode, `string`↔`[]rune`/`[]byte` — see Conversions ✗), and
byte-level mutation (Go forbids `s[i] = …` anyway; strings are immutable).

### [Slice types](https://go.dev/ref/spec#Slice_types) / [Map types](https://go.dev/ref/spec#Map_types) / [Channel types](https://go.dev/ref/spec#Channel_types) — ✓ single-goroutine
Slices = `list` (`len`/`cap`/`append`/`slice_at_ok`); maps via a heap in the world
(get-after-write are *theorems*); channels via state in the world (below).  ✓ for
single-goroutine/non-aliasing use; sub-slice aliasing / in-place append unmodeled
(Tier 3 #8a).

## Expressions — operators

### [Arithmetic operators](https://go.dev/ref/spec#Arithmetic_operators)
`+ - * / %` integers: see Integer operators / overflow.  Unary `-x = 0-x` ✓
(`neg_demo`), `+x = 0+x` ✓.
**Bitwise `& | ^ &^` and unary `^` — ✓ fixed-width (`uintN`/`intN`).**  `uN_and`/
`or`/`xor`/`andnot`/`not`, `iN_*`: machine-checked (`spec_u8_and`…`spec_i8_andnot`;
240&60=48, |=252, ^=204, &^=192, `^240`=15, `^int8(5)=-6`, `int8(-1)&^5=-6`).
Faithful by construction: `uintN` AND/OR/XOR of in-range values stay in `[0,2ⁿ)`
(no mask); `intN` operands are sign-extended so the raw int64 op is already
correct; AND-NOT/complement flip within the width (`lxor _ (2ⁿ-1)`).  Go's `&^`
and unary `^` are single operators.  **Subtlety honored:** unary `^x` on the int64
carrier is the *64-bit* complement (`^240 = -241`), so it is wrapped back to the
width (`(^x)&0xff → 15`).  **`int` (Sint63) bitwise: ✗** — the 63-vs-64-bit carrier
exposes the sign bit, so bitwise on negative `int` would differ from int64; blocked
on the full-width Z model (Tier 2 #4).
**Shift `<< >>` — ✓ fixed-width (`uintN`/`intN`).**  `uN_shl`/`shr`, `iN_shl`/`shr`:
EVIDENCE-CARRYING like `div_nz` — the count must be proven **non-negative**
(`eq_refl` for a literal; a negative count is unrepresentable — `u8_shl_neg`, a
`Fail`), so the run-time panic is unreachable.  Machine-checked (`spec_u8_shl`…
`spec_i8_shr_neg`): `1<<3=8`, over-width `1<<8=0` (no upper limit on count),
`255>>4=15`, signed `64<<1=-128` (two's-complement wrap), and `>>` is **arithmetic**
for signed — `-3>>1=-2` (toward **−∞**, via `PrimInt63.asr`), DISTINCT from `-3/2=-1`
(toward zero), and `-1>>3=-1` (not 0).  `>>` is logical for `uintN` (`lsr`, the
non-negative carrier) and arithmetic for `intN` (`asr`, sign-extended).  Plugin emits
Go `x<<k` / `x>>k`.  **`int` (Sint63) shifts: ✗** (same 63-vs-64-bit carrier issue
as `int` bitwise — Z model).

### [Integer operators](https://go.dev/ref/spec#Integer_operators) — ✓ conforms
`q=x/y`, `r=x%y`: `x=q*y+r`, `|r|<|y|`, **truncated toward zero**; the example
table; the most-negative exception `x/-1 = x`, `x%-1 = 0` (two's-complement, no
panic); zero divisor ⇒ run-time panic (constant zero ⇒ compile error).
Ours: `div_nz`/`mod_nz` = `PrimInt63.divs`/`mods`, nonzero-divisor proof demanded
(panic unreachable).  Witnesses: `spec_div_5_3 … spec_mod_n5_n3` (full table),
`spec_div_minint_neg1`/`spec_mod_minint_neg1` (the `x/-1` exception; our
most-negative = `Sint63.min_int` = -2⁶²).  ✓

### [Integer overflow](https://go.dev/ref/spec#Integer_overflow) — ✓ unsigned; ⚠ signed boundary
Spec: unsigned `+ - * <<` = **mod 2ⁿ**; signed `+ - * / <<` overflow is
deterministic two's-complement, no panic.
Ours (unsigned): `uintN` mask = mod 2ⁿ — `u8_add_wraps` (300→44), `u8_mul_wraps`
(65025→1), `u8_sub_wraps` (0-1→255), `u16_mul_wraps`.  ✓  (signed): `int`/`intN`
two's-complement — `i8_add_wraps` (-106), `i16_add_wraps` (-25536),
`add_wraps_at_boundary`.  ✓ — but `int` wraps at **2⁶²**, not int64's 2⁶³.
⚠ bounded (Tier 2 #4); 64-bit/`u32_mul` **✗ fails loud**.

### [Floating-point operators](https://go.dev/ref/spec#Floating-point_operators) — ✓ ops; ⚠ FMA fusion
Spec: `+x=x`, `-x`=negation; div-by-zero "not specified beyond IEEE 754…
implementation-specific" whether it panics.  **An implementation MAY fuse** float
ops (e.g. FMA `x*y+z` without rounding the intermediate); an explicit float
conversion rounds to the target precision and prevents fusion.
Ours: `float64`=`PrimFloat` (IEEE binary64); `+ - * /`, `opp`, comparisons lower
to Go natives; float `/` unguarded (IEEE ±inf/NaN, no panic) — conforms.
`float_demo`, `float_opp_demo`.  **⚠ deviation:** we round EACH op (no fusion);
Go MAY FMA `a*b+c`, giving a more precise result — a fused expression can differ
from our per-op-rounded value.  `float32` **✗** (no native Rocq f32).

### [Comparison operators](https://go.dev/ref/spec#Comparison_operators) — ✓ conforms
Spec: integers "in the usual way", floats "as defined by IEEE 754", bools equal
iff both true/both false.  Ours (int): SIGNED `ltsb`/`lesb` → Go signed `</<=`;
unsigned `PrimInt63.ltb`/`leb` **rejected** for `int` (disagree on high bit) —
`ltb_unsigned_neg_false`/`ltb_signed_neg_true`.  (float): `PrimFloat.ltb`/`leb`/
`eqb`, IEEE incl. NaN unordered — `nan_eqb_false`, `nan_ltb_false`.  ✓
(`> >= !=` via swap / `negb(eqb…)` — tidiness gap, not conformance.)

### [Logical operators](https://go.dev/ref/spec#Logical_operators) — ✓ conforms
Spec: `p && q` = "if p then q else false", `p || q` = "if p then true else q",
`!p` = "not p"; short-circuit.  Ours: `andb`/`orb`/`negb` → `&&`/`||`/`!`, and
Coq's `andb` IS that definition — `spec_andb`/`spec_orb`/`spec_negb` by
`reflexivity`.  Short-circuit unobservable (pure total bools).  ✓

### [Conversions](https://go.dev/ref/spec#Conversions) — ✓ integer↔integer (fixed-width); ✗ rest
Spec: "When converting between integer types, ... it is then truncated to fit in
the result type's size."
**Integer conversions among `{int, uint8, int8, uint16, int16}` — ✓.**  Routed
through the `int` carrier: `int_of_FW` WIDENS (value preserved; lowers to identity)
and `FW_of_int` NARROWS (truncate — `land` for `uintN`, mask+sign-extend for `intN`
— exactly Go's `uint8(x)`/`int8(x)`, no representability proof since a conversion
truncates rather than rejects).  Cross-width by composition (`uint8(int16val)` =
`u8_of_int (int_of_i16 x)`, the low 8 bits).  These are also what make the DISTINCT
numeric types mixable — implicit mixing is rejected (`*_no_implicit`,
`u8_of_i16_direct` `Fail`s), so a value crosses types only through a conversion.
Machine-checked (`spec_u8_of_int_trunc`…`spec_i16_of_u8_cross`): `uint8(1000)=232`,
`uint8(-1)=255`, `int8(200)=-56`, widen `int(uint8 200)=200`, cross `int16(uint8 200)`.
`convert_demo` prints `200 232 / 1200`.
**Still ✗ (fails loud):** `int↔float` and `float↔float` (ties to the float gaps /
no native f32); `string`↔`[]byte`/`[]rune` (the rune view, deferred); `int`/64-bit
integer conversions (the Z-width carrier); interface conversions beyond `type_assert`.

## Statements

### [Send statements](https://go.dev/ref/spec#Send_statements) — ✓ open/closed; ⚠ nil/blocking
Spec: send on a **closed** channel ⇒ panic; send on **nil** blocks forever.
Ours: `run_send`/`run_send_closed` ⇒ `send_closed_panics` is a **theorem**.  ✓
nil-send (blocks): **✗** idealised away (divergence).

### [Receive operator](https://go.dev/ref/spec#Receive_operator) — ✓ conforms
Spec: two-value `x, ok := <-ch` gives `ok=false` when closed and drained,
returning the zero value without blocking.  Ours: `run_recv`; `recv_ok` →
comma-ok; `recv_ok_closed_empty` (closed+empty ⇒ `(zero,false)`) is a **theorem**.
✓  (blocking recv on empty open channel idealised away — a deadlock.)

### [Select statements](https://go.dev/ref/spec#Select_statements) — ✗ not modeled
Non-deterministic choice; needs control flow + the channel-state model in place
first.  ✗ fails loud.

### [Close](https://go.dev/ref/spec#Close) — ✓ panics; ⚠ nil
Spec: "Sending to or closing a **closed** channel causes a run-time panic.
Closing the **nil** channel also causes a run-time panic."  Ours:
`double_close_panics` is a **theorem**; close(nil) panic **✗** (nil channels, #16).

## The memory model

### [Go memory model](https://go.dev/ref/mem) — ✓ partial order + race freedom (axiom-free)
Spec: happens-before is a strict partial order; a send is synchronized before the
corresponding receive **completes**; the kth receive on a cap-C channel is
synchronized before the (k+C)th send completes (C=0 = unbuffered rendezvous); a
data race is two conflicting accesses unordered by happens-before.
Ours (`Print Assumptions` = *Closed under the global context* — no axioms): `hb`
= transitive closure of exactly those edges; `hb_irrefl`+`hb_transitive` (strict
partial order); `hb_send_before_recv`, `hb_recv_before_send`,
`unbuffered_rendezvous`, `buffered_sender_runs_ahead` (no over-ordering);
`data_race`/`RaceFree`; `mp_no_race` + `mp_program_race_free`.  ✓  Open: tie
events to the `run_io` world ops, `go_spawn`'s fork edge, deadlock freedom
(liveness, needs a non-terminating model).
