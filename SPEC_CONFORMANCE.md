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

### [Constants](https://go.dev/ref/spec#Constants) / [Constant expressions](https://go.dev/ref/spec#Constant_expressions) — ⚠ deviation (Known gaps #5)
Spec: "Numeric constants represent **exact values of arbitrary precision and do
not overflow**."  A constant acquires a type only at use, where "it is an error
if the constant value cannot be represented as a value of the respective type"
(a compile-time representability check); integer constants are ≥256-bit, constant
overflow is a *compile error*, and constant float arithmetic rounds once at the
typed boundary (`const 0.1+0.2` = `0.3`, not the runtime `0.30000000000000004`).
Ours: literals are modeled as already-typed fixed-width values (`int` = Sint63,
`float64` = IEEE double), conflating the untyped and typed layers.  **⚠ deviation,
tracked**: large/narrow/constant-arith cases are wrong-or-unrepresentable; no
impact yet (no demo exercises constant arithmetic).  Faithful model: untyped int
constants as `Z`, untyped floats as exact rationals, with a representability
proof at use (Go's compile-time check → safe-by-construction).

## Types

### [Boolean types](https://go.dev/ref/spec#Boolean_types) — ✓
Spec: `bool`; comparable; values `true`/`false`.  Ours: Coq `bool` → Go `bool`.
(Comparison: see Comparison operators.)  ✓

### [Numeric types](https://go.dev/ref/spec#Numeric_types) — ✓ ranges/two's-complement; ⚠ defined-type distinctness
Spec: `uint8…uint64`, `int8…int64` with exact ranges; "**the value of an n-bit
integer is n bits wide and represented using two's complement arithmetic**";
`byte`=`uint8`, `rune`=`int32`; `int`/`uint` are 32-or-64-bit.  And: "**all
numeric types are defined types and thus distinct… Explicit conversions are
required when different numeric types are mixed**."
Ours: `int`=Sint63 (⚠ faithful to int64 only within ±2⁶², Tier 2 #4); `uint8`/
`int8`/`uint16`/`int16` fully modeled (mask + two's-complement sign-extend),
`uint32`/`int32` add/sub/cmp (mul **✗ fails loud** — exceeds carrier), 64-bit
**✗ fails loud** (needs Z-model); `float64`=`PrimFloat`, `float32` **✗** (no
native Rocq f32).  Two's-complement: ✓ (`i8_add_wraps`, `i16_add_wraps`).
**⚠ deviation:** our fixed-width values share the `int` carrier, so the model
does NOT enforce that `uint8` and `int` are *distinct types requiring explicit
conversion* — the type-distinctness layer is deferred (CLAUDE.md Tier 4 #10).

### [String types](https://go.dev/ref/spec#String_types) — ⚠ deviation (Known gaps #7)
Spec: a string is bytes; `s[i]` is a **byte**, `len(s)` is the **byte** count;
`range s` yields runes.  Ours: `GoString` = `list GoRune` — the *rune* view only;
byte-level index/len would be wrong, and string ops are largely unmodeled.
**⚠/✗** tracked.

### [Slice types](https://go.dev/ref/spec#Slice_types) / [Map types](https://go.dev/ref/spec#Map_types) / [Channel types](https://go.dev/ref/spec#Channel_types) — ✓ single-goroutine
Slices = `list` (`len`/`cap`/`append`/`slice_at_ok`); maps via a heap in the world
(get-after-write are *theorems*); channels via state in the world (below).  ✓ for
single-goroutine/non-aliasing use; sub-slice aliasing / in-place append unmodeled
(Tier 3 #8a).

## Expressions — operators

### [Arithmetic operators](https://go.dev/ref/spec#Arithmetic_operators)
`+ - * / %` integers: see Integer operators / overflow.  Unary `-x = 0-x` ✓
(`neg_demo`), `+x = 0+x` ✓.  Unary `^x` (complement; `m=-1` signed): **✗ fails
loud**.  Shift `<< >>`: **✗ fails loud** — *honor when modeled:* `>>` truncates
toward **−∞** (`x>>1 = floor(x/2)`), UNLIKE `/` (toward zero), so `-11/4=-2` but
`-11>>2=-3`; count must be ≥0 (else panic); arithmetic shift signed / logical
unsigned; no upper limit on count.

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

### [Conversions](https://go.dev/ref/spec#Conversions) — ✗ not modeled (fails loud)
int↔float, numeric narrowing, `string`↔`[]byte`/`[]rune`, interface conversions
beyond `type_assert`.  None modeled; each fails loud.

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
