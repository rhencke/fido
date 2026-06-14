# Go spec conformance ledger

Tracks our model against the **Go language spec** (go.dev/ref/spec) and the **Go
memory model** (go.dev/ref/mem), one section at a time.  Each entry: the spec
rule (the SOURCE of our behavior), our model, status, and the machine-checked
witness.  Status legend:

- **✓ conforms** — verified, ideally a machine-checked witness (an `Example`/
  `Theorem` whose proof IS the conformance check).
- **⚠ bounded deviation** — conforms within a principled, documented limit (e.g.
  the 63-bit carrier); the deviation is known and tracked, never silent.
- **✗ not modeled (fails loud)** — unmodeled; any use aborts extraction
  (`unsupported`) or fails `go build`, never silently wrong (the fail-loud
  policy).  Honest gap, not a conformance violation.

This is the discipline: a primitive is "done" only when its spec section is
honored here.  When code implements a rule, it cites the section in a comment.

---

## Operators

### [Integer operators](https://go.dev/ref/spec#Integer_operators) — ✓ conforms
Spec: `q = x/y`, `r = x%y` satisfy `x = q*y + r`, `|r| < |y|`, **truncated toward
zero**; the example table (`5/3=1,5%3=2`; `-5/3=-1,-5%3=-2`; `5/-3=-1,5%-3=2`;
`-5/-3=1,-5%-3=-2`).  The ONE exception: most-negative `x / -1 = x`, `x % -1 = 0`
(two's-complement overflow, no panic).  Divisor zero ⇒ run-time panic; a constant
zero divisor ⇒ compile error.
Ours: `div_nz`/`mod_nz` = `PrimInt63.divs`/`mods` (signed, truncate toward zero);
the divisor-nonzero proof is **demanded** (safe-by-construction), so the panic
case is unreachable and a literal zero divisor is a compile-time obligation.
Witnesses (main.v): `spec_div_5_3 … spec_mod_n5_n3` (the full table), and
`spec_div_minint_neg1`/`spec_mod_minint_neg1` (the `x/-1` exception, with our
most-negative = `Sint63.min_int` = -2^62).

### [Integer overflow](https://go.dev/ref/spec#Integer_overflow) — ✓ unsigned; ⚠ signed boundary
Spec: unsigned `+ - * <<` are **mod 2ⁿ** (wrap, discard high bits).  Signed
`+ - * / <<` overflow is **deterministic two's-complement**, no panic.
Ours (unsigned): `uintN` masks to width = mod 2ⁿ — `u8_add_wraps` (300→44),
`u8_mul_wraps` (65025→1), `u8_sub_wraps` (0-1→255), `u16_mul_wraps`.  ✓
Ours (signed): `int` = Sint63 wraps two's-complement, `intN` mask + sign-extend —
`i8_add_wraps` (-106), `i16_add_wraps` (-25536), `add_wraps_at_boundary`.  ✓ —
but `int` is faithful only to **±2⁶²** (63-bit carrier), so the wrap *point*
differs from int64's 2⁶³.  ⚠ bounded, tracked (CLAUDE.md Tier 2 #4).  64-bit
unsigned/signed multiply and full width need the Z-model: **✗ fails loud**.

### [Arithmetic operators](https://go.dev/ref/spec#Arithmetic_operators)
- `+ - * / %` integer: see above.  ✓ / ⚠.
- Unary `-x = 0 - x`: ✓ via `sub 0 x` (`neg_demo`).  Unary `+x = 0 + x`: trivial.
- Unary `^x` (bitwise complement; `m = -1` signed, all-ones unsigned): **✗ not
  modeled** (bit ops fail loud — same width discipline as shifts).
- Shift `<< >>`: **✗ not modeled (fails loud)**.  *Spec note to honor when we do:*
  `>>` truncates toward **negative infinity** (`x>>1 = floor(x/2)`), UNLIKE `/`
  which truncates toward zero — so for negative `x`, `x>>1 ≠ x/2`
  (`-11/4 = -2` but `-11>>2 = -3`).  Shift count must be non-negative (negative ⇒
  run-time panic); arithmetic shift for signed, logical for unsigned; no upper
  limit on the count.

### [Floating-point operators](https://go.dev/ref/spec#Floating-point_operators) — ✓ ops; ⚠ FMA fusion
Spec: `+x = x`, `-x` = negation.  Division by zero "not specified beyond IEEE
754; whether a run-time panic occurs is implementation-specific".  **An
implementation MAY fuse** multiple float ops (e.g. FMA `x*y+z` without rounding
the intermediate), producing a result that differs from rounding each step; an
explicit float conversion rounds to the target precision and prevents fusion.
Ours: `float64` = Rocq `PrimFloat` (IEEE 754 binary64); `+ - * /`, `<`/`<=`/`==`,
unary `opp` lower to Go's native ops.  Float `/` keeps no guard (IEEE: ±inf/NaN,
no panic) — conforms.  `float_demo`, `float_cmp_demo`, `float_opp_demo`.
⚠ **deviation: our model rounds EACH op (no fusion)**; Go MAY emit an FMA, giving
a more precise result for `a*b+c`.  So a fused expression can differ from our
per-op-rounded value.  Tracked (a faithful model must either forbid the fusable
shapes or model the `mul`+`add` fusion as a single rounding).  `float32`: **✗ no
native Rocq f32** (genuinely blocked).

### [Comparison operators](https://go.dev/ref/spec#Comparison_operators) — ✓ conforms
Spec: integers "compared in the usual way"; floats "as defined by IEEE 754";
booleans equal iff both true or both false; `== != < <= > >=`.
Ours (integer): `int` uses the SIGNED primitives `ltsb`/`lesb` → Go signed
`</<=`; `uintN` values are in-range so signed = unsigned.  The UNSIGNED
`PrimInt63.ltb`/`leb` are **rejected for `int`** (they disagree with Go's signed
`<` on high-bit values) — `ltb_unsigned_neg_false`/`ltb_signed_neg_true` witness
exactly why.  ✓
Ours (float): `PrimFloat.ltb`/`leb`/`eqb` → Go `< <= ==`, IEEE incl. NaN
unordered — `nan_eqb_false`, `nan_ltb_false`.  ✓
Open: `> >= !=` have no *direct* operator (encode by swap / `negb (eqb…)`) — a
tidiness gap, not a conformance one.

### [Logical operators](https://go.dev/ref/spec#Logical_operators) — ✓ conforms
Spec: `p && q` is "if p then q else false"; `p || q` is "if p then true else q";
`!p` is "not p".  Left operand evaluated, then the right "if the condition
requires it" (short-circuit).
Ours: `andb`/`orb`/`negb` → Go `&&`/`||`/`!`.  Coq's `andb p q = if p then q else
false` is the spec phrasing verbatim.  Short-circuit is **unobservable** here —
operands are pure, total `bool` values (no effects, no divergence) — so it is
faithful by construction (`bool_op_demo`, `cond_op_demo`).  ✓

---

## Channels & concurrency

### [Send statements](https://go.dev/ref/spec#Send_statements) — ✓ open/closed; ⚠ nil/blocking
Spec: send on a **closed** channel ⇒ run-time panic; send on a **nil** channel
blocks forever; otherwise send transfers a value (blocking per buffer/peer).
Ours: `run_send` (open ⇒ enqueue) / `run_send_closed` (closed ⇒ `OPanic`), so
`send_closed_panics` is a **theorem**.  ✓  nil-channel send (blocks forever) is
idealised away with divergence: **✗ not modeled**.

### [Receive operator](https://go.dev/ref/spec#Receive_operator) — ✓ conforms
Spec: `<-ch` receives; the two-value form `x, ok := <-ch` gives `ok = false`
when the channel is closed and drained, returning the zero value without
blocking.
Ours: `run_recv` (non-empty buffer ⇒ head + dequeue); `recv_ok` lowers to Go's
comma-ok; `recv_ok_closed_empty` (closed+empty ⇒ `(zero_val, false)`) is a
**theorem** — exactly the spec's "return the zero value, not blocking".  ✓
(Blocking recv on an empty open channel is idealised away — a deadlock, like
divergence.)

### [Close](https://go.dev/ref/spec#Close) — ✓ panics; ⚠ nil
Spec: "Sending to or closing a closed channel causes a run-time panic.  Closing
the nil channel also causes a run-time panic.  After calling close, … receive
operations will return the zero value … without blocking."
Ours: `double_close_panics` (close-of-closed ⇒ panic) is a **theorem**;
receive-from-closed-drained is `recv_ok_closed_empty`.  ✓  `close(nil)` panic:
**✗ not modeled** (nil channels, with #16).

### [The Go memory model](https://go.dev/ref/mem) — ✓ partial order + race freedom
go.dev/ref/mem: happens-before is a strict partial order; channel rules — a send
is synchronized before the corresponding receive **completes**; the kth receive
on a capacity-C channel is synchronized before the (k+C)th send completes (C=0 is
the unbuffered rendezvous); a data race is two conflicting accesses unordered by
happens-before.
Ours (all **axiom-free**, `Print Assumptions` = *Closed under the global
context*): `hb` is the transitive closure of exactly those edges; `hb_irrefl` +
`hb_transitive` (strict partial order), `hb_send_before_recv`,
`hb_recv_before_send`, `unbuffered_rendezvous`, `buffered_sender_runs_ahead` (no
over-ordering).  `data_race`/`RaceFree` defined; `mp_no_race` +
`mp_program_race_free` (channel synchronization ⇒ race freedom).  ✓
Open: tie events to the `run_io` world ops, `go_spawn`'s fork edge, deadlock
freedom (liveness, needs a non-terminating model).

---

## Sections deliberately not yet modeled (all **✗ fail loud**, honest gaps)

[Conversions](https://go.dev/ref/spec#Conversions) (numeric, string↔[]byte/[]rune),
[Select statements](https://go.dev/ref/spec#Select_statements),
[Constant expressions](https://go.dev/ref/spec#Constant_expressions) (untyped
arbitrary-precision constants — CLAUDE.md Known gaps #5),
[String types](https://go.dev/ref/spec#String_types) (byte vs rune indexing),
structs / methods / interfaces, pointers, `goto`-spectrum control flow beyond
what the relooper covers.  None silently wrong — each fails at extraction or
`go build`.
