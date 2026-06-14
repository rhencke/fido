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
Ours: `uint8`/`int8`/`uint16`/`int16`/`uint32`/`int32` are each their OWN Rocq type
(a record over the `int` carrier, wrapper erased in extraction) — fully modeled
(mask + two's-complement sign-extend) across add/sub, comparison, bitwise, shift,
div/mod, conversions.  Two's-complement: ✓ (`i8_add_wraps`, `i16_add_wraps`,
`spec_i32_add_wrap`).  **DISTINCTNESS airtight, BY CONSTRUCTION**: Rocq rejects
mixing types, build-checked by `u8_no_implicit`…`u32_no_implicit` and the
cross-width `u8_u16_no_mix` — exactly the spec's "no implicit conversion; the only
implicit path is an untyped constant" (`u8_lit : int -> GoU8`).  ✓  *Remaining:*
`int`=Sint63 (⚠ faithful to int64 only within ±2⁶², Tier 2 #4) is not yet wrapped
as a distinct record; **`u32_mul`/`i32_mul` ✗ fails loud** (32-bit product exceeds
the carrier — needs Z-model); 64-bit (`uint64`/`uint`/`int`) **✗ fails loud**
(Z-model); `float32` **✗** (no native Rocq f32).  Note: distinctness makes explicit
CONVERSIONS (below) load-bearing — without them you can't use a `uint8` where an
`int` is wanted (which is correct: it fails loud, not silently).

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
*Why `[]byte(s)`/`string(b)` is deferred — a representation tension, not difficulty:*
Go's `[]byte` is `[]uint8`, but our arithmetic-faithful `uint8` erases `GoU8 → int64`
(int64 + mask), so a byte slice would emit as `[]int64`, incompatible with Go's
`[]byte`.  Faithful byte conversions need either an element-wise convert or a
`uint8`-as-native-`uint8` storage representation — a deliberate representation
decision, tracked.  (The rune view additionally needs a UTF-8 decoder — pure, but
sequenced after that decision.)

### [Array types](https://go.dev/ref/spec#Array_types) — ✗ deferred (two principled blockers)
Spec: `[N]T` — fixed length `N` (part of the **type**), **value** semantics (assign/
pass copies the whole array), comparable element-wise (unlike slices).
Deferred — NOT for difficulty, for two real blockers: **(1) substrate** — `N` lives
in the *type*, but the extraction IR (MiniML) erases dependent type indices, so we
cannot faithfully emit `[N]T` in *type positions* (function params, struct fields);
a substrate limit like the 63-bit int carrier.  (Local arrays, where Go infers
`[N]T` from the literal, would dodge this.)  **(2) semantics** — the defining
array-vs-slice distinction is value-copy vs reference-share, which is *unobservable*
until the aliasing/mutation model exists (the same model slices await, Tier 3 #8a);
so an array today would be a slice with different syntax, not a faithful array.
Revisit once aliasing is modeled — then arrays get value semantics + comparability
(`==`, which slices lack) as the genuine distinction.

### [Slice types](https://go.dev/ref/spec#Slice_types) / [Map types](https://go.dev/ref/spec#Map_types) / [Channel types](https://go.dev/ref/spec#Channel_types) — ✓ single-goroutine
Slices = `list` (`len`/`cap`/`append`/`slice_at_ok`); maps via a heap in the world
(get-after-write are *theorems*); channels via state in the world (below).  ✓ for
single-goroutine/non-aliasing use; sub-slice aliasing / in-place append unmodeled
(Tier 3 #8a).

## Expressions — operators

### [Arithmetic operators](https://go.dev/ref/spec#Arithmetic_operators)
`+ - * / %` integers: see Integer operators / overflow.  Unary `-x = 0-x` ✓
(`neg_demo`), `+x = 0+x` ✓.
**Division `/ %` — ✓ fixed-width.**  `uN_div`/`mod`, `iN_div`/`mod`: evidence-carrying
non-zero divisor (`div_nz` pattern; `u8_div_zero` `Fail`).  Machine-checked
(`spec_u8_div`…`spec_i8_div_ovf`): `200/7=28`, `200%7=4`, signed truncates toward
zero (`-7/2=-3`), and the most-negative/`-1` overflow wraps (`int8(-128)/int8(-1)=
-128`).  `uintN` via the non-negative carrier (Go int64 `/`=unsigned); `intN` via
`divs`/`mods`+`norm`.  `divmod_demo` prints `28 4 -128`.
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
**Integer conversions among `{int, uint8, int8, uint16, int16, uint32, int32}` — ✓.**  Routed
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

### [Select statements](https://go.dev/ref/spec#Select_statements) — ✓ lowering; ⚠ choice/blocking idealised
Spec: "if one or more of the communications can proceed, a single one ... is chosen
via a uniform pseudo-random selection"; `default` runs if none ready; else BLOCKS.
Ours: `select_recv2` (two recv cases) and `select_recv_default` (recv + `default`,
the non-blocking form) lower to a faithful, idiomatic Go `select { case x := <-ch:
… }` — CPS like `recv_ok`.  `select_demo` (ch1 buffered/ready, ch2 empty → picks
ch1, prints 42) and `select_default_demo` (empty ch → default, prints 99) golden-
locked.  **⚠ the LOWERING is faithful Go; the denotational CHOICE semantics** (which
ready case runs, pseudo-random fairness, blocking when none ready) **is idealised
away** — exactly like `recv`'s blocking / divergence (Tier 5 #14: needs the
scheduler / non-terminating model).  So `select` is grounded at the lowering level;
its choice semantics is the tracked incremental frontier.  *Also pending:* send
cases, N-ary (>2) cases — the same lowering, more arms.

### [Close](https://go.dev/ref/spec#Close) — ✓ panics; ⚠ nil
Spec: "Sending to or closing a **closed** channel causes a run-time panic.
Closing the **nil** channel also causes a run-time panic."  Ours:
`double_close_panics` is a **theorem**; close(nil) panic **✗** (nil channels, #16).

## Built-in functions

### [Built-in functions](https://go.dev/ref/spec#Built-in_functions) — ✓ import-free set; ✗ pointer/aliasing/complex-gated
Done: `len`, `cap`, `append`, `make` (chan/map ✓; **slice `make([]T,n)`** ✓ — fresh
zeroed slice, `len`=`n` a theorem), `delete`, `panic`, `print`/`println`, `recover`
(via `catch`/`with_defer`), `close`, and — Go 1.21 — **`min`/`max`** (on `int`,
machine-checked `spec_go_min`/`spec_go_max`) and **`clear`** (maps; empties the
map, get-after-clear is a theorem `map_get_clear`).  `builtins_demo` prints
`3 5 / 3 / 0`.
**Deferred — gated on a non-import prerequisite (not difficulty):** `new` (returns
`*T` — needs the pointer type), `copy` (mutates `dst`'s backing array — needs the
slice-aliasing/mutation model, Tier 3 #8a), `make([]T,len,cap)` and slice-`clear`
(same aliasing model), `complex`/`real`/`imag` (need the `complex64`/`complex128`
types, unmodeled).  `min`/`max` on floats (NaN/`-0` corner cases) and strings follow
once those orderings are settled.

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
`data_race`/`RaceFree`; `mp_no_race` + `mp_program_race_free`.  **All 4 channel rules
✓** + the **goroutine fork edge ✓** — every one a theorem, axiom-free (`Print
Assumptions` = *Closed under the global context*):
- rules 1/3/4 (send⤳recv-completion, kth-recv⤳(k+cap)th-send, unbuffered = cap 0):
  the open model `hb cap`.
- **rule 2** (Phase 4a) — *"closing a channel is synchronized before a receive that
  returns zero because the channel is closed"*: the finite-stream model `hbc cap
  nsent` (sender sends `nsent` then closes; `hbc_close_before_zero_recv`: close ⤳
  `CRecvDone n` for `n ≥ nsent` ONLY).  Faithful: it does NOT order close before the
  value-receives (`close_not_before_value_recv`), proven via the conserved credit
  `ev_credit_c`, so no over-ordering; irreflexive via `ev_ts_c`.
- **fork edge** (Phase 4b) — *"a go statement is synchronized before the goroutine's
  execution starts"*: `fork_hb` + `fork_program_race_free` (parent writes `x`, spawns
  a child that reads `x` with NO channel — race-free purely by the fork edge).
**Trace model ([concurrency.v]) — happens-before for ARBITRARY executions, ✓.**  The
above lives on hand-built event sets; `concurrency.v` ties it to an actual EXECUTION
TRACE — a list of events from interleaving goroutines, synchronisation recorded by
BACK-POINTERS (a receive carries its matched send's position; a goroutine's first
step carries its spawn position — what a real run records).  Central theorem
`hbt_irrefl` (axiom-free): for ANY well-formed trace, happens-before (program order ∪
synchronisation) is a STRICT PARTIAL ORDER — because the TRACE POSITION is a LINEAR
EXTENSION (`hbt_forward`: you cannot synchronise with the future).  This generalises
the bespoke `ev_ts` to arbitrary executions and ANY goroutine/channel topology (no
longer one-sender/one-receiver).  Race freedom: generic `trace_ordered_no_race` +
concrete `mp_trace_race_free` (the message-passing program as a real trace).
**Operational semantics ([concurrency.v]) — well-formed traces are GENERATED, ✓.**  A
concurrent small-step semantics (a fixed pool of goroutines over FIFO channels;
every step APPENDS an event, a send records its trace position in the channel
buffer, a receive pulls the front as its back-pointer) with the invariant `BufOk`
(buffered positions are earlier sends), preserved by every step (`step_preserves_inv`).
So `reachable_wf`: EVERY reachable execution trace is well-formed — `WfTrace` is now a
THEOREM about execution, not a hypothesis.  Composed with `hbt_irrefl`:
`reachable_hb_strict` — the happens-before of ANY real execution (any program, any
reachable state) is a strict partial order, EARNED by execution.  All axiom-free.
**Still open:** tie this operational calculus (`PAct`/`step`) to the actual
`run_io`/`World` IO model (show extracted IO programs realise it); the FIFO
refinement (kth recv ↔ kth send pairing); deadlock freedom (liveness, needs a
non-terminating/scheduler model).  Other sync mechanisms (Mutex, atomic, once) need
stdlib (imports — out of scope).
