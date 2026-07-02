# Go spec conformance ledger

Tracks our model against the **Go language spec** (go.dev/ref/spec) and the **Go
memory model** (go.dev/ref/mem), **in spec document order** — top to bottom, one
section at a time.  Our Rocq is meant to follow this order too, so each spec
section maps to a region of the model.  Each entry: the spec rule (the SOURCE of
our behavior, cited), our model, status, and the machine-checked witness.

**The entire model is AXIOM-FREE.**  The authority is Rocq's own `Print Assumptions`,
gated non-bypassably in the Docker prover stage (the manifest / printer / emit flows —
see PROGRESS.md "Current gates" — assert their surfaces' `Axioms:` reports empty); a source grep
`grep -cE '^Axiom |^Parameter ' *.v` = 0 is only a coarse commit-time tripwire (legal
declaration forms — `Local`/`Polymorphic Axiom`, attribute stacks — bypass it).  So every
✓ below rests on a `Definition`/`Theorem` over a CONCRETE model (the `World` is a
concrete record of typed heaps), and `Print Assumptions` of any result reports *Closed
under the global context* — the trust base is EMPTY (the old `PrimInt63`/`PrimFloat`
kernel substrate was eliminated: integers `Z`, locations `nat`, floats `spec_float`).
The IO monad/effect ALGEBRA (the monad laws, and every
read-after-write / commutation lemma) is now **funext-free**: stated over OBSERVATIONAL
equality `io_eq m m' := forall w, run_io m w = run_io m' w` and proved pointwise (review
#6 P2 #20) — `Print Assumptions bind_assoc` reports no `functional_extensionality`.  The
stdlib `functional_extensionality` survives at exactly ONE site, `run_io_inj` (`io_eq → =`),
used only by the concurrency `Denotes` Keystone bridge (`ptr_set_is_ref`), which must rewrite
the IO term STRUCTURALLY and so cannot use `io_eq`; removing it there needs an observational
`Denotes`, part of the concurrency unification.  Conformance witnesses that used to rest on a
`run_io`/channel/map *axiom interface* now rest on the proven laws of that concrete model.

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

## Reconciliation (2026-06-19) — markers below that are now SUPERSEDED

Several per-section ✗/⚠ markers predate later work and OVERSTATE the gaps (verified against
the committed code).  The status now:

- **`float32` — ✓ DONE & SOUND** (not "✗ no native Rocq f32").  Faithful binary32 via `SpecFloat`
  (prec 24, emax 128): arithmetic, comparisons, and ALL conversions (`float32↔float64`,
  `float32↔int64`, narrow↔`int64`) lower to native Go `float32`.  Supersedes the `float32 ✗`
  notes in *Numeric types*, *Floating-point operators*, *Conversions*.
  **Soundness fix (2026-06-20, code review):** `GoFloat32` was a *transparent alias* `:= float`,
  so a non-binary32-representable literal could be injected raw (`16777217%float : GoFloat32`) and
  widened with no rounding — making Rocq disagree with Go (`f64_of_f32 16777217 = 16777217` vs
  Go's `float32(16777217) = 16777216`) and licensing UNSOUND proofs.  Now `GoFloat32` is an
  ABSTRACT record carrying an unforgeable provenance proof (`exists a, carrier = f32_round a`);
  the only way in is a rounding smart constructor (`f32_of_f64`/`f32_lit`/arith), so widening is
  sound by construction and the raw injection no longer typechecks.  Zero new axioms (provenance
  proofs are `eq_refl`; `Print Assumptions` = Rocq float/int primitives only).  Machine-checked
  regression `f32_widen_sound`: `widen64 (f32_lit 16777217) = 16777216`, matching Go.  Extraction
  unchanged (erases to native `float32`; golden-stable).
- **Conversions — ✓ float included.**  `float64↔int64`, `float64↔uint64` (round-to-odd),
  `float32↔float64`, the full width-typed integer matrix (narrow↔`int64`↔`uint64`) all lower
  to native casts.  Supersedes "✗ float" + the "lowering deferred (proof-only)" notes.
- **Interface types — ✓ single-method + nullary DONE** via the `gr_self`/`sg_self` second
  field (a 2-field record = Go's (vtable, value) pair).  Supersedes "✗ 1-method interface".
- **Constant expressions — ✓ INTEGER + FLOAT done.**  Integer (signed + unsigned): the plugin's
  `z_eval`/`zu_eval` fold `Z.add/sub/mul/opp/shiftl/land/lor/lxor` with overflow = fail-loud.
  Float (2026-06-20): `FConst` is the exact rational `num/den`, `fc_add/sub/mul/div` are exact
  (cross-multiply), and `f64_of_fconst`/`f32_of_fconst` round ONCE to binary64/binary32 via `SFdiv`
  of the exact-integer spec_floats — correctly-rounded for ALL num/den (no `2^53` restriction; the
  earlier `f64_of_i64`-based form double-rounded for large endpoints).
- **Generics — ✓ `comparable` constraint** added (witness-erasure → `[K comparable]`, `==`).

Genuinely still open (per honest survey): FMA fusion
(bounded deviation); array-TYPED positions (DONE for any fixed size — a `GoArr<N>` type renders as Go `[N]T` in a
function param / typed var / field; the plugin parses `N` from the type NAME generically, so a new
size needs only a Coq `GoArr<N>` type + `arr<N>_lit` constructor, no plugin edit; `GoArr3`→`[3]T`,
`GoArr2`→`[2]T` exercised, `arrN_demo`.  Constructor takes exactly `N` elements ⇒ length-correct by
construction.  Open only: a SINGLE generic `[N]T` abstract over `N` — Go itself forbids that, so
n/a); struct tags / embedding non-struct types; the
`interface` keyword surface (we emit dict-structs — a deviation, not a gap); native `switch`
emission (cosmetic); and the concurrency GUARANTEE over real programs (research, largely proven —
`denote_sim_*` simulation lemmas connect the calculus to real IO reductions).

---

## Lexical elements

### [Integer literals](https://go.dev/ref/spec#Integer_literals) / [Floating-point literals](https://go.dev/ref/spec#Floating-point_literals) — ⚠ (typed/fixed-width view)
Spec: literals are *untyped constants* (see Constants).  Ours: written as Rocq
`PrimInt63` / `PrimFloat` values — i.e. the already-*typed*, fixed-width runtime
view.  The lexical shapes (decimal, sign) round-trip (`neglit_demo`:
`-7 / -1 / -2147483648`), but the untyped/arbitrary-precision layer is not
modeled here — see **Constants** below.

## Constants

### [Constants](https://go.dev/ref/spec#Constants) / [Constant expressions](https://go.dev/ref/spec#Constant_expressions) — ✓ representability + arbitrary-precision INTEGER; ⚠ float
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
**RAW CONSTRUCTOR now SEALED (2026-06-20, code review) — GoU8 done, others tracked.**
A prior hole: the wrapper constructor `MkU8` was public and unconstrained, so
`MkU8 300` forged an impossible uint8 (the type erased to int64, the constructor to
identity → printed `300`).  Same class as the float32 injection hole.  Fix: `GoU8`
now carries an **SProp range invariant** — `MkU8 { u8raw ; u8ok : Squash (u8raw <? 256
= true) }` — so `MkU8 300 _` is UNCONSTRUCTABLE (the proof `300 < 256` is false;
`u8_forged` is a `Fail` test).  Every op routes through `u8wrap` (mask + the proof
from one lemma `land255_lt256`).  SProp gives definitional proof irrelevance (no
axiom — `Print Assumptions` = Rocq primitives only), so two `GoU8` with equal
carriers are defeq; value witnesses use `reflexivity` (the VM doesn't decide SProp
irrelevance, the kernel does).  Extraction unchanged (the SProp field erases; Go is
byte-identical, golden-stable).  **`GoU16` + `GoU32` sealed the same way (2026-06-20)** — SProp `Squash (uNraw <? 2^N = true)`,
`uNwrap` + a `land`-bound lemma, `uN_forged` `Fail` test.  The unsigned-mask trio (U8/U16/U32) is
done.  **`GoI8` sealed (2026-06-20) with a PROVENANCE invariant** — the sign-extend bound is
two-sided and fiddly to prove, so (as for GoFloat32) `GoI8` carries `Squash (exists a, i8raw =
i8_norm a)` ("the carrier is a normalized 8-bit signed value").  `i8wrap x := MkI8 (i8_norm x)
(squash (ex_intro _ x eq_refl))` — the proof is `eq_refl`, NO bound lemma; `MkI8 200 _` is
unconstructable (200 ∉ image of `i8_norm`; `i8_forged` `Fail` test).  **`GoI16` sealed the same way
(2026-06-20)** — `Squash (exists a, i16raw = i16_norm a)`, `i16wrap`, `i16_forged` `Fail` test.
**`GoI32` sealed the same way (2026-06-20)** — `Squash (exists a, i32raw = i32_norm a)`, `i32wrap`,
`i32_forged` `Fail` test; `i32wrap` reaches the real extracted rune/UTF-8 codec, so it also erases at
the call site (→ its argument, like the bare `MkI32`).  **`GoU64` sealed (2026-06-20)** — Z-carried, so a RANGE invariant `Squash (in_u64 u64raw = true)`
(`in_u64 z = 0 ≤ z < 2^64`); `u64wrap z := MkU64 (z mod 2^64) (squash (in_u64_wrapU64 z))` with one
lemma via `Z.mod_pos_bound`; `u64_forged` `Fail` test.  **`GoI64` sealed (2026-06-20)** — Z-carried signed, range invariant `Squash (in_i64 i64raw = true)`
(`in_i64 z = -2^63 ≤ z < 2^63`); `i64wrap z := MkI64 (wrap64 z) (squash (in_i64_wrap64 z))` with one
two-sided bound lemma via `Z.mod_pos_bound`; `i64_forged` `Fail` test.  **ALL 8 WRAPPERS SEALED** —
the public-raw-constructor forging hole (e.g. `MkU8 300`, `MkI64 (2^63)`) is fully CLOSED.  Three
invariant shapes across the family: range-bound (`uN` masks), provenance "in the image of norm"
(`iN` sign-extend), and Z-range (`u64`/`i64`).  Axiom-free (SProp proof irrelevance — `Print
Assumptions` = Rocq primitives), extraction byte-identical (the SProp fields + `*wrap` constructors
erase; golden-stable), value witnesses use `reflexivity` (the VM can't decide SProp irrelevance).
**Arbitrary-precision INTEGER constants — DONE (A5).**  `i64c`/`u64c` model an
untyped int constant as `Z`: a closed `Z` constant expression is `vm_compute`-
evaluated at ELABORATION (real bignums, exact, no width — an INTERMEDIATE may
exceed the target, e.g. `1<<70`), then converted via `i64_lit`/`u64_lit` demanding
`in_i64`/`in_u64`.  An out-of-range constant FAILS to elaborate — exactly "constant
overflows", NOT a wrap.  ✓ witnesses `const_intermediate_exceeds` (`(1<<70)>>8 =
2^62`), `const_exact_arith`, `const_u64_upper` (`2^63` fits uint64 not int64),
`const_oob_i64`/`const_oob_u64` (`Fail`); the `Z` precision lives in `vm_compute`,
no plugin change.  *Remaining:* the fixed-width narrow `_lit` take an `int` (not
`Z`) argument, so a narrow constant's arbitrary-precision arithmetic still routes
through the bounded carrier (low priority); and **float constants** need exact
rationals (`Q`) rounding once at the typed boundary (Phase D).  ⚠ float tracked.

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
implicit path is an untyped constant" (`u8_lit : int -> GoU8`).  ✓  Distinctness now extends
to the RUNTIME type identity (break #7): every tag lowers to a DISTINCT Go type — `int` vs
`int64` included (slice 7c made `int`→Go `int`, `int64`→Go `int64`; before, both were `int64`,
a hidden distinctness violation) — machine-checked by `int_vs_int64_distinct` and the general
`tag_runtime_agrees` (`tag_eq ta tb = None → go_runtime_name ta ≠ go_runtime_name tb`, the
injectivity LOCK).  ✓  *Remaining:*
**`int64` (full width) ✓ — `GoI64`**, a distinct record carried by `Z` (not the
63-bit `int`), faithful across the WHOLE int64 range and wrapping at the true 2⁶³:
`spec_i64_add_wrap` (2⁶³−1+1→−2⁶³), `spec_i64_sub_wrap`, `spec_i64_mul_wrap`,
`spec_i64_beyond62` (an exact sum the old ±2⁶² model could not represent), and the
no-overflow-exact theorem `i64_add_no_overflow_exact` — all **axiom-free** (Z
inductives + `lia`).  Full op set: `add`/`sub`/`mul`, `eqb`/`ltb`/`leb`, `div`/`mod`
(truncate toward zero via `Z.quot`/`Z.rem` — NOT Coq's floor; `spec_i64_div_trunc`
`-7/2=-3`, MININT/−1 wraps), bitwise `and`/`or`/`xor`/`andnot`/`not`, shifts
`shl`/`shr` (`<<` wraps, `>>` arithmetic; `spec_i64_shr_arith` `-8>>1=-4`); div and
shift are evidence-carrying (`i64_div_zero`/`i64_shl_neg` Fail).  The wrapper erases
to a Go `int64` (wraps natively at 2⁶⁴, no mask).  ⚠ ONE bounded caveat: a CONSTANT `MAX+1` in extracted Go is an untyped-
constant expression, so Go's COMPILE-TIME overflow check fires (a compile error)
instead of the runtime wrap `i64_add` models — that is the untyped-constant gap
(Constants section / Tier 2 #6), not an int64 defect; the wrap is faithful for
runtime operands and is witness-proven.  **`GoI64`/`GoU64` are the CANONICAL int64/
uint64 (A4, 2026-06-17):** `Notation int64 := GoI64` / `uint64 := GoU64`; range-checked
`Number Notation` so `42%i64`/`42%u64` are literals whose representability is checked AT
PARSE (out-of-range → parse error = Go's untyped-constant overflow; `i64_lit_oob`/
`u64_lit_oob` Fail); scoped arithmetic `(a+b)%i64`; `comparable_TI64`/`comparable_TU64`
make them map-key types; end-to-end `i64_pipeline_demo`/`u64_pipeline_demo` flow int64
and a `≥2^63` uint64 through a typed channel AND map (golden-locked).  The concurrency.v
bridge value carrier was migrated to `GoI64` (axiom-free preserved).  The primitive
**✓ Platform `int` (`GoInt`) — DEVIATION CLOSED (review #6 #13):** Go's platform `int` is now a DISTINCT
`Z`-carried record (the exact `GoI64` shape, rendered Go `int`, the carrier for loop counters / slice indices /
`len`/`cap` / small-value demos), FAITHFUL across the whole int64 range `[−2⁶³, 2⁶³)` and wrapping at the true
`2⁶³` — **no longer the bounded 63-bit `Sint63` carrier** (faithful only in `[−2⁶², 2⁶²)`, the old Tier-2 #4 /
review-R6 deviation).  Arithmetic is `int_add`/`int_sub`/`int_mul` (wrap-`2⁶³`), `int_div`/`int_mod` (truncating
`Z.quot`/`Z.rem`, evidence-gated nonzero divisor); the `MININT/−1` overflow corner now wraps the TRUE int64
`−9223372036854775808` to itself (faithful — was the `Sint63` `−2⁶²`).  Literals are the proof-carrying
`int_lit z (pf : in_i64 z)`, NoInline'd and plugin-folded — a BARE decimal in expression/index position
(`xs[5]`, `a + 5`), `int(N)` when a Go type must be pinned; out-of-range constants are unrepresentable.
The ONLY residual platform assumption is the 64-bit *width* choice (Go's `int` is 32-or-64 by spec; we model
64), NOT a carrier deviation.  **Golden BYTE-IDENTICAL** (the emitted Go is unchanged — `func Add(n int, m int) int`,
`xs[5]`, `i := int(0)`).
**✓ Platform `uint` (`GoUint`) — DEVIATION CLOSED (review #6 #13):** the companion platform-UINT is likewise a
DISTINCT `Z`-carried record (the `GoU64` shape, rendered Go `uint`), FAITHFUL across `[0, 2⁶⁴)`, literals the
proof-carrying `uint_lit z (pf : in_u64 z)` folded to `uint(<decimal>)`.
⚠ **UNIFORMITY RESIDUAL (not a deviation — faithful, follow-up):** the sub-64 narrows (`GoU8`…`GoI32`) and the
heap-slice (`SliceH`) INDEX args still ride the int63 carrier; both are FAITHFUL there (sub-63 values / indices
never reach `2⁶²`), so this is a carrier-uniformity tail of the user's "all ints → Z", not a correctness gap.
The internal heap LOCATION handles stay `int` (they are not Go `int` *values*), so `PrimInt63` remains in the
trust base regardless — this fix is platform-int correctness + value-int uniformity, not `PrimInt63` removal.
**`u32_mul`/`i32_mul` ✓** (mask-after-multiply: the product may exceed the 63-bit
carrier but the masked LOW 32 bits are exact since 2³²∣2⁶³ —
`spec_u32_mul_wrap`/`spec_i32_mul_wrap`); **`uint64` (full width) ✓ — `GoU64`** (same Z
template, unsigned mod-2⁶⁴ wrap; `spec_u64_add_wrap`/`sub_wrap`/`not`/`shr`/`beyond63`,
axiom-free; emits Go `uint64`, unsigned literals via `%Lu`, sign-aware even for erased
literals); `float32` **✗** (no native Rocq
f32).  Note: distinctness makes explicit
CONVERSIONS (below) load-bearing — without them you can't use a `uint8` where an
`int` is wanted (which is correct: it fails loud, not silently).

### [String types](https://go.dev/ref/spec#String_types) — ✓ byte sequence + rune view + `range s`
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
- **slice** (`str_slice`, spec "Slice expressions"): the byte-substring `s[a:b]` →
  native Go `s[a:b]`, **proof-gated** (demands `a <= b <= len(s)`, so it cannot panic — the
  bounds proof discharged Go's check, like `div_nz`).  `s[7:12]` of `"Hello, world"` is
  `"world"` (theorem `spec_str_slice`); out-of-range bounds do not type-check
  (`str_slice_oob`, a `Fail`).  `nat` indices keep the body conversion-free. ✓
- **comparison** (`str_eqb`/`str_ltb`, spec "Comparison operators": strings are
  comparable AND ordered) → Go `==` / `<`.  `str_eqb` is byte-sequence equality
  (`String.eqb`); `str_ltb` is LEXICOGRAPHIC by byte value (compare byte-by-byte,
  proper prefix `<` longer, first differing byte decides — reusing the suppressed
  `ascii_byte` decoder, no `nat_of_ascii` drag).  Both **theorems**
  (`spec_str_eq_same`/`spec_str_eq_diff`/`spec_str_lt_byte`/`spec_str_lt_prefix`/
  `spec_str_lt_false`); `str_cmp_demo` → `true false true false`. ✓
- **immutability**: free (Coq `string` is a value). ✓
- **distinctness**: a `string` is its own type — `str_no_implicit` (a `Fail`) is
  the build-checked proof that an `int` does not implicitly convert in. ✓
- **literals**: the plugin decodes a Coq `String`/`Ascii`/`EmptyString` literal to
  a byte-faithful Go string literal (printable ASCII verbatim; other bytes via Go's
  `\xNN`), so the emitted literal denotes EXACTLY the modelled bytes. ✓
**Rune view DONE.** `string`↔`[]rune` (`str_to_runes`/`runes_to_str` → native
`[]rune(s)`/`string(rs)`, a suppressed 1–4 byte UTF-8 codec verified by round-trip),
`string(rune)` (`rune_to_str`), and `string`↔`[]byte` (`str_to_bytes`/`str_from_bytes`)
all lower to the native conversions; the runtime does the real UTF-8. ✓
**`range s` DONE (2026-06-19):** `str_range s (fun i r => …)` → the native two-variable
`for i, r := range s { … }` — `i` the BYTE offset of each code point, `r` the rune; byte
offsets are the prefix sums of the per-rune UTF-8 widths (machine-checked `str_range_offsets`,
`A 中 B → 0 1 4`), matching Go exactly. ✓
**Deferred (fails loud):** byte-level mutation (Go forbids `s[i] = …` anyway; strings
are immutable).

### [Array types](https://go.dev/ref/spec#Array_types) — ✓ fixed-size arrays (literal, index, comparability, value-copy) + TYPED POSITIONS (var / param / return / field via GoArr<N>); ⚠ positions polymorphic over a SYMBOLIC N
Spec: `[N]T` — fixed length `N` (part of the **type**), **value** semantics (assign/
pass copies the whole array), comparable element-wise (unlike slices).
**Piece 1 DONE (B4.1, 2026-06-18) — local fixed-size arrays.**  `N` lives in the *type*,
but the extraction IR (MiniML) erases dependent type indices, so it is unrecoverable
from the extracted type.  Way around it for LOCAL arrays: keep `N` OUT of the Coq type
(`GoArray A`, size-erased) and in the CONSTRUCTION — `arr_lit l` → `[len(l)]T{…}` (size
read off the list), so a local `a := arr_lit […]` has its Go type INFERRED from the
literal (`a := [3]int64{…}`), never an explicit `[N]T`.  `arr_get_ok` is the bounds-checked
read (identical lowering to `slice_at_ok`).  `arr_demo` → `20 true` / `0 false`.  *Finding:*
Go STATICALLY bounds-checks a CONSTANT array index (`a[5]` on `[3]int64` is a COMPILE error
— a STRONGER guarantee than a slice's runtime panic), so the runtime-OOB demo uses a
COMPUTED index.  **Comparability DONE (B4.2):** `arr_eqb` → Go field-wise `==` (arrays are
comparable, slices are NOT — only `== nil`); machine-checked `arr_eqb_t`/`arr_eqb_f`,
`arr_eq_demo` → `true false`.  **VALUE-COPY DONE (B4.2b):** `arr_set a i v` is a FUNCTIONAL
update — `a` is UNCHANGED (a slice would share the backing) — lowering to the copy-mutate-
return IIFE `func(_a [n]T) [n]T { _a[i] = v; return _a }(a)` (Go copies `a` into the value
param, mutates the copy, returns it); the size `n` is passed explicitly (size-in-construction,
since it is erased from the Coq type).  `arr_copy_demo`: `a` stays `[10,20,30]`, `b` becomes
`[99,20,30]` → `true true`; machine-checked `arr_set_copy`.  **Typed POSITIONS DONE (any CONCRETE
fixed size):** a `GoArr<N>` type renders as Go `[N]T` in EVERY position — typed VAR + PARAM (`arrN_demo`:
`vecN_a : [3]int64`, `vec3_eqb`'s `[3]int64` params; `GoArr2`→`[2]int64` too), and RETURN + FIELD
(`arr_field_ret_demo`: `func Vec3_id(a [3]int64) [3]int64`, `type Triple struct { T_vec [3]int64; T_label
int64 }` → `true 77`).  Each size needs only a Coq `GoArr<N>` + `arr<N>_lit` (no plugin edit), the
constructor's fixed arity guaranteeing length-correctness.  **⚠ still:** a position polymorphic over a
SYMBOLIC `N` — the size-erased `GoArray` stays LOCAL-only, and the type-level-`N` route (a phantom chain
the plugin decodes for arbitrary `N`) is deferred.

### [Struct types](https://go.dev/ref/spec#Struct_types) — ✓ value-struct (named fields) + EMBEDDING (struct-in-struct, interface-in-struct, POINTER-to-struct — field/method promotion); ⚠ tags (no-op without reflection); ✗ embedding bare primitives
Spec: a `struct` is a sequence of named fields with types; **value** semantics
(assign/pass copies every field).  A Rocq `Record` is exactly this — a single-
constructor inductive with projections, value/copy semantics — so it maps directly:
the type → `type T struct { … }`, the constructor → a KEYED struct literal `T{Field: v, …}`
(field-order-independent and self-documenting — Go style's preference; the field names come
from the record's projections, recursively, so nested/heterogeneous/pointer/interface-dict
literals are all keyed, e.g. `Wrap{W_inner: Inner{Iv: 5, …}, Wz: 9}`, `Pair{P_n: 10, P_b: true}`),
each projection → field access `x.Field`.  Field types are
printed by the general `pp_type`, so they are not hardcoded — `point_demo`'s `int`
fields lower to `int64`, `labeled_demo` mixes a `bool` and an `int` field
(`Flag bool` / `Qty int64`).  The projection *definitions* are suppressed (field
access replaces them).  Struct INVARIANTS are provable in Rocq directly:
`point_proj_px` machine-checks `px (MkPoint a b) = a`.  Witnesses: `point_demo`
(`Point{3,4}` → `3 / 4 / 7`), `labeled_demo` (`Labeled{true,5}` → `true / 5`).
**Embedding DONE (2026-06-19):** `type Dog struct { Animal; Breed string }` — a record field
whose exported name equals its record type's name is emitted as an ANONYMOUS embedded field, so
the Go struct genuinely embeds and Go promotes the embedded method set; access is through the
embedded field, emitted in the PROMOTED SHORTHAND `species (animal d)` → `d.Species` and promoted
method `speak (animal d)` → `d.Speak()` (a `peel_embedded` peephole, which compiles only because Go
promotes through the embedded field — genuinely exercising promotion; safe since Coq projection names
are unique, so no shadowing).  The embedded type needs ≥2 fields (1-field records unbox).  `embed_demo`
→ `canine / canine / 5` (the `5` = the embedded-selector regression fixture `embed_arith`: `legs (animal d) + k`
emits the peeled `d.Legs + k`, pinned exactly by the Makefile selector-bridge gate).  An INTERFACE (its
method-dictionary) embeds the SAME way — the dict IS a struct:
`type LoggedGreeter struct { Greeter; Lg_calls int64 }` promotes the embedded interface's method
(emitted `lg.Greet(5)`, NOT `lg.Greeter.Greet(…)`) alongside the struct's own field, a common Go
wrap-an-interface pattern (`embed_iface_in_struct_demo` → `105 / 7`; `promoted_greet` reflexivity).
**POINTER embedding DONE (2026-06-22):** Go's `type Node struct { *Cell; tag int64 }` — an [SPtr T]
field whose exported name is the BASE record's name is emitted as an ANONYMOUS `*T` field, so Go promotes
the embedded `*T`'s method set THROUGH the pointer.  The embed detection now matches `SPtr <record>` (base
name) at BOTH sites (field emission + `embedded_proj` registration); promoted access reuses the existing
`peel_embedded` peephole — `cell_incx (cell nd)` → `nd.Cell_incx()` (the pointer-receiver method promoted,
NOT `nd.Cell.Cell_incx()`).  Emitted `type Node struct { *Cell; Ntag int64 }`, `nd := Node{Cell: p, Ntag:
99}`, `nd.Cell_incx()` then `(nd.Cell).Cx` → `11 99` (`node_embed_demo`, golden-locked).  ✗ not yet:
embedding a bare PRIMITIVE (no methods to promote — niche), and struct tags.  Methods declared on the
struct → next section.
**RECURSIVE / self-referential struct DONE (2026-06-22):** Go's `type ListNode struct { Val int64; Next
*ListNode }` — a struct that points to ITSELF.  Modelled `Inductive ListNode := MkListNode { ln_val :
GoI64 ; ln_next : Ptr ListNode }` (`Inductive`, not the recursion-forbidding `Record` keyword; recursion
through the TAG-FREE phantom `Ptr` ⇒ `ListNode` occurs vacuously-positively, so Rocq accepts it and
`GoTypeTag ListNode` stays universe-consistent — same reason `GoChan` is tag-free).  The recursive TYPE
gets a FINITE nullary nominal tag `TListNode : GoTypeTag ListNode` (it doesn't structurally contain
itself — a base case like `TBool`; the `Next` field's tag is the finite `TPtr TListNode`), which
round-trips through `tag_eq` (`tlistnode_tag_refl`/`tlistnode_selfptr_refl`, both `reflexivity`).  So a
`*ListNode` cell lives in the typed heap: `linked_list_demo` heap-allocates 3 nodes (`ptr_new TListNode`),
pointer-chains them, and TRAVERSES head→tail (`ptr_get`/`ln_next`) → `1 2 3`.  Emits `type ListNode struct
{ Ln_val int64; Ln_next *ListNode }`, golden-locked, axiom-free (assumptions = `int : Set`).  ⚠ each named
recursive type needs its own nullary tag ctor in builtins.v (Rocq inductives are closed); auto-tagging
user-defined recursive structs needs a named-type registry (deferred).

### [Method declarations](https://go.dev/ref/spec#Method_declarations) — ✓ value + pointer receiver, method values/expressions
Spec: a method binds a function to a receiver of a defined (here, struct) type:
`func (r T) M(params) results { … }`; the call is `recv.M(args)`.  A Rocq top-level
function whose FIRST visible parameter is a record (struct) type is lowered as a
value-receiver method — type-directed, so it is automatic.  Faithful: a value
receiver gets a COPY (Go's value-receiver semantics), and structs are value types
here, so `recv.M(a)` denotes exactly `M(recv, a)`; the receiver keeps the same
de Bruijn binding (only the printed signature pulls it out front).  Projections and
inlined refs are excluded from method detection.  Pure and IO-returning methods both
work.  Method behaviour is provable in Rocq (`shifted_px`: `px (shifted p d) =
add (px p) d`).  Witnesses: `method_demo` (`func (p Point) Sum_coords() int64` /
`Shifted(dx int64) Point`, calls `p.Sum_coords()` / `p.Shifted(10)` → `7/13/14/27`),
`io_method_demo` (`func (p Point) Describe()` → `8/9`).  **POINTER receivers DONE** (on the
struct-pointer substrate): a first param of type `SPtr R` (a `*R`) → `func (r *T) M()` that
MUTATES the receiver, observed by the caller (`cell_incx` → `func (p *Cell) Cell_incx()`;
`cell3_inc_z` on a 3-field `*Cell3`; `pair_bump` on a HETEROGENEOUS `*Pair{ N int64; B bool }`).
**Method VALUES** (`p.M` as a closure → `method_value_demo` passes `p.Shifted` to a HOF) and
**method EXPRESSIONS** (`T.M` unbound → `method_expr_demo` passes `Point.Sum_coords`) are DONE
too — INCLUDING the **pointer-receiver method expression `(*T).M`** (`ptr_method_expr_demo`
passes `(*Cell).Cell_incx` — a `func(*Cell)` — to a HOF; the receiver type is recorded
parenthesized, and a func returning `IO unit` now renders VOID so it type-checks against the
method's void signature).  **DEFINED TYPES over a primitive with methods DONE (2026-06-19):**
`type MyT <prim>` — a distinct named type with the primitive's representation, carrying methods.
Modeled as a 2-field record whose 2nd field is a `GoTypeTag` PHANTOM, which is KEPT by extraction
so Coq does NOT unbox the single value field — that is what keeps the type a distinct method-
receiver (the recurring single-field-unboxing wall, beaten again because a defined type needs no
`Comparable`).  The plugin emits `type MyI64 int64` (NOT a struct; the phantom field is never
rendered), the ctor as the cast `MyI64(v)`, the value projection as `int64(x)`, and methods on it
are detected as usual: `func (m MyI64) Myi64_double() MyI64 { return Mk_myi64(int64(m) + int64(m)) }`,
`deftype_demo` → `42`, golden-locked, axiom-free.  The underlying is GENERIC (computed via `pp_type`
of the value field), so a defined type over a **string** works identically — `type Greeting string`,
ctor `Greeting(s)`, projection `string(x)`, method `func (g Greeting) Greeting_with(who string)
string { return string(g) + who }` (`deftype_str_demo` → `Hi, fido`).  And a defined type **satisfies
an INTERFACE**: `type Celsius int64` with method `Reading` is wired into a `Measurable` dictionary
(`func (c Celsius) Celsius_measurable() Measurable { return Measurable{Measure: func() int64 { return
c.Reading() }, …} }`) — behavioral satisfaction for a defined type, the dictionary closure dispatching
the defined type's own method (`deftype_iface_demo` → `120`).  **NAMED FUNC TYPES** (`type Handler
func(int64) int64`, the `http.HandlerFunc` idiom) work too: a `TArrow` `GoTypeTag` constructor carries
the phantom for a func underlying, the projection cast is parenthesised and CALLED THROUGH when applied
(`func (h Handler) Handler_run(x int64) int64 { return (func(int64) int64)(h)(x) }`), `named_func_demo`
→ `42`.  **SLICE underlyings** (`type IntList []int64`, the `sort.Interface` `type ByLen []T` idiom)
work too — underlying tag `TSlice`, cast `[]int64(l)` (valid Go without parens), `func (l IntList)
Il_len() int { return len([]int64(l)) }`, `deftype_slice_demo` → `3`.  MAP underlyings work too —
`type Counts map[string]int64`, ctor `Counts(m)`, projection cast `map[string]int64(c)`,
with an IO-value method `func (c Counts) Co_size() int { return len(map[string]int64(c)) }` (lowers
now that `pp_io_body` returns a value-returning IO tail), `gmap_deftype_demo` → `2`.  ✗ not yet:
defined types used as map KEYS (the phantom breaks equality), `Module`-namespaced method names, and defined
types over a STRUCT underlying (the `GoTypeTag` phantom needs a tag for the named struct — the tag-system
limit, not "mechanical").  **IO-value methods with a BIND-CHAIN tail DONE (2026-06-22):** `pp_io_body`'s
`ret_val` path already emits the leading effects as STATEMENTS and the `ret` tail as `return …`, not just a
single-expression tail — `func (p Point) Px_then_sum() int64 { println(p.Px); return p.Px + p.Py }`
(`io_val_method_demo` → `8 17`, golden-locked).

### [Function types](https://go.dev/ref/spec#Function_types) — multiple return values: ✓ N-ary
Spec: `func(…) (R1, R2, …)` returns a FLAT tuple of results.  Ours: a Coq function returning
`prod A B` lowers to Go `func(…) (A, B)` (`return a, b`; destructure `x, y := f()`).  **N-ary
(2, 3, …) DONE (2026-06-23):** Go's `(A, B, C)` is FLAT, but Coq's `A * B * C` is the LEFT-NESTED
`(A * B) * C` with value `pair (pair a b) c`; the plugin now flattens the left spine at all four
sites — the prod TYPE render (`flatten_prod_type` → `(int64, int64, int64)`), the `return …` value
(`flatten_pair_value` → `return a, b, c`), and BOTH destructure sites (`flatten_destructure`, which
collapses the NESTED `MLcase`s of `let '((x,y),z) := f` to one `x, y, z := f()`).  The destructure
needs NO de-Bruijn lifting: the eliminated intermediate `p` stays in the body's env as an unused
placeholder, so every index still resolves.  `triple_demo` (`triple3 : GoI64 * GoI64 * GoI64`) →
`x, y, z := Triple3(1, 2, 3)` → `1 2 3`, golden-locked; 2-ary (`swap2`/`multiret_demo`) byte-identical.
A non-left-nested `A * (B * C)` (not a valid Go flat tuple) stays fail-closed (the prod TYPE render
rejects it; a non-spine pair VALUE aborts at its `pp_expr`).  The DESTRUCTURE lowers in BOTH positions:
IO/statement (`pp_stmts`/`emit_block`) AND pure-value-returning (`pp_pure_tail`) — a non-IO `func f()
int64 { x, y := g(); return x + y }` was a fail-closed gap (found by self-review 2026-06-23, pre-dating
the N-ary work); now handled (`pure_destr_demo` → `7 6 5`: `sum_pair` 2-ary + `sum3` N-ary, golden-locked).
A WILDCARD binder `let '(_, y) := …` (Coq extracts the `_` as an unused gensym, which left as a real
`:=` binder is invalid Go — `declared and not used`) is blanked to Go `_` via `pp_destr_binder`/`dbn_free`
(`snd_of`, `stmt_blank_demo`) — both positions; this fixed a fail-OPEN the pure-position fix had exposed.
A NARROW component — `func(…) (uint8, uint8)` — is cast to its return slot (`return uint8(…), uint8(…)`)
via `value_narrow_conv`; without it the int64-carrier values were returned into uint8 slots = invalid Go
(another fail-OPEN, found by the same self-review; `narrow_pair_demo` → `44 7`, go-vet-clean, golden-locked).

### [Interface types](https://go.dev/ref/spec#Interface_types) — ⚠ method-dictionary (1 / nullary / N-method + EMBEDDING, all extracted + golden-locked); ✗ `interface` keyword
Spec: an interface is a method set; a value of interface type holds a concrete value
whose type implements those methods, with the concrete type known only at runtime
(an existential).  We model it as the method DICTIONARY directly: a Rocq `Record`
whose fields are the methods, each a closure ALREADY closed over the underlying
value.  This lowers to a Go struct of function fields (a vtable) — `type Shape struct
{ Area func(int64) int64; Perim func(int64) int64 }`; the dictionary is built with
TYPED closures (`func(s int64) int64 { … }`, via `record_ctor_ftypes`), the concrete
value is CAPTURED by the closures (so it is existential at runtime — a `Shape` cannot
be turned back into the rectangle it came from), and a method call lowers to dispatch
`sh.Area(0)`.  Faithful to the *semantics* (Go's interface IS a vtable + an erased
value); ⚠ deviation: we emit a struct-of-funcs, not the `interface { … }` keyword.
Satisfaction is checked in Rocq (the dictionary literal demands real methods) and
dispatch is provable (`dispatch_area`: `area (mk_rect w h) s = …`).  Witness:
`iface_demo` (`Shape`/`mk_rect`/`mk_square`/`show_shape` → `14/1007/20/1010`).
**1-METHOD + NULLARY DONE (verified vs golden + emitted Go, 2026-06-21 — corrects a stale ✗ that
claimed 1-method "leaks the inner lambda, fails go build"; it compiles, runs, golden-locked):** a
SINGLE-method interface is a 2-field record `{m ; gr_self : GoAny}` — the `gr_self` second field both
sidesteps Coq's 1-field-record unboxing AND is MORE faithful (a Go interface value IS a (method-table,
value) pair).  `Greeter`/`mk_adder` → emitted `type Greeter struct { Greet func(int64) int64; Gr_self
any }`; dispatch `(Mk_adder(5)).Greet(10)` → `15` (`dispatch_greet` proven by `reflexivity`;
`single_iface_demo` golden-locked).  NULLARY methods (`String()`-style — a unit-thunk `unit -> R`) lower
with the UNIT ARG ERASED: `Stringer`/`mk_namer` → `type Stringer struct { Sg_str func() string; … }`,
called `(Mk_namer("fido")).Sg_str()` (no arg) → `fido` (`dispatch_str` proven; `nullary_iface_demo`
golden-locked).  **EMBEDDING DONE (2026-06-22, model-only, NO plugin change, golden-locked):** an interface that EMBEDS
others is the FLAT UNION dictionary (all methods + the captured value); the "is-a" relation is an explicit
UPCAST that PROJECTS the embedded interface's methods (and the same hidden value) into its smaller
dictionary.  `Reader`/`Writer`/`ReadWriter` (embeds both) → emitted `type ReadWriter struct { Rw_read
func(int64) int64; Rw_write func(int64) int64; Rw_self any }` with receiver-method upcasts `func (rw
ReadWriter) Rw_as_reader() Reader { return Reader{Rd_read: rw.Rw_read, Rd_self: rw.Rw_self} }`; dispatch
via the UNION (`f.Rw_read(3)`) AND via each upcast (`f.Rw_as_reader().Rd_read(5)` / `…Wr_write(40)`) →
`13/15/30` (`embed_read`/`embed_write` proven by `reflexivity`; `embed_iface_demo` golden-locked).  Go's
implicit embedded-interface assignment is made EXPLICIT (consistent with the explicit-dictionary deviation).
**✗ still:** the native `interface { … }` KEYWORD with structural satisfaction — we emit dict-structs, tracked.

### [Slice types](https://go.dev/ref/spec#Slice_types) / [Map types](https://go.dev/ref/spec#Map_types) / [Channel types](https://go.dev/ref/spec#Channel_types) — ✓ incl. backing-array ALIASING
Two slice views: the functional `GoSlice = list` (value/immutable: `len`/`cap`/`append`/`slice_at_ok`)
AND the heap-backed mutable **`SliceH`** (`{base; off; len; cap; tag}` — a real view into a shared
backing array).  `SliceH` models the DEFINING reference-type semantics, all extracted + golden-locked
(`slice_aliasing_demo`/`slice_append_demo`/`slice_makelc_demo`): in-place `s[i]=v` (`slice_idx_set`),
`s[a:b]` SHARING the backing (`subslice`), and the **aliasing THEOREM** `subslice_alias` (a write
through a sub-slice is observed through the parent), its **complement** `slice_idx_set_frame`
(SEPARATION: distinct backing cells are independent — 2026-06-21), and `append`'s subtle
in-cap-aliases-vs-past-cap-reallocates (`slice_append_incap_aliases`), `make([]T,len,cap)`, slice
`clear`/`copy`.  Maps via a heap in the world (get-after-write are *theorems*); channels via state in
the world (below).  *Still ⚠:* a CONCURRENT (cross-goroutine) aliasing/race account rides the
concurrency calculus, not this functional layer.  **Pointer↔calculus bridge, slice 1 (2026-06-21):**
`concurrency.v` `Section KeystonePtr` ties the EXTRACTABLE pointer derefs `ptr_set`/`ptr_get` to the
operational shared-memory steps `rstep_write`/`rstep_read` (`ptr_write_sim`/`ptr_read_sim`, the derefs
being DEFINITIONALLY the bridge's ref-accesses at `ptr_as_ref`) — so the calculus's `nat` locations
ARE genuine `*T` cells, and `mp_trace_race_free`'s race guarantee now concerns a real pointer, not an
abstract `nat`.  Substrate base only (no funext, no Fido axiom).  **Slice 2a DONE (2026-06-21):** the EXECUTION
direction — `mp_exec_trace` proves the two-goroutine pointer-handoff program steps to exactly
`mp_trace` (`rsteps (mp_init v0 v1) cfg /\ rc_trace cfg = mp_trace`) and `mp_exec_race_free` ⇒ that run
is `TraceRaceFree`, so the trace is grounded in a real program run (both Closed-under-global-context).  **Slice 2b DONE (2026-06-21):**
each goroutine of `mp_prog` is the Keystone-denotation of an EXTRACTABLE typed pointer-handoff IO program
(`mp_g0_denotes`/`mp_g1_denotes`: `mp_g0_io = *p=v0; ch<-v1`, `mp_g1_io = <-ch; _:=*p`), the memory ops
being the genuine `ptr_set`/`ptr_get` — so the race-free execution is the operational image of real typed
pointer-over-channel code (substrate base; no funext, no Fido axiom).  **Value correctness (2026-06-21):**
`mp_handoff_delivers` — the extractable typed program run in `run_io` DELIVERS exactly `(inj v1, inj v0)`
(g1 receives v1 over the channel AND reads v0 back through the pointer; pointee survives send+recv via the
channel/heap World frames), so it is not only race-free but COMPUTES the right values end-to-end.  **Slice
2c DONE (2026-06-22):** `mp_end_to_end` — THE one closed end-to-end theorem — COMPOSES every slice for the
concrete typed pointer-handoff `mp_prog` under ONE coherent environment (`chenv`/`ptrenv`/`inj`/`prj`): the
extractable typed concurrent program (a) executes to `mp_trace`, (b) is race-free on this run AND on every
interleaving (`mp_all_interleavings_race_free`), (c) with each goroutine the Keystone-denotation of real
typed IO (`mp_g0_denotes`/`mp_g1_denotes`), (d) its FULL state — channels AND memory — realized by one
`run_io` world (`wstate_steps`), and (e) the equivalent single-threaded handoff IO delivering exactly
`(inj v1, inj v0)` (`mp_handoff_delivers`).  Assumptions = PrimInt63/PrimFloat + the documented funext
holdout (`run_io_inj`); no Fido axiom.  (N-goroutine generality of the GUARANTEE is already
`reachable_owned_safe_r`, over arbitrary programs + all schedules; `mp_end_to_end` is the concrete closed
instance — `go_spawn` has no whole-program `run_io` law, so cross-goroutine glue stays the STATE refinement.)
**SELF-REFERENTIAL channel type DONE (2026-06-22):** a channel can carry a value of a type that
contains the channel's own type — "channels that send themselves".  `Inductive ChanBox := MkChanBox
{ cb_id : GoI64 ; cb_chan : GoChan ChanBox }` = `type ChanBox struct { Id int64; Ch chan ChanBox }`
(recursion through the TAG-FREE phantom `GoChan` ⇒ vacuously positive; nullary nominal tag `TChanBox`,
the channel-of-itself tag being the finite `TChan TChanBox`).  `chanbox_demo` makes a `chan ChanBox`,
a goroutine sends `ChanBox{42, c}` whose `Ch` field IS `c`, main receives → `42`.  Stronger than
`chan_of_chan_demo`'s `chan chan int64` (element is a *different* type); here the element type contains
the channel's own type.  The channel read-after-write at `chan ChanBox` is the existing `chan_buf_write_same`
theorem (via `tag_eq_refl`), so no new proof obligation; axiom-free (`tchanbox_*_refl` rest on `int : Set`).

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
on the full-width Z model (Tier 2 #4).  **Bitwise ALGEBRA (`GoU64`) proven (2026-06-21,
axiom-free):** `u64_{and,or,xor}_comm` + `u64_{and,or,xor}_assoc` — the Boolean-algebra
counterpart of the arithmetic semiring + total-order laws; associativity rests on
`wrapU64_bit_{l,r}` (mod-2⁶⁴ depends only on the low 64 bits, one `Z.bits_inj'` each).
Idempotence `a&a=a` is SProp-BLOCKED (needs `u64raw a` in range, hidden by the `Squash`
seal) — documented, not skipped.  **SIGNED↔UNSIGNED FAITHFULNESS proven (2026-06-21,
axiom-free):** `i64_{and,or,xor}_via_u64` — `a & b == int64(uint64(a) & uint64(b))`, i.e.
the signed bitwise op = the signed reinterpretation of the UNSIGNED op on the
two's-complement bit patterns (Go's int64/uint64 bitwise agreement), verifying the signed
`GoI64` bitwise is faithful.  (Cancel the double mod-2⁶⁴, pull `wrapU64` through the bit-op,
collapse `wrap64 ∘ wrapU64`.)
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
(65025→1), `u8_sub_wraps` (0-1→255), `u16_mul_wraps`.  ✓  (signed): `intN`
two's-complement — `i8_add_wraps` (-106), `i16_add_wraps` (-25536).  Full-width
`int64`/`uint64` wrap at the TRUE 2⁶³/2⁶⁴ via `GoI64`/`GoU64` (`spec_i64_add_wrap`,
`spec_u64_add_wrap`) — the canonical int model (A4.3).  The legacy `Sint63` `int`
(wraps at 2⁶², ⚠ Tier 2 #4) survives only for indices.  32-bit multiply ✓
(`spec_u32_mul_wrap`/`spec_i32_mul_wrap`, mask keeps the exact low 32 bits).

### [Floating-point operators](https://go.dev/ref/spec#Floating-point_operators) — ✓ ops; ⚠ FMA fusion
Spec: `+x=x`, `-x`=negation; div-by-zero "not specified beyond IEEE 754…
implementation-specific" whether it panics.  **An implementation MAY fuse** float
ops (e.g. FMA `x*y+z` without rounding the intermediate); an explicit float
conversion rounds to the target precision and prevents fusion.
Ours: `float64`=`PrimFloat` (IEEE binary64); `+ - * /`, `opp`, comparisons lower
to Go natives; float `/` unguarded (IEEE ±inf/NaN, no panic) — conforms.
`float_demo`, `float_opp_demo`.  **⚠ deviation:** we round EACH op (no fusion);
Go MAY FMA `a*b+c`, giving a more precise result — a fused expression can differ
from our per-op-rounded value (Go does not GUARANTEE fusion, so this is bounded).
`float32` — **✓ DONE & SOUND** (faithful binary32 via `SpecFloat`; arithmetic + comparisons →
native Go `float32` `+ - * /` `< <= == > >= !=`, plus unary `-` (`f32_neg`) and `min`/`max`
(`f32_min`/`f32_max`) — float64 parity sans `abs`/`sqrt`, which need `math`).  `GoFloat32` is an
ABSTRACT smart-constructor type carrying an unforgeable `exists a, carrier = f32_round a` proof, so
a non-representable literal cannot be injected (would disagree with Go on widening).  NaN and
signed-zero corners machine-checked across negation/min/max (NaN propagates; `min(-0,+0) = -0`,
`max(-0,+0) = +0`).
**Conversions.**  `float32↔float64` and `int(float32)` (`f64_of_f32` widen exact; `i64_of_f64∘
f64_of_f32` truncate-toward-zero) ✓.  Range corners witnessed: overflow → `+Inf` (`f32_overflow`),
underflow → `0` (`f32_underflow`).
**⚠ CORRECTION (2026-06-20, code review) — an earlier "single-rounding-equivalent" claim here was
FALSE.**  Routing int/constant → `float32` through binary64 is NOT double-rounding-innocuous in
general: the `q ≥ 2p+2` theorem assumes the intermediate holds the *exact* value, but for `|x| >
2^53` the int→binary64 step ITSELF rounds, and a second round to binary32 can disagree.
Reproduced (Go 1.23.2): `x = 2305843146652647425 = 2^61+2^37+1` gives `float32(x) = 0x5e000001`
(rounds up) but `float32(float64(x)) = 0x5e000000` (low bit lost onto the float32 midpoint, then
ties-to-even down).  So `f32_of_f64 (f64_of_int x)` faithfully models Go's `float32(float64(x))`,
NOT direct `float32(x)`.  *Fix:* DIRECT conversions `f32_of_i64`/`f32_of_u64`/`f32_of_int` round the
exact integer ONCE to binary32 (`binary_normalize 24 128 x 0`), lowered to Go's `float32(x)`.
Machine-checked on the reviewer's witness: `f32_of_i64_differs` (direct ≠ via-float64),
`f32_of_i64_direct` (= `2^61+2^38`), `f32_of_i64_viaf64` (= `2^61`); `f32_of_int_demo` → `false`.
*Constant path — ✓ DONE:* `f32_of_fconst` rounds the EXACT rational once to binary32 via `SFdiv 24
128` of the exact-integer spec_floats (`sf_of_Z` — no intermediate binary64, so correctly-rounded for
ALL num/den, not just `< 2^53`).  Lowered to Go's `float32(num.0 / den.0)` (untyped-constant division,
arbitrary precision, single round).  Witnessed: `f32_of_fconst_direct` (`2305843146652647425/1 →
2^61+2^38`), `f32_of_fconst_differs` (≠ the via-float64 double round), `f32_of_fconst_small`
(`float32(0.1+0.2) = float32(0.3)`); `f32_fconst_demo` → `0.3`.
**Constant-vs-runtime soundness fix (2026-06-20, code review) — applies to float32 AND float64.**
Fido's model is runtime IEEE (−0, ±Inf, NaN); the extractor formerly emitted float ops on
CONSTANT operands as Go *constant expressions*, where IEEE does not hold — Go constants cannot
denote −0/±Inf/NaN, and a constant `/0` or a `float32` overflow are COMPILE ERRORS (reproduced:
`float32(1)/float32(0)`, `float32(1e40)`, `−(float32(0))` collapsing to +0).  Fix: a float op
(arith / neg / narrow / min·max) whose operands are not runtime variables is now forced to RUNTIME
via a typed IIFE (`func(x,y T) T { return x OP y }(a,b)`); ops on runtime operands stay idiomatic
(`(a+b)*c`).  Sound (forces unless an operand is a runtime var, so no all-constant op is left
unforced), value-preserving (golden output unchanged), and the three attacks now compile + yield
IEEE results — `f32_const_runtime_demo` → `+Inf −Inf +Inf +Inf` (machine-checked vs the model).
**⚠ Deferred (bounded, principled):** bit reinterpretation `math.Float32bits`/`Float32frombits`
needs the `math` import (rule 5 — imports on hold, deferred not approximated) AND would expose
that `SpecFloat` carries NO NaN payload (a substrate limit: `S754_nan` is payload-free), so
bit-exact NaN-payload round-tripping is out of scope until both are addressed.
See the Reconciliation note up top.

### [Comparison operators](https://go.dev/ref/spec#Comparison_operators) — ✓ conforms
Spec: integers "in the usual way", floats "as defined by IEEE 754", bools equal
iff both true/both false.  Ours (int): SIGNED `ltsb`/`lesb` → Go signed `</<=`;
unsigned `PrimInt63.ltb`/`leb` **rejected** for `int` (disagree on high bit) —
`ltb_unsigned_neg_false`/`ltb_signed_neg_true`.  (float): `PrimFloat.ltb`/`leb`/
`eqb`, IEEE incl. NaN unordered — `nan_eqb_false`, `nan_ltb_false`.  (string):
`str_eqb` → Go `==` (byte equality), `str_ltb` → Go `<` (lexicographic by byte
value) — both theorems (see String types).  ✓
(int64/uint64/string/float): `i64_gtb`/`i64_geb`/`i64_neqb`, `u64_*`, `str_gtb`/
`str_geb`/`str_neqb`, `f64_gtb`/`f64_geb`/`f64_neqb` now emit the DIRECT Go
`>`/`>=`/`!=` (the emitted Go matches the source operator, not a swapped encoding);
`cmp_ops_demo`/`scmp_demo`/`fcmp_demo` print `true …`.  Machine-checked incl. the
unsigned `u64_gtb (2⁶⁴-1) 1 = true` and the FLOAT NaN corner — `f64_geb` is the
swapped `leb b a` (NOT `¬(<)`), so `NaN >= 1` is `false` (`f64_geb_nan`) and
`NaN != 1` is `true` (`f64_neqb_nan`), matching IEEE/Go.  ✓  (Direct `>`/`>=`/`!=`
for the narrow fixed widths follow the same trivial pattern, pending.)

### [Logical operators](https://go.dev/ref/spec#Logical_operators) — ✓ conforms
Spec: `p && q` = "if p then q else false", `p || q` = "if p then true else q",
`!p` = "not p"; short-circuit.  Ours: `andb`/`orb`/`negb` → `&&`/`||`/`!`, and
Coq's `andb` IS that definition — `spec_andb`/`spec_orb`/`spec_negb` by
`reflexivity`.  Short-circuit unobservable (pure total bools).  ✓

### [Conversions](https://go.dev/ref/spec#Conversions) — ✓ integer↔integer (fixed-width + int64↔uint64 + narrow↔int64 + narrow↔uint64), int/int64→float64, float64→int64, float64→float32, narrow↔float32 (composable via int64/float64), string↔[]byte/[]rune + string(rune); ✗ interface conversions beyond `type_assert`
Spec: "When converting between integer types, ... it is then truncated to fit in
the result type's size."
**Integer conversions among `{int, uint8, int8, uint16, int16, uint32, int32}` — ✓.**  Routed
through the `int` carrier: `int_of_FW` WIDENS (value preserved in the model; EMITTED as a real
cast `int(x)`, NOT identity — a narrow Go value at an `int` boundary needs it, review #4 P1 #4)
and `FW_of_int` NARROWS (truncate — `land` for `uintN`, mask+sign-extend for `intN`
— exactly Go's `uint8(x)`/`int8(x)`, no representability proof since a conversion
truncates rather than rejects).  Cross-width by composition (`uint8(int16val)` =
`u8_of_int (int_of_i16 x)`, the low 8 bits).  These are also what make the DISTINCT
numeric types mixable — implicit mixing is rejected (`*_no_implicit`,
`u8_of_i16_direct` `Fail`s), so a value crosses types only through a conversion.
Machine-checked (`spec_u8_of_int_trunc`…`spec_i16_of_u8_cross`): `uint8(1000)=232`,
`uint8(-1)=255`, `int8(200)=-56`, widen `int(uint8 200)=200`, cross `int16(uint8 200)`.
`convert_demo` prints `200 232 / 1200`.
**Full-width `int64`↔`uint64` — ✓ (2026-06-18).**  `u64_of_i64`/`i64_of_u64` are Go's
`uint64(x)`/`int64(x)`: a two's-complement REINTERPRET of the 64-bit pattern, EXACT (no
rounding).  The Z carrier re-normalises mod 2⁶⁴ (`MkU64 (wrapU64 (i64raw a))` /
`MkI64 (wrap64 (u64raw a))`), faithful by `wrap64_wrapU64` (the int64 and uint64
normalisers agree mod 2⁶⁴ — axiom-free).  Distinct from the narrow widths (whose value is
int64-carried and which widen via an INLINE cast `int64(x)`/`int(x)`, not identity) because
`GoU64` lowers to a real Go `uint64`.  Emitted as
a small NAMED function `func U64_of_i64(a int64) uint64 { return uint64(a) }` so the cast
applies to the parameter VARIABLE — Go rejects `uint64(-1)` on an untyped CONSTANT but
accepts it on an int64-typed value.  Machine-checked `conv_u64_of_neg1` (`-1 → 2⁶⁴-1`),
`conv_i64_of_max` (`2⁶⁴-1 → -1`), `conv_roundtrip`; `conv64_demo` prints
`18446744073709551615 -1 255`.
**Narrow → `int64` widening — ✓ DONE (review #4 P1 #4 slice 1, commit a4e715d).**
`i64_of_u8`…`i64_of_i32` are value-preserving widens (machine-checked
`widen_u8`/`widen_i8`/`widen_u16`/`widen_u32`/`widen_i32`), now LOWERED by
NAME-RECOGNITION to Go's `int64(x)` — NOT identity: a narrow operand at a typed
boundary is a real `uint8`/`int8`, so `int64(x)` is required to land it in the `int64`
destination (a bare `return x` was the review #4 P1 #4 invalid-Go case).  The faithful
`Sint63.to_Z` body (which would pull the deliberately-REJECTED unsigned `Uint63.ltb`,
Tier 3 #9) is suppressed by the recognizer, sidestepping the carrier wall.  Extracted
via `widen_param_demo` (`func Widen_u8_to_i64(x uint8) int64 { return int64(x) }`,
golden `200 -5 100`).
`string`↔`[]byte`/`[]rune` and `string(rune)` are DONE (the rune view — see String
types).  **`int`/`int64` → `float64` DONE (2026-06-19):** `f64_of_int` (Sint63) and `f64_of_i64`
(`GoI64`) → native `float64(x)` (the nearest double, exact for `|x| < 2^53`); modeled by
`PrimFloat.of_uint63` + a sign-split (machine-checked `f64_of_int_pos`/`_neg`,
`f64_of_i64_pos`/`_neg`), recognized → cast with the body suppressed.  Both return `float`
(a primitive, not a single-field record), so they stay NAMED calls — this was the EARLY
lowering technique; the narrow→int64 widening (record result) now lowers the same way, by
name-recognition with its carrier body suppressed (review #4 P1 #4).  `f64_of_i64`'s `Z` carrier drags the
Z↔int63 helpers `of_Z`/`of_pos`/`of_pos_rec`, suppressed alongside the `Z`/`positive`
arithmetic.  Trust base gains the Rocq PRIMITIVE `PrimFloat.of_uint63` — a kernel `float` op
(like `PrimFloat.add`), NOT a Fido axiom (`of_Z`/`of_pos` are `Definition`s, not in the
base).  **`float64` → `int64` truncation — ✓ DONE (name-recognized, golden-locked):**
`i64_of_f64` truncates toward zero via the stdlib's VERIFIED `Prim2SF` decomposition
(`m * 2^e` for `e ≥ 0`, else `m / 2^(-e)` = floor of the magnitude, sign applied after —
exactly Go's rule), machine-checked across the sign / exact / zero cases
(`i64_of_f64_pos`/`_neg`/`_exact`/`_zero`/`_big`), and LOWERED to Go's native `int64(f)` by
name-recognition (the `Prim2SF`/`f64_trunc_Z` body suppressed, sidestepping the case-of-case
fusion wall the old proof-only note cited).  Extracted via `trunc64` / `i64_of_f64_demo`
(golden `3 / -2`).  Bounded deviation at NaN/±Inf/overflow (impl-defined in Go — the native
`int64(f)` gets Go's behaviour for free).  **Narrow ↔ `uint64` and `int64` ↔ narrow are also
DONE:** the uint64 hub (`u64_of_i64 ∘ i64_of_narrow`, golden `200 18446744073709551615 255
-1`) and the `int64`→narrow truncations (`u8_of_i64`…, golden `52 -56 201 -55`).  **Still ✗
(fails loud):** interface conversions beyond `type_assert` (the `interface` keyword).

## Expressions — primary

### [Index expressions](https://go.dev/ref/spec#Index_expressions) — ✓ slices/strings/maps (single-goroutine)
Spec: `a[x]` indexes; an out-of-range slice/string index PANICS; a map index `m[k]`
never panics (`v, ok := m[k]`).  Ours: `slice_get` (raw, OOB ⇒ panic, escape hatch)
and the safe `slice_at_ok`/`str_at_ok` (CPS/comma-ok — FORCE handling OOB, cannot
panic, signed-index both-ends check) → `xs[i]`/`int64(s[i])`; map `m[k]` via the
comma-ok `map_get_opt`/`map_get_or` → Go's two-value lookup.  ✓ (the panicking form
is proof-gated where range is statically known; sub-slice ALIASING is modeled — heap-backed
`SliceH`, `subslice_alias` + `slice_idx_set_frame`, see [Slice types]).

### [Composite literals](https://go.dev/ref/spec#Composite_literals) / [Function literals](https://go.dev/ref/spec#Function_literals) / [Calls](https://go.dev/ref/spec#Calls) — ✓ for the modeled forms
Struct literal `T{…}` (fields in declaration order) and slice literal `[]T{…}` via
`slice_of_list`; closures (Go func literals) carry the interface-dictionary methods
and the `go`/`defer` bodies; a function call `f(a)` / method call `recv.M(args)` lowers
directly (see Struct/Method/Interface above).  ✓ for what's modeled.

### [Type assertions](https://go.dev/ref/spec#Type_assertions) — ✓ (tagged-`GoAny`, axiom-free); ✗ assert-to-`any`
Spec: `x.(T)` asserts the DYNAMIC type of interface value `x` is `T`; the single-value
form PANICS on mismatch; the comma-ok form `v, ok := x.(T)` yields `ok = false` and the
zero value, no panic.  Ours: `GoAny` is now a TAGGED pair `{A & A * GoTypeTag A}` — Go's
`interface{}` carrying its value's runtime type — so `type_assert tag a` recovers the
value via `tag_coerce` (tag match ⇒ value; mismatch ⇒ panic) and `type_assert_safe` is
the comma-ok form (match ⇒ `(v, true)`; mismatch ⇒ `(zero_val tag, false)`).  Witnesses:
`type_assert_ok` (**theorem**: asserting `anyt tag x` to its own tag = `ret x`, via
`tag_coerce_refl`), `type_assert_safe_ok` (match ⇒ `(x, true)`), and the ADVERSARIAL
`type_assert_safe_mismatch` (**Example**: an `int`-tagged value asserted to `TBool` ⇒
`(false, false)` — never the value; this is the soundness check).  Plugin lowers to Go's
native `v.(T)` / `v, ok := x.(T)`.  Demos: `panic_and_recover` (panic→`catch`→
`type_assert TInt64` ⇒ 42), `assert_safe_demo` (`TInt64` ⇒ `n true`, `TBool` ⇒
`false false`).  ✓  **✗ deviation (tracked, fail-loud, not an axiom):** "assert TO
`any`" and typed `chan any`/`[]any` containers — removing the `TAny` tag is what breaks
the `GoTypeTag GoAny` universe cycle, sound because a value's dynamic type is always a
CONCRETE type (Go flattens nested interfaces), so `GoTypeTag GoAny` is never an actual
runtime type.

## Statements

### [Variables](https://go.dev/ref/spec#Variables) / [Assignment statements](https://go.dev/ref/spec#Assignment_statements) — ✓ mutable locals
Spec: a variable holds a value; assignment `x = v` stores; declaration `x := v`.  Ours:
`ref_new`/`ref_get`/`ref_set` (a `Ref A` = a concrete typed cell in `w_refs`) → `var x T`
/ read / `x = v`; read-after-write is a **theorem** (`ref_sel_upd_same`, `ref_get_set_same`).
Demo: `mut_demo`.  ✓  (The CFG variable-placement discipline — declaration dominates use,
no shadowing — is part of the control-flow lowering below; pointers/`&x` ✓ DONE end-to-end,
Tier 3 #8a — `ref_as_ptr r := mkPtr (r_loc r)` is the address-of operator (the inverse of `ptr_as_ref`):
`&x` of a local `x` (a `Ref`) is a `*T` aliasing x's cell.  THEOREMS (substrate base, no funext/Fido axiom):
`ref_as_ptr_not_nil` (a `Ref` lives at a nonzero location ⇒ `&x` is NEVER nil ⇒ deref never panics — taking
an address is always safe, unlike a raw `*T`), `ptr_get_ref_as_ptr` (`*(&x)` reads `x`), and
`ptr_set_ref_as_ptr_aliases` (`*(&x) = v` then `x` reads back `v` — the defining alias).  EXTRACTION: the
plugin emits Go `&x` for `ref_as_ptr` — FAIL-CLOSED, restricted to a bound-variable operand (`MLrel`, the
provably-addressable case); any other operand is `unsupported` (Go forbids `&` of a non-addressable
expression, so we never rely on a later `go build` error).  WITNESS: `addr_of_demo` (main.v) lowers to
`x := int64(10); Write_thru(&x); …` — writing through `&x` mutates `x` (10→99), the canonical reason `&`
exists; golden-locked.)

### [If](https://go.dev/ref/spec#If_statements) / [For](https://go.dev/ref/spec#For_statements) / [Switch](https://go.dev/ref/spec#Switch_statements) / [Goto](https://go.dev/ref/spec#Goto_statements) / [Return](https://go.dev/ref/spec#Return_statements) — ✓ via the goto-CFG relooper; ⚠ native `switch`
Spec: structured control flow (`if`/`else`, `for` with optional range, `switch`,
`break`/`continue`/labeled, `goto`, `return`).  Ours: ALL control flow is one complete
primitive — a goto-CFG (`run_blocks`/`Jump`/`Done`, each function body a set of labelled
basic blocks) — lifted back to idiomatic Go by a STRUCTURING relooper (computes
dominators / post-dominators as iterative fixpoints, finds natural loops by back-edges,
recurses to emit `if`/`for`/`break`/`continue`/labeled-break, falling back to raw labels
+ `goto` only where the graph is irreducible).  Completeness lives in the CFG model;
niceness in the printer.  All demos golden-locked:
- **`if`** (match on `bool`) → `if c { … } else { … }`: `sign_demo`, `pick_demo`,
  `cond_op_demo`, `inline_if_demo`, `diamond_demo` (`if b {…} else {…}`), `cond_goto_demo`
  (`if !early {…}`).  ✓
- **`for`** (+ range): `for { … break }`, nested `for`s, in-loop `if`, labeled escapes —
  `count_demo`, `loopif_demo`, `nested_loop_demo`, `labeled_break_demo` (`break L0`),
  `labeled_continue_demo`; `for_each`/`slice_fold` → `for _, x := range xs`
  (`foreach_demo`, `sum_demo`); the indexed `for_each_idx` → `for i, x := range xs`
  (`foreach_idx_demo` → `0 10 / 1 20 / 2 30`); `str_range` → `for i, r := range s` (byte
  offset + rune); the Go 1.22 integer range `int_range` → `for i := range n` (`int_range_demo`
  → `0 1 2 3`, zero iterations when `n = 0`).  ✓
- **`return`** (in-loop): `early_return_demo`.  ✓
- **`goto`** (irreducible CFG): raw Go labels + `goto`, the always-correct fallback —
  `irreducible_demo` (a two-entry loop) golden-locks it.  ✓
- **`switch`**: ⚠ an n-ary `switch`/type-switch block decomposes to chained `bool` `if`s
  in the goto model (faithful behaviour); the native Go `switch` keyword is a printer
  nicety, not yet emitted.
Lowering correctness (each variable's identity preserved under read/capture/address;
declaration dominates use; no shadowing) is the CFG discipline — golden-guarded, the
unverified plugin surface (Known gap #10).

### [Go statements](https://go.dev/ref/spec#Go_statements) — ✓ lowering; choice/scheduler idealised
Spec: `go f()` starts `f` in a new goroutine.  Ours: `go_spawn m` → `go func(){ … }()`;
demo `goroutine_demo`.  The goroutine FORK happens-before edge (`go` ⤳ goroutine start)
is PROVEN race-free (`fork_program_race_free`, see the memory model).  ✓ at the lowering
+ ordering level; the scheduler / interleaving is idealised away (Tier 5 #14).

### [Defer statements](https://go.dev/ref/spec#Defer_statements) — ✓ EMITTED Go; ✓ FAITHFUL cmd.v model; shallow `run_io` fails loud
Spec: `defer f()` runs `f` at function return (LIFO), on both normal and panic exit — and a panic does NOT
cancel the remaining defers.  Fido has THREE defer REPRESENTATIONS (R) and one shallow-semantics BOUNDARY (B);
keep them separate:
- **(R1) Plugin RUNTIME emission (trusted):** the trusted `plugin/go.ml` lowers `defer_call f` BY NAME to
  native Go `defer func(){ f }()` (Go provides the LIFO/return-time scoping); demos `defer_demo`,
  `defer_loop_demo` (a `defer` in a loop prints 2,1,0 — golden RUNTIME output faithful).
- **(R2) cmd.v `CDfr` / `run_defers` — the FAITHFUL model:** `cmd.v` models `defer` as `CDfr d k`;
  `run_defers` (via `run_cmd`, the SOLE `Cmd` interpreter) runs the LIFO stack at func-scope return — a
  panicking defer REPLACES the active panic (last-raised-wins) but the older defers STILL run (review #12),
  every defer's effects happen.  `bridge_agrees` proves the `ustep` run AGREES with this for ANY command.
- **(R3) GoAst `GsDefer` — STRUCTURED syntax (✓ emittable, ✓ DENOTED):** `defer <call>` is a real AST
  statement, print-injective (`print_stmt_inj`), syntactically SUPPORTED + certificate-emittable (gated to a
  call via `expr_stmt_ok`), and GoSem DENOTES it into R2's faithful model (`denote_stmt GsDefer = CDfr d (CRet
  tt)` via the shared `denote_effect_call`; the deferred call runs at return, LIFO — end-to-end pins
  `GoSem.rc_defer_lifo` / `rc_defer_panic`).  A deferred panic denotes a `CPan` under the `CDfr`, so the
  panic-free gate (behavioral: `cmd_no_panic` of the denotation) rejects `defer panic(v)` while accepting +
  emitting `defer println(..)` (`GoSemSafe.panic_free_gate_defer`).
- **(B) shallow `IO` (`World -> Outcome`) — NO defer meaning, FAILS LOUD (✓ rule 2):** a sequential shallow
  reading cannot reify a func-scoped defer, so `builtins.defer_call (_ : IO unit) := fun w => OPanic … w`
  PANICS rather than silently dropping the effect (review #6/#12, which replaced the old `ORet tt w` no-op).
  There is NO shallow `Cmd -> IO` interpreter — `run_cmd` (R2) is the only `Cmd` semantics.

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
locked.  **⚠ the LOWERING is faithful Go; the MODEL is an UNSOUND deterministic
under-approximation** (code review 2026-06-20, sharpening "idealised away" — which
undersold it).  Two distinct unsoundnesses:
  - **CHOICE.** Both channels ready ⇒ the model deterministically takes ch1; Go picks
    pseudo-randomly.  Counterexample: both ready, `k1 ↦ 1`, `k2 ↦ 2` — Rocq always 1,
    Go may return 2.  So native Go does NOT *refine* the deterministic function (Go
    exhibits "take ch2", which the function forbids); that function is at best ONE
    example scheduler / a test interpreter — **non-authoritative**.  The authoritative
    spec is relational, and a safety property must hold for EVERY permitted choice.
  - **BLOCKING.** None ready, no `default` ⇒ the model returns the fabricated `(0, zero)`;
    Go BLOCKS.  But blocking is **not divergence**: the goroutine simply has no transition
    *right now* while others may still step — it is DEADLOCK only when the WHOLE program
    can't step.  `concurrency.v` already models this (`Stuck := ~ can_step /\ ~ done`,
    `block_cfg`); empty-select is a LOCAL non-step, never a fabricated value.
The desugar work (`select_wait2`/`select2`, `select2_eq_recv2`) proves the
sentinel+goto factoring equals *this idealised model* — NOT Go.  **Robust fix** (in the
`rstep` calculus, not the sequential `IO` model): a nondeterministic/relational
`select_wait` ranging over every ready case, proofs quantified over the chosen index
(`rstep` is this shape); empty = a local non-step (global deadlock = `Stuck`).  **Sound
interim:** evidence-carrying subset requiring a proof that EXACTLY ONE case is ready
(then determinism = Go) — sound ONLY under an interference-freedom / ownership discipline
that keeps readiness STABLE until selection (else a TOCTOU gap between proof and select).
Tracked
(Tier 5 #14, scheduler / non-terminating model).  *Also pending:* send cases, N-ary.
**Third review (2026-06-20) — CLOSED-channel fix + remaining items.**  *Fixed:* a closed, drained
channel's recv is READY in Go (zero value immediately), but the model examined only the buffer and
mispredicted `default` / fabricated the other case (`close(ch); select{case <-ch: 1; default: 2}` —
Go prints 1, model said 2).  `select_recv_default`/`select_recv2`/`select_wait2` now check
`chan_closed`: empty+closed ⇒ that recv fires with zero; `default` only empty+OPEN.  Witnessed
(`select_default_closed`/`select_default_open_empty`); `select2_eq_recv2` re-proven.  *Remaining:*
(a) **RESOLVED (2026-06-21):** the relational select now models closed channels with NO config flag —
closed-state is read off the TRACE (`closedb`: a `KClose c` event), and a `KRecv` back-pointer may point
at that `KClose` (the close→closed-recv happens-before edge).  `step_select_closed` / `rstep_select_closed`
step a closed-drained select to zero (witnesses `closed_select_can_step` / `rclosed_select_can_step`; see
the closed-channel rows below);
(b) **DONE (2026-06-20):** the value-carrying `rstep`/`Cmd` calculus now has `CSelect : list (nat *
(nat → Cmd))` — PER-CASE channel + continuation, so `select { case <-ch: A() | case <-ch: B() }`
(same channel, distinct bodies) IS representable and BOTH cases eligible (`rselect_per_case_continuation`:
two successors running A vs B).  Its `rstep_select` fires any ready case (nondeterministic), and an
empty select is a local non-step feeding global deadlock (`rsel_block_stuck` : `RStuck`).  The
deadlock theory was extended to be select-aware (`blocked` now includes a select-with-no-ready-case
disjunct via the decidable `sel_first_ready`; `ready_can_step`/`rstuck_blocked` updated), and the
`CSelect` case rides the existing `RInv`/`RBufSorted` preservation + the multi-goroutine state
refinement (`wmatchc_step`: select's world-step = a recv on the chosen channel).  Axiom-free,
proof-only (golden-stable).  **Scheduler bridge DONE (2026-06-20):** `sel_first_ready` IS the
ch1-priority scheduler the typed `select_recv2` realises, so `det_select_sound` proves that choice
is always a PERMITTED `rstep_select` (the typed select is a SOUND scheduler), and
`det_select_incomplete` proves that when two cases are ready it realises only ch1 while
`rstep_select` ALSO permits the ch2 successor (so it is INCOMPLETE) — making the review verdict
"the deterministic interpreter is one example scheduler, non-authoritative" a theorem.
**Completeness boundary DONE (2026-06-21):** the exact converse of `det_select_incomplete` —
`det_select_complete_unique` proves that when the cases have a UNIQUE buffered-ready case, every buffered
`rstep_select` firing collapses to the SAME successor `sel_first_ready` takes, and `det_select_exact_unique`
packages sound (⊇, from `det_select_sound`) ∧ complete (⊆) into one EXACT statement.  So the cheap typed
`select_recv2` is fully faithful to Go PRECISELY in the unique-ready regime — Go's pseudo-random pick then
ranges over a single candidate, so the deterministic model forbids nothing Go permits; incompleteness
arises ONLY from a genuine choice among ≥2 ready cases.  (Honest scope: the uniqueness is over BUFFERED
readiness; full Go-completeness also needs the open-channel side condition, since a closed-drained case is
an orthogonal ready successor.)  Proof-only, golden-stable, and `Print Assumptions det_select_exact_unique`
= **Closed under the global context** — fully axiom-free, resting on nothing at all (pure `nat`/`list`/
inductive reasoning over `rstep`, not even the Int63/Float substrate).
**WORLD-level select↔recv bridge DONE (2026-06-21):** `det_select_sound` used `sel_first_ready` as a
STAND-IN for the real `select_recv2`; now the actual `select_recv2` is tied to `run_io` directly — a
READY first channel makes it reduce to a plain `recv` on that channel: `select_recv2_ch1_buffered` /
`select_recv2_ch1_closed` (and the ch2 fall-through `_ch2_buffered` / `_ch2_closed`) prove
`run_io (select_recv2 …) w = run_io (bind (recv …) k) w`.  So select INHERITS `recv`'s `run_io`/
operational refinement (`denote_sim_recv` / `rstep_recv`); the calculus mirror `select_fire_is_recv_fire`
shows firing a buffered select case reaches the IDENTICAL successor as `rstep_recv` on that channel.
Both rest only on the `PrimInt63`/`PrimFloat` base (no `functional_extensionality`, no Fido axiom).
**Closed-channel readiness (relational), trace-core slice DONE (2026-06-20):** a recv from a CLOSED,
drained channel returns the zero value, and per the Go memory model the CLOSE happens-before that
recv.  The trace core now expresses this — a `KClose` event-kind, and a `KRecv`'s back-pointer may
point at a `KClose` of the channel (not only a `KSend`).  `WfTrace` carries the send-OR-close
disjunction; all happens-before / race-freedom proofs preserved.  Witnesses `closed_recv_wf` (a
closed-recv trace is well-formed) and `closed_recv_hb` (close happens-before the closed-recv).
**Operational slice DONE (2026-06-20):** the simple-calculus `step` gains `PClose` + `step_close`
(records a `KClose`), and — reading "closed" off the trace, no config field — `step_recv_closed` /
`step_select_closed`: a recv/select on a CLOSED, drained channel STEPS (yields zero), the emitted
`KRecv`'s producer being the close position.  `step_preserves_inv`/`step_preserves_sorted` extended
(closed-recv keeps `Inv`; `WfTrace` discharged by the close back-pointer).  Witnesses
`closed_recv_can_step` / `closed_select_can_step` (a closed-drained recv/select is ENABLED, where
`block_stuck`/`sel_block_stuck` show the OPEN-empty one is stuck) and `closed_recv_preserves_inv`.
**Rich-calculus port DONE (250a8c3):** the same closed steps in the value-carrying `rstep`/`Cmd`
calculus (`CClose` + `rstep_close` + `rstep_recv_closed` / `rstep_select_closed`, binding the zero
value); witnesses `rclosed_recv_can_step` / `rclosed_select_can_step` / `rclosed_recv_preserves_inv`;
Keystone `SimInv` carries a `NoCloseTrace` invariant.  **Closed-PRECISE deadlock DONE (e11b60f):**
`closedb` (decidable trace-closedness) + `sel_ready_cl` (closed-aware select readiness) make `blocked`
exact — a closed-drained recv/select is READY, not blocked; `ready_can_step`/`rstuck_blocked` are now
exact inverses (`rclosed_recv_not_blocked` / `rclosed_select_not_blocked`).  **Closed PERMANENCE DONE
(2026-06-20):** `closedb` only grows along `rstep` (every step appends one event; `existsb` monotone)
— `rsteps_closedb_mono`, so a channel once closed stays closed; `rclosed_chan_stays_closed` and
`reachable_closed_recv_can_step` (a closed-drained recv can step at ANY reachable later state — no
deadlock on a closed channel).
**Operational double-CLOSE = PANIC DONE (2026-06-21):** `rstep_close` is now GUARDED by
`closedb tr c = false` — a close of an already-closed channel has NO step (Go panics), classified
`rpanicking` (decidable, `rpanicking_dec`), NOT a silent re-close.  The deadlock theory is now
PANIC-AWARE: `rstuck_blocked` reads *stuck ⇒ done ∨ blocked ∨ panicking* (the three ways a live
goroutine fails to step — Go distinguishes deadlock from panic, and so do we); `ready_can_step` gains
`~ rpanicking`; `recvfree_progress` / `reachable_recvfree_progress` read *progress ∨ panic* (a
receive-free program never DEADLOCKS — its only non-step is a double-close panic).  Witnessed:
`rdouble_close_panicking` (a poised double-close IS panicking) and `rdouble_close_cant_step` (it
genuinely cannot step — the guard works; the operational image of `double_close_panics`).
**Operational SEND-on-closed = PANIC DONE too (2026-06-21):** `rstep_send` is now GUARDED by the same
`closedb tr c = false`; `rpanicking` gains a CSend disjunct (still decidable); a `closedb (rc_trace)
0 = false` invariant added to `SRShape` (the `sr` deadlock-free witness SENDS on 0 — its send never
panics, preserved because `sr` never closes 0).  Witnessed `rsend_closed_panicking` /
`rsend_closed_cant_step`.  So BOTH operational close- and send-on-closed are now faithful panics,
matching the IO model.  All zero-axiom.  *Remaining:* the full WORLD-level `select_recv2`↔`CSelect`
bridge (extend the Keystone `WMatchC` refinement to a select operation in the `World`).

### [Close](https://go.dev/ref/spec#Close) — ✓ panics; ⚠ nil
Spec: "Sending to or closing a **closed** channel causes a run-time panic.
Closing the **nil** channel also causes a run-time panic."  Ours:
`double_close_panics` is a **theorem**; close(nil) panic **✗** (nil channels, #16).

## Built-in functions

### [Built-in functions](https://go.dev/ref/spec#Built-in_functions) — ✓ import-free set; ✗ pointer/aliasing/complex-gated
Done: `len`, `cap`, `append`, `make` (chan/map ✓; **slice `make([]T,n)`** ✓ — fresh
zeroed slice, `len`=`n` a theorem), `delete`, `panic`, `print`/`println`, `recover`
(via `catch`/`with_defer`), `close`, and — Go 1.21 — **`min`/`max`** (on `int`
via `go_min`/`go_max`, and on the canonical full-width `int64`/`uint64` via
`i64_min`/`i64_max` [SIGNED order] / `u64_min`/`u64_max` [UNSIGNED order] — each
lowers to Go's `min(a,b)`/`max(a,b)`; machine-checked `spec_go_min`/`spec_go_max`,
`spec_i64_min`/`spec_i64_max`, and `spec_u64_max_high`/`spec_u64_min_high` — the
last two pin the UNSIGNED order at `2^64-1` where a signed order would disagree;
`minmax64_demo` prints `-2 1 18446744073709551615`; and on **`float`** via
`f64_min`/`f64_max` — faithful on the two IEEE corners Go's builtin handles: NaN
PROPAGATION (`f64_min_nan`/`f64_max_nan_b`: a NaN arg gives a NaN result) and
SIGNED ZERO (`f64_min_negzero`/`f64_max_poszero`: `min(-0,+0)=-0`, `max(-0,+0)=+0`),
which a naive `if a<b` gets wrong; `fminmax_demo` prints `+3.000000e+000
+5.000000e+000`) and **`clear`** (maps; empties the map, get-after-clear is a
theorem `map_get_clear`).  `builtins_demo` prints `3 5 / 3 / 0`.
**Deferred — gated on a non-import prerequisite (not difficulty):** `new` (returns
`*T` — needs the pointer type), `copy` (mutates `dst`'s backing array — needs the
slice-aliasing/mutation model, Tier 3 #8a), `make([]T,len,cap)` and slice-`clear`
(same aliasing model), `complex`/`real`/`imag` (need the `complex64`/`complex128`
types, unmodeled).  `min`/`max` on floats (NaN/`-0` corner cases) and strings follow
once those orderings are settled.

## The memory model

### [Go memory model](https://go.dev/ref/mem) — ✓ partial order + race freedom (axiom-free)
Spec: "sequenced before" and "synchronized before" are each a **partial order**
(the 2022-revised text says "partial order", NOT "strict"); happens-before is the
transitive closure of their union; a send is synchronized before the corresponding
receive **completes**; the kth receive on a cap-C channel is synchronized before the
(k+C)th send completes (C=0 = unbuffered rendezvous); a data race is two conflicting
accesses unordered by happens-before.
Ours (`Print Assumptions` = *Closed under the global context* — no axioms): `hb`
= transitive closure of exactly those edges; `hb_irrefl`+`hb_transitive` — we prove
the STRONGER **strict** partial order (irreflexive + transitive — the correct reading
for an order where no event happens-before itself; the spec's looser "partial order"
is implied by it); `hb_send_before_recv`, `hb_recv_before_send`,
`unbuffered_rendezvous`, `buffered_sender_runs_ahead` (no over-ordering);
`data_race`/`RaceFree`; `mp_no_race` + `mp_program_race_free`.  **All 4 channel rules
✓** + the **goroutine fork edge ✓** — every one a theorem, axiom-free (`Print
Assumptions` = *Closed under the global context*):
- rules 1/3/4 (send⤳recv-completion, kth-recv⤳(k+cap)th-send, unbuffered = cap 0):
  the open model `hb cap`.  **Operationally (2026-06-21):** the unbuffered (cap-0) HANDOFF is
  REPRESENTABLE in the rich `rstep` calculus with NO capacity field — `rendezvous_via_buffer`: a
  `rstep_send` immediately followed by the matching `rstep_recv` passes the value STRAIGHT from
  sender to receiver's continuation (`k2 v`) with the buffer returning to empty (the value never
  rests), the operational shadow of the cap-0 rendezvous edge.  Axiom-free; cascade-free (a derived
  two-step, not a new rule).  **FORCING now modelled (2026-06-21)** in the self-contained
  capacity-parameterised channel calculus (`Section BoundedChannels`, concurrency.v): `cstep_send` is
  GUARDED by `length (buf c) < cap c`, so a cap-0 channel can NEVER buffer — `cstep_cap0_buf` /
  `csteps_cap0_buf` prove its buffer is empty in every reachable state; transfer is forced through the
  synchronous `cstep_sync` rendezvous (`urv_can_sync`), and an unbuffered send with no waiting receiver
  is STUCK (`all_senders_stuck` / `ublock_stuck` — the blocking that the unguarded buffered model
  cannot express).  This is the genuine unbuffered semantics ("send blocks until a receiver"), not just
  the derived handoff.  Axiom-free.  **The capacity sub-model is now COMPLETE** — SAFETY:
  `cstep_cap_respected` / `csteps_cap_respected` / `csteps_from_empty_cap_respected` prove the buffer
  NEVER exceeds capacity (no overflow on any run); LIVENESS: `buffered_send_progresses` proves a send
  with room never blocks (capacity > length ⇒ progress) — the dual of `all_senders_stuck` (capacity 0
  ⇒ block), so both halves of Go's channel blocking are captured.  (Integrating `cap` into the full
  `rstep` — heap/spawn/select, an `rc_cap` field at ~42 `mkRCfg` sites — is the remaining cascade; the
  SEMANTICS is proven here.)
- **rule 2** (Phase 4a) — *"closing a channel is synchronized before a receive that
  returns zero because the channel is closed"*: the finite-stream model `hbc cap
  nsent` (sender sends `nsent` then closes; `hbc_close_before_zero_recv`: close ⤳
  `CRecvDone n` for `n ≥ nsent` ONLY).  Faithful: it does NOT order close before the
  value-receives (`close_not_before_value_recv`), proven via the conserved credit
  `ev_credit_c`, so no over-ordering; irreflexive via `ev_ts_c`.
- **fork edge** (Phase 4b) — *"a go statement is synchronized before the goroutine's
  execution starts"*: `fork_hb` + `fork_program_race_free` (parent writes `x`, spawns
  a child that reads `x` with NO channel — race-free purely by the fork edge).
  **Now GROUNDED IN EXECUTION** (concurrency.v, rich calculus): `rstep_spawn` emits BOTH
  the parent's `KSpawn` and the child's `KStart` (a two-event step), so `fork_exec_trace`
  RUNS `write 7; go (read 7)` and proves its trace EQUALS the once-hand-built
  `fork_handoff_trace`, with `fork_exec_race_free` deriving race-freedom from
  `reachable_owned_safe_r` — the fork synchronisation is a consequence of the operational
  semantics, not an assertion about a literal.  Both axiom-free.  ✓
- **channel handoff edge** (the primary go-mem mechanism) — *"a send on a channel happens-before
  the corresponding receive completes"*: `handoff_race_free` (hand-built) **+ now GROUNDED IN
  EXECUTION** (`chan_pub_exec_trace` / `chan_pub_exec_race_free`): a real 2-goroutine program where
  `main` SPAWNS the child, THEN writes loc 7 and sends — so the write happens AFTER the spawn and the
  fork edge canNOT publish it; only the channel send/recv can.  Running it emits a 6-event trace
  proven race-free via `transfer_orders` over the `KSend`/`KRecv` pair (the canonical "publish a
  write over a channel" idiom).  Axiom-free.  ✓  Both go-mem synchronisation edges are now grounded
  operationally, not just witnessed on literals.
- **closed-form race-freedom DISCIPLINE** — the per-trace witnesses are now subsumed by ONE checkable
  structural condition (`HandoffDisciplined`): every conflicting same-location pair is EITHER same
  goroutine (program order) OR a single `po`·`sync`·`po` handoff.  `handoff_disciplined_owned` proves
  it ⇒ `Owned` ⇒ race-free, UNIFYING the two bases — `locprivate_handoff_disciplined` (no-sharing) and
  `handoff_trace_disciplined` (the channel handoff, re-deriving `handoff_race_free`).  A program earns
  race-freedom by exhibiting the structure, not a bespoke `Owned` proof.  Axiom-free.  ✓
- **ABSTRACT OWNERSHIP-TRANSFER RACE-FREEDOM — the GENERAL theorem (2026-06-23), ✓.**  The above is
  trace-level; the per-PROGRAM results (`mp`/`fork`/`xfer`/`dst`) were each a hand-built phase
  enumeration (`MpReach`/…) that did not compose.  Now ONE abstract reachability invariant earns
  `Owned` for an *arbitrary* program by an `rstep` induction: `owned_step_snoc` (incremental `Owned` —
  appending an access preserves it given a single per-step hb obligation) ← `AcqConn`/`owned_step_by_owner`
  (a dynamic OWNER discharges that obligation: same-owner ⇒ program order, transferred-owner ⇒ the
  send/recv or spawn/start sync edge) ← `WTf flp`, a LINEAR region-threading typing (`WT` non-linear
  `OnlyAcc` cannot express transfer; `flp c v` = the location a send transfers, unifying pointer-handoff
  `flp c v = v`, signal-handoff a channel-fixed footprint, and spawn-split) ← `RegionInvF` + `BufLinF` +
  `OwnerLive` (single-valued ghost owner ⇒ disjointness free; buffer carries each in-transit location's
  hb-support; linearity ⇒ a recv pop leaves no duplicate) ← `region_inv_f_step` (every `rstep` preserves
  all of it) ← `region_inv_f_race_free`.  So **ALL THREE Go ownership-transfer mechanisms — pointer-handoff,
  spawn-split, signal-handoff — are race-free for arbitrary (no-spawn-typed-or-spawn) programs, ALL
  interleavings, under ONE theorem.**  Witnesses: `witness`/`relay` (pointer, multi-hop), `splitw`/`fork`
  (spawn-split), `sig` (signal/`mp_prog` idiom), `combo`/`fcombo` (cell traveling spawn→channel).
  SUBSUMPTION: `mp_subsumed_by_general` / `xfer_subsumed_by_general` re-prove the flagship bespoke
  witnesses as instances.  NON-VACUITY: `region_inv_rejects_race` — a genuine unsynchronised write/write
  program CANNOT satisfy the invariant (the discipline has teeth); `wt_rejects_unowned_*` (typing rejects
  un-owned access).  Everything **Closed under the global context — axiom-free AND funext-free**
  (`wt_region_ext` re-types continuations under pointwise-updated regions with no axiom).  IO-LIFT status:
  the channel fragment connects to EXTRACTABLE typed pointer/channel Go (`mp_g0_denotes`/`mp_end_to_end` +
  the subsumption); the spawn fragment cannot be lifted via `run_io` (`go_spawn` has no `run_io` law — the
  documented strategic fork; concurrency lives on `rstep`).  ✓ (abstract; the calculus↔emitted-Go step is
  the trust gap #10 / plugin, as everywhere).
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
**Calculus ↔ `run_io` bridge (`Section Keystone`/`KeystoneMulti`) — ✓ for the
channel+memory fragment.**  `Cmd` is the DEEP embedding of an IO program; `Denotes`
relates it to the `run_io` shallow term; `denote_sim_send`/`recv`/`write`/`read` show
each `rstep` run-reduces the denotation exactly per the `run_io` laws, and
`denote_adequate` composes them into a whole-program adequacy (single-channel,
single-goroutine).  For MULTIPLE goroutines — where `run_io`, being sequential, cannot
sequence the interleaving — the connection is a STATE refinement: `wmatchc_step` proves
every `rstep` (any goroutine, any channel) keeps the calculus's channel state matched to
the `run_io` `World`, using the two channel-SEPARATION (frame) LAWS
(`chan_buf_send_frame`/`chan_buf_recv_frame` — now THEOREMS, derived from
`chan_read_write_frame` over the concrete per-channel heap; once axioms, eliminated in the
108→0 work); `reachable_refines_and_safe` bundles this with the proven race-freedom on the
same execution.  Trust base verified by `Print Assumptions` (the authority — gated by the
Docker axiom-manifest gate; the `grep -cE '^Axiom |^Parameter ' *.v` = 0 is only a coarse
tripwire): the whole model is now AXIOM-FREE, so `Print Assumptions` of these keystone
results = *Closed under the global context* — the trust base is EMPTY (`PrimInt63`/`PrimFloat`
eliminated and the effect algebra made funext-free via observational equality); `Hret`/`chenv_inj`
are discharged hypotheses.
**Deadlock — characterized + freedom for a real class (axiom-free).**  The operational
semantics represents deadlock (`rblock_stuck`) and now CHARACTERIZES it (`rstuck_blocked`:
a stuck config has someone unfinished yet every live goroutine is finished or blocked on
an empty-channel receive — "all waiting to receive, no one sending"); and deadlock-FREEDOM
is PROVEN for RECEIVE-FREE programs (`reachable_recvfree_progress`: real concurrency via
spawn/send/write/read but no receive ⇒ every reachable state lets any unfinished goroutine
step).  Disciplined freedom for receiving programs (a session/no-circular-wait discipline)
is the remaining liveness frontier.
**Other "Synchronization" subsections of go.dev/ref/mem (honestly scoped):**
- **Initialization** (`init` ⤳ `main.main`; imported package's `init` ⤳ importer's):
  N/A — we emit a single `package main` with no imports and no user `init`, so there
  is no init-ordering edge to model.  ✗ (not applicable under the no-imports scope).
- **Goroutine destruction** — the spec MANDATES that a goroutine's exit is NOT
  synchronized before any event (deliberately **no** edge — "an aggressive compiler
  might delete the go statement").  We add only the fork edge and no exit edge, so the
  model is faithful BY OMISSION; ✓ (the absence is deliberate, matching the non-guarantee).
- **Locks (Mutex/RWMutex), Once, Atomic values** — need `sync`/`sync/atomic` stdlib
  imports → out of scope (imports on hold).  ✗ deferred.

**Still open (the honest formal gaps the model does NOT yet cover):**
- **The READ-OBSERVATION rule (Requirement 3 / the write-map `W(r)`, "visible") — the
  spec's CORE memory semantics — is ✗ unmodeled.**  We prove the race-freedom COROLLARY
  (`hb`-ordered ⇒ no race) but not *which* write a read observes: there is no `W(r)`, no
  "visible write" (`w` hb `r`, and `w` hb no other write to `x` that hb `r`).  So the
  guarantee proven is "races are absent under the ownership discipline", not "a read
  returns the latest hb-preceding write" — the spec's actual definition of memory.
- **Implementation Restrictions (no-out-of-thin-air; word-tearing of multi-word
  interface/slice/map/string headers) — ✗ unmodeled.**  These are bounded-race
  guarantees for *racy* programs; we reason only about race-FREE programs, so they are
  out of the modeled fragment (tracked).
- **`sequenced before` is modeled as a TOTAL per-goroutine order** (same goroutine,
  earlier trace position), STRONGER than the spec's *partial* sequenced-before (which
  inherits the language spec's evaluation-order, leaving some intra-goroutine operations
  unordered).  Sound for the straight-line traces we generate; a faithful partial
  sequenced-before is a tracked refinement.
- the heap analogue of the frame law (ref separation, to mix memory + channels under
  interleaving); the FIFO refinement (kth recv ↔ kth send pairing); disciplined
  deadlock-freedom for receiving programs; and the unverified plugin lowering
  (`Cmd` ↔ extracted Go).

## Bounds-panic payload (2026-07-02)

`rt_index_oob i n` now renders Go's EXACT runtime payload (verified against gc 1.23 via `go run`):
a non-negative out-of-range index yields `runtime error: index out of range [i] with length n`; a
NEGATIVE index yields `runtime error: index out of range [i]` with NO length part.  Digits via the
model's own `Z_dec_string` (proof-side only — the digit chain is suppressed at extraction; emitted Go
panics natively).  Consumers: `slice_get`/`slice_idx_get`/`slice_idx_set` and GoSem's runtime-index
denotation (tier R2) — one payload authority, no collapsed class-wide value.
