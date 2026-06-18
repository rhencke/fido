# Go spec conformance ledger

Tracks our model against the **Go language spec** (go.dev/ref/spec) and the **Go
memory model** (go.dev/ref/mem), **in spec document order** — top to bottom, one
section at a time.  Our Rocq is meant to follow this order too, so each spec
section maps to a region of the model.  Each entry: the spec rule (the SOURCE of
our behavior, cited), our model, status, and the machine-checked witness.

**The entire model is AXIOM-FREE.**  `grep -cE '^Axiom |^Parameter ' *.v` = 0
across `builtins.v`/`main.v`/`concurrency.v`/`preamble.v`; no `Admitted`.  So every
✓ below rests on a `Definition`/`Theorem` over a CONCRETE model (the `World` is a
concrete record of typed heaps), and `Print Assumptions` of any result reports only
the named external boundaries — Coq's kernel `PrimInt63`/`PrimFloat` primitives and
stdlib `functional_extensionality` (the 108→0 axiom elimination).  Conformance
witnesses that used to rest on a `run_io`/channel/map *axiom interface* now rest on
the proven laws of that concrete model.

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
implicit path is an untyped constant" (`u8_lit : int -> GoU8`).  ✓  *Remaining:*
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
`Sint63` `int` (⚠ ±2⁶², Tier 2 #4) COEXISTS (→ Go `int64`) as a bounded convenience for
indices / `nat`-coding / small-value demos — faithful in range; use `GoI64`/`GoU64` for
the full width.
**`u32_mul`/`i32_mul` ✓** (mask-after-multiply: the product may exceed the 63-bit
carrier but the masked LOW 32 bits are exact since 2³²∣2⁶³ —
`spec_u32_mul_wrap`/`spec_i32_mul_wrap`); **`uint64` (full width) ✓ — `GoU64`** (same Z
template, unsigned mod-2⁶⁴ wrap; `spec_u64_add_wrap`/`sub_wrap`/`not`/`shr`/`beyond63`,
axiom-free; emits Go `uint64`, unsigned literals via `%Lu`, sign-aware even for erased
literals); `float32` **✗** (no native Rocq
f32).  Note: distinctness makes explicit
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

### [Struct types](https://go.dev/ref/spec#Struct_types) — ✓ value-struct (named fields); ✗ embedding/tags
Spec: a `struct` is a sequence of named fields with types; **value** semantics
(assign/pass copies every field).  A Rocq `Record` is exactly this — a single-
constructor inductive with projections, value/copy semantics — so it maps directly:
the type → `type T struct { … }`, the constructor → a struct literal `T{…}` (fields
in declaration order), each projection → field access `x.Field`.  Field types are
printed by the general `pp_type`, so they are not hardcoded — `point_demo`'s `int`
fields lower to `int64`, `labeled_demo` mixes a `bool` and an `int` field
(`Flag bool` / `Qty int64`).  The projection *definitions* are suppressed (field
access replaces them).  Struct INVARIANTS are provable in Rocq directly:
`point_proj_px` machine-checks `px (MkPoint a b) = a`.  Witnesses: `point_demo`
(`Point{3,4}` → `3 / 4 / 7`), `labeled_demo` (`Labeled{true,5}` → `true / 5`).
✗ not yet: embedded (anonymous) fields + field promotion, struct tags.  Comparability
(`==` field-wise) awaits the same operator work as other composite equality.
Methods declared on the struct → next section.

### [Method declarations](https://go.dev/ref/spec#Method_declarations) — ✓ value receiver; ✗ pointer receiver
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
`io_method_demo` (`func (p Point) Describe()` → `8/9`).  ✗ not yet: pointer receivers
(`func (r *T) M()` — needs the pointer/aliasing model, Tier 3 #8a), method values/
expressions (`recv.M`, `T.M` as first-class), and `Module`-namespaced method names.

### [Interface types](https://go.dev/ref/spec#Interface_types) — ⚠ vtable-struct dictionary (≥2 methods); ✗ 1-method/`interface` keyword
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
✗ not yet: a SINGLE-method interface (Coq unboxes a 1-field record `{m}` ≡ `m`, so it
needs curried-return lowering — currently leaks the inner lambda, fails `go build`,
tracked), nullary (unit-thunk) methods (need unit-arg erasure), embedding, and the
native `interface` keyword with structural satisfaction.

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
from our per-op-rounded value.  `float32` **✗** (no native Rocq f32).

### [Comparison operators](https://go.dev/ref/spec#Comparison_operators) — ✓ conforms
Spec: integers "in the usual way", floats "as defined by IEEE 754", bools equal
iff both true/both false.  Ours (int): SIGNED `ltsb`/`lesb` → Go signed `</<=`;
unsigned `PrimInt63.ltb`/`leb` **rejected** for `int` (disagree on high bit) —
`ltb_unsigned_neg_false`/`ltb_signed_neg_true`.  (float): `PrimFloat.ltb`/`leb`/
`eqb`, IEEE incl. NaN unordered — `nan_eqb_false`, `nan_ltb_false`.  (string):
`str_eqb` → Go `==` (byte equality), `str_ltb` → Go `<` (lexicographic by byte
value) — both theorems (see String types).  ✓
(`> >= !=` via swap / `negb(eqb…)` — tidiness gap, not conformance.)

### [Logical operators](https://go.dev/ref/spec#Logical_operators) — ✓ conforms
Spec: `p && q` = "if p then q else false", `p || q` = "if p then true else q",
`!p` = "not p"; short-circuit.  Ours: `andb`/`orb`/`negb` → `&&`/`||`/`!`, and
Coq's `andb` IS that definition — `spec_andb`/`spec_orb`/`spec_negb` by
`reflexivity`.  Short-circuit unobservable (pure total bools).  ✓

### [Conversions](https://go.dev/ref/spec#Conversions) — ✓ integer↔integer (fixed-width + int64↔uint64); ✗ float, strings, interfaces
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
**Full-width `int64`↔`uint64` — ✓ (2026-06-18).**  `u64_of_i64`/`i64_of_u64` are Go's
`uint64(x)`/`int64(x)`: a two's-complement REINTERPRET of the 64-bit pattern, EXACT (no
rounding).  The Z carrier re-normalises mod 2⁶⁴ (`MkU64 (wrapU64 (i64raw a))` /
`MkI64 (wrap64 (u64raw a))`), faithful by `wrap64_wrapU64` (the int64 and uint64
normalisers agree mod 2⁶⁴ — axiom-free).  Distinct from the narrow widths (which erase
to int64, so widen = identity) because `GoU64` lowers to a real Go `uint64`.  Emitted as
a small NAMED function `func U64_of_i64(a int64) uint64 { return uint64(a) }` so the cast
applies to the parameter VARIABLE — Go rejects `uint64(-1)` on an untyped CONSTANT but
accepts it on an int64-typed value.  Machine-checked `conv_u64_of_neg1` (`-1 → 2⁶⁴-1`),
`conv_i64_of_max` (`2⁶⁴-1 → -1`), `conv_roundtrip`; `conv64_demo` prints
`18446744073709551615 -1 255`.
**Still ✗ (fails loud):** `int↔float` and `float↔float` (ties to the float gaps /
no native f32); `string`↔`[]byte`/`[]rune` (the rune view, deferred); narrow↔
`{int64,uint64}` (same reinterpret template, pending); interface conversions beyond
`type_assert`.

## Expressions — primary

### [Index expressions](https://go.dev/ref/spec#Index_expressions) — ✓ slices/strings/maps (single-goroutine)
Spec: `a[x]` indexes; an out-of-range slice/string index PANICS; a map index `m[k]`
never panics (`v, ok := m[k]`).  Ours: `slice_get` (raw, OOB ⇒ panic, escape hatch)
and the safe `slice_at_ok`/`str_at_ok` (CPS/comma-ok — FORCE handling OOB, cannot
panic, signed-index both-ends check) → `xs[i]`/`int64(s[i])`; map `m[k]` via the
comma-ok `map_get_opt`/`map_get_or` → Go's two-value lookup.  ✓ (the panicking form
is proof-gated where range is statically known; aliasing of a sub-slice unmodeled,
Tier 3 #8a).

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
no shadowing — is part of the control-flow lowering below; pointers/`&x` ✗, Tier 3 #8a.)

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
  (`foreach_demo`, `sum_demo`).  ✓
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

### [Defer statements](https://go.dev/ref/spec#Defer_statements) — ✓
Spec: `defer f()` runs `f` at function return (LIFO), on both normal and panic exit.
Ours: `defer_call f` → `defer func(){ f }()` (function-scoped, LIFO, run-at-return — Go
provides the scoping/ordering); the block-scoped `with_defer` (IIFE + `defer`) coexists.
Demos: `defer_demo`, `defer_loop_demo` (a `defer` in a loop captures each iteration's
value — prints 2,1,0, not 2,2,2).  ✓

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
same execution.  Trust base verified by `Print Assumptions`: the whole model is now
AXIOM-FREE (`grep -cE '^Axiom |^Parameter ' *.v` = 0), so `Print Assumptions` of these
keystone results = *Closed under the global context* modulo Coq's kernel primitives
(`PrimInt63`/`PrimFloat`) and stdlib `functional_extensionality`; `Hret`/`chenv_inj` are
discharged hypotheses.
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
