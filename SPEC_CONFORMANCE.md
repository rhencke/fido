# Go spec conformance ledger

Tracks our model against the **Go language spec** (go.dev/ref/spec) and the **Go
memory model** (go.dev/ref/mem), **in spec document order** — top to bottom, one
section at a time.  Our Rocq is meant to follow this order too, so each spec
section maps to a region of the model.  Each entry: the spec rule (the SOURCE of
our behavior, cited), our model, status, and the machine-checked witness.

**Trust base (honest ledger).**  NO project-declared axioms; every GATED `Print
Assumptions` surface (the manifest / printer / emit flows — PROGRESS.md "Current gates")
is asserted EMPTY non-bypassably in the Docker prover stage; the source grep is only a
coarse tripwire.  The model is `Definition`s/`Theorem`s over CONCRETE data (integers `Z`,
locations `nat`, floats `spec_float` — the old `PrimInt63`/`PrimFloat` kernel substrate
is eliminated), and the IO/effect algebra is funext-free (observational equality
`io_eq`, proved pointwise).  Stdlib `functional_extensionality` survives at exactly TWO
NAMED, NON-GATED families: `run_io_inj` (the Keystone `Denotes` bridge, which rewrites
IO terms structurally) and `unified.v`'s rstep-embedding lemmas (`rstep_embeds` — see
its header note).  A per-section "Closed under the global context" claim below means
THAT family's own `Print Assumptions`, not a blanket statement.

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

## Open-items index (details live in each section — this is only a pointer list)

Genuinely open: FMA fusion (bounded deviation — Floating-point operators); a position
polymorphic over a SYMBOLIC array size (Array types); struct tags / embedding bare
primitives (Struct types); the `interface` keyword surface (we emit dict-structs — a
deviation, not a gap; Interface types); the concurrency guarantee's remaining gaps
(Go memory model "Still open").  **Generics:** type-parameter functions with the
`comparable` constraint are ✓ (witness erasure → `[K comparable]`, native `==`).

---

## Lexical elements

### [Integer literals](https://go.dev/ref/spec#Integer_literals) / [Floating-point literals](https://go.dev/ref/spec#Floating-point_literals) — ⚠ (typed/fixed-width view)
Spec: literals are *untyped constants* (see Constants).  Ours: written as the typed,
fixed-width runtime view over the `Z`-carried records (`GoInt`/`GoI64`/… — proof-carrying
literals).  The lexical shapes (decimal, sign) round-trip (`neglit_demo`); the
untyped/arbitrary-precision layer is modeled in **Constants**.

## Constants

### [Constants](https://go.dev/ref/spec#Constants) / [Constant expressions](https://go.dev/ref/spec#Constant_expressions) — ✓ representability + arbitrary-precision INTEGER + exact-rational FLOAT (`FConst`); ⚠ the GATE's float subset is dyadic
Spec: numeric constants are exact, arbitrary precision, never overflow; a constant
acquires a type at use where non-representability is a COMPILE error; constant float
arithmetic rounds once at the typed boundary.
Ours:
- **Representability airtight for the fixed widths:** `u8_lit`…`i16_lit` DEMAND a proof
  the constant fits (discharged `eq_refl` in range), so an out-of-range constant is
  UNREPRESENTABLE — exactly "constant overflows uint8", never a silent wrap
  (`u8_const_oob`…`i16_const_oob` `Fail` tests). The proof erases; Go unchanged.
- **ALL 8 WRAPPERS SEALED against constructor forging** (`MkU8 300`, `MkI64 (2^63)` are
  UNCONSTRUCTABLE): each wrapper carries an SProp invariant — range-bound for the
  unsigned masks (`Squash (uNraw <? 2^N)`), provenance "in the image of norm" for the
  signed sign-extends, Z-range (`in_i64`/`in_u64`) for the 64-bit pair — with every op
  routed through its `*wrap` normalizer and a `*_forged` `Fail` test per type. SProp
  gives definitional proof irrelevance (no axiom); the fields erase, extraction
  byte-identical; value witnesses use `reflexivity` (the kernel decides SProp
  irrelevance, not the VM).
- **Arbitrary-precision INTEGER constants ✓:** `i64c`/`u64c` `vm_compute`-evaluate a
  closed `Z` constant expression at ELABORATION (an intermediate like `1<<70` may
  exceed the target), then convert demanding `in_i64`/`in_u64` — out-of-range FAILS to
  elaborate. Witnesses `const_intermediate_exceeds`/`const_exact_arith`/
  `const_u64_upper` + `const_oob_*` `Fail`s; no plugin change.
- **Float constants — TWO scoped paths, do not conflate:** the LIVE constant path is
  `FConst` — an exact rational `num/den` with EXACT `fc_add`/`fc_sub`/`fc_mul` and
  `f64_of_fconst`/`f32_of_fconst` rounding exactly ONCE via `SFdiv` on exact-integer
  spec_floats (the MODEL is correct for all num/den; ±Inf/NaN unconstructable — the
  denominator is a `positive`).  The PLUGIN FOLD is bounded to int64
  endpoints/intermediates with CHECKED literal parsing — a magnitude beyond int64
  declines the fold and extraction fails loud (`neg_fconst_overflow.v`), never a
  silently wrong rational.  SEPARATELY, the GoTypes/GoSafe checker subset is DYADIC
  exact-or-reject (`m·2^e`; a rounding case like `float64(1)/float64(3)` is valid Go
  that the GATE rejects — quarantined incompleteness, never a wrong value).
- *Remaining:* the narrow `_lit`s take an `int` argument (narrow constant arithmetic
  routes through the bounded carrier; low priority).

### [Boolean types](https://go.dev/ref/spec#Boolean_types) — ✓
Spec: `bool`; comparable; values `true`/`false`.  Ours: Coq `bool` → Go `bool`.
(Comparison: see Comparison operators.)  ✓

### [Numeric types](https://go.dev/ref/spec#Numeric_types) — ✓ ranges/two's-complement/distinctness; ⚠ `int` width
Spec: exact ranges for `uint8…uint64`/`int8…int64`; n-bit two's complement;
`byte`=`uint8`, `rune`=`int32`; `int`/`uint` are 32-or-64-bit; all numeric types are
DISTINCT (explicit conversions required).
Ours:
- Sub-64 widths (`uint8…int32`) are each their OWN Rocq record (wrapper erased),
  modeled mask + two's-complement sign-extend across add/sub, comparison, bitwise,
  shift, div/mod, conversions (`i8_add_wraps`, `spec_i32_add_wrap`,
  `spec_u32_mul_wrap` — the masked low 32 bits of a 63-bit product are exact since
  2³²∣2⁶³).
- **DISTINCTNESS by construction**: Rocq rejects mixing (build-checked
  `u8_no_implicit`…`u8_u16_no_mix`); the only implicit path is an untyped constant.
  Runtime type identity: every tag lowers to a DISTINCT Go type, `int` vs `int64`
  included — `int_vs_int64_distinct` + the injectivity lock `tag_runtime_agrees`.
- **`int64`/`uint64` full width ✓ — `GoI64`/`GoU64`**, `Z`-carried, faithful across the
  whole range, wrapping at the true 2⁶³/2⁶⁴: wrap witnesses
  (`spec_i64_add_wrap`/`sub`/`mul`/`beyond62`, `spec_u64_*`), truncating div/mod
  (`Z.quot`/`Z.rem`; MININT/−1 wraps), bitwise, `<<` wraps / `>>` arithmetic
  (`spec_i64_shr_arith`); div and shift are evidence-carrying
  (`i64_div_zero`/`i64_shl_neg` Fail). Range-checked `%i64`/`%u64` literal notations
  (out-of-range = parse error = Go's untyped-constant overflow); map-key comparability;
  end-to-end chan+map pipeline demos golden-locked. ⚠ ONE bounded caveat: a CONSTANT
  `MAX+1` in emitted Go trips Go's compile-time untyped-constant check instead of the
  modeled runtime wrap (the Constants-section gap, not an int64 defect).
- **Platform `int`/`uint` (`GoInt`/`GoUint`) — deviation CLOSED:** distinct `Z`-carried
  records rendered Go `int`/`uint`, faithful across `[−2⁶³,2⁶³)` / `[0,2⁶⁴)` with
  proof-carrying literals (`int_lit`/`uint_lit`); the `MININT/−1` corner wraps the true
  int64 value. The ONLY residual platform assumption is the 64-bit WIDTH choice (spec
  allows 32-or-64), not a carrier deviation. Golden byte-identical.
- ⚠ UNIFORMITY RESIDUAL (faithful, follow-up): sub-64 narrows and `SliceH` INDEX args
  still ride the int63 carrier — faithful there (sub-63 values / indices never reach
  2⁶²); internal heap LOCATION handles are not Go `int` values.

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
offsets are the prefix sums of the CONSUMED source widths — the encoded rune width for valid
UTF-8, ONE byte per invalid unit (U+FFFD), machine-checked `str_range_offsets`
(`A 中 B → 0 1 4`) and `str_range_invalid_offsets` — matching Go exactly. ✓
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

### [Struct types](https://go.dev/ref/spec#Struct_types) — ✓ value-struct + EMBEDDING (struct/interface/pointer — field/method promotion); ⚠ tags; ✗ embedding bare primitives
Spec: a struct is a sequence of named fields; VALUE semantics (assign/pass copies).
- A Rocq `Record` maps directly: type → `type T struct{…}`, constructor → a KEYED
  literal `T{Field: v, …}` (field names from the projections, recursively), projection →
  `x.Field` (projection definitions suppressed). Field types via the general `pp_type`.
  Invariants provable in Rocq (`point_proj_px`). Witnesses `point_demo`, `labeled_demo`.
- **Embedding ✓:** a field whose exported name equals its record type's name is emitted
  ANONYMOUS, so Go genuinely promotes the embedded method set; access emits the PROMOTED
  shorthand via the `peel_embedded` peephole (compiles only because Go promotes —
  genuinely exercised; Coq projection names are unique, so no shadowing). The embedded
  type needs ≥2 fields (1-field records unbox). `embed_demo` (incl. the `embed_arith`
  selector-bridge regression fixture, pinned by the Makefile gate). An INTERFACE
  (its dictionary struct) embeds the same way (`embed_iface_in_struct_demo`,
  `promoted_greet`).
- **POINTER embedding ✓:** a `GSPtr T` field named after the BASE record → anonymous
  `*T` field; promotion THROUGH the pointer (`node_embed_demo` — `nd.Cell_incx()`, not
  `nd.Cell.Cell_incx()`).
- **RECURSIVE structs ✓:** `Inductive ListNode := … ln_next : Ptr ListNode` (recursion
  through the tag-free phantom `Ptr` is vacuously positive); a FINITE nullary nominal
  tag (`TListNode`) round-trips `tag_eq`; `linked_list_demo` heap-allocates and
  traverses → `1 2 3`, golden-locked. ⚠ each named recursive type needs its own tag
  ctor in GoRuntimeTypes.v (auto-tagging needs a named-type registry — deferred).
- ✗ not yet: embedding a bare PRIMITIVE (no methods to promote — niche); struct tags
  (no-op without reflection).

### [Method declarations](https://go.dev/ref/spec#Method_declarations) — ✓ value + pointer receiver, method values; method expressions CONCRETE receivers only
Spec: a method binds a function to a receiver of a defined type; the call is `recv.M(args)`.
- **Eligibility (ONE authority, `method_eligible`, shared by declaration + call sites):**
  first visible parameter a record type; the receiver's type args distinct type
  VARIABLES; every remaining signature tvar receiver-carried (Go methods add no type
  params of their own); no comparable witness. An ineligible record-first function stays
  a plain (possibly generic) function (witness `box_second`, golden). Projections and
  inlined refs excluded.
- **Faithful:** a value receiver gets a COPY and structs are value types, so `recv.M(a)`
  denotes exactly `M(recv, a)` (same de Bruijn binding). Behaviour provable in Rocq
  (`shifted_px`). Witnesses: `method_demo`, `io_method_demo`.
- **POINTER receivers ✓:** an eligible `GSPtr R` first param → `func (r *T) M()` that
  MUTATES the receiver, observed by the caller (`cell_incx`, `cell3_inc_z`,
  heterogeneous `pair_bump`).
- **Method VALUES** (`p.M` closure — `method_value_demo`) and **method EXPRESSIONS**
  (`T.M` — `method_expr_demo`, pointer form `(*T).M` — `ptr_method_expr_demo`) work for
  CONCRETE receivers only; a GENERIC-receiver method used bare is REJECTED at extraction
  (`neg_method_expr_generic` — Go's `T.M` needs an instantiation the erased type does
  not carry).
- **DEFINED TYPES over a primitive with methods ✓:** `type MyT <prim>` modeled as a
  2-field record with a `GoTypeTag` PHANTOM (kept by extraction, so the single value
  field does not unbox — what keeps the type a distinct receiver); emitted `type MyI64
  int64` with cast ctor/projection. Generic over the underlying: string
  (`deftype_str_demo`), interface satisfaction via the dictionary
  (`deftype_iface_demo`), NAMED FUNC types with called-through casts
  (`named_func_demo`), slice underlyings (`deftype_slice_demo`), map underlyings with an
  IO-value method (`gmap_deftype_demo`). All golden-locked.

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
int64 { x, y := g(); return x + y }` was a fail-closed gap (pre-dating
the N-ary work); now handled (`pure_destr_demo` → `7 6 5`: `sum_pair` 2-ary + `sum3` N-ary, golden-locked).
A WILDCARD binder `let '(_, y) := …` (Coq extracts the `_` as an unused gensym, which left as a real
`:=` binder is invalid Go — `declared and not used`) is blanked to Go `_` via `pp_destr_binder`/`dbn_free`
(`snd_of`, `stmt_blank_demo`) — both positions; this fixed a fail-OPEN the pure-position fix had exposed.
A NARROW component — `func(…) (uint8, uint8)` — is cast to its return slot (`return uint8(…), uint8(…)`)
via `value_narrow_conv`; without it the int64-carrier values were returned into uint8 slots = invalid Go
(another fail-OPEN of the same class; `narrow_pair_demo` → `44 7`, go-vet-clean, golden-locked).

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
Two slice views: the functional `GoSlice = list` (value/immutable) AND the heap-backed
mutable **`SliceH`** (`{base; off; len; cap; tag}` — a real view into a shared backing
array), all extracted + golden-locked: in-place `s[i]=v`, `s[a:b]` SHARING the backing,
the aliasing THEOREM `subslice_alias` + its separation complement `slice_idx_set_frame`,
`append`'s in-cap-aliases-vs-past-cap-reallocates (`slice_append_incap_aliases`),
`make([]T,len,cap)`, `clear`/`copy`. Maps via a heap in the world (get-after-write are
theorems); channels via world state. *Still ⚠:* cross-goroutine aliasing rides the
concurrency calculus, not this functional layer.
**Pointer↔calculus bridge:** `Section KeystonePtr` ties the EXTRACTABLE `ptr_set`/
`ptr_get` to the operational `rstep_write`/`rstep_read` (`ptr_write_sim`/`ptr_read_sim`
— the derefs ARE the bridge's ref-accesses), so calculus locations are genuine `*T`
cells. The message-passing flagship composes end-to-end as **`mp_end_to_end`**: the
extractable typed pointer-handoff program (a) executes to `mp_trace` (`mp_exec_trace`),
(b) is race-free on this run and EVERY interleaving (`mp_all_interleavings_race_free`),
(c) each goroutine the Keystone-denotation of real typed IO (`mp_g0_denotes`/
`mp_g1_denotes`), (d) full state realized by one `run_io` world (`wstate_steps`),
(e) delivering exactly `(inj v1, inj v0)` (`mp_handoff_delivers`). Assumptions = the
documented funext holdout (`run_io_inj`); no Fido axiom. (N-goroutine generality is
`reachable_owned_safe_r`; `mp_end_to_end` is the concrete closed instance — `go_spawn`
has no whole-program `run_io` law, so cross-goroutine glue stays the STATE refinement.)
**SELF-REFERENTIAL channel type ✓:** `ChanBox` (`{ cb_id; cb_chan : GoChan ChanBox }` —
recursion through the tag-free phantom is vacuously positive; nominal tag `TChanBox`):
a channel carrying values that contain the channel's own type. `chanbox_demo` → `42`;
read-after-write at `chan ChanBox` proven. Stronger than `chan_of_chan_demo`'s
`chan chan int64`.

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
width (`(^x)&0xff → 15`).  **`int` bitwise/shifts:** the MODEL has them over the
Z-carried `GoInt` (`int_and`/`int_shl`/… — GoSem tier R8 denotes them); the PLUGIN does
not emit them yet (✗ plugin-side only).  **Bitwise ALGEBRA (`GoU64`) proven (2026-06-21,
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
for signed — `-3>>1=-2` (toward **−∞**, the model's arithmetic shift), DISTINCT from `-3/2=-1`
(toward zero), and `-1>>3=-1` (not 0).  `>>` is logical for `uintN` (`lsr`, the
non-negative carrier) and arithmetic for `intN` (`asr`, sign-extended).  Plugin emits
Go `x<<k` / `x>>k`.  **Plugin `int` shifts: ✗** (not plugin-emitted; the MODEL's `int`
shifts + bitwise exist and DENOTE — GoSem tier R8, `int_shl`/`int_shr`/`int_and`… over
the Z-carried `GoInt`).  GATE count rule: Go requires an UNTYPED constant count
representable by `uint`; the classifier enforces the conservative platform-`uint`
window (`untyped_count_overflow`, 32-bit-safe — a typed const count is bounded by its
own width instead), and GoSem saturates counts ≥ 64 (exact for ≤64-bit carriers).

### [Integer operators](https://go.dev/ref/spec#Integer_operators) — ✓ conforms
`q=x/y`, `r=x%y`: `x=q*y+r`, `|r|<|y|`, **truncated toward zero**; the example
table; the most-negative exception `x/-1 = x`, `x%-1 = 0` (two's-complement, no
panic); zero divisor ⇒ run-time panic (constant zero ⇒ compile error).
Ours: `int_div`/`int_mod` over the Z-carried `GoInt` — truncating `Z.quot`/`Z.rem`
with an evidence-carried nonzero divisor (panic unreachable).  Witnesses:
`spec_div_5_3 … spec_mod_n5_n3` (full table) + the `x/-1` exception wrapping the TRUE
int64 most-negative (see Numeric types).  ✓

### [Integer overflow](https://go.dev/ref/spec#Integer_overflow) — ✓ unsigned; ⚠ signed boundary
Spec: unsigned `+ - * <<` = **mod 2ⁿ**; signed `+ - * / <<` overflow is
deterministic two's-complement, no panic.
Ours (unsigned): `uintN` mask = mod 2ⁿ — `u8_add_wraps` (300→44), `u8_mul_wraps`
(65025→1), `u8_sub_wraps` (0-1→255), `u16_mul_wraps`.  ✓  (signed): `intN`
two's-complement — `i8_add_wraps` (-106), `i16_add_wraps` (-25536).  Full-width
`int64`/`uint64` wrap at the TRUE 2⁶³/2⁶⁴ via `GoI64`/`GoU64` (`spec_i64_add_wrap`,
`spec_u64_add_wrap`) — the canonical int model; platform `int`/`uint` are the same
Z-carried shape (deviation closed — see Numeric types).  32-bit multiply ✓
(`spec_u32_mul_wrap`/`spec_i32_mul_wrap`, mask keeps the exact low 32 bits).

### [Floating-point operators](https://go.dev/ref/spec#Floating-point_operators) — ✓ ops; ⚠ FMA fusion
Spec: IEEE semantics; div-by-zero implementation-specific whether it panics; an
implementation MAY fuse ops (FMA); an explicit conversion rounds and prevents fusion.
- `float64` = IEEE binary64: `+ - * /`, `opp`, comparisons lower to Go natives; float
  `/` unguarded (±Inf/NaN, no panic) — conforms (`float_demo`, `float_opp_demo`).
  **⚠ deviation:** we round EACH op; Go MAY fuse `a*b+c` (bounded — Go does not
  guarantee fusion).
- **`float32` ✓ & SOUND** (faithful binary32 via SpecFloat; arithmetic, comparisons,
  `-`, `min`/`max` → native Go `float32` ops). `GoFloat32` is an abstract
  smart-constructor type carrying an unforgeable `exists a, carrier = f32_round a`
  proof — a non-representable literal cannot be injected. NaN/signed-zero corners
  machine-checked (NaN propagates; `min(-0,+0) = -0`, `max(-0,+0) = +0`).
- **Conversions:** `float32↔float64` widen-exact + truncations ✓; overflow → `+Inf`
  (`f32_overflow`), underflow → `0` (`f32_underflow`). ⚠ INT→float32 through binary64 is
  NOT double-rounding-innocuous for `|x| > 2^53` (gc-reproduced distinguishing witness),
  so DIRECT conversions `f32_of_i64`/`f32_of_u64`/`f32_of_int` round the exact integer
  ONCE (`binary_normalize 24 128`), lowered to Go's `float32(x)`; machine-checked
  `f32_of_i64_differs`/`_direct`/`_viaf64`. The constant path `f32_of_fconst` rounds the
  exact rational once via `SFdiv 24 128` (correct for ALL num/den;
  `f32_of_fconst_differs`/`_small`; `f32_fconst_demo` → `0.3`).
- **Constant-vs-runtime soundness (float32 AND float64):** Go constant expressions
  cannot denote −0/±Inf/NaN (constant `/0` / overflow are COMPILE errors), so a float op
  whose operands are not runtime variables is FORCED to runtime via a typed IIFE;
  runtime-operand ops stay idiomatic. Value-preserving;
  `f32_const_runtime_demo` → `+Inf −Inf +Inf +Inf` machine-checked vs the model.
- **⚠ Deferred (bounded):** `math.Float32bits`/`frombits` needs the `math` import AND
  SpecFloat carries no NaN payload — bit-exact NaN round-tripping out of scope until
  both are addressed.

### [Comparison operators](https://go.dev/ref/spec#Comparison_operators) — ✓ conforms
Spec: integers "in the usual way", floats "as defined by IEEE 754", bools equal
iff both true/both false.  Ours (int): SIGNED Z-compare → Go signed `</<=`
(an unsigned-order comparison on signed `int` is rejected — the historical
high-bit disagreement class).  (float): `spec_float` comparisons, IEEE incl. NaN
unordered — `nan_eqb_false`, `nan_ltb_false`.  (string):
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

### [Conversions](https://go.dev/ref/spec#Conversions) — ✓ integer↔integer (all widths), int/int64→float64, float64→int64, float64↔float32, narrow↔float32, string↔[]byte/[]rune + string(rune); ✗ interface conversions beyond `type_assert`
Spec: integer conversions truncate to the result type's size.
- **Among `{int, uint8…int32}` ✓:** routed through the `int` carrier — `int_of_FW`
  widens (emitted as a REAL cast `int(x)`, not identity: a narrow Go value at an `int`
  boundary needs it), `FW_of_int` narrows (mask / mask+sign-extend — a conversion
  truncates, never rejects). Cross-width by composition. Implicit mixing rejected
  (`*_no_implicit` `Fail`s). Machine-checked `spec_u8_of_int_trunc`…
  `spec_i16_of_u8_cross`; `convert_demo` golden.
- **`int64`↔`uint64` ✓:** two's-complement REINTERPRET, exact; faithful by
  `wrap64_wrapU64`. Emitted as a named `func U64_of_i64(a int64) uint64 { return
  uint64(a) }` — the cast must apply to a VARIABLE (Go rejects `uint64(-1)` on an
  untyped constant). `conv_u64_of_neg1`/`conv_i64_of_max`/`conv_roundtrip`;
  `conv64_demo` golden.
- **Narrow→`int64` widening ✓:** value-preserving (`widen_*` witnesses), lowered by
  name-recognition to `int64(x)` — NOT identity (the narrow-boundary invalid-Go class);
  the carrier body is suppressed. Narrow↔`uint64` and `int64`→narrow truncations ✓
  (via the 64-bit hubs; golden-locked).
- **`int`/`int64`→`float64` ✓:** native `float64(x)` (exact for `|x| < 2^53`),
  machine-checked sign-split; recognized → cast, body suppressed.
- **`float64`→`int64` ✓:** truncation toward zero via the verified `Prim2SF`
  decomposition (`i64_of_f64_pos`/`_neg`/`_exact`/`_zero`/`_big`), lowered to native
  `int64(f)`. Bounded deviation at NaN/±Inf/overflow (impl-defined in Go; the native
  cast gets Go's behavior).
- string↔[]byte/[]rune, string(rune): see String types. **Still ✗ (fails loud):**
  interface conversions beyond `type_assert`.

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

### [Short variable declarations](https://go.dev/ref/spec#Short_variable_declarations) — AST gate (GoSafe `supported_program`): ✓ core rules; ⚠ named narrowings
Spec: `x := e` declares and initializes; redeclaring in the same block / a lone blank LHS
is "no new variables on left side of :="; `x := nil` is "use of untyped nil"; an unused
local is "declared and not used" (a COMPILE error); predeclared identifiers are shadowable.
Ours — the program gate `supported_program`, distinct from the model-layer `ref_new` row
above: the scope-threaded fold `stmt_okS`/`body_okS` over the sealed `ScopeS` (declarations
only via `scope_declare`, uses marked by `type_expr` in the same traversal) plus the final
`scope_all_used` unused-local rejection.  ✓ redeclare / blank LHS / untyped nil / unused / use-before-declare
all rejected (`bad_programs` rows, each error verified against gc).  ⚠ NAMED NARROWINGS —
valid Go the gate refuses (`valid_unsupported_programs` rows, each verified gc):
aggregate/map locals (`x := []int{1}`, `m := map[int]int{1:2}` — the evaluator has no
aggregate values, so `bind_category` rejects the binding); shadowing a checker-recognized
name (`len := 1` / `int := 1` / `nil := 1` — `decl_ident_ok` rejects uniformly); the
conservative 32-bit default-`int` bound on the RHS (`x := 2^40` — sound on every target).
The EXPRESSION-level env evaluator exists (`denote_expr_env` — a bound local evaluates,
tag-checked); STATEMENT denotation of `x := e` is ABSENT until the env statement layer:
decl programs are supported-but-undenoted (`shortdecl_supported_undenoted`).

### [If](https://go.dev/ref/spec#If_statements) / [For](https://go.dev/ref/spec#For_statements) / [Switch](https://go.dev/ref/spec#Switch_statements) / [Goto](https://go.dev/ref/spec#Goto_statements) / [Return](https://go.dev/ref/spec#Return_statements) — ✓ via the plugin's goto-CFG structurer (TRUSTED); ⚠ native `switch`
Spec: structured control flow (`if`/`else`, `for` with optional range, `switch`,
`break`/`continue`/labeled, `goto`, `return`).  Ours: the constructs in this row lower
through ONE primitive — a goto-CFG (`run_blocks`/`Jump`/`Done`, each function body a set
of labelled basic blocks) — lifted back to idiomatic Go by the trusted plugin's
STRUCTURING pass (dominators / post-dominators as iterative fixpoints, natural loops by
back-edges, emitting `if`/`for`/`break`/`continue`/labeled-break, raw labels + `goto`
where the graph is irreducible).  The lowering is TRUSTED plugin code (gap #10): coverage
below is DEMO-BY-DEMO and golden-locked — no theorem relates the emitted Go to the CFG,
and no completeness claim is made beyond the pinned demos:
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
- **`goto`** (irreducible CFG): raw Go labels + `goto`, the fallback that needs no
  structural assumptions (TRUSTED plugin lowering) — `irreducible_demo` (a two-entry
  loop) golden-locks it.  ✓
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
- **(R2) cmd.v `CDfr` — the FAITHFUL model:** `cmd.v` models `defer` as `CDfr d k`;
  `run_cmd` (the SOLE `Cmd` interpreter — total, structural, no step bound) unwinds the LIFO defers at
  func-scope return — a panicking defer REPLACES the active panic (last-raised-wins) but the older defers STILL run,
  every defer's effects happen.  `bridge_effects_agree` proves the `ustep` run AGREES with this for ANY completing command (heap ops, allocation, the channel trio, and defers included — final heaps, buffers, and closedness agreeing under the `chans_open` start; `structurally_total_cmd` completion is a theorem).
- **(R3) GoAst `GsDefer` — STRUCTURED syntax (✓ emittable, ✓ DENOTED):** `defer <call>` is a real AST
  statement, print-injective (`print_stmt_inj`), syntactically SUPPORTED + certificate-emittable (gated to a
  call via `expr_stmt_ok`), and GoSem DENOTES it into R2's faithful model (`denote_stmt GsDefer = CDfr d (CRet
  tt)` via the shared `denote_effect_call`; the deferred call runs at return, LIFO — end-to-end pins
  `GoSem.rc_defer_lifo` / `rc_defer_panic`).  A deferred panic denotes a `CPan` under the `CDfr`, so the
  panic-free gate (behavioral: `cmd_no_panic` of the denotation) rejects `defer panic(v)` while accepting +
  emitting `defer println(..)` (`GoSemSafe.panic_free_gate_defer`).
- **(B) shallow `IO` (`World -> Outcome`) — NO defer meaning, FAILS LOUD (✓ rule 2):** a sequential shallow
  reading cannot reify a func-scoped defer, so `GoExtractionHooks.defer_call (_ : IO unit) := fun w => OPanic … w`
  PANICS rather than silently dropping the effect (which replaced the old `ORet tt w` no-op).
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
Spec: one ready communication is chosen via uniform pseudo-random selection; `default`
runs if none ready; else BLOCKS.
Ours: `select_recv2` (two recv cases) and `select_recv_default` (recv + `default`) lower
to faithful idiomatic Go `select` (CPS like `recv_ok`); `select_demo` /
`select_default_demo` golden-locked. **⚠ the LOWERING is faithful Go; the sequential
MODEL is an unsound deterministic under-approximation**, in two ways:
- **CHOICE.** Both ready ⇒ the model takes ch1; Go picks pseudo-randomly — so Go does
  NOT refine the deterministic function; it is one example scheduler, non-authoritative
  (a THEOREM: `det_select_incomplete`). A safety property must hold for EVERY permitted
  choice — the relational layer below is the authority.
- **BLOCKING.** None ready, no `default` ⇒ the sequential model fail-louds
  (`OPanic rt_select_block` — the IO model has no Blocked outcome and never fabricates a
  value); Go BLOCKS. Blocking is a LOCAL non-step (deadlock only when the WHOLE program
  cannot step — `concurrency.v`'s `Stuck`).
The desugar proofs (`select_wait2`/`select2_eq_recv2`) equal *this idealised model*, not
Go. *Pending:* send cases, N-ary.
**CLOSED-channel READINESS:** a closed drained recv is READY in Go (zero immediately) —
`select_recv2`/`select_recv_default`/`select_wait2` check `chan_closed`: empty+closed ⇒
that recv fires with zero; `default` only on empty+OPEN (witnesses
`select_default_closed`/`select_default_open_empty`).
**The relational/operational select layer (axiom-free, proof-only):**
- Closed channels are modeled off the TRACE (`closedb` reads a `KClose`; a `KRecv`
  back-pointer may point at that close — `WfTrace` carries the send-OR-close
  disjunction); `step_recv_closed`/`rstep_select_closed` step a closed-drained
  recv/select to zero.
- `CSelect : list (nat * (nat → Cmd))` is first-class — per-case channel +
  continuation, same-channel distinct bodies representable
  (`rselect_per_case_continuation`); `rstep_select` fires ANY ready case; an empty
  select is a local non-step feeding deadlock (`rsel_block_stuck`); readiness has ONE
  closed-aware authority (`sel_ready_cl`), shared with the deadlock theory and the
  multi-goroutine refinement.
- The typed `select_recv2` is SOUND (`det_select_sound`), INCOMPLETE
  (`det_select_incomplete`), and EXACT on unique BUFFERED readiness
  (`det_select_complete_unique`/`det_select_exact_unique`; full Go-completeness also
  needs the open-channel side condition).
- A ready first channel reduces `select_recv2` to plain `recv` at `run_io`
  (`select_recv2_ch1_buffered`/`_ch1_closed` + fall-throughs), so select inherits
  `recv`'s operational refinement (`select_fire_is_recv_fire` in the calculus).
**Robust fix (tracked):** proofs quantified over the chosen index in the relational
`rstep` shape; a sound deterministic subset needs an exactly-one-ready proof under an
ownership discipline keeping readiness stable (else TOCTOU).

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
Spec: "sequenced before" / "synchronized before" are partial orders; happens-before is
the transitive closure of their union; a send is synchronized before the corresponding
receive completes; the kth receive on a cap-C channel is synchronized before the (k+C)th
send completes (C=0 = unbuffered rendezvous); a data race is two conflicting accesses
unordered by happens-before.
Ours: `hb` = transitive closure of exactly those edges, proven a STRICT partial order
(`hb_irrefl` + `hb_transitive` — stronger than the spec's "partial order").  Trust base:
the hb / trace / Owned / region families are `Print Assumptions` = *Closed* AND
funext-free; the Keystone `run_io` bridge family carries the ONE documented
`functional_extensionality` holdout (`run_io_inj` — see the header note).
- **Channel rules 1/3/4** (send⤳recv-completion, kth-recv⤳(k+cap)th-send, unbuffered):
  `hb_send_before_recv` / `hb_recv_before_send` / `unbuffered_rendezvous` /
  `buffered_sender_runs_ahead`. Operationally: `rendezvous_via_buffer` (cap-0 handoff in
  `rstep`); the capacity-parameterised calculus (`Section BoundedChannels`) FORCES cap-0
  blocking (`cstep_cap0_buf`, `all_senders_stuck`/`ublock_stuck`) and proves SAFETY
  (`csteps_cap_respected` — the buffer never exceeds capacity) + LIVENESS
  (`buffered_send_progresses` — a send with room never blocks). (Integrating `cap` into
  the full `rstep` config is a tracked cascade; the semantics is proven here.)
- **Rule 2** (close ⤳ zero-receive): `hbc_close_before_zero_recv`, with
  `close_not_before_value_recv` proving NO over-ordering (via the conserved credit).
- **Fork edge** (go ⤳ goroutine start): `fork_hb` + `fork_program_race_free`; grounded
  in execution — `rstep_spawn` emits `KSpawn`+`KStart`, `fork_exec_trace` runs the
  program and `fork_exec_race_free` derives race-freedom operationally.
- **Channel handoff edge**: `handoff_race_free` + execution-grounded
  `chan_pub_exec_trace`/`chan_pub_exec_race_free` (the write happens after the spawn, so
  only the send/recv edge can publish it).
- **Closed-form discipline**: `HandoffDisciplined` (every conflicting pair is same
  goroutine or one po·sync·po handoff) ⇒ `Owned` ⇒ race-free
  (`handoff_disciplined_owned`), unifying `locprivate_handoff_disciplined` and
  `handoff_trace_disciplined`.
- **ABSTRACT OWNERSHIP-TRANSFER RACE-FREEDOM (the general theorem)**: ONE `rstep`
  induction (`owned_step_snoc` ← `AcqConn`/`owned_step_by_owner` ← the linear
  region-threading typing `WTf flp` ← `RegionInvF`+`BufLinF`+`OwnerLive` ←
  `region_inv_f_step` ← `region_inv_f_race_free`) makes ALL THREE Go
  ownership-transfer mechanisms — pointer-handoff, spawn-split, signal-handoff —
  race-free for arbitrary programs and ALL interleavings. Witnesses: `witness`/`relay`,
  `splitw`/`fork`, `sig`, `combo`/`fcombo`; subsumption `mp_subsumed_by_general` /
  `xfer_subsumed_by_general`; NON-VACUITY `region_inv_rejects_race` +
  `wt_rejects_unowned_*`. Axiom-free AND funext-free. IO-LIFT: the channel fragment
  connects to extractable Go (`mp_g0_denotes`/`mp_end_to_end`); the spawn fragment lives
  on `rstep` only (`go_spawn` has no `run_io` law — the documented strategic fork).
**Trace model** — `hbt_irrefl`: for ANY well-formed trace (synchronisation recorded by
back-pointers), happens-before is a strict partial order (trace position is a linear
extension — `hbt_forward`). Race freedom: `trace_ordered_no_race` + `mp_trace_race_free`.
**Operational semantics** — every step appends an event under the `BufOk` invariant
(`step_preserves_inv`), so `reachable_wf`: EVERY reachable trace is well-formed;
composed: `reachable_hb_strict` — the happens-before of any real execution is a strict
partial order, earned by execution.
**Calculus ↔ `run_io` bridge (Keystone)** — `Cmd` deep-embeds an IO program; `Denotes`
relates it to `run_io`; `denote_sim_send`/`recv`/`write`/`read` +
`denote_adequate` (single-goroutine adequacy). Multi-goroutine: `wmatchc_step` keeps the
calculus channel state matched to the `World` via the channel frame THEOREMS;
`reachable_refines_and_safe` bundles refinement with race-freedom.
**Deadlock** — characterized (`rstuck_blocked`: someone unfinished, every live goroutine
finished or blocked on an empty-channel receive) and freedom PROVEN for RECEIVE-FREE
programs (`reachable_recvfree_progress`); disciplined freedom for receiving programs is
the liveness frontier.
**Other go.dev/ref/mem subsections:** Initialization — N/A (single `package main`, no
imports, no user `init`). Goroutine destruction — faithful BY OMISSION (the spec mandates
NO exit edge; we add none) ✓. Locks/Once/Atomics — need `sync` imports, ✗ deferred.

**Still open (honest gaps):**
- **The READ-OBSERVATION rule (`W(r)`) — ⚠ PRIOR-WRITE slice under `Owned` only:**
  the model is operationally sequentially consistent, so WHEN a prior trace write to
  the location exists, the observed writer is by construction the trace-last one
  (`last_write_before`, `last_write_before_spec`), and `visible_write_hb_maximal`
  proves that under `Owned` it happens-before the read and is hb-MAXIMAL among prior
  writes.  NOT total: a read with no prior trace write (initial-heap reads) has no
  `W(r)` — no initial-write events are modeled — and there is no visible-write
  semantics outside `Owned` (racy programs).
- **Implementation Restrictions (no-out-of-thin-air; word-tearing) — ✗ unmodeled**
  (bounded-race guarantees for racy programs; we reason only about race-free ones).
- **`sequenced before` is modeled as a TOTAL per-goroutine order** — stronger than the
  spec's partial one; sound for the straight-line traces generated; a faithful partial
  order is a tracked refinement.
- The heap analogue of the frame law; the FIFO refinement (kth recv ↔ kth send);
  disciplined deadlock-freedom for receiving programs; the unverified plugin lowering.

## Bounds-panic payload (2026-07-02)

`rt_index_oob i n` now renders Go's EXACT runtime payload (verified against gc 1.23 via `go run`):
a non-negative out-of-range index yields `runtime error: index out of range [i] with length n`; a
NEGATIVE index yields `runtime error: index out of range [i]` with NO length part.  Digits via the
model's own `Z_dec_string` (proof-side only — the digit chain is suppressed at extraction; emitted Go
panics natively).  Consumers: `slice_get`/`slice_idx_get`/`slice_idx_set` and GoSem's runtime-index
denotation (tier R2) — one payload authority, no collapsed class-wide value.  Every payload length is
STRUCTURAL (`List.length` / `sh_len` / the constructed-element count), never a round-trip through the
wrapped `len`; `slice_get`'s guard shares that same authority, sealed two-sided by the manifest-gated
`slice_get_bounds_surface` (with `len_agrees_structural` proving the wrapped `len` agrees on every
representable slice).
