# Plan: finish the no-import primitive layer (the pre-import gate)

**Goal.** Model every remaining Go *builtin / primitive* faithfully — the whole
no-import surface — so the project can cross into **library imports** with the
primitive layer locked down perfect.  This is the standing rule
([[primitives-before-libraries]]): a library inherits every subtlety of the
primitives under it, so no primitive may be left partial or wrong before we type
an imported package.

**Definition of done (this plan's scope).** Every item below is either (1)
modeled faithfully with a machine-checked witness and a `SPEC_CONFORMANCE.md`
entry, or (2) reclassified as an explicit, tracked post-import boundary (e.g.
`math.Abs`).  No silently-wrong or plausible-but-wrong lowering survives — the
fail-loud meta-invariant holds throughout.  `make check` (golden) stays green at
every step; any intended behavior change is a deliberate `make golden` + commit.

**Non-negotiables (carry every phase).**
- `*.go` is never hand-edited — always extracted from `*.v`.
- Zero of *our own* axioms (108 → 0 achieved 2026-06-16); a new `Axiom`/`Parameter`
  in the closed world is a regression.  `Print Assumptions` on each phase's
  headline result must show only named external boundaries (Coq kernel,
  `PrimInt63`/`PrimFloat`, stdlib `functional_extensionality`).
- Every primitive "done" only when its `SPEC_CONFORMANCE.md` section is honored
  and cites the Go spec rule it implements.
- Fail-loud: an unmodeled construct aborts `make extract`, never emits wrong Go.

----

## What the zero-axioms work already closed (do not relist)

- **Joint axiom consistency** (old Tier 1 #2) — MOOT.  The `World` is a concrete
  record; the model is consistent by construction.
- **Heap get-after-write** for maps + refs (old Tier 3 #8b) — now derived
  theorems over the real heap, not a degenerate axiom.
- **Overflow-safe arithmetic** `add_nz`/`sub_nz`/`mul_nz` (old Tier 2 #5) — done,
  evidence-carrying.

----

## The two foundational keystones (unblock the most)

These gate the widest set of downstream items.  Do them first; everything in
"the rest" gets easier or becomes possible once they land.

### A — Full-width 64-bit integer model

**Problem.** `int` is Rocq `Sint63` (63-bit), faithful only on `[-2⁶², 2⁶²)` —
one bit short of Go int64.  The genuine blocker is the **64-bit width** only:
anything narrower already works on the 63-bit carrier (see A1 below — the 32-bit
multiply was a *false* blocker).

**Unblocks:** `uint64`/`uint`/`int64`/`int` at full width · `int` bitwise
(`& | ^ &^ ^`) and shifts (the sign bit at 62 not 63) on the full-width type ·
untyped **integer constants** as `Z` with a representability check at use (Known
gap #5 / spec "Constants"; `1<<70` is unrepresentable today).

**Approach.** A Z-based wrapper record (`GoI64`/`GoU64` over `Z`, normalized into
the int64/uint64 range after each op) — the SAME proven numint template, just a
`Z` carrier instead of a masked `int`, at the full width.  Plugin erases the
wrapper (like `GoU8`…) and emits native Go int64/uint64 ops (Go already wraps at
2⁶⁴, so the emitted Go needs no mask — the wraparound is free).

**Sub-phases (dependency order within A):**
- **A1 — `u32_mul`/`i32_mul` (DONE, 2026-06-17).** Was a *false* blocker: a 32-bit
  product can exceed the 63-bit carrier, but the masked LOW 32 bits are EXACT
  (`PrimInt63.mul` is mod 2⁶³, `2³²∣2⁶³`, so `(a*b mod 2⁶³) mod 2³² = a*b mod 2³²`).
  Defined via mask-after-multiply; the over-conservative plugin guard (`2W>62`)
  relaxed to the true limit (`W≥63`).  Witnesses `spec_u32_mul_wrap` (100000²→
  1410065408), `spec_u32_mul_max` ((2³²−1)²→1), `spec_i32_mul_wrap` (46341²→
  -2147479015); `u32_demo` golden-locked.  No Z model needed.
- **A2 — `GoI64` full-width signed type (DONE, 2026-06-17).**
  Distinct record over `Z` (`MkI64 { i64raw : Z }`), normalised mod 2⁶⁴ by `wrap64`.
  Full op set: `i64_lit` (representability proof; `i64_const_oob` Fail),
  `add`/`sub`/`mul` (wrap at the true 2⁶³), `eqb`/`ltb`/`leb` (signed Z compare),
  `div`/`mod` (truncate toward zero via `Z.quot`/`Z.rem` — NOT Coq's floor; MININT/−1
  wraps; evidence-carrying non-zero divisor, `i64_div_zero` Fail), bitwise
  `and`/`or`/`xor`/`andnot`/`not`, shifts `shl`/`shr` (`<<` wraps, `>>` arithmetic;
  evidence-carrying non-negative count, `i64_shl_neg` Fail).  Witnesses
  `spec_i64_add_wrap`/`sub_wrap`/`mul_wrap`/`beyond62`/`div_trunc`/`mod_sign`/
  `div_ovf`/`shl_wrap`/`shr_arith`/`and`/`not` + `i64_add_no_overflow_exact`, all
  **axiom-free** (`Print Assumptions` = *Closed under the global context*).  Plugin:
  rides the numint erasure (type→int64, ctor/proj erased) since `is_ui_digits "I64"`;
  ops route through `binop_of` (BARE Go int64 ops — Go's `/` truncates and `>>` is
  arithmetic, matching the model; no mask); `i64_lit` folds its `Z` literal
  (`z_value` via `Int64`); the `Z`/`Pos` arith helpers + the generic eliminators they
  drag in (`CompOpp`/`fst`/`snd`) are suppressed (`is_zarith_helper`), never emitted.
  `i64_demo`/`i64_ops_demo` golden-locked.  *Surfaced:* Go constant-folds `MAX+1` →
  untyped-constant compile error (the A5 gap), so the demos show in-range values; the
  wrap/overflow corner cases are witness-proven.
- **A3 — `GoU64` full-width unsigned type (DONE, 2026-06-17).**  Distinct record over
  `Z` (`MkU64 { u64raw : Z }`), normalised by `wrapU64` (mod 2⁶⁴, always non-negative).
  Full op set: `u64_lit` (representability proof; `u64_const_oob` Fail),
  `add`/`sub`/`mul` (unsigned wrap at 2⁶⁴), `eqb`/`ltb`/`leb` (Z compare on
  non-negative — unsigned order), `div`/`mod` (Z.div/Z.modulo, floored = truncated
  for non-negative; evidence-carrying non-zero divisor, `u64_div_zero` Fail), bitwise
  `and`/`or`/`xor`/`andnot`/`not` (lnot + wrapU64), shifts `shl`/`shr` (<<wraps,
  >>logical via Z.shiftr on non-negative; `u64_shl_neg` Fail).  Witnesses
  `spec_u64_add_wrap`/`sub_wrap`/`not`/`shr`/`beyond63`, all axiom-free.  Plugin:
  numint erasure gives free type/ctor/proj suppression; type is `uint64` (exception
  to `int64` default — explicit check on `"GoU64"` in `pp_type`); `u64_lit` uses
  `Printf.sprintf "%Lu"` for unsigned decimal (handles [2⁶³,2⁶⁴) correctly);
  ops route through `binop_of` as bare Go uint64 ops (unsigned arithmetic = signed
  arithmetic at the bit level; comparison/division differ but Go's unsigned
  `<`/`/` match the Z model on non-negative operands).  `TU64 → "uint64"` in
  go_type_tag_map.  `u64_demo` golden-locked.
- **A4 — migrate the default `int`/`int64` to the full-width type** (DECISION
  2026-06-17: FULL MIGRATION — make `GoI64`/`GoU64` THE canonical Go int64/uint64,
  not the bounded `Sint63`).  Done in sub-steps:
  - **A4.1 — concurrency.v bridge value carrier (DONE, 2026-06-17).**  The
    Keystone / KeystoneMulti deep↔shallow bridge now carries `GoI64` (tag `TI64`)
    values, NOT `int`/`TInt64` — so the modeled channel/heap values are the faithful
    full-width int64.  Mechanical: the bridge proofs use only the POLYMORPHIC IO laws
    (`run_send`/`recv`/`chan_buf_send`/`recv`/`ref_*` + the frame laws), never any
    `int`-specific computation, so swapping the carrier tag is sound by construction.
    Verified: build green; `Print Assumptions denote_adequate`/`reachable_refines_and_safe`/
    `denote_sim_recv` = exactly the Coq primitive kernel axioms (`int`/`eqb`/`eqb_refl`/
    `eqb_correct`/`PrimFloat.float` — from channel/location plumbing, UNCHANGED by the
    swap; Z is axiom-free), `hbt_irrefl` = Closed.  No new/degenerate axioms.  Emits no
    Go (proof-only), golden unchanged.  `inj`/`prj` realizable across the WHOLE int64
    range now (`inj n := MkI64 (Z.of_nat n)`), not just `< 2^62`.
  - **A4.2a — ergonomic surface (DONE, 2026-06-17).**  `Notation int64 := GoI64` /
    `uint64 := GoU64` (the canonical names); range-checked `Number Notation` so
    `42%i64` / `42%u64` are int64/uint64 LITERALS whose representability is checked AT
    PARSE TIME (out-of-range numeral → `None` → parse error = Go's untyped-constant
    overflow; `i64_lit_oob` / `u64_lit_oob` `Fail` tests — closes A5 for int64/uint64
    *literals*, constant *arithmetic* still A5); scoped arithmetic (`+`/`-`/`*`/`=?`/
    `<?`/`<=?` in `i64_scope`/`u64_scope`).  Demos `i64_demo`/`u64_demo` converted to
    `(a + b)%i64` form — golden BYTE-IDENTICAL (the `MkI64`/`MkU64` literal lowers
    through the numint-ctor erasure to the same bare Go int).  Plugin: a dedicated
    `MkU64 z` arm prints UNSIGNED (`%Lu`) — the Number-Notation literal form would
    otherwise hit the signed bare-`Z` arm and render `[2^63,2^64)` negative.  The four
    parse helpers (`i64_of_Z`/`Z_of_i64`/`u64_of_Z`/`Z_of_u64`) are parse-time only,
    suppressed in `is_inlined_ref`.  No new axioms (Number Notation is parsing, not
    proof).
  - **A4.2b — close-out (DONE, 2026-06-17).**  `comparable_TI64`/`comparable_TU64`
    (axiom-free in the project sense — only the primitive `key_eqb` boundary) make
    int64/uint64 first-class MAP KEYS.  `i64_pipeline_demo` flows a `>2^62` int64
    through a buffered channel AND a `map[int64]int64`; `u64_pipeline_demo` flows a
    `≥2^63` uint64 (the upper half, unrepresentable as signed) through `chan uint64` +
    `map[uint64]uint64` — golden-locked, proving the full-width types are first-class in
    EVERY position `int` occupies, not just arithmetic.  Plugin correctness for erased
    literals: the bare-`Z` arm is now SIGN-AWARE (a `Zpos` whose 64-bit pattern is
    negative-as-`Int64` is a `uint64 ≥ 2^63` → `%Lu`; else signed), and bare literals in
    typed slots are pinned via the value tag (`pp_typed_lit_tagged`, e.g. a map's
    `uint64(0)` default).  Docs reframed: `GoI64`/`GoU64` are the canonical int64/uint64;
    primitive `Sint63` `int` COEXISTS (→ Go `int64`) as a bounded convenience.  *Scope
    note:* the 78 incidental `(n:int)` demo sites were deliberately NOT churned — they
    model small int64 values faithfully in range, and converting them changes each
    demo's focus without a fidelity gain.
- **A5 — untyped integer constants as `Z`** with representability checked at use
  (`Fail` test for the compile-error analog).

**Witnesses to add (A2+):** `int64` add/sub/mul wrap at the true 2⁶³ boundary;
`int` bitwise/shift on negatives match int64; `spec_const_*` representability.

### B — Aliasing / mutation / pointer model

**Problem.** Maps and refs have honest *state* now, but everything that depends
on *shared backing storage* is unmodeled.  This is the deepest build and the
substrate for the closed-world wishlist (value-level ownership).

**Unblocks:**
- **slices** — sub-slicing (`s[a:b]` shares the array), in-place `append`,
  `copy`, `make([]T,len,cap)`, slice-`clear`
- **arrays** — value-vs-reference semantics distinct from slices
- **pointers** — `new`, `*T`, `&x`, dereference → and therefore **pointer
  receivers** on methods (section C below)
- **value-level ownership** (no aliasing / use-after-close on heap values) — the
  wishlist item that rests on this

**Approach.** A backing-store heap (like the ref/chan/map heaps), with a slice =
`(backing-id, offset, len, cap)` handle so sub-slices alias.  Pointers = typed
locations into the same heap.  Ties into the concurrency model for aliased /
concurrent access (Tier 1 #1).

**Witnesses to add:** sub-slice write observed through the parent · `append`
past `cap` reallocates (no aliasing) vs within `cap` aliases · `copy` semantics ·
`*p` after `*p = v` · pointer-receiver method mutates the receiver.

**Sub-phases (LISTED IN DEPENDENCY ORDER; the letter labels are historical — assigned
as each piece was discovered, NOT a strict sequence.  In particular B2 (pointer
receivers) needs struct-in-storage, which builds on B3's cell heap, so its true position
is AFTER B3 + the struct substrate, recorded here — earlier drafts mis-listed it before
B3, which was backwards):**
- **B1 — Pointers (DONE, 2026-06-17).**  `Ptr A` — a typed heap LOCATION sharing the
  `w_refs` cell heap with `Ref`, but lowering to Go `*T` (so a COPIED pointer ALIASES
  the same cell, the defining pointer behaviour) and nil-able (`ptr_nil`, loc 0).
  `ptr_new tag v` (Go `p := new(T); *p = v`, emitted as the single-expression IIFE
  `func(_v T) *T { return &_v }(v)` since Go forbids `&expr`), `ptr_get tag p` → `*p`,
  `ptr_set p v` → `*p = v`.  Read-after-write `ptr_get_set_same` and the ALIASING
  theorem `ptr_alias` (a write through one handle seen through another — inherited from
  the axiom-free `ref_sel_upd_same`, NO new heap/axiom).  Plugin: `Ptr A` → `*T`
  (`pp_type`); ops by name; `mkPtr`/`p_loc`/`p_tag`/`ptr_as_ref` suppressed.  `ptr_demo`
  prints `10`/`99`, golden-locked.  *Raw deref panics on nil (escape hatch); the safe
  comma-ok `ptr_get_ok` is B1b.*
- **B1b — nil-deref safety (DONE, 2026-06-17).**  `ptr_get_ok tag p (fun v ok => …)`
  — the safe-by-construction default: a comma-ok CPS form (like `slice_at_ok`/
  `recv_ok`) that BRANCHES on `p != nil` (`var v T; ok := p != nil; if ok { v = *p }`),
  so the nil-deref panic is UNREACHABLE.  `ptr_get_ok_nil` (nil → the safe `ok=false`
  branch, `v=zero`, a THEOREM) + `ptr_get_ok_nonnil` (live pointer reads through).  Raw
  `ptr_get`/`ptr_set` stay the escape hatch.  `ptr_nil` lowers to a TYPED `(*T)(nil)`
  so the `p != nil` comparison type-checks.  `ptr_safe_demo` prints `42 true` / `0
  false`, golden-locked.
- **B3 — Slice aliasing** (the big one): a faithful aliasing-handle slice model.
  - **B3a — aliasing handles (DONE, 2026-06-17).**  `SliceH A` = an aliasing handle
    `(base, offset, len, cap, tag)` that REUSES the `w_refs` cell heap — element `i` is
    the cell at `base + (offset + i)`.  `slice_make_h` (alloc `n` fresh zeroed cells),
    `slice_idx_get`/`slice_idx_set` (`s[i]` / `s[i] = v`), `subslice s a b` (`s[a:b]` —
    shifts `offset` over the SAME cells).  THEOREMS (no new heap/axiom, from
    `ref_sel_upd_same`): `subslice_shares_cell` (sub-slice elem `j` IS parent elem
    `a+j`), `subslice_alias` (a write through a sub-slice seen through the parent),
    `slice_idx_get_set_same`.  Lowers to native Go `[]T` (`make`/index/`[a:b]`), which
    IS the aliasing handle, so runtime aliases correctly.  `slice_alias_demo`:
    `(s[1:3])[0] = 99` then `s[1]` reads 99, golden-locked.  The list-based `GoSlice`
    (value, no aliasing) coexists for immutable uses.
  - **B3b — append (DONE, 2026-06-17).**  `slice_append tag s v` models Go's subtle
    `append`: WITHIN cap (`len < cap`) it writes the cell at index `len` IN PLACE and
    returns a `len+1` handle over the SAME backing (ALIASES); PAST cap (`len = cap`) it
    REALLOCATES a fresh DISJOINT backing (at `w_next`), copies the old elements (via
    `ref_sel`), appends `v` (no aliasing).  Lowers to native Go `append(s, v)` (which
    makes the cap choice itself).  THEOREMS: `slice_append_incap` (within-cap = the
    in-place cell update) + `slice_append_incap_aliases` (the appended element is
    written into the shared backing, from `ref_sel_upd_same`).  `slice_append_demo`:
    a full slice reallocates, `s2[2] = 9` (the appended element), golden-locked.
    *Past-cap NON-aliasing as a theorem needs a world invariant (all live cells <
    `w_next`) — a follow-up.*
  - **B3c — `make([]T,len,cap)` / `copy` / `clear` (DONE, 2026-06-17).**
    `slice_make_lc tag len cap` → `make([]T, len, cap)` (allocate `cap` zeroed cells,
    handle has `len`/`cap`), so a slice has spare capacity; `make_lc_append_inplace`
    THEOREM (`len < cap` ⇒ append is the in-place cell update); `slice_makecap_demo`
    RUNTIME-demonstrates the B3b in-place-append aliasing (`make([]int64,1,3)`, append in
    place shares backing, `s2[0]=77` seen through `s[0]` → `77`).  `slice_clear_h` →
    `clear(s)` and `slice_copy` → `copy(dst,src)` are single DECLARATIVE heap updates over
    the cell range (the clear zeros, the copy takes `src`'s value at each relative index;
    no loop).  `slice_clear_demo` → `0`, `slice_copy_demo` → `7`, golden-locked.
    **Phase B3 (slice aliasing) is COMPLETE** — aliasing handles, sub-slice sharing,
    append (in-place/realloc), make-with-cap, copy, clear; all golden-locked and the
    aliasing theorems inherited axiom-free from `ref_sel_upd_same`.
- **Bs — struct-storage substrate** (the prerequisite **B2 needs**, BUILDS ON B3's cell
  heap).  A user struct cannot be a `w_refs` cell directly — `GoTypeTag` has no struct
  constructor and `tag_eq`'s decidable type-equality can't produce the `A = B` proof for
  opaque struct types (the wall, 2026-06-17).  The principled model: a struct value in
  storage is a BUNDLE of scalar FIELD-CELLS in the cell heap (only the scalar field tags
  are needed — sidesteps the un-decidable struct tag), the same shape as `SliceH`'s
  consecutive cells.  ALSO unblocks structs-in-`any`/channel/map (all blocked by the same
  wall).
  - **Bs.1 — proof foundation (DONE, 2026-06-17).**  `HStruct` = a base location; field
    `k` is the cell at `base + k`, tagged with its OWN scalar tag (`hfield_cell`/
    `hfield_get`/`hfield_set`).  THEOREMS (proof-only, axiom-free, all from
    `ref_sel_upd_same`/`ref_sel_upd_diff`): `hfield_get_set_same` (field read-after-write),
    `hfield_independent` (writing field `k` leaves field `k'` at a distinct cell alone —
    even with different field TYPES), `hstruct_alias` (two pointers to the same `base` see
    each other's field writes — the aliasing a `*T` receiver relies on).  Emits no Go
    (the storage MODEL); the idiomatic lowering is Bs.2.
  - **Bs.2 — struct pointers (DONE).**  The heap-backed struct pointer is the GENERIC
    `GSPtr R` over the arity-free `StructRep R ts` (builtins.v): a field op carries the
    typed de Bruijn index + the COHERENCE-PINNED projection, and the lowering emits
    `*R` / `&R{…}` / `*p` / `*p = R{…}` / `p.Field` / `p.Field = v` via the same
    `record_proj_field` map value structs use — it never touches the proof-only rep.
    All rep machinery is suppressed; `gsptr_demo` prints `7 4` (a genuine mutation
    through the pointer, golden-locked).  Theorems: `gsptr_field_get_set` /
    `gsptr_alias` over the field-cell heap substrate (`hfield_*`).
- **B2 — Pointer receivers** (DONE; on **Bs.2**): a method whose receiver is
  a `GSPtr Struct` (a `*T`) and MUTATES the receiver.  The plugin lowers an eligible
  `GSPtr (record)` first param → `func (recv *T) M(...)` (the SAME `method_eligible`
  authority as the value receiver, shared by `pp_function` and `register_method` —
  `pp_type (GSPtr R) = *R`), and a call `m p …` → `p.M(…)`.
  `cell_incx` → `func (p *Cell) Cell_incx() { a := p.Cx; p.Cx = a + 1 }`; `ptr_method_demo`
  mutates a `*Cell` through the method and prints `11`, observed by the caller — backed by
  `gsptr_field_get_set`.
- **B4 — Arrays** (PENDING; independent of B2/Bs): VALUE semantics distinct from slices —
  `[N]T` COPIES on assign/pass (mutable elements within one array, but `b := a; b[0]=9`
  leaves `a[0]` unchanged).  Not the cell-heap handle model (that is reference/aliasing);
  a fresh backing per array value, or a functional-update value model.  `copy`/
  `make([]T,len,cap)`/slice-`clear` are DONE in **B3c** (the old "B5" — removed).

  **DESIGN (2026-06-18) — the size-in-type problem and the way around it.**  Go `[N]T`
  carries `N` in the TYPE, but Coq extraction ERASES value-level type indices (a
  `nat`-indexed array or `Vector.t A n` loses `n`), so `[N]` cannot be recovered from the
  extracted type — the fundamental blocker.  *Two routes:*
  (i) **Type-level `N` (general).**  Encode the size as a TYPE, not a value — phantom
  `AZ : Type` / `AS : Type -> Type`, so `[3]T = arr (AS (AS (AS AZ))) T`; the size SURVIVES
  extraction (they're types), and the plugin decodes the `AS`-chain to count → `[3]T`.
  General (any position) but elaborate (the phantom nat + plugin chain-decoder).
  (ii) **Size-in-LITERAL (minimal, the recommended first slice).**  Keep the size OUT of
  the Coq type (`GoArray A`, size-erased) and put it in the CONSTRUCTION: `arr_lit (l :
  list A)` lowers to `[len(l)]T{…}` (the size read off the list, exactly as `slice_of_list`
  reads it for `[]T{…}`).  A local `a := arr_lit […]` then has its Go type INFERRED from
  the literal (`a := [3]int64{…}`), so the plugin NEVER emits a bare `[N]T` annotation —
  the hard part is sidestepped.  *Bounded restriction (fail-loud, principled):* arrays may
  only appear as local `:=` + index; an array-typed PARAM / FIELD / RETURN (which needs an
  explicit `[N]T`) is refused — that is exactly route (i)'s job, deferred.  `GoArray` is a
  recognized-erased type (no struct decl); `arr_lit`/`arr_get_ok`(bounds-checked index,
  CPS like `slice_at_ok` — arrays panic on OOB too)/`arr_eqb` are recognized BY NAME, so
  the unboxing of a 1-field wrapper is irrelevant (the ops never go through the type).
  *Distinct-from-slice properties to demo:* the `[N]T{…}` literal; COMPARABILITY (`arr_eqb`
  → Go `==`, field-wise — arrays are `==`, slices are NOT); and VALUE-COPY (`b := a; mutate
  b; a unchanged`) — the last needs the functional-update/mutation step, a later slice.
  Build order: (1) `arr_lit` + `arr_get_ok` (read-only) — DONE; (2a) `arr_eqb` (comparability)
  — DONE; (2b) value-copy (`arr_set` → copy-mutate-return IIFE `func(_a [n]T) [n]T { _a[i] = v;
  return _a }(a)`, size `n` passed explicitly; `a` UNCHANGED) — DONE; (3) route (i) type-level
  `N` for non-local arrays (array-typed params/fields/returns) — PENDING.

  **Piece 1 DONE (B4.1, 2026-06-18).**  `GoArray A` (size-erased, recognized-erased type;
  an array-typed annotation fails loud with a clear message), `arr_lit tag l` → `[len l]T{…}`
  (the `slice_of_list` arm with an `[N]` prefix), `arr_get_ok` (the SAME arm/recognizer/
  suppression as `slice_at_ok` — array and slice both index `a[i]` with `len(a)`).
  `arr_demo` → `a := [3]int64{10, 20, 30}; … a[1] … a[Sub(10,5)] …` prints `20 true` /
  `0 false`, golden-locked; `arr_data_lit` is the round-trip theorem.  *Finding:* Go
  STATICALLY bounds-checks a CONSTANT array index (`a[5]` on `[3]int64` is a COMPILE error,
  unlike a slice's runtime panic — a STRONGER guarantee), so the runtime-OOB demo needs a
  COMPUTED index (`sub 10 5` → a runtime `Sub(10,5)`); `arr_get_ok`'s guard then rejects it
  at runtime.

----

## The rest (smaller, mostly independent)

### C — Structs / methods / interfaces completion

Core works (embedded fields + promotion DONE — `peel_embedded`; pointer receivers DONE (B2);
method values + CONCRETE-receiver method expressions DONE — a generic-receiver `T.M` is
rejected at extraction).  Remaining: struct tags · field-wise
`==` (struct comparability) · single-method interface
curried-return form · nullary (unit-thunk) methods · native `interface{…}`
keyword + structural satisfaction · **type switch** (`switch v := x.(type)`).

### D — Floats

`float32` is an opaque placeholder (no native Rocq f32) — model via
round-to-float32 over `PrimFloat`, or reclassify as a boundary · int↔float and
float↔float **conversions** · untyped **float constants** as exact rationals
(`Q`), the float analog of A's `Z` work.  *Note:* `abs`/`sqrt` need `math` —
they live on the **post-import** side by decision, not here.

### E — Strings: rune view

Byte model is done and faithful.  Remaining: `range s` UTF-8 decoding ·
`string`↔`[]rune`/`[]byte` conversions · gated on the `[]byte` representation
decision, i.e. on **B**.

### F — Concurrency completion (mostly proof-layer, not a builtin to emit)

Happens-before / race-freedom spine is proven + axiom-free.  Honest gaps from
the memory-model audit: the **read-observation rule** (`W(r)` / visible-writes —
which write a read observes — unmodeled) · divergence / liveness /
deadlock-freedom for receiving programs · cross-goroutine panic semantics · the
keystone refinement tying the calculus to the real `run_io` heap.  Runs
alongside; does not strictly gate imports.

### G — Panic-freedom discipline (cross-cutting)

Propagate panic obligations (nil deref, OOB, failed assert, send-on-closed) as
Hoare preconditions to every call site.  Architecturally ready; not yet wired.

### H — Lowering correctness (cross-cutting trust gap)

The ~1500-line OCaml plugin is trusted; no theorem relates emitted Go to the
source term (Known gap #10 / Tier 1 #3).  Largest trust gap, orthogonal to
"model more builtins" — Go operational semantics in Rocq + a simulation proof.

### I — Tidiness (cosmetic, losslessly expressible today)

Direct `>`/`>=`/`!=` operators (currently encoded) · composite `==` · native
`switch` keyword.

----

## Phase order (dependency-driven)

The two keystones first because they unblock C/D/E; the cross-cutting tracks
(F/G/H) run in parallel and gate nothing by themselves; tidiness (I) is filler.

1. **Phase A — full-width int model.**  A1 (`u32_mul`/`i32_mul`) DONE; then the
   `GoI64`/`GoU64` Z-record carrier (A2/A3), the default-`int` migration (A4), and
   untyped int constants as `Z` (A5).
2. **Phase B — aliasing / mutation / pointers.**  Backing-store heap; slices as
   aliasing handles; arrays; pointers; pointer receivers.  Deepest build.
3. **Phase C — structs/methods/interfaces completion.**  Pointer receivers land
   here (need B); type switch; comparability; interface gaps.  (Embedded fields + promotion DONE.)
4. **Phase D — floats.**  float32 model (or boundary), conversions, `Q`
   constants.  (Stops at the `math`-import line: `abs`/`sqrt` deferred.)
5. **Phase E — strings rune view.**  After B's `[]byte` decision.
6. **Phase F — concurrency completion.**  Proof-layer; parallelizable throughout.
7. **Phase G — panic-freedom discipline.**  Parallelizable.
8. **Phase H — lowering correctness.**  Largest, independent; the trust frontier.
9. **Phase I — tidiness.**  Direct operators, composite `==`, native `switch`.

After A + B + C + D + E land (and F/G as far as they go without imports), the
no-import primitive layer is closed and imports can begin.  H is the standing
trust debt that imports do not depend on but the guarantee does.

----

## Discipline per phase

- One coherent change per commit; `make build` green + `make check` golden-locked
  (byte-identical unless the change is an intended behavior change → `make golden`
  + commit the baseline) before committing.
- Add the machine-checked witness(es) in `main.v` and the `Fail` negative(s) for
  the rejected cases (the fail-loud / unrepresentable-bad-program gate).
- Update `SPEC_CONFORMANCE.md`: the spec section, the rule cited, our behavior,
  status (✓ / ⚠ bounded / ✗ fails loud), and the witness name.  Cite the section
  in the implementing code comment.
- After each phase, `Print Assumptions` on a representative downstream result to
  confirm no new axiom entered the trust base.
- Update the Status checklist below as items land.  Retire the corresponding
  CLAUDE.md "Correctness debt" tier entry when its item closes.
- Push after each green commit (durably authorized, [[push-authorized]]).

----

## Status

Keystones:
- [x] **A — full-width int model** — A1 (u32/i32_mul) ✓; A2 signed `GoI64` ✓; A3 `GoU64` ✓; A4 default-`int` migration ✓ (A4.1 concurrency-bridge carrier → `GoI64`; A4.2a ergonomic range-checked `%i64`/`%u64` literals + scoped arith; A4.2b Comparable + int64/uint64 chan+map pipelines; A4.3a overflow-safe arithmetic on full-width `GoI64`; **A4.3b FULL int-model migration — ALL value/payload/struct/interface/typestate/repinv/slice/arithmetic demos converted to `GoI64`, and the Sint63 VALUE-overflow theory removed**).  `GoI64`/`GoU64` are THE canonical Go int64/uint64.  Primitive `Sint63` `int` survives ONLY as index arithmetic (loop counters, computed slice indices), `nat`-coding, and the `go_min`/`go_max` builtin demo.  All conversions golden-IDENTICAL (`GoI64` and `int` both → Go `int64`).  **A5 — untyped INTEGER constants as `Z` (DONE):** `i64c`/`u64c` notations `vm_compute`-evaluate a closed `Z` constant expression at elaboration (arbitrary precision — an intermediate like `1<<70` may exceed the target), then convert demanding representability; out-of-range fails to elaborate (= Go's untyped-constant overflow).  No plugin change.  Witnesses `const_intermediate_exceeds`/`const_exact_arith`/`const_u64_upper` + `Fail` `const_oob_*`; `const_demo` golden-locked.  *Untyped FLOAT constants (exact rationals) → Phase D.*
- [~] **B — aliasing / mutation / pointers** — B1 pointers ✓, B1b nil-deref safety ✓,
  **B3 slice aliasing ✓ COMPLETE** (handles over the cell heap, sub-slice sharing, append
  in-place/realloc, make-with-cap, copy, clear — all golden-locked, aliasing theorems
  axiom-free from `ref_sel_upd_same`).  PENDING (in dependency order): **Bs** struct-storage
  substrate (struct = bundle of scalar field-cells — the prerequisite B2 needs, also
  unblocks structs-in-`any`/chan/map) → **B2** pointer receivers (needs Bs) → **B4** arrays
  (value semantics, independent).

The rest:
- [ ] C — structs/methods/interfaces completion (pointer receivers, type switch, embedded, comparability, interface gaps)
- [ ] D — floats (float32, conversions, Q constants; abs/sqrt deferred post-import)
- [ ] E — strings rune view (gated on B's []byte decision)
- [ ] F — concurrency completion (read-observation rule, liveness/deadlock, goroutine panic, keystone refinement)
- [ ] G — panic-freedom discipline (Hoare preconditions to call sites)
- [ ] H — lowering correctness (Go semantics + simulation proof; the trust frontier)
- [x] I — tidiness (direct >/>=/!= ✓; composite struct == ✓ [struct_eqb → native `a == b`, evidence-carrying]; native switch ✓ [type_switchN → `switch v := x.(type)`; int_switch2 → native expression `switch x { case v: … }`])

**Critical path to imports:** A → B → C → D → E (with F/G alongside).  H is the
standing trust debt; it does not gate imports but the guarantee's honesty
depends on naming it.
