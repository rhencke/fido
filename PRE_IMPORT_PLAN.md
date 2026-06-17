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
- **A2 — `GoI64` full-width signed type.** Z-record; literals (representability
  proof), add/sub/mul wrapping at the true 2⁶³, the no-overflow-exact theorems at
  2⁶³, signed comparison, div/mod (truncating, MININT/−1 wrap), bitwise, shifts
  (arithmetic). Plugin lowering + demo. **The keystone build.**
- **A3 — `GoU64` full-width unsigned type.** Same template, unsigned wrap at 2⁶⁴.
- **A4 — migrate the default `int`/`int64` (`TInt`/`TInt64`/`GoInt`) to the
  full-width type**, *or* keep `Sint63` as an explicit "bounded int" and make
  `GoI64`/`GoU64` the faithful full-width pair. Touches concurrency.v's `TInt64`
  channel-carrier and the int demos — the invasive decision; scope it then.
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
  receivers** on methods (ladder 9b/9c)
- **value-level ownership** (no aliasing / use-after-close on heap values) — the
  wishlist item that rests on this

**Approach.** A backing-store heap (like the ref/chan/map heaps), with a slice =
`(backing-id, offset, len, cap)` handle so sub-slices alias.  Pointers = typed
locations into the same heap.  Ties into the concurrency model for aliased /
concurrent access (Tier 1 #1).

**Witnesses to add:** sub-slice write observed through the parent · `append`
past `cap` reallocates (no aliasing) vs within `cap` aliases · `copy` semantics ·
`*p` after `*p = v` · pointer-receiver method mutates the receiver.

----

## The rest (smaller, mostly independent)

### C — Structs / methods / interfaces completion (ladder 9)

Core works.  Remaining: embedded fields + promotion · struct tags · field-wise
`==` (struct comparability) · **pointer receivers** (needs B) · method
values/expressions (`recv.M` as a closure, `T.M`) · single-method interface
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
   here (need B); type switch; embedded fields; comparability; interface gaps.
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
- [~] **A — full-width int model** — A1 (u32/i32_mul) ✓ done; A2–A5 (GoI64/GoU64 Z-record, default-int migration, Z constants) pending
- [ ] **B — aliasing / mutation / pointers** (unblocks slices/arrays/pointers/pointer-receivers)

The rest:
- [ ] C — structs/methods/interfaces completion (pointer receivers, type switch, embedded, comparability, interface gaps)
- [ ] D — floats (float32, conversions, Q constants; abs/sqrt deferred post-import)
- [ ] E — strings rune view (gated on B's []byte decision)
- [ ] F — concurrency completion (read-observation rule, liveness/deadlock, goroutine panic, keystone refinement)
- [ ] G — panic-freedom discipline (Hoare preconditions to call sites)
- [ ] H — lowering correctness (Go semantics + simulation proof; the trust frontier)
- [ ] I — tidiness (direct >/>=/!=, composite ==, native switch)

**Critical path to imports:** A → B → C → D → E (with F/G alongside).  H is the
standing trust debt; it does not gate imports but the guarantee's honesty
depends on naming it.
