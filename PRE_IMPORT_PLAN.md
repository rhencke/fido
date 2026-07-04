# Plan: finish the no-import primitive layer (the pre-import gate)

**Goal.** Model every remaining Go builtin/primitive faithfully — the whole no-import
surface — before crossing into library imports ([[primitives-before-libraries]]): a
library inherits every subtlety of the primitives under it.

**Definition of done.** Every item below is either (1) modeled faithfully with a
machine-checked witness and a `SPEC_CONFORMANCE.md` entry, or (2) reclassified as an
explicit, tracked post-import boundary (e.g. `math.Abs`). Fail-loud throughout; `make
check` (golden) green at every step; intended behavior changes are deliberate
`make golden` commits.

**Non-negotiables (every phase).** `*.go` never hand-edited; zero project axioms (a new
`Axiom`/`Parameter` is a regression); each primitive "done" only with its
`SPEC_CONFORMANCE.md` row; an unmodeled construct aborts `make extract`.

----

## A — Full-width 64-bit integer model — DONE

`GoI64`/`GoU64` (`Z`-carried, normalized mod 2⁶⁴) are THE canonical Go int64/uint64:
full op sets (wrap arithmetic, signed/unsigned compare, truncating div/mod with
evidence-carried divisors, bitwise, shifts with evidence-carried counts), range-checked
`%i64`/`%u64` literal notations, first-class in every position (chan/map/any/struct),
witnesses axiom-free, demos golden-locked. Untyped integer constants evaluate as exact
`Z` at elaboration with representability checked at use (`i64c`/`u64c`; out-of-range
fails to elaborate = Go's untyped-constant overflow). Primitive `Sint63` `int` survives
only as index arithmetic / `nat`-coding.

## B — Aliasing / mutation / pointers

- **B1/B1b — pointers + nil-deref safety: DONE.** `Ptr A` = typed heap location → Go
  `*T` (copies alias); safe comma-ok `ptr_get_ok` makes the nil-deref panic
  unreachable; raw deref stays the evidence-gated escape hatch. Aliasing theorem
  `ptr_alias` axiom-free.
- **B3 — slice aliasing: DONE.** `SliceH` = `(base, offset, len, cap)` handle over the
  cell heap: sub-slice sharing, in-place/realloc `append`, `make(len,cap)`, `copy`,
  `clear` — aliasing theorems from `ref_sel_upd_same`; lowers to native `[]T`.
  *Follow-up:* past-cap NON-aliasing as a theorem needs a live-cells-< `w_next` world
  invariant.
- **Bs — struct-storage substrate: DONE.** A stored struct = a bundle of scalar
  field-cells (`HStruct`; field independence + aliasing theorems); the generic
  `GSPtr R` over arity-free `StructRep R ts` lowers to `*R` / `&R{…}` / `p.Field`
  through the coherence-pinned projections.
- **B2 — pointer receivers: DONE.** An eligible `GSPtr (record)` first param →
  `func (recv *T) M(...)` (the shared `method_eligible` authority); mutation observed
  by the caller.
- **B4 — arrays: PARTIAL.** Size-in-LITERAL route DONE: `arr_lit` → `[N]T{…}` (size
  from the literal, local `:=` + index only), `arr_get_ok` (CPS bounds check),
  `arr_eqb` (array `==`), `arr_set` (value-copy mutate via IIFE — `a` unchanged).
  REMAINING: type-level `N` (phantom-type route) for array-typed params/fields/returns
  — an array-typed annotation currently fails loud.

## C — Structs / methods / interfaces completion

Core works (embedded fields + promotion; pointer receivers; method values;
CONCRETE-receiver method expressions — a generic-receiver `T.M` is rejected at
extraction). REMAINING: struct tags · field-wise `==` (struct comparability) ·
single-method interface curried-return form · nullary (unit-thunk) methods · native
`interface{…}` keyword + structural satisfaction · type switch on user interfaces.

## D — Floats

Float64 + float32 are modeled (spec_float; exact-or-reject constants behind
`floats_checked`; the dyadic↔SF agreement arc is complete — see PROGRESS).
REMAINING: untyped float constants as exact rationals beyond the current dyadic
window; `abs`/`sqrt` are post-import by decision (`math`).

## E — Strings: rune view

Byte model done and faithful; rune/byte slice conversions and `range s` UTF-8 decoding
exist. REMAINING: audit vs the B `[]byte` representation for aliasing fidelity.

## F — Concurrency completion (proof-layer)

Happens-before / race-freedom spine proven + axiom-free. REMAINING: the
read-observation rule (which write a read observes) · divergence/liveness for
receiving programs · cross-goroutine panic semantics · the keystone refinement tying
the calculus to the real `run_io` heap. Runs alongside; does not gate imports.

## G — Panic-freedom discipline (cross-cutting)

Propagate panic obligations (nil deref, OOB, failed assert, send-on-closed) as
preconditions to call sites. Architecturally ready; not wired.

## H — Lowering correctness (the trust frontier)

The OCaml plugin is trusted; no theorem relates emitted Go to the source term (gap
#10). Orthogonal to modeling more builtins; the AST-first spine (ARCHITECTURE.md) is
the path.

## I — Tidiness — DONE

Direct `>`/`>=`/`!=` · composite struct `==` (`struct_eqb` → native `a == b`) · native
`switch` (type switch + expression switch).

----

## Phase order & discipline

Critical path to imports: **A ✓ → B (B4 route-i remaining) → C → D → E**, with F/G
alongside; H is the standing trust debt (does not gate imports; the guarantee's honesty
depends on naming it). Per phase: one coherent change per commit; witnesses + `Fail`
negatives in `main.v`; `SPEC_CONFORMANCE.md` row citing the spec rule; `Print
Assumptions` on a representative downstream result; push after each green commit.
