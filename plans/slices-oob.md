# Plan: slices + OOB — the first NON-panic unsafe op (boss-chosen 2026-07-01)

Behavioral safety today = panic-freedom (slice 1 denotes no ptrs/slices/chans, so `panic()` is the only
unsafe op). The boss chose to make it MORE than panic-freedom: denote slices and model **out-of-bounds** (OOB),
the first unsafe op that is not an explicit `panic()`, and prove the gate rejects it.

## What already exists
- **AST**: `EIndex e i` (`e[i]`), `ESlice`, `ESliceLit t es` (`[]T{..}`). No new syntax needed.
- **Model** (`builtins.v`): `GoSlice A := list A`, `TSlice` tag, and the OOB panic value
  `rt_index_oob : GoAny := "runtime error: index out of range"`.
- **GoTypes**: `ptype (ESliceLit t es)` = `PtAgg` when every element is `assignable_to_ty _ t`. `PtRunInt t` is
  a RUNTIME (non-constant) int (how `len` classifies).
- **GoSem**: `eval_value` is ptype-driven (folds `PtIntConst`/`PtTIntConst`/`PtFloatConst`/`PtStr`/`PtBool`);
  denotes NO indexing. **cmd.v** has no slice/index effect.

## The faithfulness pin (drives the brick order) — VERIFIED against gc 1.23
- Slice indexing yields a **non-constant** value — `[]int{10,20}[1]` is a runtime `int`, NOT a Go constant.
- gc compile-checks a **constant** slice index only for **non-negative + int-representable**: it rejects
  `[]int{10,20}[-1]` ("must not be negative") and `[..][2^63]` ("overflows int"), but ACCEPTS an **OOB
  positive** constant `[]int{10,20}[5]` — for a SLICE (unlike an array) OOB is a **run-time PANIC**, not a
  compile error. (Tested with `go build`.)
- So a negative / overflow constant index is **INVALID Go** (supportedness reject); an OOB-positive constant,
  and any **runtime** integer index, are **VALID Go** — their OOB is **behavioral** (a run-time panic) and
  needs runtime values GoSem lacks.
- ⚠ Do NOT guess Go semantics — `go build` a tiny program to settle it. (Cost me 3 bounces before I tested.)

## Bricks (each: faithful, self-contained, accepted-good + rejected-bad fixtures)
- **B1 — supportedness (ptype).** `ptype (EIndex (ESliceLit t es) idx)` for an INT element type `t`: a
  CONSTANT integer index is checked non-negative + int-representable (`0 <= k` && `int_const_repr k GTInt`) —
  a negative/overflow constant → `None` (gc compile error); an OOB-POSITIVE constant, or a RUNTIME integer
  index → `PtRunInt t` (SUPPORTED, valid Go, bounds behavioral); a non-integer index / non-int element →
  `None`. Result is a runtime int (supported-but-not-denoted). GoTypes/GoSafe only; fixtures pin supported
  (`[1]` in-bounds, `[5]` OOB-positive, `[len(..)]` runtime) vs rejected (`[-1]` negative, `["x"]` string).
  **← done.**
- **B2 — denote the in-bounds value.** Fold `[]int{..}[k]` to the k-th element's value so the gate ACCEPTS it.
  Needs a faithful "runtime value with a known static fold" — either a new ptype category or an eval_value arm
  that computes the value while ptype keeps it `PtRunInt` (folding is faithful in VALUE contexts, which is all
  the current fragment has). Pick the least-unfaithful mechanism; do NOT claim it is a Go constant.
- **B3 — runtime index + runtime OOB panic.** The behavioral core: a runtime index `s[i]` denotes to an effect
  that bounds-checks and PANICS (`rt_index_oob`, a `CPan`) on OOB. Needs runtime values in GoSem + a slice
  effect in cmd.v. The behavioral gate must then require in-bounds EVIDENCE (`i < len s`) — the evidence-carrying
  / check-and-branch discipline (CLAUDE rule 4) — or reject. This is where the gate proves NO runtime OOB.
- **B4 — extend the panic-free/behavioral gate + soundness** to cover OOB: `panic_free_denotable` (or its
  successor) accepts a slice-using program only if all indexing is provably in-bounds; the gated emitter's
  soundness theorem extends to "emit ⟹ no explicit panic AND no OOB".

## Honesty
B1 alone is the SUPPORTEDNESS (compile-time OOB) brick — it does NOT yet denote slices or model the runtime
OOB panic. Frame it exactly so; the "behavioral safety > panic-freedom" claim lands with B3/B4.
