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

## The faithfulness pin (drives the brick order)
- Go treats slice indexing as **non-constant** — `[]int{10,20}[1]` is a runtime `int`, NOT a Go constant.
- A **constant** index OOB on a known-length literal (`[]int{10,20}[5]`) is a Go **COMPILE error**
  ("index out of bounds"), NOT a runtime panic.
- A **runtime** index (`s[i]`, `i` a runtime value) is where OOB is a genuine **runtime panic** — and that
  needs a runtime-value model GoSem does not have yet (it is constant-folding only).

So OOB splits into a compile-time half (decidable now) and a runtime half (needs runtime values).

## Bricks (each: faithful, self-contained, accepted-good + rejected-bad fixtures)
- **B1 — compile-time bounds check (ptype).** `ptype (EIndex (ESliceLit t es) (EInt k))` for an INT element
  type `t`: in-bounds (`0 <= k < len es`, elements well-typed) → `PtRunInt t` (SUPPORTED, runtime, like `len`);
  OOB / non-constant index / non-int element → `None` (UNSUPPORTED — faithful to Go's compile error). Result:
  an in-bounds constant int-slice index is supported-but-not-denoted; an OOB one is REJECTED by the gate (via
  unsupportedness). GoTypes-only; fixtures pin both. **← first brick, this tick.**
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
