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
- **GoSem** (post-B2): `eval_value` is ptype-driven EXCEPT an `EIndex (ESliceLit..)` arm that folds a constant
  in-bounds int-slice index to the element; it denotes CONSTANT in-bounds indexing (B2), NOT runtime/OOB.
  **cmd.v** still has no slice/index effect (needed for B3's runtime index + OOB panic).

## The faithfulness pin (drives the brick order) — VERIFIED against gc 1.23
- Slice indexing yields a **non-constant** value — `[]int{10,20}[1]` is a runtime `int`, NOT a Go constant.
- gc compile-checks a **constant** slice index only for **non-negative + int-representable**: it rejects
  `[]int{10,20}[-1]` ("must not be negative") and `[..][2^63]` ("overflows int"), but ACCEPTS an **OOB
  positive** constant `[]int{10,20}[5]` — for a SLICE (unlike an array) OOB is a **run-time PANIC**, not a
  compile error. (Tested with `go build`.)
- So a negative, or a genuinely int-overflowing (strictly **greater** than the platform `int` max — e.g.
  `2^63`, one past the 64-bit `int64` max `2^63-1`), constant index is **INVALID Go** on any platform
  (supportedness reject); an **OOB-positive** constant that *fits* the platform `int`, and any **runtime**
  integer index, are **VALID Go** — their OOB is **behavioral** (a run-time panic) and needs runtime values
  GoSem lacks. (Fido's 32-bit `GTInt` guard rejects *more* than this — see the conservatism bullet below.)
- ⚠ Fido models `int` CONSERVATIVELY (`GTInt` = 32-bit min, since Go `int` is platform 32/64-bit), so B1's
  representability check (`int_const_repr _ GTInt`) is fail-CLOSED, NOT an exact gc match: a large index valid
  only on a 64-bit gc (`[2^40]`) is conservatively REJECTED (safe incompleteness), consistent with Fido's
  existing conservative int-literal handling. The `[2^63]` fixture is genuinely invalid on any platform.
- ⚠ Do NOT guess Go semantics — `go build` a tiny program to settle it. (Cost me 3 bounces before I tested.)

## Bricks (each: faithful, self-contained, accepted-good + rejected-bad fixtures)
- **B1 — supportedness (ptype).** `ptype (EIndex (ESliceLit t es) idx)` for an INT element type `t`: a
  CONSTANT integer index is checked non-negative + int-representable (`0 <= k` && `int_const_repr k GTInt`) —
  a negative constant (a gc compile error) or one over Fido's conservative 32-bit `int` (fail-closed, see the
  pin) → `None`; an OOB-POSITIVE constant, or a RUNTIME integer
  index → `PtRunInt t` (SUPPORTED, valid Go, bounds behavioral); a non-integer index / non-int element →
  `None`. Result is a runtime int (supported-but-not-denoted). GoTypes/GoSafe only; fixtures pin supported
  (`[1]` in-bounds, `[5]` OOB-positive, `[len(..)]` runtime) vs rejected (`[-1]` negative, `[2^63]` overflow,
  `["x"]` string). **← done.**
- **B2 — denote the in-bounds value (DONE).** `eval_value` gains an `EIndex (ESliceLit t es) idx` arm: a
  CONSTANT in-bounds index folds to the k-th element's boxed value (evidence-carrying — `nth_error` yields a
  value ONLY in-bounds, so OOB / negative / runtime → `None`, undenoted). `ptype` keeps it `PtRunInt` (Go: a
  non-constant int); folding is faithful in the VALUE contexts the fragment has (verified `go run`:
  `println([]int{10,20}[1])` prints `20`). Result — the boss's goal for the CONSTANT fragment: the gate ACCEPTS
  a provably-in-bounds constant slice-index (`println([]int{10,20}[1])` denotes) and REJECTS an OOB one (`[5]`
  undenoted → gate rejects; a slice OOB is a run-time panic). GoSem only; the in-bounds denotation is
  transitively CERTIFIED via the gated `denotable_stmts_main_denotes`.
- **B3 — runtime index + runtime OOB panic.** The behavioral core: a runtime index `s[i]` denotes to an effect
  that bounds-checks and PANICS (`rt_index_oob`, a `CPan`) on OOB. Needs runtime values in GoSem + a slice
  effect in cmd.v. The behavioral gate must then require in-bounds EVIDENCE (`i < len s`) — the evidence-carrying
  / check-and-branch discipline (CLAUDE rule 4) — or reject. This is where the gate proves NO runtime OOB.
- **B4 — extend the panic-free/behavioral gate + soundness** to cover OOB: `panic_free_denotable` (or its
  successor) accepts a slice-using program only if all indexing is provably in-bounds; the gated emitter's
  soundness theorem extends to "emit ⟹ no explicit panic AND no OOB".

## Honesty
B1+B2 cover the CONSTANT-index fragment. B1 (supportedness) makes an int-slice index SUPPORTED, rejecting only
what gc compile-errors — a negative constant, a non-integer index, and (CONSERVATIVELY, fail-closed, Fido's
32-bit `int` — NOT exactly gc's boundary; a 64-bit gc accepts `[2^40]` that Fido rejects, safe incompleteness)
an int-overflowing constant. It does NOT bounds-check (a slice OOB is a valid-Go run-time panic — SUPPORTED).
B2 (denotation) folds a constant IN-BOUNDS index to the element value and DECLINES OOB — so the gate now ACCEPTS
a provably-in-bounds constant slice-index and REJECTS a constant OOB one. That IS "behavioral safety >
panic-freedom" for the CONSTANT fragment (a non-`panic()` unsafe op the gate rejects). STILL MISSING: RUNTIME
indexing + the runtime OOB panic effect (B3 — needs GoSem runtime values + a cmd.v slice effect) and the
gate/soundness extension over slices (B4).
