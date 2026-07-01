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
  in-bounds int-slice index to the element; it denotes only the FULLY-EVALUABLE ALL-CONSTANT in-bounds
  subfragment (B2) — a runtime index, a runtime element, or OOB is NOT denoted. **cmd.v** still has no
  slice/index effect (needed for B3's runtime index + OOB panic).

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
- **B2 — denote the in-bounds value (DONE).** `eval_value` gains an `EIndex (ESliceLit t es) idx` arm that
  evaluates the WHOLE literal (`eval_int_slice_elems` — EVERY element assignability-gated to `t`, then boxable
  constants boxed to `t` (a wrong-typed const is DECLINED, not retyped), all-or-`None`) then
  indexes the value list at the constant in-bounds `k`. Whole-literal is REQUIRED, not just bounds: Go builds
  the entire literal before indexing, so a runtime/panicking/out-of-range element — even an UNSELECTED one
  (`[]int{20, 1/len([]int{})}[0]` PANICS, verified `go run`) — makes the fold `None` (undenoted), never a wrong
  value. OOB / negative / non-int-representable / runtime INDEX → `None` too. `ptype` keeps it `PtRunInt` (Go: a
  non-constant int); folding is faithful in the VALUE contexts the fragment has (`println([]int{10,20}[1])` prints
  `20`). The evaluator boundary is SEALED to `ptype`'s: `eval_int_slice_elems` gates each element on
  `assignable_to_ty` (so `[]int{int64(1)}` — a wrong-typed const — is declined exactly as `ptype` declines it),
  and the arm's constant index is gated on `int_const_repr k GTInt` — proved by `eval_slice_index_supported`
  (the reduction's hypotheses IMPLY `ptype (EIndex ..) = Some (PtRunInt t)`, a strict INCLUSION), so there is NO
  looser second boundary. Result — the boss's B2 denotation goal at the DENOTATION layer, proved at
  CLASS level (`forall`) over the FULLY-EVALUABLE ALL-CONSTANT subfragment (a strict SUBSET of `ptype`-support —
  runtime index/elements are supported but B2-undenoted, `slice_index_supported_but_undenoted`) by
  `eval_slice_index_inbounds_class` (in-bounds → k-th boxed element value) + `eval_slice_index_oob_class`
  (OOB → `None`) via `eval_slice_index_reduces` (all gated in `gosem_trust_surface`): a provably-in-bounds
  all-constant slice-index DENOTES, while an OOB one (or one with a runtime element) is DECLINED (not folded to a
  wrong value). GoSem only; the in-bounds denotation is transitively CERTIFIED via the gated
  `denotable_stmts_main_denotes`. The EMISSION-GATE consequence on a representative valid-Go pair is
  `GoSemSafe.panic_free_gate_slice` (see Honesty).
- **B3 — runtime index + runtime OOB panic.** The behavioral core: a runtime index `s[i]` denotes to an effect
  that bounds-checks and PANICS (`rt_index_oob`, a `CPan`) on OOB. Needs runtime values in GoSem + a slice
  effect in cmd.v. The behavioral gate must then require in-bounds EVIDENCE (`i < len s`) — the evidence-carrying
  / check-and-branch discipline (CLAUDE rule 4) — or reject. This is where the gate proves NO runtime OOB.
- **B4 — extend the panic-free/behavioral gate + soundness** to cover OOB: `panic_free_denotable` (or its
  successor) accepts a slice-using program only if all indexing is provably in-bounds; the gated emitter's
  soundness theorem extends to "emit ⟹ no explicit panic AND no OOB".

## Honesty
Three distinct authorities, do NOT conflate: (1) B1 = `ptype` SUPPORTEDNESS, which covers the broad
constant-index cases (and even a runtime index / runtime same-typed element — valid Go); (2) B2 = the CLASS
DENOTATION theorem, which covers ONLY the fully-evaluable all-constant slice-index SUBFRAGMENT (strictly smaller
than B1 — a runtime index/element is supported but B2-undenoted); (3) the representative EMISSION-GATE fixture
`panic_free_gate_slice`. B1 (supportedness) makes an int-slice index SUPPORTED, rejecting only
what gc compile-errors — a negative constant, a non-integer index, and (CONSERVATIVELY, fail-closed, Fido's
32-bit `int` — NOT exactly gc's boundary; a 64-bit gc accepts `[2^40]` that Fido rejects, safe incompleteness)
an int-overflowing constant. It does NOT bounds-check (a slice OOB is a valid-Go run-time panic — SUPPORTED).
B2 (denotation) folds an IN-BOUNDS index into an ALL-CONSTANT slice literal to the element value — the WHOLE
literal must evaluate (a runtime/panicking element, even unselected, rejects it, since Go builds the literal
before indexing) — and DECLINES OOB. The CLASS-LEVEL property (over the FULLY-EVALUABLE ALL-CONSTANT slice-index
SUBFRAGMENT, not a fixture) is proved by the `forall` theorems `GoSem.eval_slice_index_inbounds_class` (in-bounds
→ the k-th boxed element VALUE) and `eval_slice_index_oob_class` (OOB → `None`), both via the reduction
`eval_slice_index_reduces` (`eval_value` of the index = `nth_error vs (Z.to_nat k)`), all gated zero-axiom in
`gosem_trust_surface`. That subfragment is a STRICT SUBSET of `ptype`-support, NOT a looser private evaluator:
the evaluator gates elements on `assignable_to_ty` and the index on `int_const_repr k GTInt` — the SAME checks
`ptype` uses — and `eval_slice_index_supported` proves those hypotheses IMPLY `ptype (EIndex ..) = Some (PtRunInt
t)` (an INCLUSION, not equality — `ptype` ALSO supports a runtime index or runtime elements, which B2 does not
yet denote: `slice_index_supported_but_undenoted`). So a wrong-typed element (`[]int{int64(1)}`) or a
non-representable index is declined identically by both (regressions `slice_index_illtyped_element_undenoted` /
`slice_index_unrepresentable_index_undenoted`). That IS "behavioral safety > panic-freedom" for that subfragment
at the DENOTATION layer (a non-`panic()` unsafe op the denotation declines, never folding it to a wrong value). B2's OOB handling
REACHES the behavioral EMISSION gate on a REPRESENTATIVE valid-Go pair: `GoSemSafe.panic_free_gate_slice` (gated
in `gosem_panic_free_surface`) proves BOTH programs are SUPPORTED (valid Go — sharing the fixture with the
support authority), the in-bounds one is ACCEPTED + EMITTED by `panic_free_gate` / `emit_panic_free_gated`, and
the OOB one (valid Go!) is REJECTED — behaviorally, via NON-DENOTATION (GoSem declines to model the OOB run-time
panic, the same faithful-or-absent mechanism that declines any unmodeled construct — NOT a positive proof the OOB
program is unsafe). That emission-gate fixture is a representative PIN (a non-`panic()` unsafe op reaching the
gate on a valid-Go program), distinct from the class-level denotation theorems above. (Boss deferred B3 —
runtime index — so the RUNTIME half stays open.) STILL MISSING: RUNTIME indexing + the runtime OOB panic effect
(B3 — needs GoSem runtime values + a cmd.v slice effect) and the gate/soundness extension over slices (B4).
