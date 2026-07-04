# The cmd↔unified EFFECT-bridge arc (chan/heap/spawn) — PAUSED at the heap milestone

GOAL: extend the bridge's common fragment past output/panic/return/defer — `Cmd` grows
heap/channel/spawn effects, `run_cmd` stays THE sequential authority, the public agreement
theorems grow to cover the new constructors. Proof-only (no golden/plugin risk).

DONE (theorems are the authority): slice 1 — value-parametric calculus (`Section
UnifiedVal`); slice 2 — heap read/write (`CWrite`/`CRead`, unallocated access = ABSENCE)
and the ONE conditional bridge `bridge_heap_agrees` (heap + defers + panics, final-heap
agreement from the `ustart_w` mirrored start; gated via `cmd_unified_surface`).

⚠ STANDING VALUE-SEMANTICS RULE: the GoAny instance carries NO zero semantics — Go's
closed-recv zero is PER ELEMENT TYPE, so every public bridge statement quantifies the
calculus' `vzero` universally, licensed by side conditions keeping runs inside mirrored
allocated cells. ⛔ PRECONDITION FOR CHANNELS: the closed-recv zero must be represented
STRUCTURALLY first (the channel element tag at the `URecv`/`USelect` boundary with
`zero_val`-style typed zeros); a global `GoAny` fallback is FORBIDDEN, and the slice must
land closed-recv proofs for at least TWO distinct element types.

## Remaining slices

2d. **`CAlloc` (design v2, UNSTARTED).** Allocation must be DETERMINISTIC — an observably
   nondeterministic allocator leaks through the binder continuation and could clobber a
   mirrored-but-untraced cell. Shape: `CAlloc : GoAny -> (nat -> Cmd A) -> Cmd A`; `go`
   allocates at `w_next w` and bumps; unified side mirrors `uc_next` and `ustep_alloc`
   allocates EXACTLY there (emits `KWrite l` — allocation IS a write). Freshness is a
   THEOREM only under `builtins.ValidWorld`, so every public allocation surface carries a
   `ValidWorld w` premise with preservation through the body run and the defer unwind;
   the allocator agreement `uc_next = w_next w` threads beside `heap_agrees`. Landing
   obligations: no clobber of an allocated cell; no nil (location-0) allocation from a
   valid start; no unified allocation behavior beyond the cmd side's; a continuation
   branching on `Nat.eqb l 0` cannot reach the `l = 0` branch from a mirrored start.
   `no_heap`/`cmd_no_panic` map `CAlloc` to `false`; `UFrag`/`Cmd_rect'`/`cbind`/`CmdEq`
   gain the arm (and the `unwind_defers`/`eval_cmd` cases follow the interpreter's).

3. **CHANNELS** (single-goroutine deterministic fragment): `CSend`/`CRecv`/`CClose`
   against `w_chans` — BLOCKED on the ⛔ precondition. The ustep side BLOCKS on
   full/empty buffers; `run_cmd` models would-block as `None` (absent), so run_cmd
   COMPLETION is itself the deterministic-fragment gate. Send-on-closed is the modeled
   panic on both sides.

4. **SPAWN** (capstone; design deferred until reached): multi-goroutine ustep runs are
   schedule-nondeterministic vs sequential `run_cmd`. Candidate shapes: ∃-schedule
   agreement (weak); DRF ⇒ all schedules agree on observables (the payoff, composing
   `concurrency.v`); a restricted no-shared-effect child fragment. Decide with 1–3 DONE.

## Standing rules for this arc

- Ground every new projection in the existing authority via a proven equality and USE it
  the same tick. Public statements use PUBLIC vocabulary — completion is `run_cmd c w =
  Some oc`, never a bound. A real result is `Theorem` + `Print Assumptions` + PROGRESS
  "Current gates", never `Local`.
- At every landing: delete newly-subsumed demos/theorems, sweep status prose repo-wide,
  verify every "consumes/via X" against the actual proof.
- Work invariants + reductions on paper BEFORE coding (look for the one reconciliation
  law, not a parallel structure).
