# The cmd↔unified EFFECT-bridge arc (chan/heap/spawn) — PAUSED at the heap milestone

GOAL: extend the bridge's common fragment past output/panic/return/defer — `Cmd` grows
heap/channel/spawn effects, `run_cmd` stays THE sequential authority, and the public agreement
theorems grow to cover the new constructors.  Proof-only (no golden/plugin risk).

DONE (detail lives in the theorem statements + git history, not re-enumerated here):
slice 1 — the value-parametric calculus (`Section UnifiedVal`, `V`/`vzero`; `rstep` embedding at
`V := nat` unchanged); slice 2 — heap read/write (`CWrite`/`CRead` typed against `w_refs`,
unallocated access = ABSENCE, `no_heap` fragment carries `run_cmd_terminates`) and the ONE
conditional heap bridge `bridge_heap_agrees` (any completing command — heap + defers + panics —
agrees end-to-end incl. final heaps from the `ustart_w` mirrored start; gated via
`cmd_unified_surface`).

⚠ STANDING VALUE-SEMANTICS RULE (governs every future bridge statement): the GoAny instance
carries NO zero semantics — Go's closed-recv zero is PER ELEMENT TYPE, so every public bridge
statement quantifies the calculus' `vzero` universally (`Section BridgeVal`'s `vz`), licensed by
side conditions keeping runs inside mirrored allocated cells.  ⛔ PRECONDITION FOR CHANNELS: the
closed-recv zero must be represented STRUCTURALLY first — the channel element tag at the
`URecv`/`USelect` boundary with `zero_val`-style typed zeros; a global `GoAny` fallback (any tag)
is FORBIDDEN, and the slice must land closed-recv proofs for at least TWO distinct element types.

## Remaining slices

2d. **`CAlloc` — allocator-EXACT design v2, UNSTARTED** (v1's trace-freshness sketch was REJECTED
   in review: an observable nondeterministic allocator — the binder continuation can branch on
   the chosen location, and a trace-fresh choice could clobber a mirrored-but-untraced cell.
   Deterministic allocation + explicit freshness invariants beat churn avoidance):
   - cmd side: `CAlloc : GoAny -> (nat -> Cmd A) -> Cmd A`; `go`'s arm allocates at `w_next w`
     and bumps it — freshness there is a THEOREM only under `builtins.ValidWorld`, so every
     public allocation surface carries a `ValidWorld w` premise with PRESERVATION obligations
     through the body run and the defer unwind (`valid_alloc_*` analogs for `go`/`run_defers`).
   - unified side: `uc_next : nat` on `UConfig` (mirrored from `World.w_next`); `ustep_alloc`
     allocates EXACTLY at `uc_next` and bumps it.  PRECISION: this makes the allocation choice
     DETERMINISTIC (no location nondeterminism to leak) — it does NOT make bad allocator states
     unrepresentable (`UConfig` is freely constructible); freshness/consistency remain EXPLICIT
     premises/invariants carried by every public allocation surface.  Config churn (every
     `mkUCfg` literal, the rstep embedding) is the accepted cost.  The rule emits `KWrite l`
     (allocation IS a write — no new event kind).
   - proof gates, all explicit at the landing: `ValidWorld w` on every public allocation surface;
     `ValidWorld` preservation through `go` and `run_defers`; the allocator agreement
     `uc_next = w_next w` threaded beside `heap_agrees` through the bridge machinery; no clobber
     of an allocated cell; no nil (location-0) allocation from a valid start; no unified
     allocation behavior beyond the cmd side's.
   - regression obligations AT LANDING: (i) a continuation branching on `Nat.eqb l 0` cannot
     reach the `l = 0` branch from a `ValidWorld`-mirrored start; (ii) allocation never lands on
     an existing allocated cell; (iii) no unified allocation behavior beyond the cmd side's.
   - `no_heap`/`cmd_no_panic` map `CAlloc` to `false` (binder); `UFrag` grows the alloc case;
     `Cmd_rect'`/`cbind`/`CmdEq`/`go_no_panic` gain the arm.

3. **CHANNELS** (single-goroutine deterministic fragment): `CSend`/`CRecv`/`CClose` against
   `w_chans` — BLOCKED on the ⛔ precondition above.  The ustep side BLOCKS (a full-buffer send /
   empty-buffer recv has no rule); model would-block in `run_cmd` as `None` (absent — the ∃-fuel
   discipline), so run_cmd COMPLETION is itself the deterministic-fragment gate, no side
   predicate.  Send-on-closed is the modeled panic (both sides have it: `ustep_send_closed`).

4. **SPAWN** (the capstone — design deferred until reached): multi-goroutine ustep runs are
   schedule-nondeterministic while `run_cmd` is sequential.  Candidate shapes: (a) ∃-schedule
   agreement (honest but weak); (b) the real payoff: DRF ⇒ all schedules agree on observables,
   composing `concurrency.v`'s race-freedom; (c) a restricted no-shared-effect child fragment.
   Decide with slices 1–3 DONE.

## Standing rules for this arc (from the defer arc's bounce history)

- Ground every new projection in the existing authority via a proven equality, and USE it the
  same tick.  Public statements use PUBLIC vocabulary only (fuel quantified existentially).  A
  real result is `Theorem` + `Print Assumptions` + PROGRESS "Current gates", never `Local`.
- At every landing: delete newly-subsumed demos/theorems (hypothesis-strength test, ALL
  siblings), sweep status/count/framing prose repo-wide, verify every "consumes/via X" against
  the actual proof, full boundary on every conditional-theorem mention.  Replacement prose
  describes what REMAINS, never what left.
- Work invariants + reductions on paper BEFORE coding (the defer capstone's seed-linearity
  lesson: look for the one reconciliation law, not a parallel structure).
