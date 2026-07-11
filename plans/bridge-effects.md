# The cmd↔unified EFFECT-bridge arc — heap + allocation + CHANNELS landed; SPAWN remains

GOAL: extend the bridge's common fragment past output/panic/return/defer — `Cmd` grows
heap/channel/spawn effects, `run_cmd` stays THE sequential authority, the public agreement
theorems grow to cover the new constructors. Proof-only (no golden/plugin risk).

DONE (theorems are the authority; per-slice landing detail is in git + PROGRESS "Current gates"):
- slice 1 — value-parametric calculus (`Section UnifiedVal`).
- slice 2 — heap read/write/ALLOC (`CWrite`/`CRead`/`CAlloc`; unallocated access = ABSENCE;
  deterministic allocation, freshness a THEOREM only under `GoHeap.AllocFrontierOk`).
- slice 3 — the CHANNEL trio (`CChSend`/`CChRecv`/`CChClose`; per-site TYPED closed-recv zeros
  through each cell's own tag; would-block = ABSENCE; capacities pinned via `ucap_of_world`).
  The closed-recv zero is a per-site FIELD (`URecv`/`USelect`) — the global `vzero` parameter is
  DELETED, so no `GoAny` fallback is representable through the public path.
The ONE conditional bridge `bridge_effects_agree` covers it all (heap + buffers + closedness +
allocator + defers + panics, from the `ustart_w` mirrored start under `chans_open`), manifest-gated
via `cmd_unified_surface`.

⚠ WfTrace / HAPPENS-BEFORE BOUNDARY (permanent invariant): the bridge concludes
`bufs_agree`/`closed_agree` only, NEVER `WfTrace`. `bufs_of_world` gives every INITIAL buffered
value synthetic position 0 with no producing `KSend` in the empty start trace, so a buffered recv
can emit `KRecv c 0` unbacked. This bridge MUST NOT compose with `concurrency.v`'s happens-before /
race-freedom without an extra invariant (empty initial buffers, or a per-value buffer-origin
invariant). Docs must never imply race-freedom from `bridge_effects_agree` alone.

## REMAINING — SPAWN (capstone; design deferred until reached)

Multi-goroutine `ustep` runs are schedule-nondeterministic vs sequential `run_cmd`. Candidate
shapes: ∃-schedule agreement (weak); DRF ⇒ all schedules agree on observables (the payoff,
composing `concurrency.v`); a restricted no-shared-effect child fragment.

## Standing rules for this arc

- Ground every new projection in the existing authority via a proven equality and USE it the same
  tick. Public statements use PUBLIC vocabulary — completion is `run_cmd c w = Some oc`, never a
  bound. A real result is `Theorem` + `Print Assumptions` + PROGRESS "Current gates", never `Local`.
- At every landing: delete newly-subsumed demos/theorems, sweep status prose repo-wide, verify every
  "consumes/via X" against the actual proof.
- Work invariants + reductions on paper BEFORE coding (look for the one reconciliation law, not a
  parallel structure).
