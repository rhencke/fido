# The cmd↔unified EFFECT-bridge arc (chan/heap/spawn)

GOAL: extend the bridge's common fragment past output/panic/return/defer — `Cmd` grows
heap/channel/spawn effects, `run_cmd` stays THE sequential authority (interpreting them
against `World`'s typed `w_refs`/`w_chans`), and the public agreement theorems grow to
cover the new constructors.  Proof-only (no golden/plugin risk).  Predecessor arc (defer,
COMPLETE): its ladder discipline and landing checklist apply verbatim (its capstone theorem has since been subsumed by the heap bridge).

## The value-universe fork (decided up front — the design crux)

`unified.v`'s memory/channel values are `nat` (mirroring the `rstep` calculus);
`World`'s cells are dependently typed — `RefCell = { T & tag×T }` is the SAME data as
`GoAny = { A & A×tag }` up to pair order.  Three ways to relate them:

- (A) nat-mirrored `Cmd` constructors — REJECTED: forks a second value universe inside
  the typed model (`run_cmd` would need a parallel nat-state bolted onto `World`).
- (B) typed `Cmd` + a partial `GoAny → option nat` ERASURE at the bridge — REJECTED as
  the half-measure: the agreement theorem gets gated on an encodability predicate, and
  it leaves `UOut`'s already-exact `GoAny` payload asymmetric with the other effects.
- (C) ★CHOSEN + LANDED (slice 1): the calculus is VALUE-PARAMETRIC — ONE definition
  `Section UnifiedVal / Context {V} / Variable vzero` covering `UCmd`/`UConfig`/`ustep`
  and every generic theorem, with TWO instantiations: the `rstep` embedding at `V := nat`
  (values IDENTITY — the existing simulation survives verbatim, no injection at all) and
  the cmd bridge at `V := GoAny`.  WHY THIS IS SAFE: the TRACE (the race-freedom
  substrate) carries NO values — `KWrite l` / `KRecv c s` / `KSend c` are
  location/position-only — so `concurrency.v`'s trace theory and `unified.v`'s
  race/liveness theorems are value-agnostic; `UOut` carries `list GoAny` at every
  instantiation.  (The originally-sketched `nat → GoAny` concretization with an embedding
  injection was superseded during implementation: an injection through an unbounded
  carrier exists (e.g. string-encoded naturals under `TString`), but it is not
  SEMANTICS-PRESERVING as a model — calculus naturals masquerading as Go strings, with a
  projection bolted onto every value-consuming rule; parametricity keeps each side's
  values exactly what that side says they are.)  `vzero` at `nat` is `0`, exactly the old
  rule.
  ⚠ THE GoAny INSTANCE CARRIES NO ZERO SEMANTICS: Go's closed-recv zero is PER ELEMENT
  TYPE, and no single `GoAny` can stand for all of them.  Every public bridge statement
  therefore QUANTIFIES the calculus' `vzero` parameter universally (`cmd_unified`'s
  `Section BridgeVal` variable `vz`): `bridge_heap_agrees`'s license is its side
  conditions — the `ustart_w` start heap mirrors the World's ALLOCATED
  cells (`heap_of_world_agrees`) and the `go`-completion premise keeps the run inside
  them, so the `vz` defaults on unallocated locations are never consulted.  ⛔ PRECONDITION
  FOR SLICE 3 (channels): the closed-recv zero must be represented STRUCTURALLY first —
  the channel element tag at the `URecv`/`USelect` boundary with `zero_val`-style typed
  zeros; a global `GoAny` fallback (any tag) is FORBIDDEN, and the slice must land
  closed-recv proofs for at least TWO distinct element types, each binding that type's
  own zero.

## The ladder (each slice an independently green commit)

1. **Value generalization — LANDED**: `unified.v` value-parametric (`{V}` + `vzero`,
   the constructors/step-composition lemmas carry both implicitly via `Arguments`, the
   relations keep them explicit for statements); demos/embedding/sessions instantiate
   `nat` (relation sites gain the literal `0`), `cmd_unified.v`/`GoSemSafe.v` instantiate
   `GoAny` with the vzero parameter UNIVERSALLY QUANTIFIED (`vz`; licenses per theorem —
   see the fork note above); the slice-9 embedding compiled UNCHANGED at `V := nat`.
2. **HEAP (read/write)** — COMPLETE (parts i + ii; the general conditional heap bridge is landed).  ALLOCATION is separate and NON-CORE today: no `CAlloc` constructor exists — a `Cmd` cannot express allocation at all (unrepresentable, not merely unproven) — and adding it is 2d below.
   CURRENT STATE (one authority; the theorem names carry the detail):
   - `Cmd` has the typed heap pair (`CWrite` tag-preserving via `tag_eq`; `CRead` binds
     the boxed cell — the syntax's first BINDER constructor); an UNALLOCATED access is
     ABSENCE (`go` is option-valued, `run_cmd`'s signature unchanged; the completion
     premise `run_cmd = Some` is the well-formedness gate; `cread_unallocated_absent`
     pins why no unconditional heap bridge exists).
   - Fragments: `no_heap` (decidable; `cmd_no_panic ⊆ no_heap`, `no_defer ⊆ no_heap`)
     carries `run_cmd_terminates`;
     `run_cmd_out_monotone` stays premise-free for ANY `c` (grounded in `go` via
     `go_out_monotone`).
   - Seal: `UFrag`/`cmd_to_ucmd_fragment` = translated image (no channel/spawn form
     ever — so no closed-recv rule is reachable from a bridged run).
   - The heap agreement (part ii-a): `heap_agrees` (allocated locations only) +
     `heap_of_world`/`ustart_w` (canonical mirrored start heap — premise-free public
     statements) + `body_runs_sem` (Phase A grounded in `go`'s RESULT; trace existential,
     heap steps emit `KWrite`/`KRead`) + the seed-linearity pair
     (`run_defers_panic_stays`/`run_defers_seed_linear`) + `unwind_heap` (the semantic
     2-mode deferred-heap unwind) + `bridge_heap_agrees` (gated): ANY completing command
     (heap ops and defers included) agrees end-to-end INCLUDING final heaps.
   DESIGN FACTS that shaped it (details in git history): monad laws restated over the
   pointwise `CmdEq` (eq unprovable under a binder without funext); boolean predicates
   map heap ctors to `false` (cannot scan under a binder); the syntactic size/projection
   layer is undefinable under a binder, so semantic grounding in `go` replaces it where
   heap ops must be covered; every `Cmd` match stays WILDCARD-FREE (a wildcard arm is
   fail-open in proof form).
   ONE bridge, ONE lane: `bridge_heap_agrees` over the semantic machinery
   (`body_runs_sem` / seed-linearity / `unwind_heap` / `pop_defer_step`); the no-panic
   laws are `go`-grounded (`go_no_panic` → `run_defers_no_panic` →
   `run_cmd_no_panic_ret`); GoSemSafe's operational theorems compose
   `run_cmd_terminates` + the bridge over the `ustart_w` mirrored-heap start.
   Then 2d `CAlloc` — DESIGN v2 (allocator-EXACT; the v1 trace-freshness sketch was
   REJECTED in review as an observable nondeterministic allocator — the binder
   continuation can branch on the chosen location, and a trace-fresh choice could clobber
   a mirrored-but-untraced allocated cell.  Deterministic allocation + explicit
   freshness invariants beat churn avoidance):
   - cmd side: `CAlloc : GoAny -> (nat -> Cmd A) -> Cmd A`; `go`'s arm allocates at
     `w_next w` and bumps it — BUT freshness there is a THEOREM only under
     `builtins.ValidWorld` (`ref_new`'s own invariant), so every public allocation bridge
     surface carries a `ValidWorld w` premise, with PRESERVATION obligations through the
     body run and the defer unwind (the `valid_alloc_*` analogs for `go`/`run_defers`).
   - unified side: `uc_next : nat` on `UConfig` (mirrored from `World.w_next`);
     `ustep_alloc` allocates EXACTLY at `uc_next` and bumps it.  PRECISION: this makes
     the allocation choice DETERMINISTIC (no location nondeterminism exists to leak) —
     it does NOT by itself make bad allocator states unrepresentable, since `UConfig` is
     a freely constructible record; freshness/consistency remain EXPLICIT theorem
     premises and invariants (next bullet), carried and preserved by every public
     allocation surface.  The config churn (every `mkUCfg` literal, the rstep embedding
     at `V := nat`) is the accepted cost of determinism.  The rule emits `KWrite l`
     (allocation IS a write — no new event kind).
   - the EXACT future proof gates, all explicit at the landing: `ValidWorld w` on every
     public allocation surface; `ValidWorld` preservation through `go` and `run_defers`
     (the `valid_alloc_*` analogs); the allocator agreement `uc_next = w_next w`
     threaded beside `heap_agrees` through `body_runs_sem`/`unwind_heap`/the assembly;
     no clobber of an allocated cell; no nil (location-0) allocation from a valid start;
     no unified allocation behavior beyond the cmd side's.
   - regression obligations AT LANDING: (i) a continuation branching on `Nat.eqb l 0`
     cannot reach the `l = 0` branch from a `ValidWorld`-mirrored start (location 0 is
     reserved nil); (ii) allocation never lands on an existing allocated cell; (iii) no
     unified allocation behavior exists beyond the cmd side's (the rule is deterministic
     by construction).
   - `no_heap`/`cmd_no_panic` map `CAlloc` to `false` (binder); `UFrag` grows the alloc
     case; `Cmd_rect'`/`cbind`/`CmdEq`/`go_no_panic` gain the arm.
   2d is UNSTARTED — the design above is its ladder.
3. **CHANNELS** (single-goroutine deterministic fragment): `CSend`/`CRecv`/`CClose`
   against `w_chans` — BLOCKED on the ⛔ precondition above (structural typed closed-recv
   zero; two-element-type proofs).  The ustep side BLOCKS (a full-buffer send / empty-buffer recv has
   no rule); model would-block in `run_cmd` as `None` (absent — the ∃-fuel discipline),
   so run_cmd COMPLETION is itself the deterministic-fragment gate, no side predicate.
   Send-on-closed is the modeled panic (both sides have it: `ustep_send_closed`).
4. **SPAWN** (the capstone — design deferred until reached): multi-goroutine ustep runs
   are schedule-nondeterministic while `run_cmd` is sequential.  Candidate shapes:
   (a) ∃-schedule agreement (run_cmd's order is one valid interleaving — honest but
   weak); (b) the real payoff: DRF ⇒ all schedules agree on observables, composing
   `concurrency.v`'s race-freedom; (c) a restricted no-shared-effect child fragment.
   Decide with slices 1–3 landed.

## Standing rules for this arc (from the defer arc's bounce history)

- Ground every new projection in the existing authority via a proven equality, and USE
  it the same tick.  Public statements use PUBLIC vocabulary only (fuel included —
  quantify it existentially).  A real result is `Theorem` + `Print Assumptions` +
  PROGRESS "Current gates", never `Local`.
- At every landing: delete newly-subsumed demos/theorems (hypothesis-strength test,
  ALL siblings), sweep status/count/framing prose repo-wide, verify every
  "consumes/via X" against the actual proof, full boundary on every conditional-theorem
  mention.  Replacement prose describes what REMAINS, never what left.
- Work invariants + reductions on paper BEFORE coding (the defer capstone's
  seed-linearity lesson: look for the one reconciliation law, not a parallel structure).
