# The cmd↔unified EFFECT-bridge arc (chan/heap/spawn)

GOAL: extend the bridge's common fragment past output/panic/return/defer — `Cmd` grows
heap/channel/spawn effects, `run_cmd` stays THE sequential authority (interpreting them
against `World`'s typed `w_refs`/`w_chans`), and the public agreement theorems grow to
cover the new constructors.  Proof-only (no golden/plugin risk).  Predecessor arc (defer,
COMPLETE): `bridge_agrees` — its ladder discipline and landing checklist apply verbatim.

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
  the cmd bridge at `V := GoAny` (`cmd_unified.uzero = anyt TUnit tt` for the closed-recv
  zero — unreachable today, `cmd_to_ucmd`'s image has no `URecv`).  WHY THIS IS SAFE: the
  TRACE (the race-freedom substrate) carries NO values — `KWrite l` / `KRecv c s` /
  `KSend c` are location/position-only — so `concurrency.v`'s trace theory and
  `unified.v`'s race/liveness theorems are value-agnostic; `UOut` carries `list GoAny` at
  every instantiation.  (The originally-sketched `nat → GoAny` CONCRETIZATION with an
  embedding injection was superseded during implementation: Go's tags are bounded/sealed,
  so no TOTAL `nat → GoAny` injection exists — parametricity dissolves the problem instead
  of encoding around it.)  `vzero` at `nat` is `0`, exactly the old rule; TYPED zero-value
  faithfulness stays on the `run_cmd`/`World` side.

## The ladder (each slice an independently green commit)

1. **Value generalization — LANDED**: `unified.v` value-parametric (`{V}` + `vzero`,
   the constructors/step-composition lemmas carry both implicitly via `Arguments`, the
   relations keep them explicit for statements); demos/embedding/sessions instantiate
   `nat` (relation sites gain the literal `0`), `cmd_unified.v`/`GoSemSafe.v` instantiate
   `GoAny` via `uzero`; the slice-9 embedding compiled UNCHANGED at `V := nat`.  All
   gates green, golden byte-identical, zero-axiom manifest unchanged.
2. **HEAP**: `Cmd` += `CWrite : nat → GoAny → Cmd A → Cmd A` and
   `CRead : nat → (GoAny → Cmd A) → Cmd A` (the cmd side stays CONCRETE at `GoAny` —
   it is the typed model, not a calculus) (⚠ first BINDER constructor — `Cmd_rect'`
   and every structural induction gain a under-the-binder case); `run_cmd` interprets
   against `w_refs` (cell ≅ any); `cmd_to_ucmd` maps 1-for-1; `bridge_agrees` extends
   with a heap-state component in the invariant.  ⚠ OPEN DESIGN (work on paper first):
   `uc_heap` is TOTAL (default zero) while `w_refs` is PARTIAL — reading unallocated is
   a modeled nil-deref panic on the cmd side (the `rt_div_zero` precedent) but a
   default-bind on the ustep side; the agreement must relate heaps on ALLOCATED
   locations and scope reads accordingly.  Allocation (`CAlloc` binding a fresh
   location off `w_next`) has NO ustep counterpart rule — defer alloc to its own
   sub-slice with the unified.v rule addition, or scope slice 2 to pre-allocated
   configurations.
3. **CHANNELS** (single-goroutine deterministic fragment): `CSend`/`CRecv`/`CClose`
   against `w_chans`.  The ustep side BLOCKS (a full-buffer send / empty-buffer recv has
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
