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
  TYPE, and no single `GoAny` can stand for all of them.  The bridge therefore QUANTIFIES
  the calculus' `vzero` parameter universally (`cmd_unified`'s `Section BridgeVal`
  variable `vz` — every public bridge statement holds for an ARBITRARY value), licensed
  by the gated image seal `cmd_to_ucmd_fragment` (the image is the output/panic/defer
  fragment — no `URecv`/`USelect`, so no rule consulting `vz` can fire).  ⛔ PRECONDITION
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
   `GoAny` with the vzero parameter UNIVERSALLY QUANTIFIED (`vz`, sealed unreachable by
   the gated `cmd_to_ucmd_fragment`); the slice-9 embedding compiled UNCHANGED at
   `V := nat`.  All gates green, golden byte-identical, zero-axiom manifest unchanged.
   Payload faithfulness claims stop at the landed fragment (output/panic/defer) — heap
   and channel VALUE faithfulness arrive only with slices 2–3's typed state agreement.
2. **HEAP** — design WORKED (the boundary crux is resolved; sub-slices below):
   `Cmd` += `CWrite : nat → GoAny → Cmd A → Cmd A` and
   `CRead : nat → (GoAny → Cmd A) → Cmd A` (the cmd side stays CONCRETE at `GoAny` —
   it is the typed model, not a calculus; ⚠ first BINDER constructor — `Cmd_rect'` and
   every structural induction gain an under-the-binder case).
   ★THE BOUNDARY RESOLUTION: unallocated access is ABSENCE, not a panic — in Go's safe
   fragment a location-valued read/write cannot hit unallocated memory (nil is caught at
   the POINTER level before a location exists; there are no dangling locations), so the
   model gives it NO behavior: `go` becomes OPTION-VALUED and an access with
   `w_refs l = None` makes the whole run `None`.  `run_cmd` is ALREADY option-valued, so
   its signature (and every `run_cmd` consumer) is UNCHANGED — the ripple is contained to
   `go`/`run_defers`/`go_chars` and the proofs that unfold them.  The agreement theorems
   carry `run_cmd fuel c w = Some oc`, so malformed runs are excluded BY THE EXISTING
   COMPLETION PREMISE — the same discipline as the channel slice's would-block-is-`None`;
   no side predicate, and the cmd/ustep divergence on unallocated reads (typed absence vs
   total default-bind) is unreachable inside the agreement.
   ⚠ 2a–2c are PHASES of ONE landing, not independent green commits: adding constructors
   forces total coverage of every `match` over `Cmd` in the same commit (Coq
   exhaustiveness), and Phase A's statement itself generalizes (the config heap is no
   longer fixed across a body run once writes exist) — the invariant IS the landing.
   Work the phases in order locally; commit when the whole slice is green.
   - 2a. `Cmd` ctors + `Cmd_rect'` binder case + option-valued `go`/`run_defers` +
     re-green cmd.v and every proof that unfolds them (cmd_unified's Local machinery,
     GoSemSafe's runs-ret lemmas).  `cbind` recurses under the read binder.
   - 2b. `cmd_to_ucmd` heap arms (`CWrite → UWrite`, `CRead → URead` — cell ≅ any, the
     pair-swap isos `any_of_cell`/`cell_of_any`); `UFrag` GROWS write/read cases (its
     role is unchanged: the image still contains no rule consulting `vz` — no
     `URecv`/`USelect` — and no channel/spawn forms; re-word its banner to the BRIDGED
     fragment, not "output/panic/defer").
   - 2c. the agreement: `heap_agrees h rh := forall l cell, rh l = Some cell ->
     h l = any_of_cell cell` (allocated locations only — `vz` elsewhere is fine since a
     completing run never touches them); `ustart` generalizes over the initial heap (or
     the theorem states a general start config with a `heap_agrees` premise against the
     start `World`); the conclusion adds FINAL-heap agreement (writes landed identically).
     Phase A / the unwind / the assembly thread the invariant.
   Allocation (`CAlloc` off `w_next`) still has NO ustep counterpart rule — its own
   sub-slice (2d) adding the unified.v rule + trace event, AFTER 2a–2c.
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
