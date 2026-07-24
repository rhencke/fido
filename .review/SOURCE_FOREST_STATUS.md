# Source Forest Campaign — Status Ledger

Campaign: **Specification-Shaped Source Forest, Snapshot-Local Occurrence Identity, and Occurrence-Anchored
Compilation.** The full design is `.review/SOURCE_FOREST_MASTER_PLAN.md`. **Git history is the detailed archive:
superseded per-repair theorem tables and prior candidate detail live in the git log and the superseded repair
directives, NOT in this file.** This ledger is the COMPACT CURRENT state only.

## Completed checkpoints

- **C0–C3 GREEN and accepted by Rob** (C3 accepted at the original C4 baseline `8c9212a`): preflight + proof
  spike; spec-shaped file roots + path-keyed `GoFileSet`; production `GoIndex` + `NodeRef` navigation;
  occurrence-anchored diagnostics + one `AnalysisResult`.

## C4 authority

- Active checkpoint: **C4** — source type names, compiler resolution, and unified numeric conversions.
- Functional contract: `.review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md`; contract SHA-256
  `9ec55b38444e3a32eaf6cb024f72285527992ba1612dabfdc99ce6f89c8517b4`.
- Accepted review basis: `.review/REVIEW_BASIS.md`.
- Original C4 baseline: `8c9212a8c814c7a99a5e3ef1970a0ae32425a918`.
- **Blocked C4 candidates (all ten):** `89b8e54` (1) · `1c4a7de` (2) · `806ce87` (3) · `af2fc87` (4) ·
  `9d4aff5` (5) · `3b4f40e` (6) · `3a92d22` (7) · `91e8dbb` (8) · `a2a5b46` (9) ·
  `a8a44723250edd776c62dbb362d8fab51c21ab8f` (10 — the repair-9 freeze; **the current repair-10 baseline**).
- **Repair authority (active): `.review/C4_IMPLEMENTATION_REPAIR_10.md`**, human authorization token
  `C4-evidence-status-closeout-repair-10`. Repairs 1–9 are superseded (each deleted in the first implementation
  commit of the next repair; git history is their archive).
- Automatic Codex review: DISABLED (not requested or run). On completion the candidate is frozen with EXACTLY ONE
  `review(final): C4 — freeze exact acceptance-evidence candidate` and reported for Rob's human Implementation
  Review.
- C5, every later checkpoint, and the post-C4 trim remain forbidden (the trim until C4 acceptance).

## Repair 10 — evidence and status closeout — CANDIDATE COMPLETE (awaiting human review)

**§0 human disposition: the production architecture PASSES the causal-path review; NO new production-path defect
found; the repair-9 architecture is RETAINED.** The candidate was BLOCKING only on acceptance-evidence and
current-status exactness (a narrow evidence/prose closeout, not an architecture redesign) — all now CLOSED: the
final-to-tail closure fixtures + the exact `EOConvFail`→`DRInvalidConversion` diagnostic theorem
(`deep_fail_innermost_diag`) + the universal closures (`retained_convsuccess_closure` /
`retained_childfail_closure` +no-local-reason / `retained_convfail_diag`) + the unique-trace-insertion theorem
(`outcome_trace_unique_step`) are proved and NAMED in the readable assumption gate (456/456), and this ledger is a
compact current record. Frozen at the `review(final): C4 — freeze exact acceptance-evidence candidate` commit
(repository HEAD); human C4 Implementation Review pending; full human review range `8c9212a..`<freeze>; full repair
range `89b8e54..`<freeze>; repair-10 range `a8a4472..`<freeze>. The original blocking classes (for the record):

- **2.1** the new final-to-tail closure fixtures (`deep_fail_childfail_closure_at`, `deep_nested_ok_closure_at`,
  `deep_fail_outer_operands_final_fail`, `deep_nested_chain_operands_final_ok`) are NOT in the readable assumption
  gate; the gate still prints only the older shape fixtures. The readable gate is the reviewed public claim
  surface — it must name the accepted closure evidence.
- **2.2** `deep_fail_innermost_convfail` proves the retained `EOConvFail` cause but does NOT connect it to the
  exact stored `DRInvalidConversion` diagnostic (same primary ExprRef / target TypeNameRef / operand ExprRef /
  resolved target / operand status); `deep_fail_exactly_one_diag` proves only length = 1 via the source-spec
  bridge.
- **2.3** `deep_fail_outer_operands_final_fail` projects `deep_fail_childfail_closure_at` down to arbitrary
  existentials — its statement no longer shows `opw = proj1_sig (cs_operand_suffix step)` nor tail = final; and it
  does not prove no local `DRInvalidConversion` is emitted for each outer member.
- **2.4** `deep_nested_chain_operands_final_ok` discards the success cause (exact operand member, tail query,
  query equality, `convert_const` success, current final fact, target fact); and there is no unique-trace-step
  theorem over `OutcomeTrace`.
- **2.5** this status ledger previously carried a false, contradictory "CURRENT: exact retained work-object
  repair 7 ACTIVE" section and old "repository HEAD" claims for superseded candidates — false current authority,
  now removed (this compact rewrite).

## Current implementation architecture (repair-9 design, RETAINED)

One immutable `GoProgram` source authority → one retained `CompilationInput` → one proof-carrying
`ExprWorkForest` (exact `WorkMember`/`SuffixMember` handles; `ConversionWork`/`ConversionStep`). The expression
outcome authority is the **intrinsic causal object** `ForestOutcomeTable = fot_acc + fot_trace`: an
`OutcomeTrace forest tnft items acc` (a regular inductive INDEXED by the `OutcomeAccumulator` it builds — `acc` is
computed by the non-recursive `extend_acc`, so no induction-recursion; `TraceCons` retains the exact tail trace,
tail accumulator, current item, freshness, and the member/suffix-indexed `StepCause` over the exact tail), indexed
by `fot_acc` so accumulator and causal predecessor chain are NOT freely pairable. `total_forest_outcome_cause`
PROJECTS the trace (`trace_retained_cause`) to each member's `RetainedMemberCause` carrying the authenticated tail
accumulator + `StepCause` producing the FINAL outcome + tail-to-final QUERY PRESERVATION; `final_operand_outcome`
connects the exact tail operand result to the final-table operand result. The conversion semantic branch consumes
one `ConversionStep` + one exact operand `SuffixMember`, one total tail query, one `convert_const` — no raw
operand lookup, no recursive rescan, no table rebuild, no post-hoc reconstruction. One dependent
`ExpressionPhase` object chain; facts and diagnostics projected from the same retained outcome table; exact table
sealing on successful elaboration; source-name/alias/renderer/diagnostic/differential results and the canonical
generated Go bytes unchanged; no C5.

## Current verification state (at `a8a4472`, repair-9 freeze)

`make prove` — readable gate axiom-free + whole-theory `Fido Audit Assumptions` + self-tests A–E; `make e2e`
(materialize + pinned-Go `go build ./...` + goldens + sink + full alias matrix); `make check` working-tree
generated bytes byte-match the pristine build; `make regenerate` no drift; `make regen-guard` DAG edge
load-bearing; `git diff --check` clean. (Repair 10 adds acceptance-evidence theorems and re-gates; the freeze
records the final gate count.)

## Scope

ADR-0001-PINNED-64-BIT-TARGET **PROPOSED**; ADR-0002-BOUNDED-DECIMALFLOAT-DOMAIN **REJECTED AS WRITTEN / OPEN**;
SR-009 **UNRESOLVED EXISTING RESTRICTION**; every `.review/UNSUPPORTED_AND_RESTRICTED_SCOPE.md` entry PROPOSED
with a neutral classification unless Rob explicitly accepts it (a model does not certify its own trade-offs). No
numeric-model or scope change in repair 10; the DecimalFloat decision work is not begun.
