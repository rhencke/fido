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

- Active checkpoint: **C4** — source type names, compiler resolution, and unified numeric conversions (including
  the `byte`→`uint8` / `rune`→`int32` SOURCE ALIASES, which are C4 work and are present in the current candidate).
- Functional contract: `.review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md`; contract SHA-256
  `9ec55b38444e3a32eaf6cb024f72285527992ba1612dabfdc99ce6f89c8517b4`.
- Accepted review basis: `.review/REVIEW_BASIS.md`.
- Original C4 baseline: `8c9212a8c814c7a99a5e3ef1970a0ae32425a918`.
- **Blocked C4 candidates (all eleven):** `89b8e54` (1) · `1c4a7de` (2) · `806ce87` (3) · `af2fc87` (4) ·
  `9d4aff5` (5) · `3b4f40e` (6) · `3a92d22` (7) · `91e8dbb` (8) · `a2a5b46` (9) · `a8a4472` (10) ·
  `3ecf32e3f7b9514070a1025b73231f541990e93c` (11 — the repair-10 freeze; **the current repair-11 baseline**).
- **Repair authority (active): `.review/C4_IMPLEMENTATION_REPAIR_11.md`**, human authorization token
  `C4-final-evidence-authority-closeout-repair-11`. Repairs 1–10 are superseded (each deleted in the first
  implementation commit of the next repair; git history is their archive).
- **C4 disposition: HUMAN IMPLEMENTATION REVIEW GREEN — C4 ACCEPTED by Rob at
  `48c0b31beb547326b058748a4d38c6cc41013009`** (`review(final): C4 — freeze final exact acceptance candidate`). No
  remaining production-path, provenance, theorem-surface, diagnostic, gate, rendering, generated-output, or
  current-authority defect was found. Automatic Codex review remained DISABLED throughout. Repair 11 (final evidence
  and authority closeout) is COMPLETE.
- The next authorized activity is a SEPARATE **post-C4 foundation consolidation / ruthless trim** checkpoint
  (deletion + abstraction consolidation without changing C4's accepted guarantees; explicit identification of
  unresolved foundation-scope decisions), which requires its OWN explicit contract and human review. **No C5 feature
  may enter the trim.** C5 (= `uintptr` + rune constants/literals, which reopens ADR-0001) and every later checkpoint
  remain FORBIDDEN until the trim is separately reviewed and accepted and Rob authorizes C5.

## Repair 11 — final evidence and authority closeout — COMPLETE; C4 ACCEPTED at `48c0b31` (baseline `3ecf32e3`)

**The production architecture PASSED review; NO new production-path defect; the repair-9 + repair-10
architecture/evidence is RETAINED and no production change was made.** A narrow theorem-statement, gate-comment,
and authority-prose closeout (NOT an architecture repair), delivered and now ACCEPTED as part of the C4 foundation:

- **2.5** the accepted concrete valid-chain success theorem now STATES the full success evidence its proof obtains
  (exact `ConversionStep`, target fact query, tail = final = `EOOk opf`, one `convert_const` success, exact current
  final `ExprFact`): `deep_nested_convsuccess_at` (proving `nested_success_bundle`) + `deep_nested_chain_success_evidence`
  over all four conversions; `deep_nested_ok_closure_at` is relabeled the operand-closure-only corollary.
- **2.6** the concrete diagnostic theorem `deep_fail_innermost_diag` now additionally STATES `t = tnf_type
  (type_name_fact_at_table (ep_tnft phase) (cw_target_ref (cs_conversion step)))` and the exact retained annotated
  member/context pair (`retained_convfail_diag` returns `wma` with `In (wma, outer) (aewf_items aw)` ∧
  `proj1_sig wma = proj1_sig wm`) that supplied `outer`.
- **2.1–2.4/2.7/2.8** the authority / status / progress / architecture prose and gate comments now describe the
  CURRENT candidate (present tense = current code + current review state only), the C4/C5 alias timing is corrected,
  gate comments match the exact printed statements, and range wording names this freeze commit.

## Current implementation architecture (RETAINED)

One immutable `GoProgram` source authority → one retained `CompilationInput` → one proof-carrying
`ExprWorkForest` (exact `WorkMember`/`SuffixMember` handles; `ConversionWork`/`ConversionStep`). The expression
outcome authority is the intrinsic causal object `ForestOutcomeTable = fot_acc + fot_trace`: an `OutcomeTrace`
INDEXED by the `OutcomeAccumulator` it builds (`TraceCons` retains the exact tail trace/accumulator/current
member/freshness/`StepCause`), so accumulator and causal predecessor chain are NOT freely pairable.
`total_forest_outcome_cause` PROJECTS the trace to each member's `RetainedMemberCause` carrying the authenticated
tail accumulator + `StepCause` producing the FINAL outcome + tail-to-final QUERY PRESERVATION;
`final_operand_outcome` connects the exact tail operand result to the final-table operand result. The conversion
semantic branch consumes one `ConversionStep` + one exact operand `SuffixMember`, one total tail query, one
`convert_const`. One dependent `ExpressionPhase` object chain; facts and diagnostics projected from the same
retained outcome table; exact table sealing on successful elaboration; source-name/alias/renderer/diagnostic/
differential results and the canonical generated Go bytes unchanged; no C5.

## Current acceptance evidence (theorem / gate surfaces)

Universal (over any retained table/member): `retained_convsuccess_closure` / `retained_childfail_closure`
(+no-local-reason) / `retained_convfail_diag` (returns the exact retained annotated member/context pair) /
`outcome_trace_unique_step` (+`trace_currents_eq`). Concrete (over the deep programs): the exact valid-chain success
bundle `deep_nested_convsuccess_at` (proving `nested_success_bundle`) instantiated on all four conversions
(`deep_nested_chain_success_evidence`); the exact `EOConvFail`→`DRInvalidConversion` diagnostic theorem
`deep_fail_innermost_diag` (stating `t = tnf_type (type_name_fact_at_table (ep_tnft phase) (cw_target_ref
(cs_conversion step)))`, the annotated member, and the stored singleton); the outer child-failure closure
`deep_fail_childfail_closure_at`, `deep_fail_exactly_one_diag`, the exact work count, wrong-kind/foreign exclusion,
fact-table sealing, and the two-`uint8` retained-fact fixture — all NAMED in the readable assumption gate; the weaker
projections (`deep_nested_ok_closure_at`, `deep_fail_outer_operands_final_fail`, `deep_nested_chain_operands_final_ok`,
`deep_nested_all_ok`) are labeled corollaries.

## Current verification state

`make prove` — readable Print-Assumptions gate axiom-free (458/458 surfaces closed) + whole-theory `Fido Audit
Assumptions` + self-tests A–E; `make e2e` (materialize + pinned-Go `go build ./...` + goldens + sink + full alias
matrix); `make check` working-tree generated bytes byte-match the pristine build; `make regenerate` no drift;
`make regen-guard` DAG edge load-bearing; `git diff --check` clean. The repair-11 freeze commit is the candidate
head; the final report gives its exact SHA.

## Scope

ADR-0001-PINNED-64-BIT-TARGET **PROPOSED**; ADR-0002-BOUNDED-DECIMALFLOAT-DOMAIN **REJECTED AS WRITTEN / OPEN**;
SR-009 **UNRESOLVED EXISTING RESTRICTION**; every `.review/UNSUPPORTED_AND_RESTRICTED_SCOPE.md` entry PROPOSED with
a neutral classification unless Rob explicitly accepts it. No numeric-model or scope change in repair 11; the
DecimalFloat decision work is not begun.
