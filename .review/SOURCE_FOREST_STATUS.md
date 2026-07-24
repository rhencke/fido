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
- **Blocked C4 candidates (all twelve):** `89b8e54` (1) · `1c4a7de` (2) · `806ce87` (3) · `af2fc87` (4) ·
  `9d4aff5` (5) · `3b4f40e` (6) · `3a92d22` (7) · `91e8dbb` (8) · `a2a5b46` (9) · `a8a4472` (10) · `3ecf32e` (11) ·
  `48c0b31beb547326b058748a4d38c6cc41013009` (12 — **the current repair-12 baseline**).
- **Repair authority (active): `.review/C4_IMPLEMENTATION_REPAIR_12.md`**, human authorization token
  `C4-final-identity-collection-audit-closeout-repair-12`. Repairs 1–11 are superseded (each deleted in the first
  implementation commit of the next repair; git history is their archive).
- **C4 disposition: NOT accepted at `48c0b31`. Repair 12 (exact success identity + collection-audit closeout)
  candidate COMPLETE and FROZEN at this freeze commit; the twelfth BLOCKING result is repaired and a NEW human C4
  Implementation Review is pending.** The production architecture continues to PASS the causal-path review (no new
  production-path defect; no production change made). Commit `37c9597` (`review(accept): C4 — accept exact source-type
  conversion foundation`) is a **SUPERSEDED documentation-only acceptance closeout** — based on the withdrawn GREEN
  disposition, it did NOT repair the two defects and does not accept C4. Ranges: full human C4 review
  `8c9212a..`this freeze commit; full repair `89b8e54..`this freeze commit; repair-12 `48c0b31..`this freeze commit.
  Automatic Codex review is DISABLED.
- The post-C4 foundation consolidation / ruthless trim and C5 (= `uintptr` + rune constants/literals, reopens
  ADR-0001) remain FORBIDDEN until C4 is accepted.

## Repair 12 — exact success identity and collection-audit closeout — COMPLETE and FROZEN (baseline `48c0b31`)

**The production architecture PASSES the causal-path review; NO new production-path defect; no production change was
made.** A narrow theorem-statement, gate-comment, collection-audit, and authority-prose closeout of two exact defects,
now complete:

- **2.1–2.3 (success identity)** the conversion-success theorem family now exposes source-step identity. Root:
  `StepCause_ok_conv_inv` returns the `ConversionStep` at the EXACT source `ts0`/`x0` supplied — it inverts `SCConvOk`
  (whose own `ew_expr current = EConvert ts x` is injected against the premise `ew_expr current = EConvert ts0 x0`)
  and substitutes, so no existential source-type distinction survives. `retained_convsuccess_closure` and
  `nested_success_bundle` return `step : ConversionStep ... ts x` (no existential `ts0`/`x0`);
  `deep_nested_convsuccess_at` / `deep_nested_chain_success_evidence` expose the exact source `ConversionStep` for
  each of the four valid conversions; the gate comments quote the source-step identity.
- **2.4–2.6 (collection audit)** `.review/COLLECTION_AUDIT.md` is rewritten around the current objects:
  `ExprWorkForest`/`AnnotatedExprWorkForest` (ordered retained `list` views), `OutcomeAccumulator.oa_map` /
  `ForestOutcomeTable.fot_acc` (the standard `NodeKeyMapBase` FMapAVL identity map, one entry per key, NO list bucket,
  no overwrite), `OutcomeTrace` (intrinsic causal inductive), `ForestExprFactTable`/`ExprFactTable` (the EOOk
  projection), and the separate `TypeNameFactTable`; the current source form is `DMain body`. A full symbol-existence
  pass confirms every current token exists, and the deleted `prog_conv_outcomes` / `TFun` (and old `FMap.v` /
  radix `NodeTable`) names are labeled rejected/historical, not current.

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
(`deep_nested_chain_success_evidence`) — **the returned `ConversionStep` carries the source `ts`/`x` identity (no
existential `ts0`/`x0`, repair 12), so the "exact ConversionStep" claim is justified by the public type**;
the exact `EOConvFail`→`DRInvalidConversion` diagnostic theorem
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
`make regen-guard` DAG edge load-bearing; `git diff --check` clean. The repair-12 freeze commit will be the candidate
head; the exact readable-gate count and SHA are given in the final report.

## Scope

ADR-0001-PINNED-64-BIT-TARGET **PROPOSED**; ADR-0002-BOUNDED-DECIMALFLOAT-DOMAIN **REJECTED AS WRITTEN / OPEN**;
SR-009 **UNRESOLVED EXISTING RESTRICTION**; every `.review/UNSUPPORTED_AND_RESTRICTED_SCOPE.md` entry PROPOSED with
a neutral classification unless Rob explicitly accepts it. No numeric-model or scope change in repair 11; the
DecimalFloat decision work is not begun.
