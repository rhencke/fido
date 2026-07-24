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
- **Blocked C4 candidates (all thirteen):** `89b8e54` (1) · `1c4a7de` (2) · `806ce87` (3) · `af2fc87` (4) ·
  `9d4aff5` (5) · `3b4f40e` (6) · `3a92d22` (7) · `91e8dbb` (8) · `a2a5b46` (9) · `a8a4472` (10) · `3ecf32e` (11) ·
  `48c0b31` (12) · `af7d5d3e23c26850887c4fb178dad5f29c616385` (13 — **the current repair-13 baseline**).
- **Repair authority (active): `.review/C4_IMPLEMENTATION_REPAIR_13.md`**, human authorization token
  `C4-standard-work-member-index-repair-13`. Repairs 1–12 are superseded (each deleted in the first implementation
  commit of the next repair; git history is their archive).
- **C4 disposition: NOT accepted at `af7d5d3`. Repair 13 (exact standard work-member index) is ACTIVE.** Commit
  `37c9597` (`review(accept): C4 — accept exact source-type conversion foundation`) is a **SUPERSEDED
  documentation-only acceptance closeout** — based on the withdrawn GREEN disposition, it does not accept C4 and is
  not an implementation candidate. Ranges: full human C4 review `8c9212a..`the repair-13 freeze commit; full repair
  `89b8e54..`the repair-13 freeze commit; **repair-12 `37c9597..af7d5d3`**; **repair-13 `af7d5d3..`the repair-13
  freeze commit.** Automatic Codex review is DISABLED.
- The post-C4 foundation consolidation / ruthless trim and C5 (= `uintptr` + rune constants/literals, reopens
  ADR-0001) remain FORBIDDEN until C4 is accepted.

## Repair 13 — exact standard work-member index — ACTIVE (baseline `af7d5d3`)

**The defect.** `ExprWorkForest.ewf_items` is a legitimate ordered per-file-order list, but it is ALSO used as a
production `NodeKey` identity lookup table. `forest_member_at` searches it with `List.find` on `nodekey_eqb`, using
the carried `ewf_keys_nodup` field as its uniqueness mechanism, and it sits in the live semantic path
`build_outcome_trace → build_conversion_step → build_conversion_work → forest_member_at` — once per conversion. That
is the `list + NoDup` keyed-table shape the binding collection law forbids: identity-keyed roles must use a mature
finite map. The scan survives proof erasure and makes a nested conversion chain's operand lookup avoidably
quadratic. The previous collection audit's "no `List.find` for identity/membership storage", "`NoDup` is never a
carried uniqueness field standing in for a map", and "every identity-keyed collection has a mature standard
backing" rows were therefore FALSE.

**The required repair.** Replace the hidden list-key authority with an exact standard-map-backed work-member index
(`GoIndex.NodeKeyMapBase`, built ONCE from the already-retained `ewf_items`, tied to that exact list by dependent
typing and exact bidirectional laws, no silent overwrite, no fallback, no second work discovery), and replace
`forest_member_at` with a total map-backed member query threaded through `build_conversion_work` /
`build_conversion_step`. The ordered list stays the source-order authority; the map is the derived identity index,
not a second source or semantic authority. Repair 12's exact source-step identity results are RETAINED unchanged.

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

At the repair-13 baseline `af7d5d3`: `make prove` — readable Print-Assumptions gate axiom-free (458/458 surfaces
closed) + whole-theory `Fido Audit Assumptions` + self-tests A–E; `make e2e` (materialize + pinned-Go
`go build ./...` + goldens + sink + full alias matrix); `make check` working-tree generated bytes byte-match the
pristine build; `make regenerate` no drift; `make regen-guard` DAG edge load-bearing; `git diff --check` clean.
Those commands were green at `af7d5d3` and did NOT catch the collection-role defect — green commands do not replace
inspection of the actual lookup path. The repair-13 freeze commit and its exact readable-gate count are reported
when repair 13 completes.

## Scope

ADR-0001-PINNED-64-BIT-TARGET **PROPOSED**; ADR-0002-BOUNDED-DECIMALFLOAT-DOMAIN **REJECTED AS WRITTEN / OPEN**;
SR-009 **UNRESOLVED EXISTING RESTRICTION**; every `.review/UNSUPPORTED_AND_RESTRICTED_SCOPE.md` entry PROPOSED with
a neutral classification unless Rob explicitly accepts it. No numeric-model or scope change in repair 12 or repair
13; the DecimalFloat decision work is not begun.
