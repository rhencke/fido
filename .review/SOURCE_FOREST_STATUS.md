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
- **C4 disposition: NOT accepted at `af7d5d3`. Repair 13 (exact standard work-member index) candidate COMPLETE and
  FROZEN at this freeze commit; the thirteenth BLOCKING result is repaired and a NEW human C4 Implementation Review
  is pending.** Commit `37c9597` (`review(accept): C4 — accept exact source-type conversion foundation`) is a
  **SUPERSEDED documentation-only acceptance closeout** — based on the withdrawn GREEN disposition, it does not
  accept C4 and is not an implementation candidate. Ranges: full human C4 review `8c9212a..`this freeze commit; full
  repair `89b8e54..`this freeze commit; **repair-12 `37c9597..af7d5d3`**; **repair-13 `af7d5d3..`this freeze
  commit.** Automatic Codex review is DISABLED.
- The post-C4 foundation consolidation / ruthless trim and C5 (= `uintptr` + rune constants/literals, reopens
  ADR-0001) remain FORBIDDEN until C4 is accepted.

## Repair 13 — exact standard work-member index — COMPLETE and FROZEN (baseline `af7d5d3`)

**The defect (real production code, now removed).** `ExprWorkForest.ewf_items` is a legitimate ordered
per-file-order list, but it was ALSO used as a production `NodeKey` identity lookup table: `forest_member_at`
searched it with `List.find` on `nodekey_eqb`, using the carried `ewf_keys_nodup` field as its uniqueness
mechanism, in the live semantic path `build_outcome_trace → build_conversion_step → build_conversion_work →
forest_member_at` — once per conversion. That is the `list + NoDup` keyed-table shape the binding collection law
forbids; it survived proof erasure and made a nested chain's operand recovery avoidably quadratic. The previous
collection audit's "no `List.find` for identity/membership storage", "`NoDup` is never a carried uniqueness field
standing in for a map", and "every identity-keyed collection has a mature standard backing" rows were FALSE.

**The repair as landed.** `forest_member_at` and its `List.find` are DELETED. Identity now lives in a separate
carried field `ewf_index : ExprWorkIndex ewf_items`, backed ENTIRELY by the pinned-stdlib `GoIndex.NodeKeyMapBase`
(`FMapAVL`) — Fido authors no tree, bucket, or find/add. It is built ONCE by `build_work_index` from the
ALREADY-BUILT item list (`work_index_map` takes the list, so no second work discovery and no `ci_visit`
re-traversal); OVERWRITE-FREE (`work_index_fresh` / `work_index_add_fresh` prove every `add` writes an absent key);
TOTAL with no option/fallback/empty-default precisely because the key-`NoDup` is a PROOF ARGUMENT (a
duplicate-keyed list cannot be handed to the builder, and `ExprWorkIndex` is uninhabitable for one anyway); and
EXACT in both directions (`work_index_exact` / `ewi_exact` — sound and complete, so every item has exactly one
entry and every entry is exactly one item). The record is INDEXED BY the item list and the forest field is
dependent, so a foreign map is not pairable with a forest. `ewi_domain` and `ewi_key_inj` are DERIVED, never
stored — no second domain or uniqueness authority, and `ewf_key_inj` is now that map-derived theorem instead of a
hand-rolled NoDup induction. `index_member_at` / `forest_index_member_at` are the TOTAL member queries (ONE
`NodeKeyMapBase.find`, the impossible `None` discharged by a Prop existence hypothesis, no stand-in member);
`index_member_at_retained`, `index_no_foreign` and `index_nonexpr_absent` pin exactness, foreign-key absence and
wrong-kind absence. `build_conversion_work` queries at the key of the operand `ExprRef` the item ALREADY CARRIES
(`ew_conv`) rather than the separately computed `operand_key`, preserving `cw_operand_ref_eq` / `cw_operand_expr` /
`cw_operand_role` / `cw_operand_key`; `build_conversion_step` places that SAME member in the processed suffix and
the outcome trace is untouched. The ordered list keeps its SOURCE-ORDER role only. Repair 12's exact source-step
identity results are RETAINED unchanged.

**New direct fixtures.** `deep_nested_index_at` / `deep_nested_chain_index_evidence`: on the real four-deep chain,
each of the four conversions recovers its EXACT operand member through the index at the CARRIED operand ref's key,
that member is the one the `ConversionStep` placed in the processed suffix, and the operand/current outcomes are
the accepted `EOOk` values. `twin_expr_index_distinct`: two occurrences carrying the LITERALLY SAME expression
value (`uint8(7)` twice) are distinct work items with distinct `NodeKey`s and distinct index entries, each key
answering with its own retained member — expression-value equality cannot conflate them.

**Collection audit rewritten** (`.review/COLLECTION_AUDIT.md`) with the two inventories the summary form hid: an
EXPLICIT `find`/list-scan site inventory (every site named — `GoNames.classify` survives and is classified in full
as a spelling classification over the fixed closed sixteen-name descriptor enumeration with a proved inverse, not
keyed storage; `forest_member_at` is recorded as deleted) and an EXPLICIT `NoDup` inventory naming the only two
carried `NoDup` record fields in the theory (`ewf_keys_nodup`, now a fact about the ordered enumeration that
licenses the index build and never the lookup mechanism; `aewf_context_nodup`, a fact about each item's context ref
list). No `list + NoDup` identity table remains anywhere.

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
`deep_nested_all_ok`) are labeled corollaries. Repair 13 adds the work-index surfaces to the same gate: construction
(`work_index_map`, `work_index_fresh`, `work_index_add_fresh`, `work_index_exact`, `build_work_index`, `ewf_index`),
exactness/uniqueness (`ewi_exact`, `ewi_domain`, `ewi_key_inj`, `ewf_key_inj`), the total queries
(`index_member_at`, `index_member_at_retained`, `forest_index_member_at`, `forest_index_member_at_retained`),
exclusion (`index_no_foreign`, `forest_index_no_foreign`, `index_nonexpr_absent`), the conversion path
(`build_conversion_work`), and the two direct fixtures (`deep_nested_index_at` /
`deep_nested_chain_index_evidence`, `twin_expr_index_distinct`).

## Current verification state

At this repair-13 freeze commit: `make prove` — readable Print-Assumptions gate axiom-free (**479/479** surfaces
closed, up from 458 at the `af7d5d3` baseline) + whole-theory `Fido Audit Assumptions` + self-tests A–E; `make e2e`
(materialize + pinned-Go `go build ./...` + goldens + sink + full alias matrix); `make check` working-tree
generated bytes byte-match the pristine build; `make regenerate` no drift; `make regen-guard` DAG edge
load-bearing; `git diff --check` clean; the staged pre-commit verification ran on the exact freeze.

⚠ Every one of those commands was ALSO green at `af7d5d3` and none of them caught the collection-role defect — a
`List.find` keyed by `NodeKey` typechecks, proves, builds and emits identical bytes. Green commands do not replace
inspection of the actual lookup path and the actual collection roles; that is why the collection audit now carries
per-site inventories instead of summary claims.

## Scope

ADR-0001-PINNED-64-BIT-TARGET **PROPOSED**; ADR-0002-BOUNDED-DECIMALFLOAT-DOMAIN **REJECTED AS WRITTEN / OPEN**;
SR-009 **UNRESOLVED EXISTING RESTRICTION**; every `.review/UNSUPPORTED_AND_RESTRICTED_SCOPE.md` entry PROPOSED with
a neutral classification unless Rob explicitly accepts it. No numeric-model or scope change in repair 12 or repair
13; the DecimalFloat decision work is not begun.
