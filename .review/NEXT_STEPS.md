# NEXT_STEPS — active authority pointer

- **Active checkpoint:** C4 **member-indexed causal outcome repair 8**. Repair 7 closed the broad
  retained-object-flow defects (KEEP them). The ONE remaining defect is narrow and load-bearing: the final table
  carries the OLD raw-map `OutcomeCause`, not a cause indexed by the exact conversion `WorkMember`, processed
  suffix, exact operand `WorkMember`, and exact suffix accumulator. `build_outcomes_forest` proves an operand
  exists in the processed tail, then DISCARDS that member and does a raw map `find` by the operand `ExprRef`
  key; `phase_*_work_cause` rebuild `ConversionWork` and translate the raw cause afterward — reconstruction, not
  a projection of a cause the fold retained. REQUIRED (repair-8 directive §3–§7): a `SuffixMember forest items`
  handle + a total `ConversionStep forest current rest ts x` (carrying `cs_conversion : ConversionWork` +
  `cs_operand_suffix : SuffixMember forest rest` + `cs_operand_exact`); a proof-carrying `OutcomeAccumulator`/
  `OutcomeTrace` indexed by the exact suffix (`oa_total : forall sm : SuffixMember forest items, ExprOutcome`,
  member/suffix-indexed `oa_causes`) whose conversion cons-step consumes ONE `ConversionStep` and queries the
  REST accumulator THROUGH `cs_operand_suffix` (NO raw `find`, NO `from_some` on a raw lookup, NO `operand_key`
  live, NO re-run of `ewf_operand_in_tail`, NO `conversion_*_ref` calls, NO post-hoc `ConversionWork`); a
  member/suffix-indexed direct cause (delete/replace the raw `OutcomeCause`); `ForestOutcomeTable` retaining the
  exact insertion cause with a `total_forest_outcome_cause` returning a `FinalMemberCause` carrying the exact
  `ewf_items = prefix ++ current :: rest` split + the suffix accumulator/step cause. KEEP the phase chain,
  objects, domains, sealing, alias/render/byte results, and scope-ledger wording. Reprove the projections.
  **Post-C4 trim: FORBIDDEN until C4 is accepted.**
- **Functional contract:** `.review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md`.
- **Contract SHA-256:** `9ec55b38444e3a32eaf6cb024f72285527992ba1612dabfdc99ce6f89c8517b4`.
- **Accepted review basis:** `.review/REVIEW_BASIS.md`.
- **Original C4 baseline:** `8c9212a8c814c7a99a5e3ef1970a0ae32425a918`.
- **First blocked C4 candidate:** `89b8e54634e7012612a51990756ad29a579c1b0f`.
- **Second blocked C4 candidate:** `1c4a7de8e9e265b929a3ba9ce1c8fb1317ca98ca`.
- **Third blocked C4 candidate:** `806ce87373e29b6980e5c3d9d274ffa86580449b`.
- **Fourth blocked C4 candidate:** `af2fc87e7726a4fc68bb9480c53cf64faa83717b`.
- **Fifth blocked C4 candidate:** `9d4aff5d94d9aac293ff7fb98a7d9fdd59159022`.
- **Sixth blocked C4 candidate:** `3b4f40e1f14c501fd76333ec8a8cd3e582ed1598`.
- **Seventh blocked C4 candidate:** `3a92d22820705f55093c0e2b3ff18a0f8ad7f4dc`.
- **Eighth blocked C4 candidate / repair-8 baseline:** `91e8dbbcd24fc7df678e6b3d68eabb13b686efa1`
  (the repair-7 freeze; eighth BLOCKING — the final table's causal outcome is still the raw-map cause).
- **Repair authority:** `.review/C4_IMPLEMENTATION_REPAIR_8.md`.
- **Human repair authorization token:** `C4-member-indexed-causal-outcome-repair-8`.
- **State:** C4 Implementation Review BLOCKING; member-indexed causal outcome repair 8 active.
- **Scope decisions:** ADR-0001 remains **PROPOSED** pending explicit Rob disposition. **ADR-0002 is REJECTED AS
  WRITTEN / OPEN — no numeric implementation change authorized.** SR-009 = UNRESOLVED EXISTING RESTRICTION. Every
  PROPOSED ledger entry uses a NEUTRAL classification (no REVIEWED) until Rob accepts.
- **Automatic Codex review:** DISABLED (do NOT request or run a Codex review).
- **C5 is FORBIDDEN** until explicit Rob authorization.
- **Post-C4 simplification / trim is FORBIDDEN** until C4 is accepted (a separate ruthless trim checkpoint
  follows human C4 acceptance).
