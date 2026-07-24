# NEXT_STEPS — active authority pointer

- **Active checkpoint:** C4 **final-to-tail causal closure repair 9 — CANDIDATE COMPLETE, awaiting Rob's human
  C4 Implementation Review.** The ninth-BLOCKING defect (the final table retained no causal structure proving the
  existential `acc_rest` inside `FinalMemberCause` was the actual recursive tail of `fot_acc`, so a foreign rest
  accumulator producing the same head outcome typechecked — the last proof-beside-path gap) is REPAIRED by an
  INTRINSIC causal object. `ForestOutcomeTable` = `fot_acc` + `fot_trace : OutcomeTrace … fot_acc` — the
  accumulator PAIRED WITH the `OutcomeTrace` that BUILT it (`TraceCons` retains the exact tail trace + tail
  `OutcomeAccumulator` + head member + head-freshness + the `StepCause` over the EXACT tail), indexed by
  `fot_acc` so accumulator and causal predecessor chain are NOT freely pairable. `build_forest_outcome_table`
  folds `build_outcome_trace` (ONE causal object). `total_forest_outcome_cause` PROJECTS the trace
  (`trace_retained_cause`) to each member's `RetainedMemberCause` — the exact suffix split, the AUTHENTICATED
  tail accumulator, the `StepCause` producing the FINAL outcome, and tail-to-final QUERY PRESERVATION;
  `final_operand_outcome` closes a conversion's operand into the final table (operand's tail query = final-table
  query). Direct fixtures prove causal CLOSURE into the final table: `deep_fail_innermost_convfail` (§9.1),
  `deep_fail_outer_operands_final_fail` (§9.2), `deep_nested_chain_operands_final_ok` (§9.3). Foreign causal
  witnesses are excluded by the preservation clause + `ewf_key_inj`. The old `build_outcome_accumulator` (+
  separate cause function) and `FinalMemberCause` (no final-accumulator relation) are DELETED. The repair-8
  semantic branch, objects, phase chain, domains, sealing, and alias/render/byte results are KEPT. **Post-C4
  trim: FORBIDDEN until C4 is accepted.**
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
- **Eighth blocked C4 candidate:** `91e8dbbcd24fc7df678e6b3d68eabb13b686efa1`
  (the repair-7 freeze; eighth BLOCKING — the final table's causal outcome was still the raw-map cause).
- **Ninth blocked C4 candidate / repair-9 baseline:** `a2a5b46026cc658f41cb04f6d6cb30a29335671c`
  (the repair-8 freeze; ninth BLOCKING — the final table retains no final-to-tail causal relation, so the
  cause's `acc_rest` is a possible derivation, not the authenticated recursive tail of `fot_acc`).
- **Repair authority:** `.review/C4_IMPLEMENTATION_REPAIR_9.md`.
- **Human repair authorization token:** `C4-final-to-tail-causal-closure-repair-9`.
- **Repair-9 candidate head:** the `review(final): C4 — freeze causally closed outcome-trace candidate` freeze
  commit (repository HEAD).
- **Full human C4 Implementation Review range:** `8c9212a..`<freeze> (original C4 baseline → candidate head).
- **Full repair range:** `89b8e54..`<freeze>.
- **Repair-9 range:** `a2a5b46..`<freeze>.
- **State:** C4 Implementation Review — **final-to-tail causal closure repair 9 candidate COMPLETE; all nine
  blocked candidates ended at `a2a5b46`; human C4 Implementation Review pending.**
- **Scope decisions:** ADR-0001 remains **PROPOSED** pending explicit Rob disposition. **ADR-0002 is REJECTED AS
  WRITTEN / OPEN — no numeric implementation change authorized.** SR-009 = UNRESOLVED EXISTING RESTRICTION. Every
  PROPOSED ledger entry uses a NEUTRAL classification (no REVIEWED) until Rob accepts.
- **Automatic Codex review:** DISABLED (do NOT request or run a Codex review).
- **C5 is FORBIDDEN** until explicit Rob authorization.
- **Post-C4 simplification / trim is FORBIDDEN** until C4 is accepted (a separate ruthless trim checkpoint
  follows human C4 acceptance).
