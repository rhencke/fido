# NEXT_STEPS — active authority pointer

- **Active checkpoint:** C4 **final-to-tail causal closure repair 9.** Repair 8 correctly repaired the live
  semantic step (KEEP it). The ONE remaining defect is the final RETENTION boundary: the fold computes each
  member from the actual tail `OutcomeAccumulator`, but the final table retains NO causal structure proving that
  the existential `acc_rest` inside `FinalMemberCause` IS the actual tail of `fot_acc`. `FinalMemberCause` = a
  source-list split + an ARBITRARY `OutcomeAccumulator` for the rest + a `StepCause` over it, with NO
  restriction/extension/trace relation between `acc_rest` and the final `fot_acc`. So the final object proves
  only "there EXISTS some exact-domain rest accumulator which could cause this outcome," not "this is the exact
  rest accumulator retained by the recursive construction, whose operand outcome is the SAME retained operand
  outcome visible in the final table." The public `ForestOutcomeTable` type lets `fot_acc`/`fot_causes` be paired
  with a foreign rest accumulator (e.g. an `EOOk` operand fact with equal `ConstInfo` but a different
  `ef_use_resolved`, producing the same head outcome). This is the last proof-beside-path gap. REQUIRED
  (directive §3–§9): an intrinsic causal object — preferred `OutcomeTrace forest tnft items acc` (accumulator as
  INDEX; `TraceNil`/`TraceCons` retaining the exact tail trace + tail `OutcomeAccumulator` + current member +
  `StepCause` over the exact tail + freshness) — so the recursive tail is intrinsic; `build_outcome_trace`
  returns ONE causal object (not accumulator × separate cause function); `ForestOutcomeTable` = `fot_acc` +
  `fot_trace : OutcomeTrace … fot_acc`; `total_forest_outcome_cause` PROJECTS the trace, returning a cause
  indexed by the final accumulator carrying tail-to-final QUERY PRESERVATION (`oa_total acc_rest sm =
  total_forest_outcome_at ot (lift sm)`), so the operand's tail query = its final-table query; direct fixtures
  prove causal CLOSURE into the final table (not just the tail); foreign causal witnesses excluded. KEEP the
  repair-8 semantic branch, objects, phase chain, domains, sealing, alias/render/byte results, scope-ledger
  wording. **Post-C4 trim: FORBIDDEN until C4 is accepted.**
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
- **State:** C4 Implementation Review BLOCKING; **final-to-tail causal closure repair 9 active** (all nine
  blocked candidates end at `a2a5b46`, the current repair baseline).
- **Scope decisions:** ADR-0001 remains **PROPOSED** pending explicit Rob disposition. **ADR-0002 is REJECTED AS
  WRITTEN / OPEN — no numeric implementation change authorized.** SR-009 = UNRESOLVED EXISTING RESTRICTION. Every
  PROPOSED ledger entry uses a NEUTRAL classification (no REVIEWED) until Rob accepts.
- **Automatic Codex review:** DISABLED (do NOT request or run a Codex review).
- **C5 is FORBIDDEN** until explicit Rob authorization.
- **Post-C4 simplification / trim is FORBIDDEN** until C4 is accepted (a separate ruthless trim checkpoint
  follows human C4 acceptance).
