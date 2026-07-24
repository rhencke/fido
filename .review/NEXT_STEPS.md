# NEXT_STEPS — active authority pointer

- **Active checkpoint:** C4 **exact success identity and collection-audit closeout repair 12 — candidate COMPLETE
  and FROZEN at this freeze commit; pending Rob's human C4 Implementation Review.** The production architecture
  continues to PASS the causal-path review — **no new production-path defect, and no production change was made** (this
  repair changed theorem statements/proofs, the readable gate, the collection audit, and current-authority prose
  only). Both defects are addressed: (2.1–2.3) the conversion-success theorem family now exposes source-step identity
  — `StepCause_ok_conv_inv` returns the `ConversionStep` at the EXACT source `ts0`/`x0` supplied (inverting `SCConvOk`
  and injecting its own `ew_expr current = EConvert ts x` against the premise), `retained_convsuccess_closure` and
  `nested_success_bundle` return `step : ConversionStep ... ts x` (no existential `ts0`/`x0`), and
  `deep_nested_convsuccess_at` / `deep_nested_chain_success_evidence` expose the exact source `ConversionStep` for
  each of the four valid conversions; (2.4–2.6) `.review/COLLECTION_AUDIT.md` is rewritten around the current objects
  (`ExprWorkForest`/`AnnotatedExprWorkForest`, `OutcomeAccumulator.oa_map`/`ForestOutcomeTable.fot_acc`,
  `OutcomeTrace`, `ForestExprFactTable`/`ExprFactTable`, the separate `TypeNameFactTable`, and `DMain body`), with a
  symbol-existence pass confirming every current token exists and the deleted `prog_conv_outcomes` / `TFun` names are
  labeled rejected/historical.
- **Superseded current head:** commit `37c9597` (`review(accept): C4 — accept exact source-type conversion
  foundation`) is a **SUPERSEDED documentation-only acceptance closeout** — it was based on the withdrawn GREEN
  disposition and did NOT repair the two blocking defects above. C4 is **NOT accepted** at `48c0b31`. Repair 12 is
  implemented on top of `37c9597` without resetting, reverting, rewriting, or force-pushing history; `37c9597` is not
  counted as an implementation candidate.
- **Functional contract:** `.review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md`.
- **Contract SHA-256:** `9ec55b38444e3a32eaf6cb024f72285527992ba1612dabfdc99ce6f89c8517b4`.
- **Accepted review basis:** `.review/REVIEW_BASIS.md`.
- **Original C4 baseline:** `8c9212a8c814c7a99a5e3ef1970a0ae32425a918`.
- **Blocked C4 candidates (all twelve):** `89b8e54` (1) · `1c4a7de` (2) · `806ce87` (3) · `af2fc87` (4) ·
  `9d4aff5` (5) · `3b4f40e` (6) · `3a92d22` (7) · `91e8dbb` (8) · `a2a5b46` (9) · `a8a4472` (10) · `3ecf32e` (11) ·
  `48c0b31beb547326b058748a4d38c6cc41013009` (12 — **the current repair-12 baseline**).
- **Repair authority:** `.review/C4_IMPLEMENTATION_REPAIR_12.md`.
- **Human repair authorization token:** `C4-final-identity-collection-audit-closeout-repair-12`.
- **Candidate ranges (this freeze commit is the repair-12 candidate head; the report gives the exact SHA):** full
  human C4 Implementation Review range `8c9212a..`this freeze commit; full repair range `89b8e54..`this freeze commit;
  repair-12 range `48c0b31..`this freeze commit.
- **State:** C4 Implementation Review — **exact success identity and collection-audit closeout repair 12 COMPLETE and
  FROZEN** at this freeze commit (the twelfth BLOCKING result repaired); **new human C4 Implementation Review pending.**
  All twelve prior blocked candidates ended at `48c0b31` (the repair-12 baseline); this freeze is the new candidate
  head.
- **Production architecture disposition:** no new production-path defect found; **no production change made**
  (theorem statements/proofs, gate, collection audit, and authority prose only). Exact source-step identity is now
  exposed in the success theorem family; the collection audit is current and symbol-checked.
- **Scope decisions:** ADR-0001 remains **PROPOSED**. **ADR-0002 is REJECTED AS WRITTEN / OPEN.** SR-009 =
  UNRESOLVED EXISTING RESTRICTION. Every PROPOSED ledger entry stays PROPOSED until Rob accepts.
- **Automatic Codex review:** DISABLED (do NOT request or run a Codex review).
- **C5 is FORBIDDEN** until explicit Rob authorization (C5 = `uintptr` + rune constants/literals, which reopens
  ADR-0001).
- **Post-C4 simplification / trim is FORBIDDEN** until C4 is accepted (a separate ruthless trim checkpoint follows
  human C4 acceptance).
