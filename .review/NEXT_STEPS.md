# NEXT_STEPS — active authority pointer

- **Active checkpoint:** C4 **exact success identity and collection-audit closeout repair 12.** The production
  architecture continues to PASS the causal-path review — **no new production-path defect was found, and no production
  change is authorized** (this repair changes theorem statements/proofs, the readable gate, the collection audit, and
  current-authority prose only). The candidate `48c0b31` is **BLOCKING** for two exact closeout defects: (2.1–2.3) the
  accepted conversion-success theorem family (`StepCause_ok_conv_inv` → `retained_convsuccess_closure` →
  `nested_success_bundle` → `deep_nested_convsuccess_at` / `deep_nested_chain_success_evidence`) returns an existential
  `ConversionStep ... ts0 x0` with no stated `ts0 = ts` / `x0 = x`, so its public type does not justify calling the
  returned step "the exact ConversionStep for the source conversion"; (2.4–2.6) `.review/COLLECTION_AUDIT.md` (a
  declared living current-state inventory) still names the deleted `prog_conv_outcomes` authority, a nonexistent
  "bucket value prevents overwrite" behavior for `ExprOutcome` storage, a stale combined outcome/fact/type-name row,
  and the nonexistent `TFun` body as current syntax.
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
- **State:** C4 Implementation Review **BLOCKING**; **exact success identity and collection-audit closeout 12 active.**
- **Production architecture disposition:** no new production-path defect found; **no production change authorized**
  (theorem statements/proofs, gate, collection audit, and authority prose only).
- **Scope decisions:** ADR-0001 remains **PROPOSED**. **ADR-0002 is REJECTED AS WRITTEN / OPEN.** SR-009 =
  UNRESOLVED EXISTING RESTRICTION. Every PROPOSED ledger entry stays PROPOSED until Rob accepts.
- **Automatic Codex review:** DISABLED (do NOT request or run a Codex review).
- **C5 is FORBIDDEN** until explicit Rob authorization (C5 = `uintptr` + rune constants/literals, which reopens
  ADR-0001).
- **Post-C4 simplification / trim is FORBIDDEN** until C4 is accepted (a separate ruthless trim checkpoint follows
  human C4 acceptance).
