# NEXT_STEPS — active authority pointer

- **Active checkpoint:** C4 **single retained work-domain repair 6**. Replace the remaining split structural root:
  build ONE retained typed-work domain object (`ExprWorkForest`) — built once from the retained input, carrying
  conversion-work refinement and exact domain/NoDup/one-per-expression laws — and have the outcome fold, the
  outcome table, the annotation forest, facts, and diagnostics ALL consume that ONE retained object (no second
  work discovery, no reminting of conversion refs). Retain work / annotated work / outcome table / fact table /
  diagnostics in ONE intrinsic `ExpressionPhase` with dependent provenance so a foreign component is
  unrepresentable. Delete `build_outcomes` (raw), `build_work_sig`, `prog_work`, `prog_work_fold`, `build_awork`,
  `build_awork_blocks`, and the `exists w : ExprWork` domain form. PLUS: correct the scope-decision records
  (ADR-0002 REJECTED AS WRITTEN and rewritten; remove REVIEWED from PROPOSED ledger classes; SR-009 = UNRESOLVED
  EXISTING RESTRICTION).
- **Functional contract:** `.review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md`.
- **Contract SHA-256:** `9ec55b38444e3a32eaf6cb024f72285527992ba1612dabfdc99ce6f89c8517b4`.
- **Accepted review basis:** `.review/REVIEW_BASIS.md`.
- **Original C4 baseline:** `8c9212a8c814c7a99a5e3ef1970a0ae32425a918`.
- **First blocked C4 candidate:** `89b8e54634e7012612a51990756ad29a579c1b0f`.
- **Second blocked C4 candidate:** `1c4a7de8e9e265b929a3ba9ce1c8fb1317ca98ca`.
- **Third blocked C4 candidate:** `806ce87373e29b6980e5c3d9d274ffa86580449b`.
- **Fourth blocked C4 candidate:** `af2fc87e7726a4fc68bb9480c53cf64faa83717b`.
- **Fifth blocked C4 candidate:** `9d4aff5d94d9aac293ff7fb98a7d9fdd59159022`.
- **Sixth blocked C4 candidate / repair-6 baseline:** `3b4f40e1f14c501fd76333ec8a8cd3e582ed1598`.
- **Seventh C4 candidate (repair 6 APPLIED, frozen):** the `review(final): C4 — freeze single retained
  work-domain candidate` commit at repository HEAD (repair-6 implementation range `3b4f40e..HEAD`).
- **Repair authority:** `.review/C4_IMPLEMENTATION_REPAIR_6.md`.
- **Human repair authorization token:** `C4-single-retained-work-domain-repair-6`.
- **State:** C4 single retained work-domain repair 6 APPLIED and frozen; **pending Rob's HUMAN Implementation
  Review**. `make check` + `make regenerate` no-drift + staged pre-commit hook GREEN; gate 428/428 axiom-free.
- **Scope decisions:** ADR-0001 remains **PROPOSED** pending explicit Rob disposition (the corrected linux/amd64/
  Go-1.23 decision is defensible and ready for human acceptance, subject to its automatic C5 reopening rule).
  **ADR-0002 is REJECTED AS WRITTEN — open decision; no numeric implementation change authorized** (per §12/§13.2).
  Every PROPOSED ledger entry uses a NEUTRAL classification (no REVIEWED) until Rob accepts.
- **Automatic Codex review:** DISABLED (do NOT request or run a Codex review).
- **C5 is FORBIDDEN** until explicit Rob authorization.
