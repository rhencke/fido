# NEXT_STEPS — active authority pointer

This file alone owns the current checkpoint and candidate state. No other document, and no canonical data row,
carries a candidate identity.
`.review/fcb/current/FIDO_FCB_HUMAN_ACTS.tsv` alone owns the set of open human acts.

<!-- FIDO-HUMAN-ACT:C4-REVIEW -->

- **REPAIR 21 IS THE SOLE ACTIVE C4 IMPLEMENTATION TASK.**
  Authority: `.review/C4_IMPLEMENTATION_REPAIR_21.md`. <!-- FIDO-FCB-REF:REVIEW-C4-IMPLEMENTATION-REPAIR-21-MD -->
- **C4 is NOT accepted.** Only Rob accepts it. `964575286acdb3c16df4bb9a11f1194a9418978c` is the
  twenty-second blocked candidate; `d17fbe37d28a71c6f64e166409b494b30287c8b6` was its documentation-only
  freeze and is not a separate candidate.
- **The two blocker classes repair 21 must close.**
  1. **`D-24` still proves a self-selected subset.** The gate encoded the repository path grammar in Python —
     hard-coded namespace roots and root files, substring marker binding, unchecked path spellings, owner
     paths that could leave the tree, and a repository path that could be exempted by retyping it as external
     evidence. A gate that chooses which namespaces exist can only prove the subset it recognised. The path
     universe must come from the repository inventory of the exact snapshot being checked, through one
     canonical repository-path parser shared by manifest targets, owners, live-set entries, Index table cells
     and paths found in authority prose.
  2. **The canonical human-act data contradicted this file.** The `C4-REVIEW` row carried a candidate SHA and
     a "no candidate is offered" state while this file offered one. `NEXT_STEPS` alone owns mutable candidate
     identity; the human act states only the durable act, and the generator refuses any Git object ID in open
     human-act data.
- **A007 is installed as authority, not as permission.** `FCB-A007-POST-C4-MECHANICAL-SERIES` and Governance
  `D-27` are in Git; `.review/M_SERIES_PLAN.md` is a live authority. **M1, M2, M3 and M4 implementation remain
  FORBIDDEN until Rob accepts C4.** So do C5, checkpoint-definition Step 0, post-C4 features, the broad source
  cleanup and proof-module partitioning.
- **Obligation tracking.** `.review/C4_REPAIR_21_OBLIGATION_MATRIX.tsv` holds one row per repair-21 <!-- FIDO-FCB-REF:REVIEW-C4-REPAIR-21-OBLIGATION-MATRIX-TSV -->
  obligation. `make claims` refuses to let `.review/REVIEW_REQUEST.md` request review while any row is
  absent, duplicate, malformed or open.
- **Retained results — do NOT regress.** Repair 20: A007 and the M-series authority installed before
  implementation, `Local Notation` judged over Rocq statements, corpus membership carried by the manifest's
  `corpus_role`, and the live FCB set declared. Repair 19: the exact source occurrence in the public cause
  theorems (accepted locals 11/9/7/5 via `accepted_conversion_at`, rejected via `childfail_conversion_at` and
  `deep_fail_innermost_diag_claim`), the A005 class rule, and the two-stage sealed controls that prove the
  module loaded. Repair 18: one accepted and one rejected root fixture over one exact returned object, the
  cause-owned predicates projecting their suffix and tail accumulator from `total_forest_outcome_cause`, the
  exact singleton rejected diagnostic, and D-07. Repair 17: the A006 mint, the sealed `Safe.Program`, the
  causal theorems over any retained phase. Repair 16: the direct package chain and the sealed `Core`. Repair
  15: the whole-elaboration core, the sealed capability, the one mint path. Repair 13: the exact standard
  work-member index. Repair 12: exact source-step identity. A005: the module rename and byte-identical output.
- **Scope decision (reviewer, standing):** **do NOT delete `Index.Program` during a repair.**
- **Functional contract:** `.review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md`. <!-- FIDO-FCB-REF:REVIEW-C4-SOURCE-TYPE-NAME-CONVERSION-PLAN-MD -->
  **Accepted review basis:** `.review/REVIEW_BASIS.md`. <!-- FIDO-FCB-REF:REVIEW-REVIEW-BASIS-MD -->
  **Campaign authority:** `.review/SOURCE_FOREST_MASTER_PLAN.md`, <!-- FIDO-FCB-REF:REVIEW-SOURCE-FOREST-MASTER-PLAN-MD -->
  whose per-checkpoint status is `.review/SOURCE_FOREST_STATUS.md`. <!-- FIDO-FCB-REF:REVIEW-SOURCE-FOREST-STATUS-MD -->
- **Original C4 baseline:** `8c9212a8c814c7a99a5e3ef1970a0ae32425a918`.
- **Blocked C4 implementation candidates (all twenty-two):** `89b8e54` (1) · `1c4a7de` (2) · `806ce87` (3) ·
  `af2fc87` (4) · `9d4aff5` (5) · `3b4f40e` (6) · `3a92d22` (7) · `91e8dbb` (8) · `a2a5b46` (9) · `a8a4472` (10) ·
  `3ecf32e` (11) · `48c0b31` (12) · `af7d5d3` (13) · `9d5246e` (14) · `3386c02` (15) · `20c5ad5` (16) ·
  `deda8bd` (17) · `12b1bc9` (18) · `92fc04e` (19) · `50c3bcc` (20) · `0ffdc5f` (21) ·
  `964575286acdb3c16df4bb9a11f1194a9418978c` (22).
  Not candidates: `37c9597`; the documentation-only freezes `c5b67495`, `25bcd7aa`, `c8ce2d8c`, `e15232d3`,
  `2b848871`, `cc63a78c`, `8b98080` and `d17fbe37d28a71c6f64e166409b494b30287c8b6`; the life-document commit
  `392d2084`; the A007 authority commit `fad5514`; and `0d0036c`, an intermediate implementation commit
  superseded within repair 20.
- **Governing accepted amendments.** `A001` through `A007` are **ACCEPTED**; Governance owns `D-01` through
  `D-27`.
- **Documentation basis:** the live Fido Conformance Basis is `.review/fcb/current` (Git-canonical per **A002**,
  living-document form per **A003**; identity is `git rev-parse HEAD:.review/fcb/current`).
- **Scope decisions:** **ADR-0001 / SR-001 ACCEPTED FOR CURRENT BASIS** (Rob, 2026-07-25) — Go 1.23 on
  `linux/amd64` with `GOAMD64=v1`; `int`/`uint` 64-bit and distinct from fixed-width types. `uintptr` requires
  reopening ADR-0001 or adopting a replacement scope/target decision and paying its full inclusion price.
  ADR-0002 remains REJECTED AS WRITTEN / OPEN. SR-009 remains an unresolved existing restriction. `LAT-X004` is
  settled as option (ii), the rounding-invariant accepted domain.
- **Open questions:** `.review/OPEN_QUESTIONS.md`.
- **Automatic Codex review:** DISABLED.
