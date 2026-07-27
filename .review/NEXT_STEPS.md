# NEXT_STEPS — active authority pointer

This file alone owns the current checkpoint and candidate state.
`.review/fcb/current/FIDO_FCB_HUMAN_ACTS.tsv` alone owns the set of open human acts.

<!-- FIDO-HUMAN-ACT:C4-REVIEW -->

- **C4 REPAIR 20 IS IMPLEMENTED AND COMPLETE.**
  Authority: `.review/C4_IMPLEMENTATION_REPAIR_20.md` (installed verbatim). <!-- FIDO-FCB-REF:REVIEW-C4-IMPLEMENTATION-REPAIR-20-MD -->
- **Candidate offered for human review.** `964575286acdb3c16df4bb9a11f1194a9418978c` is the C4
  implementation candidate. `0ffdc5f7019204a868d75ef709a16fb69a9979d5` was the twenty-first blocked candidate
  and is superseded. Both blocker classes are closed; the mandatory whole-system closure audit is
  `.review/C4_REPAIR_20_CLOSURE_AUDIT.md` <!-- FIDO-FCB-REF:REVIEW-C4-REPAIR-20-CLOSURE-AUDIT-MD --> and the
  obligation matrix reads 12 of 12 closed.
- **C4 is still NOT accepted.** Only Rob accepts it. Awaiting his human C4 Implementation Review.
- **The two blocker classes repair 20 closed.** Both were enforcement defects reproduced against the exact
  candidate before anything was edited, and each disproved a public completion claim. Both repairs were then
  mutation-tested by reverting them, so the controls that now cover them have been watched failing.
  1. **`D-24` scanned a hard-coded subset of authority.** The manifest rows validated correctly, but the
     scanned corpus was a Python constant, so the active repair directive, the functional contract and the
     accepted review basis were never read; a dangling operational path appended to the active directive left
     the gate green. Corpus membership now comes from the canonical typed manifest through a closed
     `corpus_role` field, the four declarations that ASSIGN authority are themselves checked, the FCB Index
     live-file table states a role for every live-set file and must agree with the manifest both ways, and a
     new authority row causes its target to be scanned with no Python edit. 69 rows, 23 authorities, 49
     controls.
  2. **`A005` missed a multiline `Local Notation`.** The class rule was checked one physical line at a time,
     so an UpperCamelCase alias split across lines was invisible — and every negative control had put the
     whole declaration on one line. It is now parsed from the same stripped-code statement stream every other
     declaration rule uses, with the identifier extracted generally and judged afterwards; extraction is never
     conditional on the first character. 72 controls, including four repository-level ones that mutate a
     tracked certified module and run both input modes, each with a clean twin.
- **A007 is installed as authority, not as permission.** `FCB-A007-POST-C4-MECHANICAL-SERIES` and Governance
  `D-27` are in Git; `.review/M_SERIES_PLAN.md` is a live authority. **M1, M2, M3 and M4 implementation remain
  FORBIDDEN until Rob accepts C4.** So do C5, checkpoint-definition Step 0, post-C4 features, the broad source
  cleanup and proof-module partitioning.
- **Obligation tracking.** `.review/C4_REPAIR_20_OBLIGATION_MATRIX.tsv` holds one row per repair-20 <!-- FIDO-FCB-REF:REVIEW-C4-REPAIR-20-OBLIGATION-MATRIX-TSV -->
  obligation. `make claims` refuses to let `.review/REVIEW_REQUEST.md` request review while any row is open —
  freezing early is a gate failure, not a judgement call.
- **Retained results — do NOT regress.** Repair 19: the exact source occurrence in the public cause theorems
  (accepted locals 11/9/7/5 via `accepted_conversion_at`, rejected via `childfail_conversion_at` and
  `deep_fail_innermost_diag_claim`), the A005 class rule, the two-stage sealed controls that prove the module
  loaded, the executed read-failure control, and the two-way D-24 relation. Repair 18: one accepted and one
  rejected root fixture over one exact returned object, the cause-owned predicates projecting their suffix and
  tail accumulator from `total_forest_outcome_cause`, the exact singleton rejected diagnostic, and D-07.
  Repair 17: the A006 mint, the sealed `Safe.Program`, the causal theorems over any retained phase. Repair 16:
  the direct package chain and the sealed `Core`. Repair 15: the whole-elaboration core, the sealed
  capability, the one mint path. Repair 13: the exact standard work-member index. Repair 12: exact source-step
  identity. A005: the module rename and byte-identical output.
- **Scope decision (reviewer, standing):** **do NOT delete `Index.Program` during a repair.**
- **Functional contract:** `.review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md`. <!-- FIDO-FCB-REF:REVIEW-C4-SOURCE-TYPE-NAME-CONVERSION-PLAN-MD -->
  **Accepted review basis:** `.review/REVIEW_BASIS.md`. <!-- FIDO-FCB-REF:REVIEW-REVIEW-BASIS-MD -->
  **Campaign authority:** `.review/SOURCE_FOREST_MASTER_PLAN.md`, <!-- FIDO-FCB-REF:REVIEW-SOURCE-FOREST-MASTER-PLAN-MD -->
  whose per-checkpoint status is `.review/SOURCE_FOREST_STATUS.md`. <!-- FIDO-FCB-REF:REVIEW-SOURCE-FOREST-STATUS-MD -->
- **Original C4 baseline:** `8c9212a8c814c7a99a5e3ef1970a0ae32425a918`.
- **Blocked C4 implementation candidates (all twenty-one):** `89b8e54` (1) · `1c4a7de` (2) · `806ce87` (3) ·
  `af2fc87` (4) · `9d4aff5` (5) · `3b4f40e` (6) · `3a92d22` (7) · `91e8dbb` (8) · `a2a5b46` (9) · `a8a4472` (10) ·
  `3ecf32e` (11) · `48c0b31` (12) · `af7d5d3` (13) · `9d5246e` (14) · `3386c02` (15) · `20c5ad5` (16) ·
  `deda8bd` (17) · `12b1bc9` (18) · `92fc04e` (19) · `50c3bcc` (20) ·
  `0ffdc5f7019204a868d75ef709a16fb69a9979d5` (21).
  The intermediate implementation commit `0d0036c` is superseded within repair 20, not a blocked candidate.
  Not candidates: `37c9597`; the documentation-only freezes `c5b67495`, `25bcd7aa`, `c8ce2d8c`,
  `e15232d3`, `2b848871` and `cc63a78c3729772b9114b20e653942cda23cc53a`; the life-document commit `392d2084`;
  and the A007 authority commit `fad5514`, which changed no Rocq, OCaml, Go or generated byte.
- **Governing accepted amendments.** `A001` through `A007` are **ACCEPTED**; Governance owns `D-01` through
  `D-27`.
- **Documentation basis:** the live Fido Conformance Basis is `.review/fcb/current/` (Git-canonical per **A002**,
  living-document form per **A003**; identity is `git rev-parse HEAD:.review/fcb/current`).
- **Scope decisions:** **ADR-0001 / SR-001 ACCEPTED FOR CURRENT BASIS** (Rob, 2026-07-25) — Go 1.23 on
  `linux/amd64` with `GOAMD64=v1`; `int`/`uint` 64-bit and distinct from fixed-width types. `uintptr` requires
  reopening ADR-0001 or adopting a replacement scope/target decision and paying its full inclusion price.
  ADR-0002 remains REJECTED AS WRITTEN / OPEN. SR-009 remains an unresolved existing restriction. `LAT-X004` is
  settled as option (ii), the rounding-invariant accepted domain.
- **Open questions:** `.review/OPEN_QUESTIONS.md`.
- **Automatic Codex review:** DISABLED.
