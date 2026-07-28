# NEXT_STEPS — active authority pointer

This file alone owns the current checkpoint and candidate state. No other document, and no canonical data row,
carries a candidate identity.
`.review/fcb/current/FIDO_FCB_HUMAN_ACTS.tsv` alone owns the set of open human acts.

<!-- FIDO-HUMAN-ACT:M1-REVIEW -->

- **M1 SOURCE DIET REPAIR 5 IS THE SOLE ACTIVE WORK.**
  Authority: `.review/M1_SOURCE_DIET.md`. <!-- FIDO-FCB-REF:REVIEW-M1-SOURCE-DIET-MD -->
  The blocking review it answers is `.review/M1_IMPLEMENTATION_REPAIR_5.md`. <!-- FIDO-FCB-REF:REVIEW-M1-IMPLEMENTATION-REPAIR-5-MD -->
  Accepted review basis: `.review/REVIEW_BASIS.md`. <!-- FIDO-FCB-REF:REVIEW-REVIEW-BASIS-MD -->
  Baseline: the exact ref sealed in `.review/M1_BASELINE.tsv`.
- **Earlier M1 candidates are superseded.** Git history owns their refs, freezes, findings, and repair narratives.
- **C4 and M0 are accepted.** Their permanent guarantees are owned by the FCB Architecture Charter and
  Governance; M1 must preserve them unchanged. Rob's dispositions are `C4-ACCEPT-39ea7e3` and
  `M0-ACCEPT-86a63db`.
- **Scope decision (reviewer, standing):** **do NOT delete `Index.Program`.**
- **M2, M3, M4, C5 Step 0 and C5 remain FORBIDDEN until Rob accepts M1.** Installing a plan is not
  permission to run it, and a green intermediate gate is not acceptance.
- **Obligation tracking.** `.review/M1_OBLIGATION_MATRIX.tsv` holds one row per M1 obligation, `M1-01` <!-- FIDO-FCB-REF:REVIEW-M1-OBLIGATION-MATRIX-TSV -->
  through `M1-15`. `tools/claim-matrix-gate.py` follows the active checkpoint: its subject moves with the
  matrix, and its behaviour does not.
- **Scope rule (D-28).** Review the whole system. Block the active checkpoint only for a defect in its accepted
  contract or an explicit acceptance dependency. Assign every other finding to the earliest mandatory
  follow-up — M1 for source prose and dead code, M2 for build evidence, M3 for tool and build architecture, M4
  for approved restructuring — and keep it visible in Git. Discovery does not determine scope.
- **Governing accepted amendments.** `A001` through `A008` are **ACCEPTED**; Governance owns `D-01` through
  `D-29`.
- **Documentation basis:** the live Fido Conformance Basis is `.review/fcb/current` (Git-canonical per **A002**,
  living-document form per **A003**; identity is `git rev-parse HEAD:.review/fcb/current`).
- **Scope decisions:** **ADR-0001 / SR-001 ACCEPTED FOR CURRENT BASIS** (Rob, 2026-07-25) — Go 1.23 on
  `linux/amd64` with `GOAMD64=v1`; `int`/`uint` 64-bit and distinct from fixed-width types. `uintptr` requires
  reopening ADR-0001 or adopting a replacement scope/target decision and paying its full inclusion price.
  ADR-0002 remains REJECTED AS WRITTEN / OPEN. SR-009 remains an unresolved existing restriction. `LAT-X004` is
  settled as option (ii), the rounding-invariant accepted domain.
- **Open questions:** `.review/OPEN_QUESTIONS.md`.
- **Automatic Codex review:** DISABLED.
