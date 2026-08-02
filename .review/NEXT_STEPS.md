# NEXT_STEPS — active authority pointer

This file owns mutable checkpoint and candidate state. `.review/REVIEW_REQUEST.md` may pin the exact candidate
under human review, but it does not own mutable state. Canonical data rows carry no candidate identity.
`.review/fcb/current/FIDO_FCB_HUMAN_ACTS.tsv` alone owns the set of open human acts.

<!-- FIDO-HUMAN-ACT:M2-REVIEW -->

- **M1 SOURCE DIET IS ACCEPTED** at `6524b437bd7a7d6b2616563b8789e28a00c7af13`, under Rob's disposition
  `M1-ACCEPT-6524b43`. Git history owns its contract, its obligation matrix and its evidence. Its permanent
  result — the source-comment law and the gate enforcing it — is owned by `.review/M_SERIES_PLAN.md` and
  `tools/source-diet.py`, and outlives the checkpoint that produced it.
- **M2 BUILD OBSERVATORY IS FROZEN AWAITING ROB'S REVIEW.** Candidate
  `1003734e67e2f07f5a10ec931e5c5729981d4652`, whose canonical observation measures that exact ref: 19
  traces, 153 samples, 34.4 minutes, closed lifecycle, all five validation components measured.
  Authority: `.review/M2_IMPLEMENTATION_REPAIR_5.md`, the sole permitted implementation work. <!-- FIDO-FCB-REF:REVIEW-M2-IMPLEMENTATION-REPAIR-5-MD -->
  Earlier M2 candidates are superseded. Git history owns their refs, freezes, findings, and repair narratives.
  The live M2 contract is `.review/M2_BUILD_OBSERVATORY.md`; the accepted review basis is
  `.review/REVIEW_BASIS.md`. <!-- FIDO-FCB-REF:REVIEW-REVIEW-BASIS-MD -->
  Repair 5 closes the remaining authority and self-validation defects inside the trace-cover framework, which
  is kept: one exact captured basis makes each observation self-validating; one retained `AcquisitionPlan`
  owns the expected relation and trace acquisition; one root validator owns observation validity and every
  path invokes it; checkpoint evidence obeys the exact grammar its trace declares; every trace carries one
  explicit atomic or decomposed partition recomputed from retained events; suite self-cost follows from one
  monotonic lifecycle closed in two phases; and every completed bundle carries both comparison files.
  Fourteen obligations are reopened and close only on exact evidence and controls.
  M2 measures and reports. It does not optimize or restructure; every finding is assigned in
  `.review/M2_RECOMMENDATIONS.tsv` to M3, M4 or retain.
- **C4 and M0 are accepted.** Their permanent guarantees are owned by the FCB Architecture Charter and
  Governance; M2 must preserve them unchanged. Rob's dispositions are `C4-ACCEPT-39ea7e3` and
  `M0-ACCEPT-86a63db`.
- **Scope decision (Rob, this checkpoint, authorized explicitly):**
  `M2-SCOPE-AMENDMENT-NO-DUPLICATE-MEASUREMENT` — the timing suite measures each phase exactly once cold and
  exactly once hot, duplicated sub-phases included, and must finish inside one hour. `project.cached.fresh`
  and the five `project.incremental.<edit>` scenarios are withdrawn with their edits; the canonical relation
  falls from 252 required metrics to 153. Recorded as M2 contract §1C, which also names what it supersedes:
  Repair 5 §9 step 14's fixed 27 traces / 252 metrics, taken through that step's own registry escape, and
  contract §3A.2 and §3A.6, amended in place. **The reviewer authored none of it.** Rob authored and
  accepted it; Fido applied it as Committer.
- **Scope decision (reviewer, standing):** **do NOT delete `Index.Program`.**
- **M3, M4, C5 Step 0 and C5 remain FORBIDDEN until Rob accepts M2.** Installing a plan is not
  permission to run it, and a green intermediate gate is not acceptance.
- **Obligation tracking.** `.review/M2_OBLIGATION_MATRIX.tsv` holds one row per M2 obligation, `M2-01`
  through `M2-19`. `tools/claim-matrix-gate.py` follows the active checkpoint: its subject moves with the
  matrix, and its behaviour does not.
- **Scope rule (D-28).** Review the whole system. Block the active checkpoint only for a defect in its accepted
  contract or an explicit acceptance dependency. Assign every other finding to the earliest mandatory
  follow-up — M2 for build evidence, M3 for tool and build architecture, M4 for approved restructuring — and
  keep it visible in Git. Discovery does not determine scope.
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
