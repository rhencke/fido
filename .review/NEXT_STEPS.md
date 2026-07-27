# NEXT_STEPS — active authority pointer

This file alone owns the current checkpoint and candidate state. No other document, and no canonical data row,
carries a candidate identity.
`.review/fcb/current/FIDO_FCB_HUMAN_ACTS.tsv` alone owns the set of open human acts.

<!-- FIDO-HUMAN-ACT:M0-REVIEW -->

- **C4 IS ACCEPTED.** Rob's disposition is `C4-ACCEPT-39ea7e3`. The exact accepted ref is recorded once, in
  the A008 amendment register row in `.review/fcb/current/FIDO_FCB_GOVERNANCE.md` — it is history, not current
  work. Git history owns the blocked candidates and the repair narratives.
- **M0 GOVERNANCE CLOSEOUT IS THE SOLE ACTIVE WORK.**
  Authority: `.review/M0_GOVERNANCE_CLOSEOUT.md`. <!-- FIDO-FCB-REF:REVIEW-M0-GOVERNANCE-CLOSEOUT-MD -->
  M0 publishes the C4 disposition, retires repair-state archaeology to Git history, installs the strict
  checkpoint-scope law, moves current authority to the M-series, and verifies the existing D-07 and D-24 state
  against the accepted snapshot. It changes no Rocq, OCaml, build, tool, fixture or generated file.
- **M0 candidate offered for human review:** `2d40c71519365d77fd07f2b01030c47914694002`. All ten obligations
  are closed. Only Rob accepts M0.
- **M1, M2, M3, M4 and C5 remain FORBIDDEN until Rob accepts M0.** Installing a plan is not permission to run
  it, and a green intermediate gate is not acceptance.
- **Obligation tracking.** `.review/M0_OBLIGATION_MATRIX.tsv` holds one row per M0 obligation, `M0-01` <!-- FIDO-FCB-REF:REVIEW-M0-OBLIGATION-MATRIX-TSV -->
  through `M0-10`.
- **No C4 repair artifact remains in the live tree.** The repair-21 directive, obligation matrix and closure
  audit are retired to Git history. `tools/claim-matrix-gate.py` pinned the matrix as its subject, so retiring
  it needed the gate to follow the active checkpoint; Rob authorized that retarget on 2026-07-27 after it was
  reported as the smallest M0 conflict. The gate's behaviour is unchanged — only its subject moved.
- **Scope rule (D-28).** Review the whole system. Block the active checkpoint only for a defect in its accepted
  contract or an explicit acceptance dependency. Assign every other finding to the earliest mandatory
  follow-up — M1 for source prose and dead code, M2 for build evidence, M3 for tool and build architecture, M4
  for approved restructuring — and keep it visible in Git. Discovery does not determine scope.
- **Retained results — do NOT regress.** C4's accepted result: one raw `Syntax.Program` and one structural
  `Index` authority; one compiler-owned source-name resolver; one retained whole `Compilable.Core` built
  through the production path; exact accepted and rejected provenance through the returned objects; exact
  source-occurrence identity in the public cause theorems; one capability mint through `Compilable.compile`;
  sealed `Compilable.Core`, `Compilable.Program`, `Compilable.Failure`, `Compilable.Facts` and
  `Safe.Program`; the A006 opaque exact-value-indexed `Emit.Mint.Token` with a reducible image carrier; no
  compatibility result peer, reconstruction root, copied provenance or second conversion authority; source
  spelling retained through compilation and rendering, including distinct `byte`/`uint8` and `rune`/`int32`
  identities; exact diagnostics, generated Go bytes and reviewed runtime output; zero assumptions under the
  whole-theory audit. Plus the governance results: D-07 discovery, the D-24 two-way relation with its path
  universe derived from the repository, the A005 statement-level class rule, and the mutation harness that
  proves each gate helper load-bearing.
- **Scope decision (reviewer, standing):** **do NOT delete `Index.Program`.**
- **Functional contract for C4:** `.review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md`. <!-- FIDO-FCB-REF:REVIEW-C4-SOURCE-TYPE-NAME-CONVERSION-PLAN-MD -->
  **Accepted review basis:** `.review/REVIEW_BASIS.md`. <!-- FIDO-FCB-REF:REVIEW-REVIEW-BASIS-MD -->
  **Campaign authority:** `.review/SOURCE_FOREST_MASTER_PLAN.md`, <!-- FIDO-FCB-REF:REVIEW-SOURCE-FOREST-MASTER-PLAN-MD -->
  whose per-checkpoint status is `.review/SOURCE_FOREST_STATUS.md`. <!-- FIDO-FCB-REF:REVIEW-SOURCE-FOREST-STATUS-MD -->
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
