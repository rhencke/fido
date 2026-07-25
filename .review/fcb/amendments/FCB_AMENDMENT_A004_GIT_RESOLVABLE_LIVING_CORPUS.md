# FCB Amendment A004 — Every Live Documentation Reference Resolves at One Git Ref

- **ID:** `FCB-A004-GIT-RESOLVABLE-LIVING-CORPUS`
- **Status:** **PROPOSED — Rob disposition required**
- **Author:** Claude (external adversarial reviewer), Review 100
- **Human owner:** Rob
- **Committer:** Claude Code (applied the repairs; authored nothing in this amendment)
- **Date proposed:** `2026-07-25`
- **Reviewed repository head:** `267f239fe63062ed71aa32e0e81de9e5f821266f`
- **Blocked C4 implementation candidate (unchanged):** `9d5246eedf9e9a3c019b85e9dc65ce9e6f867179`

> Recorded with the status the reviewer assigned. Claude Code does not record a human disposition Rob has not
> given. The live Index therefore lists A004 as proposed; on Rob's acceptance the status here and there both
> change, and nothing else in this document needs to.

## New information

The first adversarial review of the Git-canonical corpus found that A003 was only partly applied: the live Index
still named set versions and version-suffixed files that no longer exist; live Governance and Model Operations
still required a deleted checksum manifest; A003 was absent from the amendment register; banners embedded a
pre-migration repository basis that later commits had already invalidated; the Checkpoint Authoring Guide still
demanded document hashes and set-version labels; the project-library shim still pointed at the deleted manifest;
and the fixed-point registry contained repository-looking paths that resolve to nothing in the reviewed ref.

These are not Go-language or proof-model defects. They are defects in the new documentation authority path: a
reader following the bootstrap in good faith is sent to objects that do not exist.

## Settled rule sought

Every operational reference in the live FCB must either

1. resolve to an existing file or section in the same exact Git ref, or
2. be explicitly typed as an external evidence reference with a named availability/provenance status.

A live document may not instruct a model to load a deleted manifest, a nonexistent versioned filename, or a
stale embedded repository state. **Git ref plus path is the identity of living documentation.** Historical
package hashes and third-party artifact pins remain only where they describe evidence Git does not contain.

## Governance decision added

**D-24 — Every live documentation reference resolves at one Git ref.** Every operational path, file, selector,
checkpoint authority, and consultation-map entry in the live FCB resolves within the one exact Git ref used for
the task, unless explicitly typed as an external evidence reference with a recorded availability status. A
deleted manifest, renamed file, stale self-version, or dangling repository path is a blocking documentation
defect. *Rationale:* Git can be the sole source of truth only when the live corpus is self-consistent and every
reader is sent to an object that exists.

## Fixed-point resolution performed

The registry's 42 components were resolved honestly, with every target selector verified present before the
change:

- **29 rebased** to the live corpus, where the content demonstrably lives: the twelve `ARCH-01..12` charter
  components and six EVID components to `FIDO_FCB_ARCHITECTURE_CHARTER.md` (all twelve `##` headings and the
  `12.4` / `22.3` / `25.21` / `25.22` sections and both anchored regions confirmed present); three to
  `FIDO_FCB_LATITUDE_LEDGER.tsv` and eight to `FIDO_FCB_CLOSURE_LEDGER.csv` (every row key confirmed present).
  Baseline and terminal are now distinguished by **ref**, which is the living-document model. No selector and no
  protected projection is weakened.
- **1 already correct:** `ARCH-03 / static-capability-provenance`.
- **12 typed as external evidence:** the pinned Go specification and memory-model HTML, the extraction script,
  the latitude manifest, the freeze records, the pinned toolchain evidence document, the F-dispositions, the two
  audit JSON files, and the heading and grammar manifests. Their bytes belong to the R1 spec-closure bundle and
  are not held by Git.

Two components (`EVID-04 / fma-observation` and `EVID-06 / invocation-contract`) were **not** rebased to
`FIDO_FCB_TOOLCHAIN_EVIDENCE.md`: their selectors were checked and do **not** resolve there, so rebasing would
have created fresh dangling references. They are typed external instead.

The availability of all twelve external components is an open human act: `FIXED-POINT-EXTERNAL-EVIDENCE` in the
Human Review Index. No bytes were invented and no protected projection was silently weakened.

## Scope

Documentation storage, reference integrity, and active process text only. No Closure Ledger row, Latitude Ledger
row, Acceptance Gate, Go-language meaning, proof-contract meaning, roadmap row assignment, checkpoint order, or
target/toolchain policy changes. The parent fixed-point count is unchanged. No C4 code changes; C4 remains
blocked at `9d5246e` and C5 remains forbidden.
