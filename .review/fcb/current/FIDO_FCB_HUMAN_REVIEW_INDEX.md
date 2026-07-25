# Fido FCB Human Review Index

> **Derived reference, not implementation authority.** The code and its gated theorems are the sole implementation authority.  
> **Living document.** Its identity is its Git blob at the exact ref resolved for the task; its
> history is the commit log. No version suffixes, no checksum manifest.  
> **Accepted amendments:** `FCB-A001-INTRINSIC-STATIC-CAPABILITY-PROVENANCE`; `FCB-A002-GIT-CANONICAL-FCB-STORAGE`; `FCB-A003-LIVING-DOCUMENTATION`.
> **Proposed, awaiting Rob:** `FCB-A004-GIT-RESOLVABLE-LIVING-CORPUS`.  
> **Canonical live location:** `.review/fcb/current/` in the exact Git ref used for the task.  
> **Stable bootstrap:** `.review/fcb/current/INDEX.md`  
> Project libraries contain only a bootstrap shim. They do not contain or own the FCB corpus.  
> Regenerate, verify, and commit affected FCB files in Git after each accepted checkpoint or amendment.  
> This corpus does not accept C4 and does not authorize C5; `.review/NEXT_STEPS.md` remains the live checkpoint authority.


This index lists current human acts. It is regenerated after every accepted checkpoint or documentation amendment. It is not a hand-edited memory substitute.

| ID | Status | Required human act | Source / owner | Effect |
|---|---|---|---|---|
| `C4-REVIEW` | **BLOCKED / AWAITING REPAIR-14 CANDIDATE** | Review the next C4 candidate only after intrinsic retained elaboration repair 14 is implemented and frozen. The prior implementation candidate `9d5246eedf9e9a3c019b85e9dc65ce9e6f867179` is blocked. | `.review/NEXT_STEPS.md`, A001, and the main review thread | C5 and the post-C4 trim remain forbidden. |
| `ADR-0002` | **OPEN / DEFERRED** | Choose the DecimalFloat domain after differential and proof-cost evidence. | Governance ADR register | Before C7 broadens floating constant coverage. |
| `ADR-0004` | **DEFERRED** | Choose the multi-platform 64-bit target set. | Governance ADR register | C16. |
| `TOOLCHAIN-PROVENANCE` | **PENDING** | Replace pending local-distribution evidence with verified official tarball evidence, or expressly retain pending status for a specific review use. | Toolchain Evidence | Adequacy evidence remains pending; formal architecture is unchanged. |
| `FCB-A004` | **PROPOSED / AWAITING DISPOSITION** | Accept, amend, or reject `FCB-A004-GIT-RESOLVABLE-LIVING-CORPUS` (every live documentation reference resolves at one Git ref; adds `D-24`). | Review 100; `.review/fcb/amendments/` | Until dispositioned, A004 is recorded PROPOSED and the Index lists it as such. |
| `FIXED-POINT-EXTERNAL-EVIDENCE` | **OPEN** | Decide whether the twelve external R1-bundle components (pinned spec and memory-model HTML, extractor script, latitude manifest, freeze records, pinned toolchain evidence, F-dispositions, audit JSON, heading and grammar manifests) should be committed into a Git evidence subtree, or expressly retained as external `PROVENANCE-PENDING` references. | Fixed Points registry; D-24 | Their bytes are not in Git, so their protected projections cannot currently be recomputed from the repository. |
| `FCB-SHOWROOM` | **OPEN** | Have Claude perform one adversarial showroom pass over the live Git-hosted FCB; disposition findings. | FCB transformation completion rule | Required before calling the document split final. |

## Closed

- `FCB-A002`: accepted on `2026-07-25`. Git is the sole canonical FCB store; project libraries contain bootstrap shims only; root `CLAUDE.md` uses the same bootstrap; D-23 added.
- `FCB-A001`: accepted on `2026-07-25`. The static capability and failure result must retain the exact whole elaboration by construction; `ARCH-03` reopened and strengthened; D-22 added.
- `LAT-X004`: option (ii), proved rounding-invariant accepted domain, owner fixed at `SPEC-096` / `ExprFact` / `SC-05`.
- `ADR-0001`: adopted for the current single linux/amd64 target; reopens at C16 or an earlier target/`uintptr` request.
- `ADR-0003`: adopted.
- Terminal open candidate: Rob’s 2026-07-24 instruction authorized FCB generation from it while preserving pending provenance as pending.

Old F/R/T countersign tables remain in the frozen terminal bundle as provenance. Superseded FCB sets remain in Git history; their settled contents are absorbed into Governance and Fixed Points, and their unresolved substantive acts appear above.
