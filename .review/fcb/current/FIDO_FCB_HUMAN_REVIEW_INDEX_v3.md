# Fido FCB Human Review Index v3

> **Derived reference, not authority.** The code and its gated theorems are the sole implementation authority.  
> **FCB document version:** `v3` · **FCB set:** `v3` · **Generated:** `2026-07-25`  
> **Supersedes:** `FIDO_FCB_HUMAN_REVIEW_INDEX_v2.md`  
> **Source repository basis:** `rhencke/fido@ece4c1dd0797eff6e9ebdd5d77a0e59f1c9e76e0` · source snapshot SHA-256 `6e25e8be64a77b7d98609c607d48b1d6917b2bf0480d10fa4a92f1a6bb170eff`  
> **Terminal-bundle basis:** SHA-256 `58abd876a0962bde42e5c9fc0365a8431b88b13beb790440e4b52031c7f8aad0` · handoff SHA-256 `fdfc2c235707aeeef58c566f5fd145850ca606df8d693f5cc6bc81f2112eb143`  
> **Amendments:** `FCB-A001-INTRINSIC-STATIC-CAPABILITY-PROVENANCE`; `FCB-A002-GIT-CANONICAL-FCB-STORAGE`  
> **Canonical live location:** `.review/fcb/current/` in the exact Git ref used for the task.  
> **Stable bootstrap:** `.review/fcb/current/INDEX.md` · **Manifest:** `.review/fcb/current/FIDO_FCB_MANIFEST.sha256`  
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
| `FCB-SHOWROOM` | **OPEN** | Have Claude perform one adversarial showroom pass over the Git-hosted FCB v3 set; disposition findings. | FCB transformation completion rule | Required before calling the document split final. |

## Closed in FCB v3

- `FCB-A002`: accepted on `2026-07-25`. Git is the sole canonical FCB store; project libraries contain bootstrap shims only; root `CLAUDE.md` uses the same bootstrap; D-23 added.
- `FCB-A001`: accepted on `2026-07-25`. The static capability and failure result must retain the exact whole elaboration by construction; `ARCH-03` reopened and strengthened; D-22 added.
- `LAT-X004`: option (ii), proved rounding-invariant accepted domain, owner fixed at `SPEC-096` / `ExprFact` / `SC-05`.
- `ADR-0001`: adopted for the current single linux/amd64 target; reopens at C16 or an earlier target/`uintptr` request.
- `ADR-0003`: adopted.
- Terminal open candidate: Rob’s 2026-07-24 instruction authorized FCB generation from it while preserving pending provenance as pending.

Old F/R/T countersign tables remain in the frozen terminal bundle as provenance. Superseded FCB sets remain in Git history or `.review/fcb/archive/`; their settled contents are absorbed into Governance and Fixed Points, and their unresolved substantive acts appear above.
