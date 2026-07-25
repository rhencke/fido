# Fido FCB Human Review Index v2

> **Derived reference, not authority.** The code and its gated theorems are the sole authority.  
> **FCB version:** `v2` · **Generated:** `2026-07-25`  
> **Supersedes:** `FIDO_FCB_HUMAN_REVIEW_INDEX_v1.md`  
> **Repository basis:** `rhencke/fido@ece4c1dd0797eff6e9ebdd5d77a0e59f1c9e76e0` · source snapshot SHA-256 `6e25e8be64a77b7d98609c607d48b1d6917b2bf0480d10fa4a92f1a6bb170eff`  
> **Terminal-bundle basis:** SHA-256 `58abd876a0962bde42e5c9fc0365a8431b88b13beb790440e4b52031c7f8aad0` · handoff SHA-256 `fdfc2c235707aeeef58c566f5fd145850ca606df8d693f5cc6bc81f2112eb143`  
> **Amendment basis:** `FCB-A001-INTRINSIC-STATIC-CAPABILITY-PROVENANCE` · accepted `2026-07-25` · directive SHA-256 `79a8fa3f6d5a861b82259a578eef6123369dbc9567fbd63288b93c1ce1037b8c`  
> Regenerate this document at each checkpoint acceptance. Delete every stale copy from every model library.  
> This library does not accept C4 and does not authorize C5; `.review/NEXT_STEPS.md` remains the live checkpoint authority.

This index lists current human acts. It is regenerated after every accepted checkpoint. It is not a hand-edited memory substitute.

| ID | Status | Required human act | Source / owner | Effect |
|---|---|---|---|---|
| `C4-REVIEW` | **BLOCKED / AWAITING REPAIR-14 CANDIDATE** | Review the next C4 candidate only after intrinsic retained elaboration repair 14 is implemented and frozen. The prior implementation candidate `9d5246eedf9e9a3c019b85e9dc65ce9e6f867179` is blocked. | `.review/NEXT_STEPS.md`, A001, and the main review thread | C5 and the post-C4 trim remain forbidden. |
| `ADR-0002` | **OPEN / DEFERRED** | Choose the DecimalFloat domain after differential and proof-cost evidence. | Governance ADR register | Before C7 broadens floating constant coverage. |
| `ADR-0004` | **DEFERRED** | Choose the multi-platform 64-bit target set. | Governance ADR register | C16. |
| `TOOLCHAIN-PROVENANCE` | **PENDING** | Replace pending local-distribution evidence with verified official tarball evidence, or expressly retain pending status for a specific review use. | Toolchain Evidence | Adequacy evidence remains pending; formal architecture is unchanged. |
| `FCB-SHOWROOM` | **OPEN** | Have Claude perform one adversarial showroom pass over this FCB v2 set; disposition findings. | FCB transformation completion rule | Required before calling the document split final. |

## Closed in FCB v2

- `FCB-A001`: accepted on 2026-07-25. The static capability and failure result must retain the exact whole elaboration by construction; `ARCH-03` reopened and strengthened; D-22 added.
- `LAT-X004`: option (ii), proved rounding-invariant accepted domain, owner fixed at `SPEC-096` / `ExprFact` / `SC-05`.
- `ADR-0001`: adopted for the current single linux/amd64 target; reopens at C16 or an earlier target/`uintptr` request.
- `ADR-0003`: adopted.
- Terminal open candidate: Rob’s 2026-07-24 instruction authorized FCB generation from it while preserving pending provenance as pending.

Old F/R/T countersign tables remain in the frozen terminal bundle as provenance. They do not remain live project-library documents; their settled contents are absorbed into Governance and Fixed Points, and their unresolved substantive acts appear above.
