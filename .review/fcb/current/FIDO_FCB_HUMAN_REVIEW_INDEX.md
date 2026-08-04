# Fido FCB Human Review Index

<!-- GENERATED FILE — do not edit by hand.
     Data authority: .review/fcb/current/FIDO_FCB_HUMAN_ACTS.tsv
     Generator:      tools/human-review-index.py  (make human-acts-write; verified by make human-acts)
     Governance D-07: open human acts are generated from canonical rows, never hand-copied. -->

> **Derived reference, not implementation authority.** The code and its gated theorems are the sole implementation authority.  
> **Living document.** Its identity is its Git blob at the exact ref resolved for the task; its
> history is the commit log. No version suffixes, no checksum manifest.  
> **Current state lives with its owner.** `.review/fcb/current/FIDO_FCB_GOVERNANCE.md` owns the
> accepted amendments and governance decisions; `.review/NEXT_STEPS.md` owns the active checkpoint and
> candidate. This document copies neither.  
> **Canonical live location:** `.review/fcb/current/` in the exact Git ref used for the task.  
> **Stable bootstrap:** `.review/fcb/current/INDEX.md`

This index is the generated view of the current open human acts. Each row is owned by one source file
carrying exactly one `FIDO-HUMAN-ACT` anchor, which the generator validates. A closed act is removed from the
data authority; Git history and the owning ADR, governance row, fixed-point record or accepted review commit
preserve its disposition.

| ID | Status | Required human act | Source / owner | Effect |
|---|---|---|---|---|
| `ADR-0002` | **DEFERRED** | Choose the Float.Decimal domain after differential and proof-cost evidence. | Governance ADR register | Before C7 broadens floating constant coverage. |
| `ADR-0004` | **DEFERRED** | Choose the multi-platform 64-bit target set. | Governance ADR register | C16. |
| `FCB-SHOWROOM` | **OPEN** | Have Claude perform one adversarial showroom pass over the live Git-hosted FCB; disposition findings. | FCB transformation completion rule | Required before calling the document split final. |
| `FIXED-POINT-EXTERNAL-EVIDENCE` | **OPEN** | Decide whether the twelve external R1-bundle components should be committed into a Git evidence subtree, or expressly retained as external PROVENANCE-PENDING references. | Fixed Points registry; D-24 | Their bytes are not in Git, so their protected projections cannot currently be recomputed from the repository. |
| `M3-REVIEW` | **DEFERRED** | Accept or block M3, once M3 freezes an exact candidate and offers it for review. Only Rob accepts M3. | .review/NEXT_STEPS.md and the main review thread | Until Rob accepts M3, M4 implementation and C5 remain forbidden; M4 additionally needs its own plan approval. |
| `M4-PLAN-APPROVAL` | **DEFERRED** | Approve the exact M4 Mechanical Refactor plan produced by M3, or reopen it. | Governance D-27; amendment FCB-A007-POST-C4-MECHANICAL-SERIES | M4 cannot begin until Rob accepts the exact plan; C5 checkpoint-definition Step 0 waits behind M4. |
| `TOOLCHAIN-PROVENANCE` | **PENDING** | Replace pending local-distribution evidence with verified official tarball evidence, or expressly retain pending status for a specific review use. | Toolchain Evidence | Adequacy evidence remains pending; formal architecture is unchanged. |
