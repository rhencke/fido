# Fido FCB Human Review Index

<!-- GENERATED FILE — do not edit by hand.
     Data authority: .review/fcb/current/FIDO_FCB_HUMAN_ACTS.tsv
     Generator:      tools/human-review-index.py  (make human-acts-write; verified by make human-acts)
     Governance D-07: open human acts are generated from canonical rows, never hand-copied. -->

> **Derived reference, not implementation authority.** The code and its gated theorems are the sole implementation authority.  
> **Living document.** Its identity is its Git blob at the exact ref resolved for the task; its
> history is the commit log. No version suffixes, no checksum manifest.  
> **Accepted amendments:** `FCB-A001-INTRINSIC-STATIC-CAPABILITY-PROVENANCE`; `FCB-A002-GIT-CANONICAL-FCB-STORAGE`; `FCB-A003-LIVING-DOCUMENTATION`;
> `FCB-A004-GIT-RESOLVABLE-LIVING-CORPUS`; `FCB-A005-SCOPED-NAME-OWNERSHIP`;
> `FCB-A006-INTRINSIC-EMIT-IMAGE-MINT`.  
> **Canonical live location:** `.review/fcb/current/` in the exact Git ref used for the task.  
> **Stable bootstrap:** `.review/fcb/current/INDEX.md`  
> This corpus does not accept C4 and does not authorize C5; `.review/NEXT_STEPS.md` remains the live checkpoint authority.

This index is the generated view of the current open human acts. Each row is owned by one source file
carrying exactly one `FIDO-HUMAN-ACT` anchor, which the generator validates. A closed act is removed from the
data authority; Git history and the owning ADR, governance row, fixed-point record or accepted review commit
preserve its disposition.

| ID | Status | Required human act | Source / owner | Effect |
|---|---|---|---|---|
| `ADR-0002` | **DEFERRED** | Choose the Float.Decimal domain after differential and proof-cost evidence. | Governance ADR register | Before C7 broadens floating constant coverage. |
| `ADR-0004` | **DEFERRED** | Choose the multi-platform 64-bit target set. | Governance ADR register | C16. |
| `C4-REVIEW` | **BLOCKED** | Review the next C4 implementation candidate. The nineteenth candidate is BLOCKING and repair 18 is the sole active C4 work; no review is requested until it is frozen. Only Rob accepts C4. | .review/NEXT_STEPS.md, the repair-18 directive, and the main review thread | C5, checkpoint-definition Step 0, post-C4 features, the broad source cleanup and proof-module partitioning remain forbidden. |
| `FCB-SHOWROOM` | **OPEN** | Have Claude perform one adversarial showroom pass over the live Git-hosted FCB; disposition findings. | FCB transformation completion rule | Required before calling the document split final. |
| `FIXED-POINT-EXTERNAL-EVIDENCE` | **OPEN** | Decide whether the twelve external R1-bundle components should be committed into a Git evidence subtree, or expressly retained as external PROVENANCE-PENDING references. | Fixed Points registry; D-24 | Their bytes are not in Git, so their protected projections cannot currently be recomputed from the repository. |
| `TOOLCHAIN-PROVENANCE` | **PENDING** | Replace pending local-distribution evidence with verified official tarball evidence, or expressly retain pending status for a specific review use. | Toolchain Evidence | Adequacy evidence remains pending; formal architecture is unchanged. |
