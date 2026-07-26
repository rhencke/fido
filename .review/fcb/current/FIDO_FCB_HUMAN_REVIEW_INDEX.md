# Fido FCB Human Review Index

> **Derived reference, not implementation authority.** The code and its gated theorems are the sole implementation authority.  
> **Living document.** Its identity is its Git blob at the exact ref resolved for the task; its
> history is the commit log. No version suffixes, no checksum manifest.  
> **Accepted amendments:** `FCB-A001-INTRINSIC-STATIC-CAPABILITY-PROVENANCE`; `FCB-A002-GIT-CANONICAL-FCB-STORAGE`; `FCB-A003-LIVING-DOCUMENTATION`;
> `FCB-A004-GIT-RESOLVABLE-LIVING-CORPUS`; `FCB-A005-SCOPED-NAME-OWNERSHIP`.  
> **Canonical live location:** `.review/fcb/current/` in the exact Git ref used for the task.  
> **Stable bootstrap:** `.review/fcb/current/INDEX.md`  
> Project libraries contain only a bootstrap shim. They do not contain or own the FCB corpus.  
> Regenerate, verify, and commit affected FCB files in Git after each accepted checkpoint or amendment.  
> This corpus does not accept C4 and does not authorize C5; `.review/NEXT_STEPS.md` remains the live checkpoint authority.


This index lists current human acts.

> ⚠ **Temporarily hand-maintained, pending the `D-07` generator.** `D-07` requires open human acts to be
> DISCOVERED from canonical rows and statuses, never hand-copied, and that remains the binding end state. The
> current file does not satisfy it: the surviving generator is a historical terminal-bundle stub whose schema is
> provenance, not the living-FCB schema, so the rows below were maintained by hand. **Do not read this file as
> generated output.** Implementing the living-FCB generator is a recorded process task, due before the next
> accepted checkpoint; when it lands and regenerates this file, this disclaimer is removed. `D-07` is not
> weakened or redefined by this note — softening it would require a named amendment.

| ID | Status | Required human act | Source / owner | Effect |
|---|---|---|---|---|
| `C4-REVIEW` | **PENDING — repair-15 candidate ready for human review** | Repair 15 is IMPLEMENTED and COMPLETE at candidate `deda8bd91dbfebf75895c8786732a4ed9d7952f2`; it subsumes repair 14. Its three blocking classes are closed: the A005 scoped names are finished and gated in both working-tree and staged-snapshot mode, `Compilable.Core` retains the whole elaboration, and the public failure retains the exact rejected core; the capability, failure and facts constructors are sealed behind the one production mint. The previous candidate `20c5ad5c499d5046563471624117b80c737c7157` remains BLOCKED and is the sixteenth to block. C4 is NOT accepted — only Rob accepts it, by a new human C4 Implementation Review against the candidate above. | `.review/C4_IMPLEMENTATION_REPAIR_15.md`, A001, A005, and the main review thread | C5 and post-C4 feature work remain forbidden. |
| `ADR-0002` | **OPEN / DEFERRED** | Choose the Float.Decimal domain after differential and proof-cost evidence. | Governance ADR register | Before C7 broadens floating constant coverage. |
| `ADR-0004` | **DEFERRED** | Choose the multi-platform 64-bit target set. | Governance ADR register | C16. |
| `TOOLCHAIN-PROVENANCE` | **PENDING** | Replace pending local-distribution evidence with verified official tarball evidence, or expressly retain pending status for a specific review use. | Toolchain Evidence | Adequacy evidence remains pending; formal architecture is unchanged. |
| `FIXED-POINT-EXTERNAL-EVIDENCE` | **OPEN** | Decide whether the twelve external R1-bundle components (pinned spec and memory-model HTML, extractor script, latitude manifest, freeze records, pinned toolchain evidence, F-dispositions, audit JSON, heading and grammar manifests) should be committed into a Git evidence subtree, or expressly retained as external `PROVENANCE-PENDING` references. | Fixed Points registry; D-24 | Their bytes are not in Git, so their protected projections cannot currently be recomputed from the repository. |
| `FCB-SHOWROOM` | **OPEN** | Have Claude perform one adversarial showroom pass over the live Git-hosted FCB; disposition findings. | FCB transformation completion rule | Required before calling the document split final. |

## Closed

- `ADR-0001` / `SR-001`: **ACCEPTED FOR CURRENT BASIS** by Rob on `2026-07-25` — Go 1.23 on `linux/amd64` with `GOAMD64=v1`; `int`/`uint` 64-bit and distinct from fixed-width types. Reopen at C16 or any earlier explicit request for another target or `uintptr`. Does not authorize `uintptr`, another target, C5, or the post-C4 trim.
- `FCB-A004`: **ACCEPTED AS IMPLEMENTED** by Rob on `2026-07-25`. Every live documentation reference resolves at one Git ref, or is explicitly typed as an external evidence reference; `D-24` installed as a settled decision.

- `FCB-A002`: accepted on `2026-07-25`. Git is the sole canonical FCB store; project libraries contain bootstrap shims only; root `CLAUDE.md` uses the same bootstrap; D-23 added.
- `FCB-A001`: accepted on `2026-07-25`. The static capability and failure result must retain the exact whole elaboration by construction; `ARCH-03` reopened and strengthened; D-22 added.
- `LAT-X004`: option (ii), proved rounding-invariant accepted domain, owner fixed at `SPEC-096` / `Compilable.ExpressionFact` / `SC-05`.
- `ADR-0001`: adopted for the current single linux/amd64 target; reopens at C16 or an earlier target/`uintptr` request.
- `ADR-0003`: adopted.
- Terminal open candidate: Rob’s 2026-07-24 instruction authorized FCB generation from it while preserving pending provenance as pending.

Old F/R/T countersign tables remain in the frozen terminal bundle as provenance. Superseded FCB sets remain in Git history; their settled contents are absorbed into Governance and Fixed Points, and their unresolved substantive acts appear above.
