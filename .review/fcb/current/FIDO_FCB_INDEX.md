# Fido Conformance Basis — Index

> **Derived reference, not authority.** The code and its gated theorems are the sole implementation authority.  
> **Living document** — its version is the Git blob; its history is the commit log. · **Last updated:** `2026-07-25`  
> **Source repository basis:** `rhencke/fido@ece4c1dd0797eff6e9ebdd5d77a0e59f1c9e76e0`  
> **Amendments:** `FCB-A001-INTRINSIC-STATIC-CAPABILITY-PROVENANCE`; `FCB-A002-GIT-CANONICAL-FCB-STORAGE`  
> **Canonical live location:** `.review/fcb/current/` in the exact Git ref used for the task.  
> **Stable bootstrap:** `.review/fcb/current/INDEX.md`  
> Project libraries contain only a bootstrap shim. They do not contain or own the FCB corpus.  
> Regenerate, verify, and commit affected FCB files in Git after each accepted checkpoint or amendment.  
> This corpus does not accept C4 and does not authorize C5; `.review/NEXT_STEPS.md` remains the live checkpoint authority.


This is the live Git-hosted FCB set. The stable entry point is `.review/fcb/current/INDEX.md`. The archive and old review documents remain provenance only.

## Current project boundary

**Source repository basis:** `ece4c1dd0797eff6e9ebdd5d77a0e59f1c9e76e0` — documentation/campaign basis, not a new implementation candidate.  
**Blocked implementation candidate:** `9d5246eedf9e9a3c019b85e9dc65ce9e6f867179` — C4 is blocked at the final static-capability boundary.  
**Accepted amendments:** `FCB-A001-INTRINSIC-STATIC-CAPABILITY-PROVENANCE`; `FCB-A002-GIT-CANONICAL-FCB-STORAGE`.  
**Next authorized C4 work:** install the repair-14 repository authority, then implement and freeze intrinsic retained elaboration.  
**Next permitted sequence:** `Git-canonical FCB installed → C4 repair 14 → human C4 review → checkpoint-definition Step 0 → C5`.  
**C5 status:** forbidden until C4 is accepted.  
**Scope stability:** no Closure row, Latitude row, Acceptance Gate, roadmap row assignment, checkpoint order, or target/toolchain policy changed by A002.  
**FCB policy choice:** LAT-X004 option (ii), proved rounding-invariant accepted domain.  
**External evidence:** valid but `PROVENANCE-PENDING` until the official Go distribution bytes are verified.

## Canonical storage and consultation rule

Git owns the live bytes. ChatGPT and Claude project libraries contain one bootstrap shim only. Root `CLAUDE.md` gives Claude Code the same bootstrap.

For a serious task, resolve one exact repository ref, read `.review/fcb/current/INDEX.md`, read `.review/NEXT_STEPS.md` from the same ref, and consult this Index's map. If access or verification fails, stop. Never answer from stale FCB copies or mix files from different refs.

## File manifest

| File | Version | Purpose |
|---|---:|---|
| `INDEX.md` | stable | Stable Git bootstrap pointing to this versioned Index and manifest. |
| `FIDO_FCB_INDEX.md` | v3 | Master file set, current boundary, and consultation map. |
| `FIDO_FCB_GOVERNANCE.md` | v3 | Authority rules, settled decisions D-01–D-23, amendment register, ADR register, and amendment law. |
| `FIDO_FCB_ARCHITECTURE_CHARTER.md` | v3 | Permanent architecture, intrinsic static-capability provenance, and proof-contract catalog SC-00–SC-22. |
| `FIDO_FCB_FIXED_POINTS.md` | v3 | The 24 parent fixed points and 42 protected components. |
| `FIDO_FCB_HUMAN_REVIEW_INDEX.md` | v3 | Current human decisions and blocked C4 review state. |
| `FIDO_FCB_ROADMAP.md` | v3 | C4/A001/A002 boundary and unchanged C5–C17 foundational order. |
| `FIDO_FCB_CHECKPOINT_AUTHORING_GUIDE.md` | v3 | Checkpoint contract form, whole-result retention, Git publication duty, fixtures, gates, and stop rules. |
| `FIDO_FCB_MODEL_OPERATIONS.md` | v3 | Exact-ref Git bootstrap, model delegation, amendment workflow, and shim rule. |
| `FIDO_FCB_CLOSURE_LEDGER.csv` | v2 | Canonical 491-row IN/OUT spec-closure table; semantic rows unchanged from v1. |
| `FIDO_FCB_CLOSURE_LEDGER.md` | v2 | Human view of the closure ledger; semantic rows unchanged from v1. |
| `FIDO_FCB_LATITUDE_LEDGER.tsv` | v2 | Canonical 231-row latitude table; semantic rows unchanged from v1. |
| `FIDO_FCB_LATITUDE_LEDGER.md` | v2 | Human view of the latitude ledger; semantic rows unchanged from v1. |
| `FIDO_FCB_ACCEPTANCE_GATES.md` | v2 | Standing paired-fixture and diagnostic worklist; gates unchanged from v1. |
| `FIDO_FCB_TOOLCHAIN_EVIDENCE.md` | v2 | Pinned target, probe profile, observations, and provenance boundary; evidence content unchanged from v1. |

## Consultation map

| Deciding… | Consult | Use specifically |
|---|---|---|
| What to build next | `FIDO_FCB_ROADMAP.md` | Lowest eligible checkpoint and exact row list. |
| Whether a construct is in scope | `FIDO_FCB_CLOSURE_LEDGER_v2.*` | Row disposition and inclusion price. `OUT` is priced, not forgotten. |
| What behavior the model must admit | `FIDO_FCB_LATITUDE_LEDGER_v2.*` + Charter §25 | Disposition; `STEP-NONDET` expands the formal run set. |
| What Fido must reject | `FIDO_FCB_ACCEPTANCE_GATES.md` | Fixture, diagnostic, contract, and implementing checkpoint. |
| Spec versus gc conflict | `FIDO_FCB_GOVERNANCE.md` | ADR-0003 authority tiers and interpretation clause. |
| Constant-expression value | Latitude `LAT-X004` + Charter `SC-05` | Rounding-invariant accepted domain; owner never moves. |
| Can a protected thing change? | `FIDO_FCB_FIXED_POINTS.md`, then `FIDO_FCB_GOVERNANCE.md` | Rob must reopen a protected projection with new information. |
| Whether a published capability retained enough provenance | `FIDO_FCB_ARCHITECTURE_CHARTER.md` §4 + Governance D-22 + Guide | Exact retained whole-result object and no equality-to-rerun provenance. |
| Where current documentation lives | `INDEX.md` + Governance D-23 + Model Operations | One exact Git ref; Git content addressing; shims only in project libraries. |
| What is still open for Rob? | `FIDO_FCB_HUMAN_REVIEW_INDEX.md` | Never answer from memory. |
| Toolchain/environment question | `FIDO_FCB_TOOLCHAIN_EVIDENCE.md` | One sanctioned profile and evidence status. |
| How to write the next contract | `FIDO_FCB_CHECKPOINT_AUTHORING_GUIDE.md` | Required order, frozen surfaces, whole-result retention, fixtures, gates, and Git publication. |
| Which model does what? | `FIDO_FCB_MODEL_OPERATIONS.md` | Exact-ref bootstrap, delegation, amendment workflow, and shim duties. |

## Update law

After Rob accepts a checkpoint or FCB amendment, regenerate every affected FCB file, update this Index and stable `INDEX.md` if the file set changed, and commit the result under `.review/fcb/current/`. These are living documents: no version suffixes, no checksum manifest. The blob hash is the version, the commit log is the history, and `git rev-parse HEAD:.review/fcb/current` is the identity of the whole live set.

Git history or an explicit archive preserves superseded sets. No superseded version remains in `.review/fcb/current/`. Project-library shims change only if the repository identity or stable bootstrap path changes.
