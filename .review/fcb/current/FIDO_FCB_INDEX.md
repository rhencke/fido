# Fido Conformance Basis — Index

> **Derived reference, not implementation authority.** The code and its gated theorems are the sole
> implementation authority.  
> **Living document.** Its identity is its Git blob at the exact ref resolved for the task; its history is the
> commit log. No version suffixes, no checksum manifest.  
> **Accepted amendments:** `FCB-A001-INTRINSIC-STATIC-CAPABILITY-PROVENANCE`;
> `FCB-A002-GIT-CANONICAL-FCB-STORAGE`; `FCB-A003-LIVING-DOCUMENTATION`;
> `FCB-A004-GIT-RESOLVABLE-LIVING-CORPUS`; `FCB-A005-SCOPED-NAME-OWNERSHIP`.  
> **Canonical live location:** `.review/fcb/current/`, in the exact Git ref used for the task.
> **Stable bootstrap:** `.review/fcb/current/INDEX.md`.  
> Project libraries contain a bootstrap shim only. They do not contain or own this corpus.  
> C4 is not accepted and C5 is not authorized; `.review/NEXT_STEPS.md` is the live checkpoint authority.

This is the live Git-hosted FCB. The stable entry point is `.review/fcb/current/INDEX.md`. Superseded states
live in Git history, never beside the live set.

## Current project boundary

**Blocked implementation candidate:** `20c5ad5c499d5046563471624117b80c737c7157` — C4 is blocked at the final
static-capability boundary, where the published capability keeps copied projections plus an equality to
rerunning the elaborator instead of retaining the exact causal elaboration object.  
**Current C4 state:** the repair-14 authority is installed at `.review/C4_IMPLEMENTATION_REPAIR_14.md`, and
Rob **AUTHORIZED** its implementation on 2026-07-25 (begin on the current `main` head; do not reset to
`9d5246e`; preserve the recorded out-of-band changes).  
**Current blocked candidate:** `20c5ad5c499d5046563471624117b80c737c7157` — the A005 migration candidate is
BLOCKED. **Repair 15 is active** (`.review/C4_IMPLEMENTATION_REPAIR_15.md`): finish the scoped names, make
the retained core hold the whole elaboration, and make the failure retain the exact rejected core.
Governance owns `D-01` through `D-25`.  
**Next permitted sequence:** `C4 repair 14 → human C4 review → checkpoint-definition Step 0 → C5`.  
**C5 status:** forbidden until C4 is accepted. The post-C4 trim is likewise forbidden.  
**Scope stability:** no Closure row, Latitude row, Acceptance Gate, roadmap row assignment, checkpoint order,
or target/toolchain policy is changed by A002, A003, or A004.  
**Policy choice:** `LAT-X004` — option (ii), the proved rounding-invariant accepted domain.  
**External evidence:** valid but `PROVENANCE-PENDING` until the official Go distribution bytes are verified.

## Canonical storage and consultation rule

Git owns the live bytes. ChatGPT and Claude project libraries hold one bootstrap shim only. Root `CLAUDE.md`
gives Claude Code the same bootstrap.

For a serious task: resolve one exact repository ref; read `.review/fcb/current/INDEX.md`; read this Index;
confirm every file it names exists at that ref; read `.review/NEXT_STEPS.md` from the same ref; consult the map
below. Never mix files from different refs. Stop on any missing or dangling reference (D-24).

## Live file set

Every entry below exists in `.review/fcb/current/` at the ref that carries this Index.

| File | Purpose |
|---|---|
| `INDEX.md` | Stable Git bootstrap; names this Index and the live checkpoint authority. |
| `FIDO_FCB_INDEX.md` | This file: live file set, current boundary, and consultation map. |
| `FIDO_FCB_GOVERNANCE.md` | Authority rules, settled decisions D-01–D-24, amendment register, ADR register, amendment law. |
| `FIDO_FCB_ARCHITECTURE_CHARTER.md` | Permanent architecture, intrinsic static-capability provenance, proof-contract catalog SC-00–SC-22. |
| `FIDO_FCB_FIXED_POINTS.md` | The 24 parent fixed points and their protected components. |
| `FIDO_FCB_HUMAN_REVIEW_INDEX.md` | Open human decisions and the blocked C4 review state. |
| `FIDO_FCB_ROADMAP.md` | The C4 boundary and the unchanged C5–C17 foundational order. |
| `FIDO_FCB_CHECKPOINT_AUTHORING_GUIDE.md` | Checkpoint contract form, whole-result retention, Git publication duty, fixtures, gates, stop rules. |
| `FIDO_FCB_MODEL_OPERATIONS.md` | Exact-ref Git bootstrap, model delegation, amendment workflow, shim rule. |
| `FIDO_FCB_CLOSURE_LEDGER.csv` | Canonical 491-row IN/OUT spec-closure table. |
| `FIDO_FCB_CLOSURE_LEDGER.md` | Human view of the closure ledger. |
| `FIDO_FCB_LATITUDE_LEDGER.tsv` | Canonical 231-row latitude table. |
| `FIDO_FCB_LATITUDE_LEDGER.md` | Human view of the latitude ledger. |
| `FIDO_FCB_ACCEPTANCE_GATES.md` | Standing paired-fixture and diagnostic worklist. |
| `FIDO_FCB_TOOLCHAIN_EVIDENCE.md` | Pinned target, probe profile, observations, provenance boundary. |

## Consultation map

| Deciding… | Consult | Use specifically |
|---|---|---|
| What to build next | `FIDO_FCB_ROADMAP.md` | Lowest eligible checkpoint and exact row list. |
| Whether a construct is in scope | `FIDO_FCB_CLOSURE_LEDGER.csv` / `.md` | Row disposition and inclusion price. `OUT` is priced, not forgotten. |
| What behavior the model must admit | `FIDO_FCB_LATITUDE_LEDGER.tsv` / `.md` + Charter §25 | Disposition; `STEP-NONDET` expands the formal run set. |
| What Fido must reject | `FIDO_FCB_ACCEPTANCE_GATES.md` | Fixture, diagnostic, contract, and implementing checkpoint. |
| Spec versus gc conflict | `FIDO_FCB_GOVERNANCE.md` | ADR-0003 authority tiers and interpretation clause. |
| Constant-expression value | Latitude `LAT-X004` + Charter `SC-05` | Rounding-invariant accepted domain; owner never moves. |
| Can a protected thing change? | `FIDO_FCB_FIXED_POINTS.md`, then `FIDO_FCB_GOVERNANCE.md` | Rob must reopen a protected projection with new information. |
| Whether a published capability retained enough provenance | `FIDO_FCB_ARCHITECTURE_CHARTER.md` §4 + Governance D-22 + Guide | Exact retained whole-result object; no equality-to-rerun provenance. |
| Where current documentation lives | `INDEX.md` + Governance D-23/D-24 + Model Operations | One exact Git ref; every reference resolves there; shims only in project libraries. |
| What is still open for Rob? | `FIDO_FCB_HUMAN_REVIEW_INDEX.md` | Never answer from memory. |
| Toolchain/environment question | `FIDO_FCB_TOOLCHAIN_EVIDENCE.md` | One sanctioned profile and evidence status. |
| How to write the next contract | `FIDO_FCB_CHECKPOINT_AUTHORING_GUIDE.md` | Required order, frozen surfaces, whole-result retention, fixtures, gates, Git publication. |
| Which model does what? | `FIDO_FCB_MODEL_OPERATIONS.md` | Exact-ref bootstrap, delegation, amendment workflow, shim duties. |

## Update law

After Rob accepts a checkpoint or FCB amendment, regenerate every affected file, update this Index and the
stable `INDEX.md` if the file set changed, and commit the result under `.review/fcb/current/`. No version
suffixes and no checksum manifest: the blob hash is the version, the commit log is the history, and
`git rev-parse HEAD:.review/fcb/current` is the identity of the whole live set.

Git history preserves superseded states. No superseded file remains beside the live set. Project-library shims
change only if the repository identity or the stable bootstrap path changes.
