# Fido Conformance Basis — Index v2

> **Derived reference, not authority.** The code and its gated theorems are the sole authority.  
> **FCB version:** `v2` · **Generated:** `2026-07-25`  
> **Supersedes:** `FIDO_FCB_INDEX_v1.md`  
> **Repository basis:** `rhencke/fido@ece4c1dd0797eff6e9ebdd5d77a0e59f1c9e76e0` · source snapshot SHA-256 `6e25e8be64a77b7d98609c607d48b1d6917b2bf0480d10fa4a92f1a6bb170eff`  
> **Terminal-bundle basis:** SHA-256 `58abd876a0962bde42e5c9fc0365a8431b88b13beb790440e4b52031c7f8aad0` · handoff SHA-256 `fdfc2c235707aeeef58c566f5fd145850ca606df8d693f5cc6bc81f2112eb143`  
> **Amendment basis:** `FCB-A001-INTRINSIC-STATIC-CAPABILITY-PROVENANCE` · accepted `2026-07-25` · directive SHA-256 `79a8fa3f6d5a861b82259a578eef6123369dbc9567fbd63288b93c1ce1037b8c`  
> Regenerate this document at each checkpoint acceptance. Delete every stale copy from every model library.  
> This library does not accept C4 and does not authorize C5; `.review/NEXT_STEPS.md` remains the live checkpoint authority.

This is the live project-library set. Upload the whole set together. Do not mix files from another Index or manifest identity. The archive and old review documents remain provenance only.

## Current project boundary

**Repository basis:** `ece4c1dd0797eff6e9ebdd5d77a0e59f1c9e76e0` — a documentation/campaign commit that contains the current campaign record; it is not a new implementation candidate.  
**Blocked implementation candidate:** `9d5246eedf9e9a3c019b85e9dc65ce9e6f867179` — C4 repair-13 is blocked at the final static-capability boundary.  
**Accepted documentation amendment:** `FCB-A001-INTRINSIC-STATIC-CAPABILITY-PROVENANCE` is incorporated in this set.  
**Next authorized C4 work:** install repository authority for A001, then implement and freeze repair 14 under `C4_REVIEW_BLOCKING_FCB_A001_REPAIR_14.txt`.  
**Next permitted sequence:** `FCB A001 installed → C4 repair 14 → human C4 review → checkpoint-definition Step 0 → C5`.  
**C5 status:** forbidden until C4 is accepted.  
**Scope stability:** no Closure Ledger row, Latitude Ledger row, Acceptance Gate, roadmap row assignment, checkpoint order, or target/toolchain policy changed.  
**FCB policy choice:** LAT-X004 option (ii), proved rounding-invariant accepted domain.  
**External evidence:** valid but `PROVENANCE-PENDING` until the official Go distribution bytes are verified.

## File manifest

| File | Version | Purpose |
|---|---:|---|
| `FIDO_FCB_INDEX_v2.md` | v2 | Master manifest, current boundary, and consultation map. |
| `FIDO_FCB_GOVERNANCE_v2.md` | v2 | Authority rules, settled decisions D-01–D-22, A001 register, ADR register, and amendment law. |
| `FIDO_FCB_ARCHITECTURE_CHARTER_v2.md` | v2 | Permanent architecture, intrinsic static-capability provenance, and proof-contract catalog SC-00–SC-22. |
| `FIDO_FCB_FIXED_POINTS_v2.md` | v2 | The 24 parent fixed points and 42 protected components. |
| `FIDO_FCB_HUMAN_REVIEW_INDEX_v2.md` | v2 | Current human decisions, A001 closure, and blocked C4 review state. |
| `FIDO_FCB_ROADMAP_v2.md` | v2 | C4/A001 boundary and unchanged C5–C17 foundational order with exact row assignments. |
| `FIDO_FCB_CHECKPOINT_AUTHORING_GUIDE_v2.md` | v2 | Checkpoint contract form, whole-result retention duty, fixtures, gates, and stop rules. |
| `FIDO_FCB_MODEL_OPERATIONS_v2.md` | v2 | Model delegation, amendment workflow, library duty, and retirement register. |
| `FIDO_FCB_CLOSURE_LEDGER_v1.csv` | v1 | Unchanged canonical 491-row IN/OUT spec-closure table. |
| `FIDO_FCB_CLOSURE_LEDGER_v1.md` | v1 | Unchanged generated human view of the closure ledger. |
| `FIDO_FCB_LATITUDE_LEDGER_v1.tsv` | v1 | Unchanged canonical 231-row latitude disposition table, including closed LAT-X004. |
| `FIDO_FCB_LATITUDE_LEDGER_v1.md` | v1 | Unchanged generated human view of the latitude ledger. |
| `FIDO_FCB_ACCEPTANCE_GATES_v1.md` | v1 | Unchanged standing paired-fixture and diagnostic worklist. |
| `FIDO_FCB_TOOLCHAIN_EVIDENCE_v1.md` | v1 | Unchanged pinned target, probe profile, observations, and provenance boundary. |
| `FIDO_FCB_MANIFEST.sha256` | current | SHA-256 of every other live FCB file in this exact set. |

## Consultation map

| Deciding… | Consult | Use specifically |
|---|---|---|
| What to build next | `FIDO_FCB_ROADMAP_v2.md` | Lowest eligible checkpoint and its exact row list. |
| Whether a construct is in scope | `FIDO_FCB_CLOSURE_LEDGER_v1.*` | The row disposition and inclusion price. `OUT` is priced, not forgotten. |
| What behavior the model must admit | `FIDO_FCB_LATITUDE_LEDGER_v1.*` + Charter §25 | The disposition; `STEP-NONDET` expands the formal run set. |
| What Fido must reject | `FIDO_FCB_ACCEPTANCE_GATES_v1.md` | Fixture, diagnostic, contract, and implementing checkpoint. |
| Spec versus gc conflict | `FIDO_FCB_GOVERNANCE_v2.md` | ADR-0003 authority tiers and interpretation clause. |
| Constant-expression value | Latitude `LAT-X004` + Charter `SC-05` | Rounding-invariant accepted domain; owner never moves. |
| Can a protected thing change? | `FIDO_FCB_FIXED_POINTS_v2.md`, then `FIDO_FCB_GOVERNANCE_v2.md` | If protected, Rob must reopen it with new information. |
| Whether a published capability retained enough provenance | `FIDO_FCB_ARCHITECTURE_CHARTER_v2.md` §4 + `FIDO_FCB_GOVERNANCE_v2.md` D-22 + `FIDO_FCB_CHECKPOINT_AUTHORING_GUIDE_v2.md` | Exact retained whole-result object, total projections, and prohibition on equality-to-rerun provenance. |
| What is still open for Rob? | `FIDO_FCB_HUMAN_REVIEW_INDEX_v2.md` | Never answer from memory. |
| Toolchain/environment question | `FIDO_FCB_TOOLCHAIN_EVIDENCE_v1.md` | The one sanctioned profile and evidence status. |
| How to write the next contract | `FIDO_FCB_CHECKPOINT_AUTHORING_GUIDE_v2.md` | Required order, frozen surfaces, whole-result retention, fixtures, and gates. |
| Which model does what? | `FIDO_FCB_MODEL_OPERATIONS_v2.md` | Delegation, amendment workflow, and library update duties. |

## Update law

After Rob accepts a checkpoint or FCB amendment, regenerate every affected FCB file, bump each changed file's version, update this Index and the SHA manifest, replace the coherent set in both model libraries, and delete all stale copies.

A coherent set may contain unchanged earlier-version files only when the current Index and manifest name those exact files and hashes. No superseded version of a changed file remains in either live library. A file from another Index or manifest identity is not part of this set even when its filename or version looks compatible.
