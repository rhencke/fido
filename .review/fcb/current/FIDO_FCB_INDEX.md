# Fido Conformance Basis — Index

> **Derived reference, not implementation authority.** The code and its gated theorems are the sole
> implementation authority.  
> **Living document.** Its identity is its Git blob at the exact ref resolved for the task; its history is the
> commit log. No version suffixes, no checksum manifest.  
> **Accepted amendments:** `FCB-A001-INTRINSIC-STATIC-CAPABILITY-PROVENANCE`;
> `FCB-A002-GIT-CANONICAL-FCB-STORAGE`; `FCB-A003-LIVING-DOCUMENTATION`;
> `FCB-A004-GIT-RESOLVABLE-LIVING-CORPUS`; `FCB-A005-SCOPED-NAME-OWNERSHIP`;
> `FCB-A006-INTRINSIC-EMIT-IMAGE-MINT`; `FCB-A007-POST-C4-MECHANICAL-SERIES`;
> `FCB-A008-STRICT-CHECKPOINT-SCOPE-AND-M0-CLOSEOUT`.  
> **Canonical live location:** `.review/fcb/current`, in the exact Git ref used for the task. <!-- FIDO-FCB-REF:REVIEW-FCB-CURRENT -->
> **Stable bootstrap:** the `INDEX.md` beside this file, listed with its role in the live file set below.  
> Project libraries contain a bootstrap shim only. They do not contain or own this corpus.  
> C4, M0 and M1 are ACCEPTED; M2 Performance Snapshot is the sole active work and C5 is not authorized; `.review/NEXT_STEPS.md` remains the live checkpoint authority.

This is the live Git-hosted FCB. The stable entry point is `.review/fcb/current/INDEX.md`. Superseded states
live in Git history, never beside the live set.

## Current project boundary

**C4 acceptance:** C4 is **ACCEPTED**, under Rob's disposition `C4-ACCEPT-39ea7e3`. The exact accepted ref is
recorded once, in the A008 amendment register row; it is history, not current work. The blocked candidates and
their repair narratives live in Git history.  
**M0 acceptance:** M0 is **ACCEPTED**, under Rob's disposition `M0-ACCEPT-86a63db`. Git history owns its
contract, its obligation matrix and its evidence.  
**M1 acceptance:** M1 is **ACCEPTED** at `6524b437bd7a7d6b2616563b8789e28a00c7af13`, under Rob's
disposition `M1-ACCEPT-6524b43`. Git history owns its contract, its obligation matrix and its evidence; its
permanent source-comment law is rehomed to `.review/M_SERIES_PLAN.md` and `tools/source-diet.py`.  
**Active work:** M2 Performance Snapshot, in `.review/M2_PERFORMANCE_SNAPSHOT.md`, which
`.review/NEXT_STEPS.md` names as its authority. `NEXT_STEPS` owns candidate state; this Index names the
boundary, not the candidate.  
Governance owns `D-01` through `D-29`; amendments `A001` through `A008` are accepted.  
**Next permitted sequence:** `M2 → M3 → Rob approves the exact M4 plan → M4 →
checkpoint-definition Step 0 → C5`.  
**M3, M4 and C5 status:** forbidden until Rob accepts M2.  
**M-series authority:** `.review/M_SERIES_PLAN.md` <!-- FIDO-FCB-REF:REVIEW-M-SERIES-PLAN-MD -->  
**Scope rule (D-28):** review the whole system; block the active checkpoint only for a defect in its accepted
contract or an explicit acceptance dependency. Every other finding is assigned to the earliest mandatory
follow-up and stays visible in Git. Discovery does not determine scope.  
**Scope stability:** no Closure row, Latitude row, Acceptance Gate, roadmap row assignment, checkpoint order,
or target/toolchain policy is changed by A002, A003, A004, A007 or A008.  
**Policy choice:** `LAT-X004` — option (ii), the proved rounding-invariant accepted domain.  
**External evidence:** valid but `PROVENANCE-PENDING` until the official Go distribution bytes are verified.

## Canonical storage and consultation rule

Git owns the live bytes. ChatGPT and Claude project libraries hold one bootstrap shim only. Root `CLAUDE.md` <!-- FIDO-FCB-REF:CLAUDE-MD -->
gives Claude Code the same bootstrap.

For a serious task: resolve one exact repository ref; read `.review/fcb/current/INDEX.md`; read this Index;
confirm every file it names exists at that ref; read `.review/NEXT_STEPS.md` from the same ref; consult the map
below. Never mix files from different refs. Stop on any missing or dangling reference (D-24).

The D-24 relation is checked rather than trusted: `tools/fcb-reference-gate.py` verifies it in both <!-- FIDO-FCB-REF:TOOLS-FCB-REFERENCE-GATE-PY -->
directions, so a current authority cannot name a repository path with no typed row, and no row can point at a
path that is not there.

## Live file set

Every entry below exists at the ref that carries this Index, and each states its **corpus role** (D-24). An
`authority` is a current normative source: its own operational references are scanned and must each be typed.
A `reference` resolves and is owned, but naming it does not make it a current authority — a generated view is
a `reference` because its canonical data source carries the authority.

This table is the declaration; `FIDO_FCB_REFERENCES.tsv` is the manifest that must agree with it, and the
D-24 gate checks that agreement rather than trusting either side alone.

| Path | Role | Purpose |
|---|---|---|
| `.review/fcb/current/INDEX.md` | authority | Stable Git bootstrap; names this Index and the live checkpoint authority. <!-- FIDO-FCB-REF:REVIEW-FCB-CURRENT-INDEX-MD --> |
| `.review/fcb/current/FIDO_FCB_INDEX.md` | authority | This file: live file set with roles, current boundary, and consultation map. <!-- FIDO-FCB-REF:REVIEW-FCB-CURRENT-FIDO-FCB-INDEX-MD --> |
| `.review/fcb/current/FIDO_FCB_GOVERNANCE.md` | authority | Authority rules, settled decisions D-01–D-29, amendment register, ADR register, amendment law. <!-- FIDO-FCB-REF:REVIEW-FCB-CURRENT-FIDO-FCB-GOVERNANCE-MD --> |
| `.review/fcb/current/FIDO_FCB_ARCHITECTURE_CHARTER.md` | authority | Permanent architecture, intrinsic static-capability provenance, proof-contract catalog SC-00–SC-22. <!-- FIDO-FCB-REF:REVIEW-FCB-CURRENT-FIDO-FCB-ARCHITECTURE-CHARTER-MD --> |
| `.review/fcb/current/FIDO_FCB_FIXED_POINTS.md` | authority | The 24 parent fixed points and their protected components. <!-- FIDO-FCB-REF:REVIEW-FCB-CURRENT-FIDO-FCB-FIXED-POINTS-MD --> |
| `.review/fcb/current/FIDO_FCB_HUMAN_ACTS.tsv` | authority | Canonical rows for the open human acts; the sole authority for that set (D-07). <!-- FIDO-FCB-REF:REVIEW-FCB-CURRENT-FIDO-FCB-HUMAN-ACTS-TSV --> |
| `.review/fcb/current/FIDO_FCB_REFERENCES.tsv` | authority | Typed operational references and their corpus roles, complete in both directions: every repository path a current authority directs work to has one row and one bound owner marker, and every row resolves here or is explicitly typed off-tree with an availability (D-24). <!-- FIDO-FCB-REF:REVIEW-FCB-CURRENT-FIDO-FCB-REFERENCES-TSV --> |
| `.review/fcb/current/FIDO_FCB_HUMAN_REVIEW_INDEX.md` | reference | Generated view of the open human acts. Never edited by hand. <!-- FIDO-FCB-REF:REVIEW-FCB-CURRENT-FIDO-FCB-HUMAN-REVIEW-INDEX-MD --> |
| `.review/fcb/current/FIDO_FCB_ROADMAP.md` | authority | The C4 boundary, the A007 mechanical series, and the unchanged C5–C17 foundational order. <!-- FIDO-FCB-REF:REVIEW-FCB-CURRENT-FIDO-FCB-ROADMAP-MD --> |
| `.review/fcb/current/FIDO_FCB_CHECKPOINT_AUTHORING_GUIDE.md` | authority | Checkpoint contract form, whole-result retention, mechanical-change duty, Git publication duty, fixtures, gates, stop rules. <!-- FIDO-FCB-REF:REVIEW-FCB-CURRENT-FIDO-FCB-CHECKPOINT-AUTHORING-GUIDE-MD --> |
| `.review/fcb/current/FIDO_FCB_MODEL_OPERATIONS.md` | authority | Exact-ref Git bootstrap, model delegation, post-C4 sequencing, amendment workflow, shim rule. <!-- FIDO-FCB-REF:REVIEW-FCB-CURRENT-FIDO-FCB-MODEL-OPERATIONS-MD --> |
| `.review/fcb/current/FIDO_FCB_CLOSURE_LEDGER.csv` | authority | Canonical 491-row IN/OUT spec-closure table. <!-- FIDO-FCB-REF:REVIEW-FCB-CURRENT-FIDO-FCB-CLOSURE-LEDGER-CSV --> |
| `.review/fcb/current/FIDO_FCB_CLOSURE_LEDGER.md` | reference | Generated human view of the closure ledger. <!-- FIDO-FCB-REF:REVIEW-FCB-CURRENT-FIDO-FCB-CLOSURE-LEDGER-MD --> |
| `.review/fcb/current/FIDO_FCB_LATITUDE_LEDGER.tsv` | authority | Canonical 231-row latitude table. <!-- FIDO-FCB-REF:REVIEW-FCB-CURRENT-FIDO-FCB-LATITUDE-LEDGER-TSV --> |
| `.review/fcb/current/FIDO_FCB_LATITUDE_LEDGER.md` | reference | Human view of the latitude ledger. <!-- FIDO-FCB-REF:REVIEW-FCB-CURRENT-FIDO-FCB-LATITUDE-LEDGER-MD --> |
| `.review/fcb/current/FIDO_FCB_ACCEPTANCE_GATES.md` | authority | Standing paired-fixture and diagnostic worklist. <!-- FIDO-FCB-REF:REVIEW-FCB-CURRENT-FIDO-FCB-ACCEPTANCE-GATES-MD --> |
| `.review/fcb/current/FIDO_FCB_TOOLCHAIN_EVIDENCE.md` | authority | Pinned target, probe profile, observations, provenance boundary. <!-- FIDO-FCB-REF:REVIEW-FCB-CURRENT-FIDO-FCB-TOOLCHAIN-EVIDENCE-MD --> |

## Consultation map

| Deciding… | Consult | Use specifically |
|---|---|---|
| What to build next | `FIDO_FCB_ROADMAP.md` | Lowest eligible checkpoint and exact row list. |
| What is being worked on right now | `.review/M2_PERFORMANCE_SNAPSHOT.md` + Governance D-27 | The M2 contract, obligations `M2-01` through `M2-09`, and what M2 may not touch. |
| What runs between M2 and C5 | `.review/M_SERIES_PLAN.md` + Governance D-27 + Roadmap | The M2–M4 sequence and each candidate's mechanical contract. M3 and M4 forbidden until M2 is accepted. |
| Whether a finding blocks the active checkpoint | Governance D-28 | Only a defect in the accepted contract or an explicit acceptance dependency blocks. Everything else gets a mandatory follow-up owner. |
| Whether a construct is in scope | `FIDO_FCB_CLOSURE_LEDGER.csv` / `.md` | Row disposition and inclusion price. `OUT` is priced, not forgotten. |
| What behavior the model must admit | `FIDO_FCB_LATITUDE_LEDGER.tsv` / `.md` + Charter §25 | Disposition; `STEP-NONDET` expands the formal run set. |
| What Fido must reject | `FIDO_FCB_ACCEPTANCE_GATES.md` | Fixture, diagnostic, contract, and implementing checkpoint. |
| Spec versus gc conflict | `FIDO_FCB_GOVERNANCE.md` | ADR-0003 authority tiers and interpretation clause. |
| Constant-expression value | Latitude `LAT-X004` + Charter `SC-05` | Rounding-invariant accepted domain; owner never moves. |
| Can a protected thing change? | `FIDO_FCB_FIXED_POINTS.md`, then `FIDO_FCB_GOVERNANCE.md` | Rob must reopen a protected projection with new information. |
| Whether a published capability retained enough provenance | `FIDO_FCB_ARCHITECTURE_CHARTER.md` §4 + Governance D-22 + Guide | Exact retained whole-result object; no equality-to-rerun provenance. |
| Where current documentation lives | `INDEX.md` + Governance D-23/D-24 + Model Operations | One exact Git ref; every reference resolves there; shims only in project libraries. |
| What is still open for Rob? | `FIDO_FCB_HUMAN_ACTS.tsv`, or its generated view | Never answer from memory. <!-- FIDO-HUMAN-ACT:FCB-SHOWROOM --> |
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
