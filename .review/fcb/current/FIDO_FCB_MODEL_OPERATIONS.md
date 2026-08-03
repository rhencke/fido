# Fido FCB Model Operations

> **Derived reference, not implementation authority.** The code and its gated theorems are the sole implementation authority.  
> **Living document.** Its identity is its Git blob at the exact ref resolved for the task; its
> history is the commit log. No version suffixes, no checksum manifest.  
> **Current state lives with its owner.** `.review/fcb/current/FIDO_FCB_GOVERNANCE.md` owns the
> accepted amendments and governance decisions; `.review/NEXT_STEPS.md` owns the active checkpoint and
> candidate. This document copies neither.  
> **Canonical live location:** `.review/fcb/current/` in the exact Git ref used for the task.  
> **Stable bootstrap:** `.review/fcb/current/INDEX.md`  
> Project libraries contain only a bootstrap shim. They do not contain or own the FCB corpus.  
> Regenerate, verify, and commit affected FCB files in Git after each accepted checkpoint or amendment.  


## 1. Delegation table

| Actor | Role | May do | May not do |
|---|---|---|---|
| Rob | Human authority | Choose scope, disposition ADRs, authorize repairs, accept checkpoints, reopen fixed points | Delegate final acceptance by silence |
| ChatGPT primary project thread | Checkpoint author and FCB maintainer | Load the current Git FCB, author frozen checkpoint contracts and named amendments, reconcile source and documents | Accept its own design or implementation; edit a project-library copy as authority |
| Disposable research chats | Exploration | Attack one question, compare alternatives, produce evidence for the primary thread | Become a source of truth; carry hidden decisions forward |
| Claude Code | Implementer | Load the current Git FCB through `CLAUDE.md`, implement only the frozen checkpoint, run gates, delete replaced paths, report conflicts | Change architecture, scope, guarantees, algorithms, or contracts without Rob |
| Claude adversarial review chat | Independent reviewer | Load the current Git FCB and review the whole live architecture and path | Award acceptance or soften the contract |
| Codex | Risk-weighted extra review | At most the semantic-root review and final exhaustive review for foundational milestones when Rob enables it | Run automatically at every stop or replace human review |

## 2. Git bootstrap and exact-ref rule

Git is the sole canonical FCB store. The stable entry point is `.review/fcb/current/INDEX.md`.

For every serious Fido design, implementation, or review task:

1. Resolve one exact repository ref. Use the user-specified candidate commit or uploaded repository snapshot when one is supplied; otherwise use the latest accessible `main`.
2. Read the stable bootstrap `.review/fcb/current/INDEX.md` from that exact ref.
3. Read the FCB Index it names and use its consultation map.
4. Confirm every file the Index names exists at that same ref.
5. Read `.review/NEXT_STEPS.md` from the same ref — it is the live checkpoint authority.
6. Never mix FCB files or checkpoint status from different refs.
7. Stop on any missing or dangling reference, and on any operational path the corpus names without a typed
   row and owner marker — D-24 is a complete two-way relation, not row validation.

There is no checksum manifest and no verification tool: Git content-addresses the bytes, and the ref plus the
path is the identity. If the repository or ref is unavailable, or a named file does not resolve there, stop and
report the documentation-access defect. Do not answer from a stale project-library document or from memory.

## 3. Working sequence

1. Complete the Git bootstrap above.
2. If implementation or review reveals new information that conflicts with a protected FCB contract, stop implementation at that boundary.
3. ChatGPT authors a named FCB amendment identifying every affected document, fixed point, row, contract, checkpoint, and gate.
4. Rob accepts, rejects, or revises the amendment.
5. On acceptance, regenerate, verify, and commit the coherent FCB set under `.review/fcb/current/`.
6. Only then may Claude Code implement the amended public contract.
7. Otherwise, select the lowest eligible Roadmap checkpoint from `FIDO_FCB_ROADMAP.md` — subject to §3.1, the
   mechanical series that Governance D-27 places between C4 acceptance and C5 checkpoint-definition Step 0.
8. ChatGPT authors and freezes the checkpoint contract using `FIDO_FCB_CHECKPOINT_AUTHORING_GUIDE.md`.
9. Rob authorizes it.
10. Claude Code implements it without changing the contract.
11. Claude chat performs adversarial review of what exists, not only the diff.
12. Rob dispositions findings and accepts or blocks.
13. After acceptance, update the Git-hosted FCB through the publication duty in the authoring guide.

### 3.1 Post-C4 sequence (D-29 / A008, then D-27 / A007)

C4 is accepted. The eligible work is, in order: **M0 Governance Closeout**, then M1 Source Diet, M2
Performance Snapshot, M3 Tool and Build Architecture Audit, Rob's approval of the exact M4 plan, then M4 Mechanical
Refactor. Each is a separate reviewed candidate; C5 is not eligible until M4 is accepted. The full contracts
are the M0 closeout and the M-series plan under `.review/`; the Roadmap owns only the sequence.

**M1 through M4 implementation is forbidden until Rob accepts M0.** Installing a plan or an amendment does not
authorize implementing it, and a green intermediate gate is not acceptance.

### 3.2 Scope classification (D-28)

Review the whole system; block only on the active checkpoint's accepted contract. Classify every other finding
to its mandatory owner rather than folding it into the current work:

```text
source prose, comments, dead files and declarations → M1
build timing, dependency and edit-cost evidence       → M2
auxiliary tool and build-graph architecture           → M3
approved mechanical restructuring                     → M4
```

The classification is mandatory and stays visible in Git until dispositioned. Where a finding is discovered
does not decide which checkpoint owns it.

## 4. Project-library shim rule

ChatGPT and Claude project libraries contain one small bootstrap shim only. The shim points to `rhencke/fido` and `.review/fcb/current/INDEX.md`; it is not an FCB document and is never edited as project authority.

Root `CLAUDE.md` carries the same bootstrap rules for Claude Code. The shim and `CLAUDE.md` section change only if the repository identity or stable bootstrap path changes.

## 5. Research-chat rule

Research chats are disposable. Their useful facts must be copied into a frozen checkpoint, ADR, ledger row, or FCB amendment before they can influence implementation. Chat history never becomes a hidden authority.

## 6. Retirement and archive rule

Retired volley protocols, terminal directives, review lineage, return briefs, and superseded FCB sets remain in Git as provenance. They are not part of `.review/fcb/current/` and are never loaded as current authority merely because they are easier to find.

## 7. Standing amendment rule for models

Models must inspect constructor topology and retained-object flow when reviewing a capability boundary. They must propose an FCB amendment when the current corpus would force copied projections, equality-to-recomputation provenance, loss of an exact causal object, or a conflict between the live documentation and the implementation evidence.

The live documents for this rule are `FIDO_FCB_GOVERNANCE.md`, `FIDO_FCB_ARCHITECTURE_CHARTER.md`, `FIDO_FCB_FIXED_POINTS.md`, `FIDO_FCB_ROADMAP.md`, `FIDO_FCB_CHECKPOINT_AUTHORING_GUIDE.md`, and `FIDO_FCB_HUMAN_REVIEW_INDEX.md`.

### 7.1 Open human acts (D-07)

Consult `FIDO_FCB_HUMAN_ACTS.tsv` — it alone owns the set of open human acts. `FIDO_FCB_HUMAN_REVIEW_INDEX.md` is its generated view and is never edited by hand.

To change an act, edit its TSV row and, when the owning source changes, its single `<!-- FIDO-HUMAN-ACT:<ID> -->` anchor; then regenerate with `make human-acts-write` and publish both files in the same commit. `make human-acts` verifies the tracked view is byte-exact and that every anchor occurs exactly once in its named owning source; it runs inside `make check` and inside the pre-commit hook over the exported staged tree. Never hand-edit a generated row, and never restate the act list in another document.

## 8. Review standard

Review the whole live code and architecture. A component has only two valid fates: exact integration into the certified path, or deletion. No TODO, compatibility path, demo authority, trusted rescue, conservative gate marketed as correctness, or extensional stand-in may survive.
