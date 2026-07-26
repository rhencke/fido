# Fido FCB Model Operations

> **Derived reference, not implementation authority.** The code and its gated theorems are the sole implementation authority.  
> **Living document.** Its identity is its Git blob at the exact ref resolved for the task; its
> history is the commit log. No version suffixes, no checksum manifest.  
> **Accepted amendments:** `FCB-A001-INTRINSIC-STATIC-CAPABILITY-PROVENANCE`; `FCB-A002-GIT-CANONICAL-FCB-STORAGE`; `FCB-A003-LIVING-DOCUMENTATION`;
> `FCB-A004-GIT-RESOLVABLE-LIVING-CORPUS`; `FCB-A005-SCOPED-NAME-OWNERSHIP`;
> `FCB-A006-INTRINSIC-EMIT-IMAGE-MINT`.  
> **Canonical live location:** `.review/fcb/current/` in the exact Git ref used for the task.  
> **Stable bootstrap:** `.review/fcb/current/INDEX.md`  
> Project libraries contain only a bootstrap shim. They do not contain or own the FCB corpus.  
> Regenerate, verify, and commit affected FCB files in Git after each accepted checkpoint or amendment.  
> This corpus does not accept C4 and does not authorize C5; `.review/NEXT_STEPS.md` remains the live checkpoint authority.


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
7. Stop on any missing or dangling reference (D-24).

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
7. Otherwise, select the lowest eligible Roadmap checkpoint from `FIDO_FCB_ROADMAP.md`.
8. ChatGPT authors and freezes the checkpoint contract using `FIDO_FCB_CHECKPOINT_AUTHORING_GUIDE.md`.
9. Rob authorizes it.
10. Claude Code implements it without changing the contract.
11. Claude chat performs adversarial review of what exists, not only the diff.
12. Rob dispositions findings and accepts or blocks.
13. After acceptance, update the Git-hosted FCB through the publication duty in the authoring guide.

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
