# Fido FCB Model Operations v3

> **Derived reference, not authority.** The code and its gated theorems are the sole implementation authority.  
> **FCB document version:** `v3` · **FCB set:** `v3` · **Generated:** `2026-07-25`  
> **Supersedes:** `FIDO_FCB_MODEL_OPERATIONS_v2.md`  
> **Source repository basis:** `rhencke/fido@ece4c1dd0797eff6e9ebdd5d77a0e59f1c9e76e0` · source snapshot SHA-256 `6e25e8be64a77b7d98609c607d48b1d6917b2bf0480d10fa4a92f1a6bb170eff`  
> **Terminal-bundle basis:** SHA-256 `58abd876a0962bde42e5c9fc0365a8431b88b13beb790440e4b52031c7f8aad0` · handoff SHA-256 `fdfc2c235707aeeef58c566f5fd145850ca606df8d693f5cc6bc81f2112eb143`  
> **Amendments:** `FCB-A001-INTRINSIC-STATIC-CAPABILITY-PROVENANCE`; `FCB-A002-GIT-CANONICAL-FCB-STORAGE`  
> **Canonical live location:** `.review/fcb/current/` in the exact Git ref used for the task.  
> **Stable bootstrap:** `.review/fcb/current/INDEX.md` · **Manifest:** `.review/fcb/current/FIDO_FCB_MANIFEST.sha256`  
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
2. Read `.review/fcb/current/INDEX.md` from that exact ref.
3. Run or reproduce `.review/fcb/tools/verify_current_fcb.py` against that exact ref.
4. Read the versioned Index named by the stable bootstrap and use its consultation map.
5. Read `.review/NEXT_STEPS.md` from the same ref.
6. Never mix FCB files or checkpoint status from different refs.

If the repository/ref is unavailable or the manifest fails, stop and report the documentation-access defect. Do not answer from a stale project-library document or compressed chat memory.

## 3. Working sequence

1. Complete the Git bootstrap above.
2. If implementation or review reveals new information that conflicts with a protected FCB contract, stop implementation at that boundary.
3. ChatGPT authors a named FCB amendment identifying every affected document, fixed point, row, contract, checkpoint, and gate.
4. Rob accepts, rejects, or revises the amendment.
5. On acceptance, regenerate, verify, and commit the coherent FCB set under `.review/fcb/current/`.
6. Only then may Claude Code implement the amended public contract.
7. Otherwise, select the lowest eligible Roadmap checkpoint from `FIDO_FCB_ROADMAP_v3.md`.
8. ChatGPT authors and freezes the checkpoint contract using `FIDO_FCB_CHECKPOINT_AUTHORING_GUIDE_v3.md`.
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

The live documents for this rule are `FIDO_FCB_GOVERNANCE_v3.md`, `FIDO_FCB_ARCHITECTURE_CHARTER_v3.md`, `FIDO_FCB_FIXED_POINTS_v3.md`, `FIDO_FCB_ROADMAP_v3.md`, `FIDO_FCB_CHECKPOINT_AUTHORING_GUIDE_v3.md`, and `FIDO_FCB_HUMAN_REVIEW_INDEX_v3.md`.

## 8. Review standard

Review the whole live code and architecture. A component has only two valid fates: exact integration into the certified path, or deletion. No TODO, compatibility path, demo authority, trusted rescue, conservative gate marketed as correctness, or extensional stand-in may survive.
