# Fido FCB Model Operations v2

> **Derived reference, not authority.** The code and its gated theorems are the sole authority.  
> **FCB version:** `v2` · **Generated:** `2026-07-25`  
> **Supersedes:** `FIDO_FCB_MODEL_OPERATIONS_v1.md`  
> **Repository basis:** `rhencke/fido@ece4c1dd0797eff6e9ebdd5d77a0e59f1c9e76e0` · source snapshot SHA-256 `6e25e8be64a77b7d98609c607d48b1d6917b2bf0480d10fa4a92f1a6bb170eff`  
> **Terminal-bundle basis:** SHA-256 `58abd876a0962bde42e5c9fc0365a8431b88b13beb790440e4b52031c7f8aad0` · handoff SHA-256 `fdfc2c235707aeeef58c566f5fd145850ca606df8d693f5cc6bc81f2112eb143`  
> **Amendment basis:** `FCB-A001-INTRINSIC-STATIC-CAPABILITY-PROVENANCE` · accepted `2026-07-25` · directive SHA-256 `79a8fa3f6d5a861b82259a578eef6123369dbc9567fbd63288b93c1ce1037b8c`  
> Regenerate this document at each checkpoint acceptance. Delete every stale copy from every model library.  
> This library does not accept C4 and does not authorize C5; `.review/NEXT_STEPS.md` remains the live checkpoint authority.


## 1. Delegation table

| Actor | Role | May do | May not do |
|---|---|---|---|
| Rob | Human authority | Choose scope, disposition ADRs, authorize repairs, accept checkpoints, reopen fixed points | Delegate final acceptance by silence |
| ChatGPT primary project thread | Checkpoint author and FCB maintainer | Read FCB, author frozen checkpoint contracts, reconcile source, update the library after acceptance | Accept its own design or implementation |
| Disposable research chats | Exploration | Attack one question, compare alternatives, produce evidence for the primary thread | Become a source of truth; carry hidden decisions forward |
| Claude Code | Implementer | Implement only the frozen checkpoint, run gates, delete replaced paths, report conflicts | Change architecture, scope, guarantees, algorithms, or contracts without Rob |
| Claude adversarial review chat | Independent reviewer | Review the whole live architecture and path, raise BLOCKING/REQUIRED findings | Award acceptance or soften the contract |
| Codex | Risk-weighted extra review | At most the semantic-root review and final exhaustive review for foundational milestones when Rob enables it | Run automatically at every stop or replace human review |

## 2. Working sequence

1. Read `FIDO_FCB_INDEX_v2.md` and use its exact consultation map.
2. Read the current `.review/NEXT_STEPS.md`.
3. If implementation or review reveals new information that conflicts with a protected FCB contract, stop implementation at that boundary.
4. ChatGPT authors a named FCB amendment identifying every affected document, fixed point, row, contract, checkpoint, and gate.
5. Rob accepts, rejects, or revises the amendment.
6. On acceptance, regenerate and replace the coherent FCB set.
7. Only then may Claude Code implement the amended public contract.
8. Otherwise, select the lowest eligible Roadmap checkpoint from `FIDO_FCB_ROADMAP_v2.md`.
9. ChatGPT authors and freezes the checkpoint contract using `FIDO_FCB_CHECKPOINT_AUTHORING_GUIDE_v2.md`.
10. Rob authorizes it.
11. Claude Code implements it without changing the contract.
12. Claude chat performs adversarial review of what exists, not only the diff.
13. Rob dispositions findings and accepts or blocks.
14. After acceptance, regenerate the affected FCB set and delete stale copies.

## 3. Research-chat rule

Research chats are disposable. Their useful facts must be copied into a frozen checkpoint, ADR, ledger row, or FCB amendment before they can influence implementation. Chat history never becomes a hidden authority.

## 4. Library update duty

The ChatGPT project library is primary. The Claude project library receives the same current FCB set unless Rob explicitly strikes that duty. A stale FCB file in either library is a defect. Never upload a new version beside an old one; replace and delete.

## 5. Retirement register

Remove from live model libraries and keep only in the frozen provenance bundle:

- Volley Protocol v1–v3 and the decision-ratchet procedure;
- terminal directives v1–v12;
- volley linter, validator, send/return packaging tools;
- review lineage, return briefs, and adjudication briefs;
- superseded architecture-plan versions and review prose.

Keep live or migrate toward the repository when its checkpoint lands:

- `run_fixture.py` and `PROBE_ENVIRONMENT.tsv` as the differential-testing spine;
- the audit/verifier pattern as a checkpoint-gate template;
- pinned spec and extraction tools in frozen archive form for reproducibility.

## 6. Standing amendment rule for models

Models must inspect constructor topology and retained-object flow when reviewing a capability boundary. They must propose an FCB amendment when the current corpus would force copied projections, equality-to-recomputation provenance, or loss of an exact causal object.

The live v2 documents for this rule are `FIDO_FCB_GOVERNANCE_v2.md`, `FIDO_FCB_ARCHITECTURE_CHARTER_v2.md`, `FIDO_FCB_FIXED_POINTS_v2.md`, `FIDO_FCB_ROADMAP_v2.md`, `FIDO_FCB_CHECKPOINT_AUTHORING_GUIDE_v2.md`, and `FIDO_FCB_HUMAN_REVIEW_INDEX_v2.md`.

## 7. Review standard

Review the whole live code and architecture. A component has only two valid fates: exact integration into the certified path, or deletion. No TODO, compatibility path, demo authority, trusted rescue, conservative gate marketed as correctness, or extensional stand-in may survive.
