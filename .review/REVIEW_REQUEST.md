# Review Request

state: requested
review: Implementation Review
confirmation: no
confirmation_used: no
human_override: Rob ratified amendments M3-A1 and M3-A2 by approving .review/M3_FORENSIC_AUDIT_REPAIR_2.md
result: (pending)
candidate: (the M3 candidate named by `.review/NEXT_STEPS.md`; the freeze commit that follows it adds no work)

contract: .review/M3_TOOL_AND_BUILD_ARCHITECTURE_AUDIT.md
contract_activation_sha: 0b7fd86825936c37f31ef83879574d526d548122
amendment: .review/M3_CONTRACT_AMENDMENT_1.md
amendment: .review/M3_CONTRACT_AMENDMENT_2.md
review_basis: .review/REVIEW_BASIS.md
prior_finding_record: .review/M3_FORENSIC_AUDIT_REPAIR_2.md
candidate_sha: (this repair candidate; the freeze that follows pins it)
blocked_candidate: 5af6bc10a811e72fed48a9a1ce09c01c8f1a9e92
blocked_freeze: a7383653580e093c9ed4106938bf5be82ecf6d9b

`.review/NEXT_STEPS.md` owns mutable checkpoint and candidate state. This file pins what is under review; it
does not own mutable state.

**The M3 Implementation Review is requested.** The audit is `.review/M3_AUDIT.md`, the plan is
`.review/M4_MECHANICAL_REFACTOR_PLAN.md`, and all twelve obligations are closed with distinct evidence. M4
remains forbidden until Rob accepts M3 and separately approves the plan.

## What Repair 2 changed

The review found four things, and two of them were me confusing a mechanical fact for a semantic one.

**`M4-14` would have deleted exported theorem guarantees.** I classified 48 `Compilable.v` theorems as dead
because no name referenced them and the module declares no `Hint`. That proves they are not *current internal
proof dependencies* — nothing more. A top-level theorem can be its own externally visible guarantee, or a
standalone regression fixture whose **statement is the product**; such a theorem has no caller by design. The
list visibly contained reordering, determinism, rejected-program-report and fact-table fixtures whose own
comments say so. And `make prove` staying green would not have caught the loss, because the lost guarantees
would have been the deleted statements. The step is gone; group E is now `KEEP, no M4 change`, and any future
deletion needs a separately reviewed public-surface contract.

**`M4-06` would have deleted the set its own retained check reads.** `check_permanent_wiring` — the permanent
M-series law, run by `make diet` and by the hook on every commit — iterates `M1_ONLY_MODES` to prove no
permanent path invokes a checkpoint-only mode. I proposed deleting that tuple while keeping the check. It now
retains `M1_ONLY_MODES` as the explicit unsupported-boundary set of retired spellings, and deletes only the
argparse options, the implementations reachable through them, the dead path constants and the dormant
mutants.

**`M3-CLAIM-SUBJECT` was recorded as satisfied and was not.** The contract asks to remove the *need* for a
hand-retargeted constant; deleting a stale docstring copy leaves the constant exactly as hand-retargeted.
Amendment `M3-A2` replaces the wording with what actually closes it — one subject object owning both the
matrix path and the required obligation-ID set — and `M4-07` builds it. Dynamic discovery is explicitly not
authorized: it would still not know the required IDs, and reading them from review prose would create a
second current-state authority.

**`M3-A1`'s authority record was false, and that one was the same class of error I had just been blocked
for.** It said the reviewer authorized the amendment. A reviewer specifies; Rob alone accepts. Rob has now
ratified `M3-A1` and `M3-A2`, and both name him. No model is recorded as amending the contract.

Two more steps left the plan under `D-30`. `M4-03`'s restoration manifest recorded size, `mtime_ns` and
directories — which do not establish file type, mode, symlink identity or symlink target, while the controls
mutate all of those — so it would not have proved the property it claimed; and `M4-02` removes the multiplier
that made those copies dominant anyway. `M4-13` would have put a cache inside an adversarial proof gate
without an exact topology, next to controls that deliberately vary the prelude to prove the helper rejects
false evidence. `M4-09` is narrowed to the claim-matrix root facts the mandatory finding actually names;
`closure-ledger-view.py`'s missing controls are recorded and left alone rather than becoming a new gate
surface mid-optimization.

Six steps remain. The plan identifies every subject by stable name rather than line number, and per-step
verification is `make check` plus `make fmt`, not the five targets `make check` already runs.

## Scope

```text
no production, proof, Make, hook, Docker, Dune, generated or runtime path moved
```

The one project-tool change is the one Amendment `M3-A1` authorizes: the claim-matrix self-test precondition,
in `tools/claim-matrix-gate.py` and its mutation entry. `M4-14` is a *proposed* deletion in `Compilable.v`;
M3 did not execute it, and every `.v`, OCaml, generated Go, fixture, golden, Makefile, Dockerfile, Dune file,
hook, perf script and TSV byte is unchanged from the contract activation.

No permanent audit, timing, inventory, graph or comparison tool was created, no registry or schema added, and
no raw log committed. `.review/M3_AUDIT.md` is one temporary table.

M2 is ACCEPTED under `M2-ACCEPT-9814db7`, M1 under `M1-ACCEPT-6524b43`, C4 under `C4-ACCEPT-39ea7e3` and M0
under `M0-ACCEPT-86a63db`. M4, C5 Step 0 and C5 remain forbidden. Only Rob accepts M3.
