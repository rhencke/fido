# Review Request

state: requested
review: Implementation Review
confirmation: no
confirmation_used: no
human_override: (none required; the GREEN Contract Review authorized the audit, and Amendment M3-A1 the one tool repair)
result: (pending)
candidate: (the M3 candidate named by `.review/NEXT_STEPS.md`; the freeze commit that follows it adds no work)

contract: .review/M3_TOOL_AND_BUILD_ARCHITECTURE_AUDIT.md
contract_activation_sha: 0b7fd86825936c37f31ef83879574d526d548122
amendment: .review/M3_CONTRACT_AMENDMENT_1.md
review_basis: .review/REVIEW_BASIS.md
prior_finding_record: .review/M3_FORENSIC_AUDIT_REPAIR_1.md

`.review/NEXT_STEPS.md` owns mutable checkpoint and candidate state. This file pins what is under review; it
does not own mutable state.

**The M3 Implementation Review is requested.** The audit is `.review/M3_AUDIT.md`, the plan is
`.review/M4_MECHANICAL_REFACTOR_PLAN.md`, and all twelve obligations are closed with distinct evidence. M4
remains forbidden until Rob accepts M3 and separately approves the plan.

## What the forensic repair changed

The blocking review was right on every count, and two of its findings changed conclusions rather than wording.

**The measurements had no immutable subject.** Configuration B now names
`a0482140384de3d8c193263c3bf5281e53ccdd8b` — the commit that landed the `M3-A1` repair — and every figure was
retaken there. The naming-gate cardinalities I had were wrong: **160 core retired names, not 170** (13/73/5/69,
read from the module rather than counted by eye), and the profile is 9 371 786 `re.escape` and 10 207 628
`re.search` calls under a command that is now written out in full instead of elided to a placeholder.

**The dependency graph was mine, not the toolchain's.** It now comes from `rocq dep` in a temporary
diagnostic image. It agrees with the import declarations edge for edge — but the authority is the toolchain,
and the result changed the disposition's *reason*: `Compilable.v` is 55% of the theory and its downstream
rebuild set is **3 modules**, one of the smallest in the graph, because it sits low in the dependents order.
So a split reduces almost nothing. I had written that a split was "outside M4's mechanical remit", which
`D-27` contradicts; the honest reason is that the measured fan-out does not justify it.

**Co-change was missing, and it is the most decision-relevant evidence in the audit.** Over the
current-module-set range (`20c5ad5c…` to `39ea7e3b…`), `Compilable.v` and `gate/Assumptions.v` change
together in **12 of 25 commits**, and 16 of 25 touch the assumptions gate. The 77 s readable gate is therefore squarely on the path semantic work
walks — which is why `Q-M3-01` is worth answering and why `M4-11` stays unauthorized rather than quietly
dropped.

**The `Compilable.v` surfaces got a finite classification instead of a shrug.** 623 declarations:
200 in the readable gate, 3 referenced by another module, 1 by a witness source, 371 internal proof
dependencies, and **48 with no consumer anywhere**. That last group is actionable because `Compilable.v` declares no `Hint`, so
a lemma there cannot be applied without being named — the method's error is in the safe direction. Those 48
are named individually in `M4-14`.

## The plan is smaller

Four steps deleted under `D-30` — batching container starts, one enumeration owner, narrowing the `PYTAG`
key, and host-shell portability — each now a `KEEP` with the measured evidence that retires it. The
enumeration one is worth naming: the five Python gates differ in **selection**, not only traversal (102, 113
and 111 files at the same ref), so a shared owner is a redesign this evidence does not support.
`M4-07` is narrowed to deleting two stale strings; the generic tool-prose checker is gone.

Nine steps remain, each with one exact design. **No step contains an "or", a fallback, or a decision deferred
to M4** — `M4-02` and `M4-03` now name their designs in full, including which paths a control may mutate, how
they are restored, and the control that proves the next scenario sees a pristine tree. Per-step verification
no longer re-runs the five targets `make check` already runs.

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
