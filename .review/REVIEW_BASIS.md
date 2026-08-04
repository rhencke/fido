# M3 Proposed Review Basis

status: PROPOSED — not accepted
checkpoint: M3 — Tool and Build Architecture Audit
contract: .review/M3_TOOL_AND_BUILD_ARCHITECTURE_AUDIT.md
obligations: .review/M3_OBLIGATION_MATRIX.tsv
prior_finding_record: .review/M3_CONTRACT_REVIEW_REPAIR_1.md
human_authorization: M2-ACCEPT-9814db7

**This is a proposal, not an authority.** A review basis is the output of a GREEN Contract Review, not input
the implementer pre-approves for itself. It governs nothing until the bounded Contract Review confirmation
passes, at which point the reviewer's accepted output replaces this file, carrying the revised contract
activation SHA. Until then it states what M3 expects to be held to, so the confirmation can check it.

## Proposed claim surface

1. M3 produces a finite, evidence-backed forensic account of the current execution architecture.
2. Every mandatory stable finding and every retained tool receives one exact disposition.
3. M3 distinguishes source views, partial feedback and full acceptance.
4. M3 records exact current baselines and explains dominant cost, invalidation, fan-out and repeated work.
5. M3 produces one dependency-ordered, implementation-ready M4 plan with exact post-change measurement
   procedures and preservation gates.
6. M3 changes no production, proof, build, tool, generated or runtime path.
7. M4 remains forbidden until M3 passes, Rob accepts M3 and Rob approves the exact plan.

## Blocking defect classes

A candidate is blocked when any of these holds.

- **A finding is asserted rather than evidenced.** A disposition rests on inference where the real toolchain
  could have reported the fact, or on a measurement whose ref, command, source view or cache condition is not
  named.
- **A mandatory finding ID disappeared.** Renumbering, grouping or silent omission of any stable ID; or a
  finding that ends in "investigated" rather than an M4 step ID or an evidence-backed `KEEP / no M4 change`.
- **The audit unit grew.** An inventory of functions, theorems or proof bodies, or any unit outside the seven
  the contract closes.
- **A distinction was collapsed as an optimization.** Working-tree and staged-index work called duplicates
  because they invoke the same tool; partial feedback presented as full acceptance; unlike measured
  configurations pooled or compared as one metric.
- **A projection was presented as an observation.** An "after measurement" M3 could not have taken, or a
  target recorded as evidence.
- **The audit became a framework.** A permanent timing or audit tool, registry, schema, bundle hierarchy,
  comparator or statistics engine — the thing `D-30` exists to prevent and the last checkpoint died of.
- **The M4 plan is not implementation-ready.** A placeholder step, a missing baseline or post-change
  procedure, an unstated cache-key or source-view consequence, or a step whose preservation gates or rollback
  boundary are not named.
- **A production path moved.** Any change to Makefile recipes or dependencies, the hook, Dockerfile stages
  or cache keys, Dune files, tools, Rocq code, OCaml transport, generated Go, fixtures, goldens, the
  no-host-Python boundary, or the accepted perf script and record.
- **The contract was edited instead of stopped at.** Any change to the frozen contract or accepted basis
  during the audit.
- **Complexity does not fit.** Retained or proposed machinery mainly supports itself rather than the job.

## Required evidence at Implementation Review

- One finite audit table using the seven accepted audit units.
- Every mandatory stable finding ID present exactly once, each naming the command or file that established
  it, and each ending in exact M4 step IDs or an evidence-backed `KEEP / no M4 change`.
- One current execution graph in plain text, distinguishing repeated same-view work, required
  different-view work, cached work, always-run controls, partial feedback and full acceptance.
- Exact commands and evidence for dominant costs, invalidation, Dune fan-out and edit weighting, with
  semantic/proof ranges kept separate from M-series tooling ranges.
- One `D-30` complexity-fit disposition per tracked executable tool file and per other accepted audit unit.
- `.review/M4_MECHANICAL_REFACTOR_PLAN.md`, implementation-ready and ordered by dependency, carrying M3's
  baselines and M4's post-change measurement procedures.
- A diff proving M3 changed only authorized documentation and review-state files.
- Every current acceptance gate green, with `.v`, OCaml, generated Go and goldens byte-unchanged.

## Forbidden overreach

M3 may not create a permanent audit, inventory, graph or timing tool; commit raw timing bundles or a new
registry or schema; change production, Make, hook, Docker, Dune, tool, proof, OCaml, generated-Go or runtime
paths; collapse working-tree and staged-index checks merely because they invoke the same implementation;
present partial feedback as full acceptance; execute any M4 action; or amend its accepted contract without
stopping for review.

## Scope

M3 does not implement the refactor, and M3 acceptance does not approve it. `M4-PLAN-APPROVAL` remains a
separate act by Rob over the exact plan.

Only Rob accepts M3.
