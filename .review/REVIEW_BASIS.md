# M3 Accepted Review Basis

status: ACCEPTED
checkpoint: M3 — Tool and Build Architecture Audit
contract: .review/M3_TOOL_AND_BUILD_ARCHITECTURE_AUDIT.md
contract_activation_sha: 0b7fd86825936c37f31ef83879574d526d548122
obligations: .review/M3_OBLIGATION_MATRIX.tsv
human_authorization: M2-ACCEPT-9814db7

This is the reviewer's GREEN bounded-confirmation output, installed verbatim as the accepted basis. It
governs how the M3 candidate will be reviewed. It does not override the contract or a later human decision.

## Accepted claim surface

M3 will make only these material claims:

1. M3 produces a finite, evidence-backed forensic account of the current execution architecture.
2. Every mandatory stable finding and every accepted audit unit receives one exact disposition.
3. M3 distinguishes source views, partial feedback, and full acceptance.
4. M3 records exact current baselines and explains dominant cost, invalidation, fan-out, and repeated work.
5. M3 produces one dependency-ordered, implementation-ready M4 plan with exact post-change measurement
   procedures and preservation gates.
6. M3 changes no production, proof, build, tool, generated, or runtime path.
7. M4 remains forbidden until M3 passes Implementation Review, Rob accepts M3, and Rob approves the exact plan.

## Blocking defect classes for M3 Implementation Review

M3 is blocked if any of these holds:

- a disposition is asserted where the real toolchain or a reproducible measurement could have supplied evidence;
- a measured fact omits its ref or range, command, source view, cache condition, or observed result;
- a mandatory stable finding ID is missing, renumbered away, or ends without exact M4 step IDs or an
  evidence-backed `KEEP / no M4 change`;
- the audit grows beyond the seven accepted audit-unit classes or inventories functions, theorems, or proof
  bodies;
- unlike source views, performance configurations, or partial/full results are collapsed;
- a desired or projected result is presented as an observed measurement;
- the audit creates a permanent framework, registry, schema, comparator, bundle hierarchy, or timing system;
- the M4 plan contains placeholders, omits a current baseline or post-change procedure, leaves cache/source-view
  consequences unstated, or lacks preservation gates and rollback boundaries;
- M3 changes a production, Make, hook, Docker, Dune, tool, proof, OCaml, generated-Go, fixture, golden, or runtime
  path;
- M3 edits the accepted contract or accepted basis instead of stopping on a conflict;
- retained or proposed machinery is more complicated than its real job justifies.

## Evidence required at M3 Implementation Review

The frozen M3 candidate must provide:

- one finite audit table using only the accepted audit units;
- every mandatory stable finding ID exactly once;
- one current execution graph distinguishing:
  - repeated same-view work;
  - required different-view work;
  - cached work;
  - always-run controls;
  - partial feedback;
  - full acceptance;
- reproducible evidence for dominant costs, invalidation, Dune/Rocq fan-out, edit frequency, and co-change,
  with semantic/proof and M-series ranges kept separate;
- one D-30 disposition for every tracked executable tool file and every other accepted audit unit;
- exact M4 step IDs for every non-KEEP disposition;
- one implementation-ready, dependency-ordered M4 plan carrying:
  - M3's exact current baselines;
  - M4's exact post-change measurement procedures;
  - source-view and cache-key consequences;
  - complete preservation gates;
  - failure and Git rollback boundaries;
  - all deletions made legal;
- a diff proving M3 changed only the contract-authorized documentation and review-state surfaces;
- all current acceptance gates green;
- `.v`, OCaml, generated Go, fixtures, and goldens byte-unchanged.

## Forbidden overreach

M3 may not:

- create a permanent audit, inventory, graph, timing, or comparison tool;
- add a registry, schema, bundle hierarchy, resume system, or statistics framework;
- commit raw diagnostic bundles;
- change Makefile recipes or dependencies, the hook, Docker stages or cache keys, Dune files, tools, Rocq code,
  OCaml transport, generated Go, fixtures, goldens, or runtime behavior;
- weaken or collapse working-tree and staged-index enforcement;
- present partial feedback as full acceptance;
- execute any M4 step;
- amend this accepted contract or basis while continuing the audit.

If the frozen contract proves wrong, stop and return to the primary review thread with the exact conflict.

## Ambiguities or conflicts

None remain from the recorded Contract Review finding set.

The serial M2 performance record is diagnostic evidence for one configuration only. It is not ordinary developer
wall time. The contract's four-configuration distinction governs any additional measurement.
