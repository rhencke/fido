# ASSUM-GATE — delete the readable assumption gate

Baseline: 94c8a6dd3bb1aca77a1905f8df5d880050e5232e
Review: implementation

Rob's decision, recorded in `DECISIONS.md`: delete `gate/Assumptions.v`. The whole-theory
`Fido Audit Assumptions` and its existing adversarial self-tests own the zero-project-axiom build claim.

Goal:
Remove the redundant readable assumptions gate while preserving the complete whole-theory audit.

Change:
- delete `gate/Assumptions.v`, which empties `gate/`;
- delete all three `COPY gate/ gate/` from the Dockerfile;
- delete the readable-gate compile, grep, count and message block from the prover stage;
- rename the remaining prover-stage step letters only where the deletion leaves a gap;
- make the prover-stage success message report the whole-theory audit, module coverage and self-tests,
  with no readable-gate count;
- in `plugin/materialize.mlg`, remove only the claim that `Print Assumptions` remains a complementary
  public-surface check; leave the audit implementation untouched;
- update the references in `README.md`, `CLAUDE.md`, `ARCHITECTURE.md`, `TOOLCHAIN.md`, `ROADMAP.md`,
  `DECISIONS.md`, `Makefile` and this file;
- record `ASSUMPTION-GATE-PLACEMENT` as ACCEPTED;
- add no replacement gate, list, registry, generator, schema or compatibility path.

Preserve exactly:
- `Fido Audit Assumptions`, its root enumeration and its assumption filtering;
- the certified-module coverage check;
- audit self-tests A-E;
- the sealed-capability tests, mint controls and the positive client control;
- the emit-time provenance assumption guard;
- every certified `.v` module;
- generated Go bytes and runtime goldens;
- the staged-index and working-tree source-view distinction;
- `life.md`.

Done:
- no tracked `gate/Assumptions.v` and no remaining `COPY` of `gate/`;
- no current reference to a readable assumption gate;
- audit self-tests A-E still execute;
- generated Go and goldens unchanged;
- `make prove`, `make check`, `make audit-fresh` green; one `make perf` records the new baseline;
- Review is set to implementation and Claude stops.

Stop:
- deleting the gate would drop a guarantee the whole-theory audit does not already make;
- any step needs a replacement mechanism to keep the build green.
