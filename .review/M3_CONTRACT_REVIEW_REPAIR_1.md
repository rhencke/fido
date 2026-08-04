# M3 CONTRACT REVIEW — BLOCKING — REPAIR 1

## Result

**BLOCKING.**

The stop was correct. M3 implementation must not begin until this Contract Review passes.

Authoritative contract:

```text
.review/M3_TOOL_AND_BUILD_ARCHITECTURE_AUDIT.md
activation commit: 9d7ad8175134026ff5683e7b3c10062b48608064
```

M2 remains accepted at `9814db77ead0cfcfd8ff268303ba2afedef71197` under Rob's disposition
`M2-ACCEPT-9814db7`.

This review covers the whole proposed M3 contract. The contract has the right basic product shape — one
forensic audit, one exact M4 plan, no implementation and no audit platform — but six defects must be repaired
before the audit begins.

**Complexity fit: BLOCKED — the intended one-time audit is proportionate, but its current unit of analysis is
unbounded and its required output includes evidence M3 cannot possibly produce.**

---

## 1. Freeze the contract after Contract Review

Section 9 currently permits M3 to change:

```text
the M3 contract and matrix
```

That makes the binding contract mutable during the audit which it governs. A later implementation could change
its own acceptance rules after this review without returning to the review gate.

Replace that rule with:

- after Contract Review passes, the M3 contract and accepted review basis are frozen;
- the obligation matrix, audit, M4 plan and current review-state documents may evolve under that frozen contract;
- if implementation evidence shows the contract is incomplete, inconsistent or would force the wrong result,
  Claude stops, names the exact conflict and requests a contract amendment and another Contract Review;
- Claude may never repair the conflict by silently editing the accepted contract during the audit.

The matrix may update evidence and status. It may not redefine the claims.

---

## 2. M3 cannot carry actual “after” measurements

M3 explicitly implements no refactor.

Section 8 nevertheless requires every M4 step to state an “after measurement,” and M3-10 claims:

```text
The M4 plan carries exact before/after measurements.
```

M3 cannot measure the result of an implementation which M3 is forbidden to perform.

Correct the contract and M3-10:

- M3 records exact current baselines for every proposed optimization;
- the M4 plan names the exact post-change command, source view, cache condition and acceptance criterion;
- the M4 plan names the failure and Git rollback boundary;
- M4 produces the actual after values and compares them with the M3 baseline;
- no projected or desired number may masquerade as an observed after measurement.

A target such as “under one minute” may remain a goal. It is not evidence and not an M3 completion claim.

---

## 3. Define a finite audit unit

The current scope combines:

```text
every tool
every public target and dependency
every Docker edge and cache
every Dune edge
every Rocq proof and gate
every meaningful helper
```

and then prescribes a long field set for every surface.

That wording can be satisfied only by an enormous quasi-registry, precisely the failure D-30 is meant to
prevent. “Meaningful helper” and “every Rocq proof” have no finite boundary.

Use these audit units:

1. each tracked executable tool file;
2. each public Make target;
3. each named pre-commit stage;
4. each Docker/Buildx stage, persistent cache and source-view boundary which affects execution or invalidation;
5. each Dune alias, module dependency edge or proof-build unit which affects fan-out or the critical path;
6. each distinct proof, assumption, extraction, e2e, generated-byte or publication gate;
7. an internal helper only when it owns a distinct policy fact, source enumeration, cache key, production edge
   or dominant measured cost.

Do **not** inventory every function, theorem or proof body.

Exact sibling surfaces may share one row only when the row lists every path/ID and they truly have one job,
owner, source view and disposition.

Each audit row records only what supports its decision:

```text
stable ID
exact surface(s)
real job and owner
source view / environment
measured cost, fan-out, cache or overlap evidence when relevant
disposition
M4 step ID, or a plain retain/no-change reason
```

Allowed dispositions are:

```text
KEEP
SIMPLIFY
MERGE
DELETE
MOVE
```

Every mandatory finding also ends either in one or more exact M4 step IDs or an evidence-backed `KEEP / no M4
change` disposition. “Investigated” is not a disposition.

Narrow `M3-HOST-CONTAINER-OTHER` to the current host entrypoints and container boundaries which actually exist.
It is not authority to search for speculative future questions.

---

## 4. Separate the reproducible perf baseline from real user-facing paths

`.review/PERFORMANCE.tsv` measures a dedicated serial builder and `make -j1 check`. That is the correct
reproducible phase baseline, but it is not automatically the wall time a developer experiences under ordinary
settings.

The contract must distinguish:

```text
serial diagnostic baseline       make perf / PERFORMANCE.tsv
ordinary working-tree acceptance normal make check
staged acceptance                 the real pre-commit hook
partial feedback                  each named public partial target the M4 plan proposes to retain
```

M3 measures only the additional paths needed to explain or plan a change, using their real configuration.

Do not compare unlike configurations as one metric. A serial diagnostic value, normal-parallel value, staged
snapshot value and partial-feedback value answer different questions.

The execution graph and M4 plan must continue to say which result is partial and which is full acceptance.

---

## 5. Make edit-frequency evidence exact and non-misleading

`M3-EDIT-WEIGHT` does not define its Git range. A convenient range could mix semantic/proof development with the
M1/M2 prose and tooling campaigns and produce a weight which predicts neither kind of future work.

Require the audit to:

- name every exact Git range used;
- keep semantic/proof work and M-series mechanical/tool work separate;
- never pool those ranges into one unexplained frequency;
- state why each range is relevant to the proposed M4 decision;
- retain the exact command and result needed to reproduce each conclusion.

Every measured fact in the audit names:

```text
exact Git ref or range
exact command
source view
cache / cold / hot condition where relevant
observed result
```

Raw logs may remain disposable. The audit must retain enough of the result for Implementation Review to judge
the conclusion without trusting an unstated terminal session.

---

## 6. Repair the Contract Review state

The current review request does not name the binding activation SHA even though the review policy requires it.
It says the commit is “named by NEXT_STEPS,” but NEXT_STEPS names no SHA.

The current `.review/REVIEW_BASIS.md` also calls itself “Accepted” before Contract Review has accepted it. A
review basis is the output of a GREEN Contract Review, not input pre-approved by the implementer.

Required correction:

1. `NEXT_STEPS` and `REVIEW_REQUEST` name contract activation SHA
   `9d7ad8175134026ff5683e7b3c10062b48608064`, or the later repair SHA which becomes the revised contract
   activation.
2. Until confirmation passes, `.review/REVIEW_BASIS.md` is explicitly proposed/pending and does not call itself
   accepted.
3. After the bounded confirmation is GREEN, install the reviewer-approved basis as
   `.review/REVIEW_BASIS.md` with the exact revised contract SHA.
4. The `M3-REVIEW` human-act row must not claim that an implementation candidate already exists. It should name
   final M3 acceptance as a deferred act until an exact candidate is frozen, or otherwise state the current act
   truthfully.

Do not add another review framework or document type.

---

## Claim surface after repair

The accepted contract should make only these material claims:

1. M3 produces a finite, evidence-backed forensic account of the current execution architecture.
2. Every mandatory stable finding and every retained tool receives one exact disposition.
3. M3 distinguishes source views, partial feedback and full acceptance.
4. M3 records exact current baselines and explains dominant cost, invalidation, fan-out and repeated work.
5. M3 produces one dependency-ordered, implementation-ready M4 plan with exact post-change measurement
   procedures and preservation gates.
6. M3 changes no production, proof, build, tool, generated or runtime path.
7. M4 remains forbidden until M3 passes, Rob accepts M3 and Rob approves the exact plan.

---

## Evidence required at M3 Implementation Review

The later Implementation Review will require:

- one finite audit table using the accepted audit units;
- every mandatory stable finding ID present exactly once;
- one current execution graph distinguishing same-view repetition from required different-view work;
- exact commands and evidence for dominant costs, invalidation, Dune fan-out and edit weighting;
- one D-30 disposition for every tracked executable tool file and every other accepted audit unit;
- every non-KEEP disposition linked to exact M4 step IDs;
- one exact M4 plan with current baselines, post-change measurement commands and complete preservation gates;
- a diff proving M3 changed only authorized documentation and review-state files;
- all current correctness, proof, artifact, staged-hook, generated-byte and runtime gates green.

---

## Forbidden overreach

M3 may not:

- create a permanent audit, inventory, graph or timing tool;
- commit raw timing bundles or a new registry/schema;
- change production, Make, hook, Docker, Dune, tool, proof, OCaml, generated-Go or runtime paths;
- collapse working-tree and staged-index checks merely because they invoke the same implementation;
- present partial feedback as full acceptance;
- execute any M4 action;
- amend its accepted contract without stopping for review.

---

## Required contract-repair work

1. Install this review as the sole Contract Review finding record.
2. Amend the M3 contract and M3-10 for Findings 1–5.
3. Repair the review request, pending review-basis status and human-act wording under Finding 6.
4. Update the matrix only where the claim wording changed; keep every implementation obligation open.
5. Change no production or audit implementation.
6. Run the current document, reference, claim, naming, source-diet and host-Python gates.
7. Commit one authority-only contract-repair candidate.
8. Request the single bounded Contract Review confirmation.

The confirmation is limited to these six findings and the clauses directly changed by them.

---

## Completeness declaration

The entire proposed M3 contract, obligation matrix, review request, review basis, current checkpoint state and
relevant D-27/D-28/D-30 review rules were reviewed. No implementation was reviewed or authorized.
