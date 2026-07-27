# Fido M-Series Plan — M0 closeout and post-C4 mechanical debt removal

> **Live authority.** Installed by accepted amendment `FCB-A007-POST-C4-MECHANICAL-SERIES` and governed by
> Governance `D-27`. Its identity is its Git blob at the exact ref resolved for the task; its history is the
> commit log.
> **Sequencing:** M0 runs first, then M1 through M4, then checkpoint-definition Step 0 for C5.
> **C4 is ACCEPTED.** M0 Governance Closeout is the sole active work; M1, M2, M3 and M4 implementation are
> FORBIDDEN until Rob accepts M0. Installing a plan does not authorize implementing it.

The current repository carries source prose, proof text and build tooling that has accumulated without one
owned build architecture. Much of the prose records superseded design history that Git already preserves. Full
builds approach two to three minutes, and there is no measured account of module cost, dependency fan-out, edit
frequency, cache behaviour, or duplicated gate work.

That is a real correctness cost, not only a comfort one: stale prose obscures current authority, large serial
units delay feedback, and duplicated checks create divergent build paths. The permanent C5 `Machine` base must
not be frozen on top of it.

## Sequence

```text
C4 acceptance closeout
→ M0 Governance Closeout
→ M1 Source Diet
→ M2 Build Observatory
→ M3 Tool and Build Architecture Audit
→ Rob approves the exact M4 plan
→ M4 Mechanical Refactor
→ checkpoint-definition Step 0
→ C5 Machine base
```

Each M candidate is a separate reviewed candidate. **M0 comes first**, and its full contract is
`.review/M0_GOVERNANCE_CLOSEOUT.md`: it publishes the C4 disposition, retires repair-state archaeology to
Git history, installs the strict checkpoint-scope law, and verifies the existing governance state. M1 is
forbidden until Rob accepts M0. M4 begins only after M2 and M3 evidence exists and Rob accepts the exact
refactor plan produced by M3 — the tracked human act is `M4-PLAN-APPROVAL`.
<!-- FIDO-HUMAN-ACT:M4-PLAN-APPROVAL -->

## M1 — Source Diet

**Purpose:** remove every non-load-bearing byte without reducing accuracy, proof strength, or current
comprehension.

Git owns history. Current source must not explain what the code used to be.

### Default `.v` comment law

Applies to every tracked `.v` file, including proof gates and e2e fixtures:

- one physical line;
- at most 120 characters, including comment delimiters;
- at most one sentence;
- one current local fact;
- no repair, migration, candidate, former-name, or historical narrative.

Adjacent comment blocks separated only by whitespace count as one logical block. A paragraph may not be split
into many short comments to evade the rule.

Comments that only restate a name, definition, theorem statement, or obvious proof step are deleted. Section
banners, comment art, theorem inventories, consumer lists, repeated one-authority claims, and prose that
belongs to the FCB are deleted.

### Rare exception law

A longer comment survives only when it explains one of these current needs:

```text
invariant-not-expressed-by-type
trust-or-effect-boundary
non-obvious-proof-plan
rocq-limitation-forcing-shape
```

Each exception:

- is attached to one named declaration or module;
- has one row in a canonical checked exception ledger created by the M1 contract;
- uses at most four physical lines;
- keeps every line at or below 120 characters;
- states why the type, theorem statement, or name cannot carry the fact;
- contains no archaeology.

The exception gate is bidirectional: an exception comment without a row fails; a row without its exact comment
fails; a row whose declaration no longer exists fails; duplicate ownership fails; an over-limit exception
fails.

A large exception ledger is evidence that M1 failed.

### File and declaration law

Delete every file, definition, theorem, fixture, alias, wrapper, script, report and abstraction that is not:

1. on the certified correctness path;
2. enforcing a proved restriction or live governance rule;
3. defining an explicit unsupported boundary;
4. required evidence for a current accepted contract.

A gate entry does not give a theorem purpose.

Do not minify proofs, shorten good names, hide structure in broad automation, or merge distinct concepts to
reduce bytes.

### M1 evidence

Capture before and after:

- total tracked bytes;
- bytes by file and file kind;
- `.v` comment bytes;
- `.v` non-comment bytes;
- live-document bytes;
- tool and build bytes;
- declaration and theorem counts;
- compressed archive size;
- every deleted file and declaration with its exact disposition;
- every surviving comment exception.

There is no arbitrary byte quota. Every byte must earn its place.

## M2 — Build Observatory

M2 measures. It does not restructure.

Run in the pinned environment and record:

- cold full-build wall and CPU time;
- warm no-change time;
- common incremental times after touching each root module;
- per-module Rocq compile time;
- the Dune dependency graph;
- the critical path;
- the downstream rebuild set for each module;
- Docker stage timing and cache hit/miss state;
- extraction, plugin, Go, e2e and every policy-gate time;
- peak memory where practical;
- repeated work across Make targets, Buildx stages and the pre-commit hook.

Analyse Git history over the accepted implementation range:

- edit frequency by file;
- files changed together;
- common edit shapes;
- weighted rebuild cost — edit frequency multiplied by downstream build cost;
- large serial units;
- false dependencies and broad imports;
- proof families that can check independently without splitting semantic ownership.

Distinguish, always by name:

```text
partial edit feedback
full acceptance
cold build
warm build
no-op build
```

Under one minute for the common edit loop is a goal, not permission to omit evidence.

M2 produces evidence and recommendations only.

## M3 — Tool and Build Architecture Audit

Inventory every Python tool, shell tool, Make target, pre-commit action, Docker stage, Dune alias, Rocq gate,
extraction step, generated-output check and staged-snapshot check.

For each, record its exact purpose, the contract or policy it enforces, its inputs and outputs, its
environment, its dependencies, its cache inputs, its failure behaviour, its negative controls, its overlap
with other checks, and its current owner.

Delete or propose consolidation for:

- duplicate scanners;
- weaker checks subsumed by stronger ones;
- repeated source-enumeration logic;
- host checks whose policy logic belongs in the pinned Buildx environment;
- targets that rebuild the same theory or artifact independently;
- helpers with no distinct invariant;
- ad hoc branches outside one acceptance graph.

Host work may read the Git index and export the exact staged snapshot. Proof and policy logic normally runs in
the pinned environment against that snapshot.

M3 must produce the exact proposed M4 graph and refactor plan. It does not implement the plan.

## M4 — Mechanical Refactor

M4 starts only after Rob accepts the exact plan produced by M3.

The intended shape is:

```text
one exact source or staged snapshot
→ one pinned theory build
→ independent proof, assumption, transport, policy and e2e branches
→ one full acceptance join
```

Requirements:

- one semantic owner for every definition and authority;
- split proof modules only where measured dependency savings exist;
- no duplicate definition or semantic peer;
- no cache key omits a real source, toolchain, flag, target or environment dependency;
- no cached artifact from another snapshot is accepted;
- Make is a small user interface, not a second build graph;
- partial targets state that they are partial;
- the final whole-theory audit remains global;
- generated bytes remain exact;
- the full before-and-after M2 measurements are repeated.

## M-series acceptance gates

Every M candidate preserves:

- zero assumptions;
- all accepted public theorem guarantees;
- constructor and mint topology;
- exact accepted and rejected provenance;
- supported and rejected program sets;
- exact diagnostic results;
- extraction and transport behaviour;
- OCaml transport-only status;
- negative client controls;
- generated Go bytes;
- reviewed runtime output;
- working-tree and staged-snapshot enforcement.

The M-series may delete dead text and code, measure and reshape build dependencies, and refactor proof units
and tooling. It may not change Go meaning, the accepted or rejected program sets, diagnostic results, public
correctness guarantees, trust boundaries, or generated bytes.
