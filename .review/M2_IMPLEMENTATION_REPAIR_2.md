# M2 IMPLEMENTATION REVIEW — BLOCKING — REPAIR 2 — CONSOLIDATED

## Sole authority

This file replaces both:

```text
M2_IMPLEMENTATION_REVIEW_BLOCKING_REPAIR_2.md
M2_REPAIR_2_HOST_PYTHON_ELIMINATION_AMENDMENT.md
```

Give Claude **this file only**.

The host-Python elimination decision is an explicit human-approved M2 scope amendment. It is part of Repair 2,
not optional follow-up work.

All original Repair 2 correctness findings remain mandatory. Where the original Repair 2 text forbids changing
host/container placement, Make's Python boundary, the pre-commit Python path, profile ranking, Python writers, or
the observatory launcher, the host-Python amendment below supersedes that prohibition. No other scope is widened.

The combined required result is:

1. repair the Build Observatory's measurement correctness defects;
2. eliminate every supported host-Python execution path;
3. rerun the complete canonical suite on the resulting containerized architecture;
4. produce one exact implementation candidate followed by one documentation-only freeze.

General gate consolidation, Docker optimization, cache-key optimization, proof splitting, and unrelated build-graph
refactoring remain forbidden.

Use:

```text
/loop 3m
```

Continue until the whole consolidated directive is complete or a real contract conflict blocks progress. Do not
stop after completing only one part.

---

# PART I — HUMAN-APPROVED HOST-PYTHON SCOPE AMENDMENT

# M2 REPAIR 2 — HOST PYTHON ELIMINATION AMENDMENT

## Disposition

Rob explicitly amends M2 scope:

> Project Python must never execute on the host system. Every project-authored Python tool, gate, writer,
> profiler, observatory operation, comparison, and self-test must run inside the pinned Docker/Buildx
> environment. The host may provide only the narrow launcher boundary: POSIX shell, Make, Git, Docker, and
> Docker Buildx.

This amendment is part of M2 Repair 2 and supersedes the earlier rule that M2 measures without changing host /
container placement **only for the exact host-Python boundary described here**.

The prior M2 Repair 2 correctness findings remain in force.

This is a deliberate human scope amendment, not discovery-driven scope creep. General tool consolidation,
Docker-stage optimization, cache-key redesign, proof splitting, and Make/build-graph refactoring remain M3/M4
work unless this amendment requires the smallest direct change to eliminate host Python.

## Exact review basis

```text
Blocked M2 implementation candidate:
  e534b0ae5cc47da510e46583e47f74566589d538

Documentation-only freeze:
  70112fb645db8bb6e4ba8a6499022ffb1970b1d3

Accepted M1 candidate:
  6524b437bd7a7d6b2616563b8789e28a00c7af13
```

Use the current exact Git ref. Do not mix repository states.

## 1. Required end state

The repository must satisfy all of these:

1. No Make recipe executes `python`, `python3`, a Python shebang, or a `.py` file on the host.
2. No pre-commit action executes Python on the host.
3. No host-invoked shell tool executes Python on the host.
4. No documented project workflow instructs a human or Claude to invoke project Python on the host.
5. Every project Python dependency is provided by one pinned container dependency authority.
6. Every Python gate uses the exact working-tree, staged-index, committed-ref, or disposable source view its
   public command claims to inspect.
7. Every public Make target remains available under its existing name unless an accepted contract explicitly
   changes it.
8. `make observe`, including `HELP`, `LIST`, partial runs, full runs, comparison, validation, recording, and
   self-tests, executes its Python only in Docker.
9. `make profile` ranks the Rocq timing log in Docker; it does not export a raw log for host Python processing.
10. Mutating writers such as `fcb-write` run Python in a container and publish their exact outputs through a
    controlled bind mount or exact output transfer.
11. The staged hook runs the **staged copies** of the Python tools and their pinned container definition, not
    working-tree copies.
12. Project-authored `.py` files are non-executable repository data, never host entrypoints.
13. A permanent fail-closed gate proves the no-host-Python boundary in working-tree and staged-snapshot modes.

The preferred ordinary user interface remains Make. Users should not need a host Python installation or project
Python packages.

## 2. Narrow host trust boundary

The supported host prerequisites are:

```text
POSIX shell
Make
Git
Docker
Docker Buildx
ordinary core command-line utilities already required by the launcher path
```

Python is not a host prerequisite.

The host may:

- resolve repository and Git-index identity;
- export the staged index exactly once;
- create and remove temporary directories;
- invoke Docker or Buildx;
- mount the repository, an exported snapshot, the Docker socket, and output directories;
- copy or atomically install exact container-produced outputs;
- preserve the current user and group ownership of published files.

The host may not:

- import a Python module;
- execute a project `.py` file;
- use a Python one-liner;
- install a Python package;
- recompute Python-tool output independently;
- choose a weaker host fallback when Docker is absent.

Docker absence is a hard unsupported boundary for project commands which consume Python.

## 3. One pinned Python dependency authority

Create one basic Python tooling layer, conceptually:

```text
python-tools-base
```

Requirements:

- pin the base image by digest;
- pin the Python runtime version;
- install all third-party Python packages from one checked lock file;
- pin package versions and integrity hashes;
- copy the dependency lock before project Python sources so a normal tool edit does not reinstall dependencies;
- perform no package installation during an ordinary gate, hook, observatory, comparison, or writer run;
- use no host site packages, user packages, virtual environment, or `PYTHONPATH`;
- record the exact Python image/runtime/dependency identity in Build Observatory environment provenance.

Do not add Python to the Rocq runtime layer merely for convenience. Keep the Python tooling layer separate unless
an exact measured dependency proves one shared layer is simpler and does not broaden invalidation.

The current profile stage explicitly says ranking happens on the host because the prover image has no Python.
Delete that topology. Move ranking into a Python tooling stage which consumes the raw profile artifact and exports
both the raw and ranked reports.

## 4. Read-only Python gates

Provide pinned container targets or one pinned policy target for the read-only Python surfaces, including at least:

```text
fmt
names
claims
diet
fcb
Build Observatory validation / comparison / help / list / self-tests
```

Preserve each command's current semantics, negative controls, source view, and failure reason.

A cached Buildx verdict is permitted only where the accepted current contract already permits a cached verdict
and the target's complete input closure is part of the cache key. Do not silently change an always-run control
into a cached control.

Where an accepted gate requires its controls to execute on every invocation, force that exact policy stage rather
than weakening the contract. M2 records the cost. M3 may later propose a sound cached architecture.

Every target must copy or mount all and only the inputs which determine its result. An incomplete `COPY` set which
lets a changed authority reuse a stale green layer is a correctness defect.

## 5. Working-tree path

Working-tree Make targets may invoke Buildx directly against the working-tree context or invoke a pinned runner
container with the repository mounted read-only.

The Makefile should become simple at the Python boundary:

```text
public target
→ Docker / Buildx invocation
→ pinned Python tool in container
```

Do not retain a host Python wrapper around a containerized inner tool.

The current host Python filter in `make check` must be removed or executed inside a pinned container. Preserve the
current exact working-tree inventory semantics:

- tracked and untracked-nonignored files are considered;
- an on-disk tracked deletion is not resurrected;
- unreadable present input fails;
- generated-byte comparison still sees the exact claimed working source view.

Do not replace that behavior with an easier but weaker `find`, `git archive`, or ignored-read failure.

## 6. Staged pre-commit path

The pre-commit hook remains a small host shell launcher.

It must:

1. require Docker / Buildx;
2. export the Git index exactly once, preserving the current skip-worktree protection;
3. invoke the staged snapshot's own containerized policy path;
4. run proof, e2e, pristine materialization, and generated comparison against that exact exported staged context;
5. remove temporary state;
6. never invoke Python on the host.

The staged policy build must consume:

- the staged Python sources;
- the staged dependency lock;
- the staged Dockerfile or exact staged container authority;
- the staged FCB and review data;
- the staged source tree.

A staged edit which breaks or weakens a Python gate must be evaluated by that staged gate and its staged controls,
not by a safe working-tree image.

Do not solve this by invoking a prebuilt working-tree policy image over staged data unless the current contract is
explicitly amended to trust that image. The proposed commit must contain the checker being evaluated.

## 7. Mutating Python tools

Build contexts are immutable. Python writers therefore need a controlled publication edge.

For `fcb-write` and any other Python writer:

- run the writer in the pinned Python container;
- write first to an isolated output directory;
- validate the complete output set before publication;
- publish exact bytes through one controlled bind-mounted or output-copy path;
- preserve ownership and modes;
- never allow partial publication after a failed writer;
- never run a second host implementation which reconstructs the files.

The writer's check mode and write mode must share one implementation of the generated result.

Do not add general writer infrastructure beyond what current tools require.

## 8. Build Observatory runner

`make observe` must not require host Python.

Use one pinned observatory-runner container. It may invoke the host Docker daemon through the mounted Docker
socket and Docker / Buildx CLI inside the container.

The host Make target may:

- build or load the pinned runner image;
- run it with the exact repository path, Docker socket, output path, UID, GID, and requested Make variables;
- return its exit status.

The runner container owns:

- registry parsing;
- selector expansion;
- scenario planning;
- cache-cut control;
- disposable worktrees or source copies;
- timing;
- raw logs;
- semantic validation;
- comparison;
- canonical recording;
- generated help and listing output.

Do not use Docker-in-Docker with an independent daemon. The runner should address the same declared Buildx
builder and cache authorities the real project commands use.

Record the runner image digest, Docker / Buildx client identity, builder identity, source view, effective
concurrency, and dependency-lock identity in every observation.

The deterministic observatory self-test runs inside the Python container without invoking Docker or Rocq from
inside the test. The host still uses Docker to start that test container. Mock or inject Docker-facing operations;
do not allow a unit control to remove a real builder.

## 9. Host-Python boundary gate

Add one fail-closed checker, run inside the pinned Python container, which proves at least:

- Make recipes contain no host Python command invocation;
- pre-commit and other host hook commands contain no host Python invocation;
- every shell script reachable from a declared host entrypoint is classified and contains no host Python
  invocation;
- current usage documentation contains no supported host-Python command;
- project `.py` files are not executable;
- every public Python-consuming command resolves to a pinned container target or runner;
- no fallback says "use host Python when Docker is unavailable";
- the staged hook evaluates the staged Python/container sources.

Do not use a raw repository-wide substring ban. `Dockerfile`, Python sources, lock files, and prose explaining the
boundary legitimately contain `python`. Parse or classify actual execution surfaces.

Use stable paths, target IDs, registry IDs, and anchors. Do not identify commands by source line numbers.

## 10. Required controls

Add must-fail controls for:

- `python3 tools/naming-gate.py` inserted into a Make recipe;
- a Python one-liner inserted into `make check`;
- host Python inserted into the pre-commit hook;
- a host-invoked shell helper which calls Python;
- an executable project `.py` file;
- usage prose which instructs `python3 tools/...`;
- an unpinned Python base image;
- an unpinned third-party package;
- package installation during an ordinary gate run;
- a staged hook which uses the working-tree Python image;
- a container target whose `COPY` set omits one authority consumed by its tool;
- a Docker-unavailable fallback to host Python;
- a mutating writer which publishes before validation;
- an observatory self-test which calls the real Docker CLI;
- `make observe` invoking host Python.

Add must-accept controls for:

- a Make target which invokes only a pinned Buildx policy target;
- a staged hook which exports once and invokes the staged container path;
- a non-executable `.py` tool copied into the pinned image;
- a writer which publishes a complete validated container-produced output;
- an observatory runner container using the host Docker socket;
- a host shell diagnostic which uses no Python.

Every new root helper must be mutation-proved load-bearing. Deleting the exact boundary rule must make its named
controls fail.

## 11. Documentation and governance amendments

This change must be recorded as an explicit M2 scope amendment.

Update:

- `.review/M2_BUILD_OBSERVATORY.md`;
- the M2 obligation matrix;
- the suite registry and generated help;
- `.review/M_SERIES_PLAN.md`, removing host-Python placement from deferred M3 work while retaining all other
  host/container architecture work in M3;
- `.review/NEXT_STEPS.md`;
- `.review/REVIEW_REQUEST.md`;
- `CLAUDE.md`, with one terse durable operating rule;
- every live FCB authority or toolchain-evidence statement which currently names host Python or a host Python
  dependency.

The concise `CLAUDE.md` rule should be equivalent to:

```text
Never run project Python on the host. Use the repository Make targets: project Python and its dependencies run
only in the pinned Docker / Buildx environment. The host boundary is shell, Make, Git, Docker and Buildx.
```

Do not copy the container target inventory into `CLAUDE.md`.

If the current FCB would forbid this scope change or describes host execution as a fixed point, stop and identify
the exact rule and proposed amendment. Do not work around it.

## 12. Observatory registry and measurements

After migration:

- update the command registry to the new real execution topology;
- retain stable public command IDs where their user-visible meaning did not change;
- add distinct derived IDs for container policy stages only where they are independently measurable;
- remove obsolete host-Python stages;
- rerun the complete canonical suite from the repaired candidate;
- do not compare the new topology as directly equivalent to the old host-Python topology unless the metric
  identity and environment compatibility rules allow it;
- keep the existing round-2 numbers as exploratory Git history, not canonical post-amendment evidence.

The canonical M2 observation must describe the post-migration architecture.

## 13. Scope limits

This amendment authorizes only the changes required to establish and prove the no-host-Python boundary.

It does not authorize:

- merging unrelated gates;
- changing theorem or proof code;
- weakening controls;
- changing program meaning or generated bytes;
- Dockerfile stage reordering for speed;
- general cache-key optimization;
- replacing the mutation harness;
- broad Makefile cleanup unrelated to Python execution;
- proof partitioning;
- M3 or M4 implementation.

A simpler Makefile is an intended consequence at the Python boundary. Complete Make/build-graph simplification
remains M3.

If eliminating host Python exposes a separate build-architecture defect, record it with evidence and assign it to
M3 unless it makes this boundary impossible or false.

## 14. Work order

1. Install this amendment in the M2 authority and reopen affected obligations.
2. Inventory every current host Python invocation and every Python dependency.
3. Establish the pinned Python dependency layer and lock.
4. Move read-only working-tree gates.
5. Move staged-hook gates while preserving exact staged provenance.
6. Move profile ranking.
7. Move mutating writers.
8. Move the Build Observatory launcher and self-tests.
9. Add the permanent host-Python boundary gate and controls.
10. Remove every host Python invocation and host Python usage instruction.
11. Run full working-tree and staged-snapshot checks.
12. Rerun the corrected canonical observatory suite.
13. Produce one exact implementation candidate and later documentation-only freeze.

Do not retain compatibility aliases or host fallbacks.

## 15. Definition of done

The amendment is complete only when:

- a machine with no host Python can run every supported Make target and the pre-commit hook, given the declared
  shell / Make / Git / Docker / Buildx prerequisites;
- `make observe HELP=1`, `LIST=1`, partial runs, full runs, comparison, self-tests, and recording work without
  host Python;
- all Python dependencies are pinned in one container authority;
- every Python-consuming source view is exact;
- staged Python changes are evaluated as staged changes;
- all no-host-Python controls and mutations pass;
- generated artifacts and runtime behavior remain unchanged;
- a new post-migration canonical observation is recorded;
- no compatibility host path remains.

Only Rob accepts M2.


---

# PART II — ORIGINAL M2 REPAIR 2 CORRECTNESS DIRECTIVE

The following original directive remains in force except where PART I explicitly supersedes its host/container
scope restriction.

# M2 IMPLEMENTATION REVIEW — BLOCKING — REPAIR 2

## 0. Disposition and exact review basis

**M2 implementation candidate `e534b0ae5cc47da510e46583e47f74566589d538` is BLOCKING.**

It becomes the **second blocked M2 implementation candidate**.

Documentation-only freeze `70112fb645db8bb6e4ba8a6499022ffb1970b1d3` is not a separate implementation
candidate.

Exact review basis:

```text
Uploaded snapshot: fido-main - 2026-07-30T074245.738.zip
Uploaded Git head / documentation-only freeze:
  70112fb645db8bb6e4ba8a6499022ffb1970b1d3

Blocked M2 implementation candidate:
  e534b0ae5cc47da510e46583e47f74566589d538

Previous blocked M2 implementation candidate:
  8325ddb9ee2dcb1087dbe22d754b9a7d4c5a3b43

M2 authority:
  .review/M2_BUILD_OBSERVATORY.md

Repair-1 authority:
  .review/M2_IMPLEMENTATION_REPAIR_1.md

Cache-cut amendment:
  .review/M2_REPAIR_1_CACHE_CUT_AMENDMENT.md

Accepted review basis:
  .review/REVIEW_BASIS.md
```

Use this exact ref only. Do not reset, rebase, rewrite history, or mix code, FCB, registry, observation, or
review evidence from another ref.

C4, M0, and M1 remain accepted and are not reopened.

**M2 Repair 2 is the sole permitted implementation work.**

M3, M4, C5 Step 0, C5, and all feature work remain forbidden.

Use:

```text
/loop 3m
```

Continue until this exact repair is complete or a real M2 contract conflict blocks progress. Do not stop for
an intermediate green self-test, a partial timing run, one corrected metric family, or routine progress.

When complete or genuinely blocked, notify Rob with the notification tool.

---

## 1. What Repair 1 got right

Keep the framework. Do not replace it with a second timing system.

The permanent shape remains:

```text
one suite registry
one observatory tool
one Make target
one tracked canonical observation
one ignored local-run area
Git history for historical observations
```

Repair 1 made substantial progress:

1. `make observe` remains the one public entry point.
2. `ONLY`, `SCENARIO`, `BASE`, `COMPARE`, `RECORD`, `LIST`, and `HELP` use one tool and registry.
3. The registry covers public Make targets, named pre-commit stages, Docker stages, setup paths, and analysis
   commands.
4. Derived Docker stages now derive their producing parent relation from command targets and the Docker stage
   graph rather than restating every parent-scenario pair.
5. Group selection, unknown selectors, catalog-only commands, and partial-recording boundaries are materially
   stronger.
6. Per-command measurement chains replaced the first candidate's scenario-wide shared chain.
7. Incremental edit bytes now differ across commands and runs.
8. The runner distinguishes stable infrastructure authorities from project-result authorities.
9. Setup commands use disposable Docker and Git environments.
10. The tool retained a complete local-run and tracked-observation schema rather than only a prose report.
11. The repaired run retained module timing, dependency data, history analysis, repeated-work observations,
    cache-stage events, and recommendations.
12. The tool repeatedly refused its own bad candidate observations. That is good behavior.

The freeze reports one retained run with 719 samples and no command failure. That run contains useful exploratory
evidence, but the blockers below mean it is not yet accepted canonical timing evidence.

### 1.1 Useful exploratory findings

The current observation strongly suggests important later work:

```text
make.check:
  about 245 seconds both project-cold and warm-no-op

precommit.full warm:
  about 107 seconds

precommit.mutation warm child:
  about 71.5 seconds

precommit.naming warm child:
  about 27.3 seconds

make.prove:
  about 129.8 seconds project-cold
  about 1.6 seconds warm-no-op
  about 116–121 seconds after common .v edits

measured Rocq module critical path:
  about 15 seconds
```

These copied figures are explanatory only. The observation owns the exact samples.

The contrast is valuable: Docker project layers often cache well, while host-side policy work and broad
invalidation dominate ordinary feedback. But the current working-tree totals are likely inflated by the
observatory's own local output, and several labels still overstate what was proved. Do not implement an
optimization from these numbers during M2.

---

# 2. Strict scope

Repair 2 repairs the measurement facility and regenerates trustworthy evidence.

It may change:

- `tools/build-observatory.py`;
- `.review/BUILD_OBSERVATORY_SUITE.json`;
- `.review/M2_BUILD_OBSERVATORY.md`;
- `.review/M2_IMPLEMENTATION_REPAIR_2.md`;
- `.review/M2_OBLIGATION_MATRIX.tsv`;
- `.review/M2_RECOMMENDATIONS.tsv`;
- `.review/OPEN_QUESTIONS.md`;
- `.review/REVIEW_BASIS.md`;
- `.review/NEXT_STEPS.md`;
- `.review/REVIEW_REQUEST.md`;
- the observatory-specific entries in `tools/gate-mutation-test.py`;
- inert observatory anchors or wrappers in `.githooks/pre-commit`;
- the narrow `make observe` and `make observatory` wiring;
- `.dockerignore`, `.gitignore`, and exact temporary-output containment required to make measurement inert;
- typed FCB reference rows required by those exact changes;
- `.review/BUILD_OBSERVATION.json` only in the final documentation-only freeze.

It may not:

- change any tracked `.v` file;
- change a theorem, proof, constructor, capability, semantic authority, accepted or rejected program set, or
  diagnostic result;
- change extraction, rendering, transport, generated Go, or runtime behavior;
- optimize the Dockerfile, Make graph, pre-commit graph, policy gates, proof layout, or cache keys;
- merge or remove measured commands because they are slow;
- split proof modules;
- implement an M3 or M4 recommendation;
- rewrite `life.md`.

M2 measures and reports. It does not optimize.

---

# 3. Blocking finding A — the deterministic self-test invokes Docker

## Contract violated

The M2 contract requires:

```text
tools/build-observatory.py --self-test
```

to run deterministic fixtures without Docker or Rocq.

The current self-test calls `release_isolation`, which invokes:

```text
docker buildx rm
```

The independent review environment has no Docker command. The self-test raises `FileNotFoundError` instead of
running its deterministic controls.

This is a direct false claim in M2-03 and in the permanent observatory gate.

## Required repair

External command execution must be injected or replaced by a deterministic fake in self-tests.

The self-test must:

- execute successfully when `docker`, Rocq, Dune, Go, and Git worktree support are absent;
- test successful isolation cleanup through a fake command runner;
- test failed cleanup and leak reporting through the fake runner;
- never create or remove a real builder;
- never inspect the developer's actual Docker configuration;
- never leave a process, builder, directory, or Git state behind.

The live runner still uses the real external command path. The test and live paths share the same decision logic;
only the effect implementation differs.

Add controls proving:

- Docker absence does not stop self-tests;
- a fake cleanup failure is reported;
- a fake successful cleanup is accepted;
- a self-test cannot silently fall back to the ambient Docker command.

Add the root helper to the mutation harness.

---

# 4. Blocking finding B — sample, parent, and prime identities are not exact retained objects

## Contract violated

M2-05 and M2-07 require exact sample and cache-prime provenance.

The observation has no top-level `run_id` and no per-sample `sample_id`.

`prime_sample_id` currently stores a metric-class string such as:

```text
make.prove|project.cold.prover|-|-|host-wrapper
```

That is not the identity of one retained sample. It omits:

- run identity;
- sample index;
- source identity;
- builder identity;
- cache-chain identity;
- exact cache cut;
- temporal predecessor identity.

The record-time check only proves that some retained metric with that class is cold and successful. It does not
prove that the reused sample descends from the exact prime which populated its cache.

Derived child samples also lack an exact parent-sample identity.

The current `cache_namespace` values are logical labels. All commands use one BuildKit store. Do not describe a
label as physical cache isolation.

## Required intrinsic object

Create one exact retained run/sample topology.

### Run identity

Every local and canonical observation retains one exact `run_id`.

It must:

- be collision-safe;
- identify the local bundle;
- appear in every sample ID;
- survive into the tracked observation;
- never be inferred from a raw-log file name.

### Sample identity

Every sample retains one unique `sample_id`, derived from or containing:

```text
run ID
command ID
scenario ID
sample index
edit ID, when present
direct or derived role
exact parent sample, when derived
resource scope
measurement kind
```

Do not use a summary key as a sample identity.

### Derived parent

Every derived Docker or pre-commit sample retains:

```text
parent_sample_id
```

which names the exact direct retained sample that produced it.

The validator proves:

- the parent exists;
- the parent is direct;
- command and scenario context agree;
- the child is a stage or anchor actually observed within that parent's raw evidence;
- the parent precedes the child in the retained causal record.

### Prime relation

Every cached, warm, or incremental sample which reuses a project result retains:

```text
prime_sample_id
```

which names the exact retained direct project-cold sample that populated that command's cache chain.

The validator proves:

- the prime exists in the same observation;
- it has status `ok`;
- it is a direct sample;
- it belongs to the same command;
- it has the exact required project-cold cut and root set;
- it measured the same source or the exact declared pre-edit source;
- it used the same builder and cache-chain identity;
- it precedes the dependent sample;
- the dependent sample's project cache authority actually says `reused`.

A stable toolchain cache does not require a project prime.

### Cache-chain identity

If the implementation does not create a physically isolated BuildKit store per command, rename
`cache_namespace` to an honest logical identity such as:

```text
cache_chain_id
```

The record must not claim physical namespace isolation which does not exist.

The cache-chain ID still distinguishes causal chains and participates in prime validation.

## Required controls

Add must-fail controls for:

- duplicate sample IDs;
- missing run ID;
- derived child with no exact parent;
- child naming a parent from another run;
- cached sample naming a metric class instead of a sample;
- cached sample naming another command's prime;
- cached sample naming a later sample;
- cached sample naming a prime with another source;
- cached sample naming a prime with another builder or chain;
- stable-only cache reuse incorrectly requiring a project prime;
- logical cache-chain label represented as a physically isolated namespace.

Add must-accept controls for:

- one exact direct cold prime and one exact cached dependent;
- one derived stage with one exact parent;
- two commands sharing stable infrastructure while keeping distinct project cache chains.

Mutation-test the root identity and predecessor checks.

---

# 5. Blocking finding C — source-view identity and disposable materialization are not exact

## Contract violated

M2-05, M2-09, M2-14, and M2-15 require the measured source to be retained exactly.

`content_digest` currently hashes bytes from the ordinary working tree. It does not retain:

- Git mode;
- file type;
- symlink target identity;
- staged-index blobs and modes;
- a tracked deletion as an explicit absence.

A chmod-only change produces the same digest. A staged index which differs from the working tree is described by
the working-tree digest.

The pre-commit path measures an exported staged index, but the direct sample's source digest is computed from the
ordinary working tree.

`disposable_copy` starts from committed `HEAD` and overlays files. A tracked file deleted from the selected source
view can remain present in the disposable copy.

The digest and the materialized source are therefore parallel, disagreeing authorities.

## Required intrinsic source-view object

Implement one exact source-view object used for both:

```text
identity
materialization
```

Required source-view kinds:

```text
committed-tree
staged-index
working-tree
staged-index-export
disposable derivative of one exact source view
```

### Committed tree

Retain exact Git tree identity, modes, path set, blob identities, and symlink identities.

### Staged index

Retain exact index path set, stage-0 blob IDs, modes, and symlink targets.

The source digest must describe the index, not the working tree.

### Working tree

Retain an exact sorted relation over:

```text
path
file kind
mode
symlink target, when applicable
byte digest, for regular files
absence of tracked paths deleted in the working tree
untracked nonignored paths
```

Use `lstat`. Do not follow a symlink and hash the target as though it were a regular file.

### Materialization

The same source-view implementation creates the disposable tree.

It must:

- reproduce exact paths and supported modes;
- reproduce symlinks as symlinks;
- omit tracked files deleted in the selected view;
- include untracked nonignored files for a working-tree view;
- verify the materialized tree's source-view identity equals the selected source-view identity before running
  a command.

A disposable derivative retains its exact predecessor source-view ID plus its deterministic edit ID.

## Required controls

Add must-fail controls for:

- staged index and working tree differ but share one source digest;
- a tracked deletion remains in the disposable copy;
- a rename is materialized as two files;
- a mode-only change is invisible;
- a symlink is followed and treated as a regular file;
- a disposable tree's identity differs from its retained predecessor plus edit;
- a pre-commit sample carries a working-tree identity.

Add must-accept controls for exact committed, staged, dirty-working-tree, deletion, mode, symlink, and
untracked-file fixtures.

Mutation-test the source identity/materialization relation.

---

# 6. Blocking finding D — cache authority records overclaim what was observed

## Contract violated

M2-06 and M2-07 require exact, non-overlapping cache meanings.

The suite's project-cold scenarios declare these project cache authorities `empty` before the run:

```text
buildkit_project_layers
dune_build
generated_intermediate
go_build
```

But canonical stage evidence often shows several project stages were cache hits while only the named root rebuilt.

Examples:

- `make.check` cold from `generated-artifact` observes upstream project stages as hits;
- `make.e2e` cold from `go-e2e` observes `emit` and `generated-module` as hits;
- `make.regenerate` cold from `sync` observes its upstream project stages as hits.

The coarse authority says all project layers are empty while stage evidence says many are present.

`observe_cache_after` then marks every project authority `primed` whenever any stage rebuilt. A `make.prove` run
can therefore claim `go_build` and `generated_intermediate` became primed even though no Go or generated stage
ran.

One field is stating several different facts.

## Required repair

Per-stage BuildKit evidence owns BuildKit stage truth.

Do not retain one coarse `buildkit_project_layers` value if it cannot express a mixed state.

Use one of these correct shapes:

1. remove the coarse authority and use the exact stage map; or
2. define command-specific cache authorities with one exact meaning and prove their derivation from the stage map.

For non-BuildKit authorities such as Dune, Go build cache, generated intermediates, package caches:

- record a transition only when that exact cache was touched and the runner established its state;
- use `not-applicable` when the command does not touch it;
- use `uncontrolled` or `unavailable` when the runner cannot establish it;
- never infer a state from elapsed time;
- never mark every cache primed because one stage rebuilt.

`cache_before` and `cache_after` must agree with the retained stage evidence and command path.

## Required controls

Add must-fail controls for:

- project authority `empty` while an upstream project stage is observed hit;
- `make.prove` marking Go cache primed;
- one rebuilt stage marking every project cache primed;
- untouched cache reported empty instead of not-applicable;
- cache transition inferred only from elapsed time;
- stage map and authority map disagree.

Add must-accept controls for mixed hit/rebuilt stage maps and commands which touch only one cache family.

Mutation-test the transition derivation.

---

# 7. Blocking finding E — the invalidation root can understate what rebuilt

## Contract violated

The cache-cut amendment requires the declared project invalidation root and its graph descendants to describe the
actual rebuild.

`make.audit-fresh` runs two independent forced roots:

```text
prover
go-e2e
```

The registry declares only:

```text
project.cold.prover
```

The observation shows both roots rebuilt.

`check_cut_observed` proves the named root rebuilt and a stable ancestor did not. It does not reject an undeclared
independent root.

A synthetic sample declaring only `prover` while also rebuilding `go-e2e` is accepted.

## Required root-set model

A cache cut owns an exact nonempty set:

```text
invalidated_roots
```

Do not force compound commands into one-root names.

For example, use a stable scenario identity such as:

```text
project.cold.audit-fresh
```

with exact roots:

```text
prover
go-e2e
```

The validator proves:

- every declared root rebuilt;
- every other rebuilt project stage is a graph descendant of at least one declared root;
- no undeclared independent root rebuilt;
- every required stable ancestor remained a hit;
- comparison fingerprints the exact root set and stable boundary.

Do not make `make.audit-fresh` catalog-only. It is a real and important supported command.

## Required controls

Add controls for missing one root, extra independent root, allowed descendant rebuild, changed root set, and
comparison across different root sets.

Mutation-test exact root closure.

---

# 8. Blocking finding F — incremental samples do not prove the intended invalidation happened

## Contract violated

M2 §3A.6 requires the runner to verify the intended rebuild actually ran, not only that edit bytes differ.

The current implementation checks that source digests differ within and across metric identities. It does not
validate that a `.v` edit rebuilt the expected project root or that a non-build-input edit remained cached.

The current observation happens to show sensible effects for several edit shapes. The gate would still accept a
future all-cache-hit `.v` incremental sample if its bytes were unique.

## Required relation

Give each command/edit relation one exact expected stage effect.

Prefer derivation from:

```text
the exact edit target
the Docker build context and ignore rules
the command's build target(s)
the Docker stage graph
the Make or hook execution path
```

Do not hand-copy a second stage list when the relation can be derived.

Where derivation is not possible, the registry may declare a narrow expected effect with one owner and controls.

For every incremental direct sample, validate:

- the edit was applied to the intended exact source view;
- the source identity changed;
- the expected first invalidated stage or non-build path is observed;
- required downstream project stages rebuilt;
- stages expected to stay cached did so where observable;
- the edit was restored exactly;
- the next sample cannot reuse the prior sample's exact edit result.

Documentation and policy edits which are outside a Docker input may correctly leave Docker stages hit. The record
must state that expected effect rather than treating every incremental sample as a rebuild.

## Required controls

Add must-fail controls for:

- `.v` edit whose expected proof root stayed cached;
- tool edit whose expected policy command never ran;
- doc edit incorrectly claiming a project rebuild;
- source bytes changed but no expected stage or host path observed;
- expected stage list copied in two authorities and allowed to drift.

Add must-accept controls for one `.v`, one tool, and one documentation edit relation.

Mutation-test expected-effect validation.

---

# 9. Blocking finding G — elapsed wall time and aggregate BuildKit work are collapsed

## Contract violated

M2 §3A.7 states that the sum of BuildKit step durations is aggregate work, not elapsed wall time.

Derived BuildKit samples currently retain:

```text
wall_ns: null
aggregate_step_ns: <sum>
```

`summarise` falls back to `aggregate_step_ns` and writes that value into fields named:

```text
median_wall_ns
min_wall_ns
max_wall_ns
```

The comparator and report then describe aggregate step work as elapsed wall time.

A parallel stage can have aggregate work greater than elapsed time. These are different measurements.

## Required typed metric model

Every sample and summary retains one measurement kind:

```text
wall_elapsed
aggregate_step_work
cpu_user
cpu_system
rss_peak
duration_interval
```

At minimum, direct commands use `wall_elapsed`, and derived BuildKit step totals use `aggregate_step_work`.

Metric identity includes the measurement kind.

Summaries use honest names. Do not put aggregate work into a `*_wall_ns` field.

Comparison:

- compares only like kinds;
- labels aggregate work as aggregate work;
- reports unlike kinds as incomparable;
- preserves the raw stage events from which aggregate work is derived.

## Required controls

Add a parallel-step fixture where aggregate work differs from elapsed time and prove the two cannot be pooled or
mislabelled.

Mutation-test metric-kind separation.

---

# 10. Blocking finding H — zero durations are used for work below clock resolution or work not timed

## Contract violated

M2 says zero is a measured claim and is false when work occurred.

The current canonical observation contains zero-duration samples:

- `analysis.dune-graph` is emitted with `wall_ns: 0` although graph work occurred;
- fast pre-commit anchors can quantize to zero under the current hook clock.

## Required representation

### Untimed derived artifact

If Dune graph derivation is not timed, represent it as an untimed artifact. Do not create a zero wall sample.

If it is timed, measure it with a monotonic high-resolution clock and retain a real duration.

### Below-resolution interval

When an external anchor's clock cannot resolve the duration, retain an interval or explicit bound, for example:

```text
lower_ns
upper_ns
below_resolution: true
```

Do not store `0` as elapsed time.

Summaries and comparisons must understand interval measurements. They may report “below resolution” and must not
invent an exact percentage delta from zero.

## Required controls

Add must-fail controls for untimed work represented as zero and sub-resolution work represented as exact zero.

Add must-accept controls for an untimed artifact and a below-resolution interval.

Mutation-test zero-claim rejection.

---

# 11. Blocking finding I — environment is captured before the measured builder exists and before stable preflight

## Contract violated

`run_observation` currently captures:

```text
environment(root)
subject(root)
```

before calling:

```text
ensure_observatory_builder()
```

On first use, the observation can describe a missing or different builder, then create another builder and run the
suite.

The tool contains `toolchain_prime`, which matches the cache-cut amendment's stable preflight, but it is not used.

`reset_observatory_cache` has no live caller and would prune the whole observatory cache, contrary to the
project-cold cache-cut model.

## Required order

Canonical execution order:

```text
resolve exact source view
ensure exact observatory builder
prime or verify stable infrastructure outside the measured interval
capture environment from that exact builder
begin project measurement chains
```

Record:

- exact builder identity;
- whether preflight was required;
- stable image and toolchain identities;
- that bootstrap and pulls occurred outside measured intervals;
- actual effective concurrency.

If `toolchain_prime` is the correct root operation, wire and test it. Otherwise replace it with one exact root
operation and delete the unused function.

Delete `reset_observatory_cache` unless a distinct noncanonical bootstrap diagnostic consumes it. Canonical
project-cold work must not erase stable infrastructure.

## Required controls

Add controls for first-use builder creation, wrong builder read, preflight pull outside interval, pull inside
interval, and unused destructive reset.

Mutation-test preflight ordering.

---

# 12. Blocking finding J — observatory output changes the source trees and timings it observes

## Contract violated

M2-16 requires instrumentation to preserve normal command input and behavior.

The observatory writes growing local bundles under:

```text
.build-observatory/runs/
```

inside the repository while the suite is running.

That namespace is Git-ignored but is not excluded from all measured input paths:

- it is not excluded by the current Docker context rules;
- the mutation harness's repository copies can include it;
- later samples can see more raw logs than earlier samples;
- one exact Git subject can produce different timings depending on old local observation residue.

The current recommendation reports that mutation fixtures copied large observatory bundles. This means the
observer changed the observed command's input and likely inflated `make.fcb`, `make.check`, and pre-commit totals.

## Required inert containment

During measurement:

1. write the active raw bundle outside every measured source tree and outside every Docker context;
2. or materialize every measured source view from an exact source object which excludes observatory residue.

After the run completes or is cancelled, publish the local bundle into the ignored local-run location.

Also:

- exclude `.build-observatory/` from Docker contexts if the repository-local location remains;
- prevent M2 instrumentation residue from entering mutation fixtures;
- do not redesign the mutation harness here;
- retain the underlying copy architecture and optimization question as an M3 recommendation;
- require canonical recording to prove local observatory residue did not affect command input.

This is M2 measurement containment, not M3 optimization.

## Required controls

Add a fixture with a large old local observation bundle and prove:

- source identity for the measured view is unchanged;
- Docker context identity is unchanged;
- mutation-fixture input is unchanged;
- canonical metric relations are unchanged;
- the completed local bundle is still published and readable.

Mutation-test residue containment.

The current canonical observation must be discarded and rerun after this correction. Do not retain polluted
working-tree totals as accepted evidence.

---

# 13. Blocking finding K — comparison does not use the complete observation validator

## Contract violated

M2-13 and M2-14 require observations to validate before comparison concludes.

`compare` currently checks basic members and recomputes stored summaries. It does not call the complete record-time
validation.

The independent review removed `cache_before` from a sample. Comparison still returned metric verdicts.

Record-time cache-cut, prime, relation, and source-view checks are not all part of `validate_observation` either.
The system has more than one definition of “valid observation.”

## Required single validator

One complete observation validator owns validity.

It is used by:

```text
recording
loading the tracked canonical observation
loading a local bundle
loading a Git-ref observation
comparison, on both sides
make observatory
```

It validates, from retained data:

- schema version;
- suite or embedded definition identity;
- source-view object;
- run, sample, parent, and prime identities;
- environment and effective concurrency;
- command/scenario/edit/role/scope/measurement-kind identity;
- cache cuts and exact root sets;
- stage evidence and cache authority transitions;
- incremental expected effects;
- exact expected/observed measurement relation and counts;
- raw evidence digests where required;
- summaries;
- completion state;
- canonical recording eligibility when canonical status is claimed.

Historical or local observations must retain enough definition data to validate themselves. Do not reinterpret an
old observation solely through today's registry.

Comparison may apply a current selector after both observations validate. It cannot use selector expansion as a
substitute for observation validity.

## Required controls

Add malformed-observation controls for every required semantic family, including the independently reproduced
missing `cache_before` case.

Mutation-test validator reuse by recording and comparison.

---

# 14. Blocking finding L — exact coverage omits role, exact scope, and measurement kind

## Contract violated

M2 §3A.8 says the exact relation includes role.

The current expected/observed relation checks command, scenario, edit, parent, and a wildcard-like scope relation.
It does not close exactly over:

```text
selected_or_support
exact resource scope
measurement kind
```

A selected derived child can be mislabeled support, or a direct command can be mislabeled BuildKit scope, while
the relation still closes.

## Required exact relation

One exact measurement key contains:

```text
command ID
scenario ID
sample index or exact multiplicity position
edit ID
derived parent command and exact parent sample, when applicable
selected or support role
exact resource scope
measurement kind
```

Recording requires exact equality between the registry-derived required relation and the retained direct/derived
samples:

- no missing entry;
- no extra entry;
- exact sample count;
- exact role;
- exact scope;
- exact kind;
- exact parent producibility.

Do not use a wildcard scope.

## Required controls

Add controls for selected child labeled support, support command labeled selected, direct sample labeled
BuildKit-stage scope, aggregate work labeled wall elapsed, and exact-count mismatch.

Mutation-test the full relation key.

---

# 15. Blocking finding M — scenario authority is duplicated between contract and registry model

## Contract violated

The M2 contract currently says every scenario entry includes:

```text
sample_policy
applicable_groups
```

The repaired registry places sample count and applicability on each command-scenario relation.

The command-scoped relation is the more basic owner: sample count and applicability can differ by command. Keeping
scenario-level copies would create a second authority.

## Required documentation correction

Amend `.review/M2_BUILD_OBSERVATORY.md`:

- scenario entries own scenario meaning, family, cache cut, and canonical status;
- command-scenario relations own applicability and sample multiplicity;
- groups derive from command membership;
- derived child applicability derives from producing parents;
- no `sample_policy` or `applicable_groups` field is required at scenario scope.

Update the review basis, registry schema, controls, and matrix to say one thing.

No FCB amendment is required. This corrects the M2 contract to the accepted repaired architecture.

---

# 16. Dead and misleading tool residue

Repair these as part of the root work:

1. Delete `reset_observatory_cache` unless a live, noncanonical bootstrap diagnostic consumes it.
2. Delete the dead cache-state read/write/check path if it remains reachable only from self-tests.
3. Remove or repair `_scope_of` if its comparison can never match the full metric key. Do not retain an
   unreachable guard as evidence.
4. Remove the unused `parent_id` parameter from raw-log naming or use exact parent-sample identity.
5. Replace the invalid Makefile help example `SCENARIO=cold.cached` with a current registry-owned ID.
6. Search for other observatory functions or constants used only by self-tests or by no live path. Delete them
   unless they define an explicit unsupported boundary.

Do not use this as permission for general M3 tool cleanup. Limit deletion to dead or misleading M2 observatory
paths discovered while repairing the accepted contract.

---

# 17. Recommendations ledger corrections

M2-17 requires recommendations to follow retained evidence and to avoid conclusions stronger than the observation.

## R01

Replace:

```text
cache is not the remedy
```

with a factual statement:

> The current build graph does not realize module-sensitive edit feedback: common `.v` edits trigger roughly the
> same project rebuild despite a much shorter measured Rocq critical path. M3 must determine whether the cause is
> Docker context invalidation, Dune artifact reuse, target factoring, or another cache/build-graph boundary.

Do not decide the remedy in M2.

## R02

Retain the factual warm pre-commit child-stage evidence, subject to the repaired observation.

## R03

Separate two facts:

1. observatory output polluted measured source/copy inputs — an M2 instrumentation defect which Repair 2 fixes;
2. the mutation harness copies broad trees and reruns broad self-tests — an M3 architecture finding.

Do not retain copied-byte or percentage claims unless the exact machine evidence remains in the accepted
observation.

## R04

Retain as an M3 human decision. `build_targets` duplicates target clauses, but Repair 2 must not redesign the
authority here.

---

# 18. Open-question dispositions

These do not block M2.

## OQ-M2-01 — residue authority

Record this recommended M3 disposition:

- do not write an ad hoc `.gitignore` parser;
- if M3 derives ignored residue, use Git's own ignore engine through exact Git queries such as `git check-ignore`;
- until M3, retain the small explicit residue set with exact controls.

Do not implement the M3 decision in M2 beyond the narrow observatory containment required by §12.

## OQ-M2-02 — host versus Buildx observatory

Record this recommended M3 direction:

- consider a small host launcher which drives a pinned inner analysis and validation tool;
- do not assume moving all logic inside a container removes host-side hook instrumentation;
- decide Docker-socket trust explicitly;
- keep the current host tool for M2 unless the accepted M2 contract cannot be satisfied otherwise.

No M2 block depends on this decision.

---

# 19. Obligation-matrix repair

Reopen at least these rows:

```text
M2-02
M2-03
M2-05
M2-06
M2-07
M2-08
M2-09
M2-11
M2-13
M2-14
M2-15
M2-16
M2-17
M2-19
```

Also reopen any other row whose implementation, positive evidence, negative control, mutation control, or gate
changes during Repair 2.

Do not leave a row closed while its cited evidence belongs to the rejected observation.

Each closed row must name:

- the exact repaired implementation surface;
- one positive retained artifact;
- one must-fail control with the expected failure reason;
- one root mutation which proves the rule load-bearing;
- the exact command which executes the evidence.

The claim-matrix gate remains a presence and wiring check. Human review judges whether the named surface is strong
enough.

---

# 20. Canonical observation and freeze topology

The current canonical observation is rejected as acceptance evidence. Preserve it in Git history only.

## Implementation candidate

The repaired implementation candidate contains:

- the repaired observatory tool;
- repaired suite registry;
- repaired contract and review basis;
- open or honestly partial obligation rows;
- corrected recommendations and questions;
- inert source/hook/Make instrumentation;
- no newly recorded canonical observation for itself.

It may retain the prior tracked observation only as a clearly superseded baseline file if the contract requires
one for comparison. It must not present the rejected run as the candidate's accepted canonical observation.

## Measurement

After committing the exact implementation candidate:

1. verify stable infrastructure and the exact builder outside measured intervals;
2. run the complete suite from the exact candidate;
3. retain all local raw evidence;
4. validate the observation through the one complete validator;
5. inspect the generated report rather than trusting the green exit alone;
6. compare selected metrics with the rejected observation only as exploratory context;
7. generate the recommendations from the accepted candidate observation.

## Documentation-only freeze

The later freeze may change only:

```text
.review/BUILD_OBSERVATION.json
.review/M2_OBLIGATION_MATRIX.tsv
.review/M2_RECOMMENDATIONS.tsv
.review/NEXT_STEPS.md
.review/REVIEW_REQUEST.md
```

The freeze:

- names the exact candidate;
- records the exact complete observation;
- closes only rows whose evidence now exists;
- requests human M2 review;
- changes no implementation, registry, contract, source, hook, Make recipe, Dockerfile, proof, or generated
  artifact;
- has no commit after it.

Only Rob accepts M2.

---

# 21. Required verification

Before the implementation candidate:

```text
python3 tools/build-observatory.py --self-test
make observatory
make observe HELP=1
make observe LIST=1

make diet
make fcb
make claims
make names
make check
make regenerate
make regen-guard
make fmt
make audit-fresh
```

The observatory self-test must run successfully with Docker and Rocq removed from `PATH`.

Run the real staged hook against the exact staged snapshot without bypassing it.

After committing the candidate, run at least:

```text
make observe
make observe ONLY=make.prove
make observe ONLY=precommit.prover
make observe ONLY=setup
make observe SCENARIO=project.cold.prover ONLY=make.prove
make observe SCENARIO=project.warm.noop ONLY=make.check
make observe BASE=<rejected observation Git ref or local path>
make observe RECORD=1
```

Use only scenario IDs which the repaired registry lists.

Also prove:

1. Every canonical sample has exact run and sample identity.
2. Every derived sample names one exact parent sample.
3. Every reused project cache names one exact retained prime.
4. Every source view's identity equals the tree actually measured.
5. Every cache authority agrees with exact stage evidence.
6. Every declared root set exactly explains the rebuilt project stages.
7. Every incremental edit exhibits its intended effect.
8. No aggregate step work is labeled wall elapsed.
9. No real or untimed work is represented as exact zero duration.
10. Environment identity is captured after stable preflight from the exact builder.
11. Old local observatory residue cannot affect the measured source, Docker context, or mutation fixtures.
12. Recording, canonical loading, local loading, Git-ref loading, and comparison use one complete validator.
13. Exact coverage includes role, scope, kind, parent, edit, and count.
14. Full and selective runs use the same registry and runner.
15. Partial runs cannot record.
16. Cancellation leaves one valid incomplete bundle.
17. No `.v` file changed.
18. No theorem, proof, constructor, capability, or semantic authority changed.
19. Generated Go, goldens, and runtime output remain byte-identical.
20. M2 recommendations implement no optimization.
21. M3, M4, C5 Step 0, and C5 work did not begin.

The next freeze must quote no copied mutable counts as authority. Point to generated views and the tracked
observation.

---

# 22. Definition of done

Repair 2 is complete only when:

- deterministic self-tests run without Docker or Rocq;
- the exact source-view object owns both identity and materialization;
- exact run, sample, parent, prime, builder, and cache-chain identities are retained and validated;
- cache authorities state only facts the runner established;
- compound cuts use exact root sets;
- incremental edits prove their intended stage or host effect;
- wall elapsed, aggregate work, and interval durations remain distinct;
- no false zero duration remains;
- environment capture follows stable preflight;
- observatory residue cannot affect what is measured;
- one complete validator governs recording, loading, and comparison;
- exact coverage includes role, scope, kind, parent, edit, and multiplicity;
- scenario authority is no longer duplicated;
- dead M2 observatory paths are deleted;
- recommendations state measured facts without choosing M3/M4 remedies;
- the complete suite produces one valid observation for one exact repaired candidate;
- all required checks pass;
- one documentation-only freeze requests human review;
- no commit follows the freeze;
- Claude notifies Rob.

Do not optimize the build in this repair. The expensive numbers are the evidence M3 and M4 need. Preserve them
honestly first.
