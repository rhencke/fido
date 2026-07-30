# M2 — Build Observatory

> **Live checkpoint contract.** Installed by the accepted M1 acceptance closeout directive under Governance
> `D-27` and amendment `FCB-A007-POST-C4-MECHANICAL-SERIES`. Its identity is its Git blob at the exact ref
> resolved for the task; its history is the commit log.
> **M1 is ACCEPTED** at `6524b437bd7a7d6b2616563b8789e28a00c7af13` under `M1-ACCEPT-6524b43`. M2 Build
> Observatory is the sole active implementation work. M3, M4, C5 Step 0 and C5 remain FORBIDDEN.
> **Obligations:** `.review/M2_OBLIGATION_MATRIX.tsv`. **Review basis:** `.review/REVIEW_BASIS.md`.
> Section numbers are the directive's own, so every cross-reference from the matrix and the review basis
> resolves here.

M2 measures and reports. It does not optimize or restructure. Only Rob accepts M2.

---

# 1A. Accepted scope amendment — no project Python on the host

Rob amended M2's scope in `.review/M2_IMPLEMENTATION_REPAIR_2.md` (PART I). This is a deliberate human scope
amendment, not discovery-driven scope creep, and it is part of M2 rather than deferred follow-up work.

> Project Python must never execute on the host system. Every project-authored Python tool, gate, writer,
> profiler, observatory operation, comparison, and self-test must run inside the pinned Docker/Buildx
> environment. The host may provide only the narrow launcher boundary: POSIX shell, Make, Git, Docker, and
> Docker Buildx.

The realized architecture:

```text
Dockerfile:python-tools        the pinned runtime every gate, writer and profiler runs in
Dockerfile:observatory-runner  the one Python image carrying a Docker client, for make observe
tools/python-requirements.lock the one dependency authority — EMPTY, and proved empty
tools/host-python-gate.py      the permanent boundary gate and its adversarial controls
make hostpython                its public entry point; it also runs inside make check and the hook
```

Two consequences are worth stating because they are what make the boundary cheap to keep:

- **Sources are mounted, never copied into a policy image.** A stale green layer from an incomplete `COPY`
  set is therefore unrepresentable rather than something the gate has to detect, and the gate forbids the
  `COPY` to keep it that way. Gates are always-run by construction, not by policy.
- **The project imports the standard library alone.** "No package installation during an ordinary gate run"
  is a property of the image rather than a rule anyone has to remember, and the import-closure check turns
  the empty lock into a claim that fails loudly the moment a dependency appears.

The staged hook builds its image from the **staged** Dockerfile and lock, under a tag content-addressed over
both, so the proposed commit contains the container authority that judges it.

---

# 2. Purpose

Build one permanent, reproducible timing facility for Fido.

The facility must answer:

- How long does each supported command take?
- Which work is cold, warm, cached, or uncached?
- How much time belongs to proof, extraction, transport, Go validation, policy gates, and publication checks?
- Which Rocq modules are slow?
- What is the module dependency graph?
- What is the critical path?
- What rebuild set follows an edit to each module?
- Which files change most often?
- Which files change together?
- Which common edit shapes cause the highest rebuild cost?
- Where does the Make path repeat work also done by Buildx or the pre-commit hook?
- Did a proposed change improve or regress one named target or scenario?
- How does the current tree compare with any tracked historical observation?

M2 measures and reports. It does not optimize or restructure.

---

# 3. Permanent shape

The permanent system has five parts:

```text
.review/BUILD_OBSERVATORY_SUITE.json   one command and scenario registry
.review/BUILD_OBSERVATION.json        one tracked canonical observation
tools/build-observatory.py            one runner, validator, writer, and comparator
.build-observatory/                    ignored local run bundles and raw logs
make observe                          one human and Claude entry point (runs in the pinned runner image)
```

Git history is the historical observation database.

Do not append every run to a tracked growing ledger. Each accepted replacement of
`.review/BUILD_OBSERVATION.json` becomes historical through Git.

M2 also creates:

```text
.review/M2_BUILD_OBSERVATORY.md
.review/M2_OBLIGATION_MATRIX.tsv
.review/M2_RECOMMENDATIONS.tsv
```

`M2_RECOMMENDATIONS.tsv` records measured findings and assigns them to M3, M4, or retain. It contains no
implementation work.

---

# 3A. The repaired measurement model

The first M2 candidate implemented the shape above and got the MEASUREMENTS wrong: it reset and primed once
per scenario and then ran every command in that shared state, so a command labelled cold observed a cache an
earlier measured command had filled. This section states the model exactly, because the shape being right is
not the same as the numbers being true.

## 3A.1 The cache cut — what cold means

Governed by `.review/M2_REPAIR_1_CACHE_CUT_AMENDMENT.md`.

A canonical cold measurement is cold from one declared PROJECT-DEPENDENT INVALIDATION ROOT downward. It is not
cold from the Docker daemon, the builder, the base images, the pinned toolchain or the OS packages. The
observatory measures the cost Fido's repository and build graph create, not network pull latency or one-time
machine bootstrap.

Before every canonical project measurement the builder exists, the base images are local, and the pinned
toolchain layers are available. Registry pulls and builder bootstrap are forbidden inside the measured
interval. Stable ancestors through the declared boundary must remain cache hits; the named root and every
dependent stage must rebuild.

An empty-machine run is `environment.bootstrap` — a diagnostic, never canonical performance evidence, and
never required by `RECORD=1`.

## 3A.2 Scenario families

```text
project.cold.<root>          fresh session; exactly the named root invalidated; ancestors stay hits
project.cached.fresh         fresh session against that command's own completed prime
project.warm.noop            same source and cache, run again with nothing changed
project.incremental.<edit>   from the exact prime, one deterministic edit shape
environment.bootstrap        builder creation, pulls, toolchain acquisition — diagnostic only
```

Isolation is by INVALIDATION, not by namespace: a root forced to rebuild cannot be satisfied by anything an
earlier measured command cached. Commands share immutable infrastructure and never share a project result in a
way that would satisfy another command's declared cold sample.

## 3A.3 Every sample carries its cache cut and what actually happened

```text
cache_cut          stable_through, invalidated_from,
                   registry_pulls_included, builder_bootstrap_included
cache_observation  per stable stage ID: hit | rebuilt | skipped | not-required | unavailable
```

A sample fails validation when a registry pull or builder bootstrap occurs inside the interval, a declared
stable ancestor rebuilds, the named root stays cached, actual stage behaviour contradicts the declared cut, a
cached sample cannot identify its exact prime result, or the cut is absent. Where BuildKit does not expose a
stage's state, record `unavailable` and say why — never infer a hit from elapsed time.

## 3A.4 Cache authorities are exact

One `buildkit_layers` state cannot say both that toolchain layers are primed and that project layers are
empty, so the authorities are split:

```text
buildkit_toolchain_layers   buildkit_project_layers   dune_build   go_build
go_module                   generated_intermediate    apt_download opam_download
```

A state is `empty`, `primed`, `reused`, `not-applicable` or `uncontrolled`, and only when the runner can
ESTABLISH it. A lightweight command that touches no project cache records `not-applicable` — never `empty`.

`cache_after` is observed after the command, never copied from `cache_before`. A command that fills a cache
and reports no transition is stating something false.

## 3A.5 Metric identity

One identity is used by every sample, summary, comparison row, raw-log path and recommendation:

```text
command_id | scenario_id | edit_id or none | derived_parent_id or none | resource_scope
```

Pooling six edit shapes into one median, or one Docker stage observed under four parents into one median,
answers a question nobody asked. A selected derived child is marked selected even when its live parent is
support.

## 3A.6 Incremental samples must be independent

Repeating identical edit bytes in a fresh worktree against one builder cache produces one rebuild and then
cache hits. Each sample therefore applies a DISTINCT deterministic inert edit, owned by the registry with its
own fingerprint, and the runner verifies the intended rebuild actually ran rather than accepting a cached
no-op under an incremental label. Comparison requires the same edit fingerprint.

## 3A.7 Provenance is exact

Every disposable source is created from the SELECTED SOURCE VIEW — working tree, staged index or committed
tree — never silently from `HEAD` while the subject describes a dirty tree. Each sample retains its own source
digest.

Environment identity is read from the chain's own builder, not from the developer's. Effective concurrency is
decoded rather than captured raw, and takes part in comparison compatibility. Filesystem identity is that of
the measured root.

`RUSAGE_CHILDREN.ru_maxrss` is a high-water mark across all prior children and cannot be attributed to one
sample; per-sample resource use is measured per process or reported unavailable. Wrapper RSS is never reported
as container RSS.

Durations are monotonic everywhere, including hook anchors. A sum of BuildKit step durations is aggregate step
work and is named as such, because parallel steps overlap and the sum is not elapsed time. Zero is a measured
claim and is false when work occurred.

## 3A.8 Coverage closes in both directions

The expected measurement relation is derived from the validated registry — command, scenario, sample count,
edit multiplicity, derived parent context, role — and recording requires exact equality with the observation:
no missing pair, no extra pair, exact counts, and every derived pair producible by a parent in that scenario.
A command measured once may not stand in for a scenario it never ran.

## 3A.9 Comparison validates before it concludes

Both observations are validated and their summaries recomputed before any verdict. Command, scenario, edit,
metric identity, derived parent context, resource scope and concurrency are fingerprinted; a changed
definition makes that metric incomparable rather than improved or regressed. Comparison uses the same
registry-aware selector expansion as a run, so a group resolves and an unknown name fails.

## 3A.10 Bundles survive interruption

The local observation is written incrementally and updated after every completed sample, and cancellation
leaves it inspectable and marked incomplete. Run identity carries full precision plus a collision-safe part,
and an existing bundle path is never reused. Recording verifies every direct raw log exists and matches its
retained digest.

## 3A.11 One authority per registry fact

Group membership is derived from command entries. Scenario applicability either derives the command-scenario
matrix or does not exist. Numeric sample counts are authoritative and usage wording is generated from them.
Dependency cycles are a registry defect rejected at load.

## 3A.12 Repeated work is machine-readable

The observation retains a containment and repeated-execution relation over Make targets, pre-commit stages,
Docker stages and analysis steps, by stable ID. M2 reports it; M3 decides whether any of it is safe to merge.

---

# 4. One Make interface

Add one public Make target:

```text
observe
```

Do not add separate public targets for running, listing, help, comparison, recording, or subsets.

Supported use:

```text
make observe
```

Run the complete canonical suite, save one local run bundle, compare it with the tracked canonical observation,
and print the summary.

```text
make observe ONLY=make.prove
make observe ONLY=make.prove,precommit.prover
make observe ONLY=working-tree.policy
```

Run only the named command IDs or groups plus their required setup. This is an ad hoc run and cannot replace the
tracked canonical observation.

```text
make observe SCENARIO=project.cold.prover
make observe SCENARIO=project.warm.noop
make observe ONLY=make.prove SCENARIO=project.warm.noop
```

Run only the named scenarios. `ONLY` and `SCENARIO` may be combined.

```text
make observe BASE=HEAD~20
make observe BASE=<git-ref>
make observe BASE=.build-observatory/runs/<run-id>/observation.json
```

Run the selected suite and compare with an observation read from a Git ref or local path. When `BASE` is omitted,
use the tracked `.review/BUILD_OBSERVATION.json`.

```text
make observe COMPARE=<git-ref-or-path>
make observe COMPARE=<candidate-ref-or-path> BASE=<baseline-ref-or-path>
```

Compare two existing observations without running commands.

```text
make observe RECORD=1
```

Run the complete canonical suite and replace `.review/BUILD_OBSERVATION.json` only after every recording rule in
§12 passes.

```text
make observe LIST=1
```

Print every stable command ID, group, purpose, source view, side-effect class, scenario coverage, and whether it is
timed directly, derived from a parent, or catalog-only.

```text
make observe HELP=1
```

Print the current usage, examples, cache definitions, recording rules, comparison rules, and output locations.

Usage text must be generated from the suite registry and the tool’s argument model. Do not maintain a second full
usage guide in `README.md` or `CLAUDE.md`.

Add one terse pointer to the operating entry point:

```text
Run `make observe HELP=1` for the Build Observatory command, scenario, cache, comparison, and recording rules.
```

---

# 5. Named selection

`ONLY` accepts a comma-separated list of stable command IDs or group IDs.

Rules:

1. Unknown names fail and list the nearest valid names.
2. An empty expansion fails.
3. Duplicate names collapse without changing registry order.
4. A group expands to its registry members.
5. Required setup and dependency commands are added automatically.
6. Added dependencies are printed before execution.
7. Measurements distinguish selected commands from support commands.
8. A selected parent may expose derived child-stage measurements.
9. A selected derived child must run through the same live parent path in selective mode, not through a copied
   command invented by the observatory.
10. `RECORD=1` rejects `ONLY`.
11. A partial run cannot update the canonical observation.
12. Comparison output may be filtered by `ONLY` without changing either observation.

`SCENARIO` follows the same selection and validation rules.

The full suite is the registry’s canonical closure, not a hard-coded list in the Makefile or Python source.

---

# 6. Suite registry

`.review/BUILD_OBSERVATORY_SUITE.json` is the sole command and scenario registry.

Use canonical JSON:

- UTF-8;
- sorted object keys;
- stable array order where order has meaning;
- integers for durations, sizes, and sample counts;
- no comments;
- no copied source line numbers;
- stable IDs rather than list positions.

Its identity is the SHA-256 of its canonical bytes. Store that digest in each observation.

Each command entry must include at least:

```text
id
kind
groups
purpose
source_view
execution
side_effect
measurement
scenarios
samples
dependencies
expected_exit
outputs
owner
```

Closed values:

```text
kind:
  make-target
  precommit-stage
  precommit-full
  docker-stage
  rocq-module-analysis
  history-analysis
  setup
  diagnostic

source_view:
  working-tree
  committed-tree
  staged-index
  staged-index-export
  disposable-copy
  environment-only

side_effect:
  none
  writes-disposable-copy
  writes-local-observation
  writes-tracked-observation
  changes-repository-config

measurement:
  direct
  derived
  catalog-only
```

A `catalog-only` entry requires a current reason and must remain selectable when safe. It cannot disappear from
`LIST=1`.

Each scenario entry must include:

```text
id
purpose
session_state
cache_state
prime_steps
sample_policy
applicable_groups
```

Do not manually copy command counts into prose. The tool reports current counts.

---

# 7. Command-surface coverage

The registry must classify the whole current execution surface.

## 7.1 Make targets

Discover public targets from the Makefile, including its multiline `.PHONY` declaration.

The current surface includes these identities and any later target discovered at implementation time:

```text
make.check
make.prove
make.emit
make.e2e
make.regenerate
make.regen-guard
make.builder
make.install-hooks
make.prover-log
make.prove-errors
make.fmt
make.names
make.fcb
make.fcb-write
make.claims
make.diet
make.audit-fresh
make.profile
make.observe
```

Do not use this prose list as the executable inventory. Discovery and the registry relation are authoritative.

Every discovered public target must have exactly one registry entry or one explicit alias to another stable entry.
`make.observe` is cataloged but is not recursively benchmarked.

## 7.2 Pre-commit path

Add stable observation anchors to the live pre-commit hook. Use IDs, not line numbers.

Cover:

```text
precommit.builder
precommit.export-index
precommit.ocaml-origin
precommit.generated-output
precommit.generated-mode
precommit.naming
precommit.human-acts.self-test
precommit.human-acts.check
precommit.references.self-test
precommit.references.check
precommit.closure-ledger
precommit.mutation
precommit.claims.self-test
precommit.claims.check
precommit.source-diet.self-test
precommit.source-diet.check
precommit.source-diet.wiring
precommit.prover
precommit.go-e2e
precommit.generated-artifact
precommit.generated-compare
precommit.full
```

Anchors must be paired, unique, and registry-owned.

Normal hook behavior must remain unchanged when observatory environment variables are absent.

Selective observation of one hook stage must run the exact live stage inside the same staged-index export path. Do
not duplicate the command in Python.

## 7.3 Docker stages

Discover named Docker stages from `FROM ... AS ...`.

The current stage identities include:

```text
docker.rocq-builder
docker.rocq-base
docker.prover
docker.profile
docker.profile-log
docker.emit
docker.generated-module
docker.generated-artifact
docker.go-e2e
docker.sync
```

Every discovered stage must be classified. Stage timing should use BuildKit’s structured progress output where
available.

## 7.4 Rocq and Dune

Discover the certified Rocq module set and dependency order from the pinned build authority, not from a copied prose
list.

The registry must include:

```text
analysis.rocq-modules
analysis.dune-graph
analysis.history
```

Per-module and dependency observations are produced by these analysis entries.

## 7.5 Coverage gate

The lightweight permanent validator must fail on:

- a public Make target without a registry entry;
- a registry Make target which no longer exists;
- a pre-commit anchor without a registry entry;
- a registry pre-commit stage without one exact anchor pair;
- duplicate or nested-invalid anchor pairs;
- a Docker stage without a registry entry;
- a registry Docker stage which no longer exists;
- duplicate command IDs;
- duplicate group IDs;
- a catalog-only command with no reason;
- an invocation which identifies source by line number or list position.

Run this validator in `make check` and the staged hook. Do not run the timing suite there.

---

# 8. Observation file

`.review/BUILD_OBSERVATION.json` is one self-contained canonical observation.

It must contain:

```text
schema
suite_digest
subject
environment
cache_model
commands
measurements
module_graph
history_analysis
derived
```

## 8.1 Subject identity

Retain:

```text
commit
tree
inventory_digest
dirty
source_view
```

A local dirty run also records:

```text
head_commit
working_tree_digest
dirty_paths_digest
```

The canonical tracked observation always has:

```text
dirty: false
source_view: committed-tree
```

## 8.2 Environment identity

Record at least:

```text
platform
Docker version
Buildx version
BuildKit identity
builder driver
pinned base-image digests
Rocq version
Dune version
OCaml version
Go version
kernel
CPU model
logical CPU count
memory bytes
filesystem type where practical
concurrency settings
```

Create one stable host-class fingerprint from the fields which affect timing. Do not include transient values such
as free memory in the compatibility fingerprint.

## 8.3 Measurements

Each sample retains:

```text
command_id
scenario_id
sample_index
selected_or_support
start_utc
wall_ns
user_cpu_ns
system_cpu_ns
max_rss_bytes
resource_scope
exit_code
expected_exit
status
cache_before
cache_after
raw_log_sha256
derived_stage_events
```

Use monotonic time for duration. UTC is descriptive only.

`resource_scope` states whether CPU and memory cover the host wrapper, container, BuildKit stage, or are
unavailable. Do not report host-wrapper RSS as container peak memory.

## 8.4 Summaries

Retain raw samples. Derived median, minimum, and maximum values may also be stored, but the validator must recompute
them.

Do not store only an average.

## 8.5 Graphs and history

The same file retains:

- module dependency adjacency;
- measured module durations;
- downstream rebuild sets;
- critical path;
- edit frequency;
- co-change sets;
- common edit shapes;
- weighted rebuild cost;
- repeated-work observations by stable command ID.

The tracked observation must remain useful when local raw logs are gone.

---

# 9. Local run bundles

Ad hoc and canonical runs first write:

```text
.build-observatory/runs/<run-id>/
  observation.json
  raw/
  comparison.json
  comparison.txt
```

`run-id` is derived from UTC start time, subject identity, and a content digest. It is descriptive, not authority.

Raw logs remain local and ignored.

The observation records each raw log’s SHA-256. The tracked canonical file must not require the raw log to exist.

An interrupted or failed suite remains in the local run directory with:

```text
status: incomplete
```

It cannot be recorded.

---

# 10. Cold, warm, cached, and uncached

**Superseded by §3A.** The scenario families, the cache cut, the cache authorities and the provenance rules
are stated once, in §3A, under `.review/M2_REPAIR_1_CACHE_CUT_AMENDMENT.md`. This section previously named
`cold.uncached`, `cold.cached`, `warm.cached.noop` and `warm.cached.incremental`, and a single
`buildkit_layers` authority — the exact model the amendment replaced and the exact authority finding D split.
Two scenario vocabularies in one contract is a second authority for one fact, so this one is retired rather
than kept in agreement by hand.

Two operational rules live here because §3A does not state them:

- The host page cache is `uncontrolled` unless the suite can control it without privilege or system-wide
  effects, and the canonical suite never flushes it.
- The observatory uses its own builder and cache root, and never prunes or alters the developer's normal
  builder cache. Creating that isolation may not introduce a performance optimization.

---

# 11. Canonical scenario coverage

Not every command must run in every scenario.

The registry owns the scenario matrix.

Required principles:

1. Full acceptance paths run in project-cold, project-cached-fresh and project-warm-noop forms.
2. Major proof, emission, e2e, and pre-commit paths run in the cache forms which are meaningful to them.
3. Lightweight policy commands run enough samples to show their stable direct cost.
4. Pre-commit child stages are derived from the instrumented full hook and remain individually selectable.
5. Docker child stages are derived from structured BuildKit events and remain individually selectable.
6. Mutating commands run only in disposable copies.
7. Setup commands are cataloged and measured separately from project build time.
8. Diagnostic commands are classified separately from acceptance commands.
9. A command excluded from the canonical timing run must have a current reason.
10. A partial selector run never claims full-suite coverage.

Use a fixed canonical sample policy:

```text
cold scenarios:          one sample
warm/no-op scenarios:    three samples
incremental scenarios:   three samples per edit shape
light direct commands:   three samples
```

Store every sample.

Do not add an arbitrary timeout. Operator cancellation creates an incomplete run, not a passing result.

---

# 12. Recording rules

`make observe RECORD=1` may replace `.review/BUILD_OBSERVATION.json` only when:

1. No `ONLY`, `SCENARIO`, or partial selector is present.
2. The suite registry validates.
3. The working tree and index are clean before the run.
4. The subject is one exact committed ref.
5. Every canonical command and scenario completed.
6. Every expected-success command succeeded.
7. Every expected-failure fixture failed for the expected reason.
8. Every cache state and prime relation validates.
9. Every incremental edit was restored byte-exactly.
10. The observation validates against its schema and suite digest.
11. The environment is recorded completely.
12. The result was written first as a local run bundle.
13. Recording changes only `.review/BUILD_OBSERVATION.json`.
14. The tool does not commit or stage the file.

A failed command is a failed observation, not a slow sample.

A canonical observation is not an acceptance gate. It is measured evidence.

---

# 13. Comparison

The same tool compares observations.

Input may be:

- a local observation path;
- the tracked current observation;
- a Git ref containing `.review/BUILD_OBSERVATION.json`.

For each compatible metric, print:

```text
baseline median
candidate median
absolute delta
percentage delta
baseline range
candidate range
classification
```

Classifications:

```text
improved
regressed
overlapping-range
unchanged
added
removed
incomparable
```

Do not use a hidden fixed percentage threshold.

When sample ranges overlap, classify `overlapping-range`.

When either side has one sample, report the delta but do not claim a noise conclusion.

Mark a metric `incomparable` when its command identity, scenario meaning, resource scope, or host class is
incompatible. Show both values and the reason.

Suite changes do not make every old observation useless. Compare stable matching IDs and report added, removed, or
changed definitions.

Comparison exits nonzero only for invalid or unreadable data, not for a regression.

`ONLY` may filter comparison output.

Generate both machine-readable `comparison.json` and plain `comparison.txt`.

---

# 14. Per-module and dependency evidence

M2 must produce a current Rocq and Dune dependency account.

Requirements:

1. Discover modules from the pinned build authority.
2. Use toolchain-native dependency output where available.
3. Do not infer authority from import regex alone.
4. Retain the exact dependency adjacency list.
5. Measure each module with the pinned toolchain.
6. Retain raw per-sentence timing locally.
7. Retain per-module totals in the canonical observation.
8. Compute the longest measured dependency path.
9. Compute each module’s transitive downstream rebuild set.
10. Record false-looking broad imports as findings, not M2 fixes.
11. Do not split modules or move theorems in M2.

The existing one-file profiling path may be reused, but the observatory must own the full-module iteration,
validation, and aggregation.

---

# 15. Incremental edit scenarios

Derive the canonical edit scenarios from both:

- module dependency position;
- Git history over the exact range from accepted C4 through accepted M1.

At minimum include:

```text
one frequently edited foundation module
one high-fan-out module
one low-fan-out leaf module
one large proof module
one policy-tool edit
one documentation-only edit
one generated-artifact check case
```

Each scenario has a stable ID and exact edit procedure.

For `.v` edits, use a valid, one-line, temporary comment in a disposable copy. Do not change theorem or proof
meaning.

For other edits, use an inert current-form change which triggers the real dependency path.

Every edit must:

1. record the pre-edit digest;
2. apply one deterministic change;
3. verify the intended file changed and no other file changed;
4. run the command;
5. restore exact bytes;
6. verify the post-restore digest equals the pre-edit digest.

Do not touch the real working tree.

The registry stores edit identity, not source line numbers.

---

# 16. Git history analysis

Analyze the exact Git range:

```text
start: 39ea7e3b012ec798c6a756c971c10bb363557ef8
end:   6524b437bd7a7d6b2616563b8789e28a00c7af13
```

The analysis must separate:

```text
Rocq source changes
tool and build changes
current technical documentation changes
generated-artifact changes
review-only freezes
life.md-only changes
```

Do not let M1’s one-time broad comment sweep silently define normal edit frequency. Report:

- all commits;
- implementation-bearing commits only;
- a view excluding the M1 source-diet campaign.

Retain:

```text
edit count by file
co-change count by file pair
common changed-file sets
change class
weighted rebuild cost
```

Weighted rebuild cost is derived from:

```text
observed edit frequency × measured downstream rebuild cost
```

Keep the inputs. Do not store only the product.

---

# 17. M2 obligations

Create `.review/M2_OBLIGATION_MATRIX.tsv` with the existing nine-column schema.

Required IDs:

```text
M2-01  M1 is accepted and M2 Build Observatory is the sole active work.
M2-02  One registry classifies every public Make target, pre-commit stage, Docker stage, and analysis command.
M2-03  One `make observe` interface generates help, listings, runs, comparisons, subsets, and recording.
M2-04  Named `ONLY` and `SCENARIO` selection runs only the selected closure and cannot record partial results.
M2-05  The observation schema retains exact source, environment, cache, command, sample, graph, and history identity.
M2-06  Cold, warm, cached, uncached, no-op, incremental, and bootstrap meanings are exact and non-overlapping.
M2-07  Every cached sample retains its exact priming and isolated cache provenance.
M2-08  The complete canonical suite covers every important working-tree and staged pre-commit use case.
M2-09  Mutating and repository-configuration commands run only in disposable or isolated environments.
M2-10  The permanent command-surface validator fails on missing targets, stages, anchors, or classifications.
M2-11  Per-module timing, the Dune graph, critical path, and downstream rebuild sets are reproducible.
M2-12  Git edit frequency, co-change, common edit shapes, and weighted rebuild cost use an exact retained range.
M2-13  Local ad hoc bundles and the one tracked canonical observation use the same schema and implementation.
M2-14  Git-ref and local-path comparison reports exact deltas, ranges, compatibility, and added or removed metrics.
M2-15  Recording requires a complete clean committed run and changes only the canonical observation file.
M2-16  Measurement anchors and wrappers preserve normal command order, bytes, output, exit status, and side effects.
M2-17  Every measured finding is assigned to M3, M4, or retain; M2 performs no optimization.
M2-18  Proofs, theorem surfaces, extraction, transport, generated Go, goldens, and runtime behavior remain unchanged.
M2-19  One exact M2 candidate carries the permanent facility and one canonical observation for that candidate.
```

All rows begin open.

Do not close a row before its exact implementation, positive evidence, negative control, mutation control, and
executing gate exist.

---

# 18. Controls

`make observatory` must run deterministic fixtures without Docker or Rocq. Since the amendment this is
structural rather than a promise: the self-test runs in `python-tools`, which carries no Docker client at
all, so a control cannot reach the daemon even if its code tried. External command effects are injected, and
the injection point takes no default — dropping it is a `TypeError` at the call site, not a silent fallback
to the ambient `docker` binary.

At minimum, must-fail controls cover:

- duplicate command ID;
- duplicate group ID;
- unknown `ONLY` token;
- unknown `SCENARIO` token;
- empty selection;
- missing dependency;
- dependency cycle;
- public Make target absent from registry;
- stale registry Make target;
- pre-commit anchor absent from registry;
- registry pre-commit stage with no anchor pair;
- duplicate anchor;
- unmatched anchor;
- Docker stage absent from registry;
- catalog-only entry with no reason;
- command identified by source line number;
- partial run with `RECORD=1`;
- dirty tree with `RECORD=1`;
- incomplete suite with `RECORD=1`;
- failed command with `RECORD=1`;
- unknown cache accepted as primed;
- cached run with no prime observation;
- incremental edit not restored;
- mutating command run in the source tree;
- tampered sample summary;
- missing raw sample;
- observation suite digest mismatch;
- incompatible observations reported as ordinary percentage deltas;
- missing tracked observation at a requested Git ref;
- recording which changes a second tracked file;
- help text which does not match the registry;
- a selector which runs an unrelated command;
- a skipped control counted as passed.

Must-accept controls cover:

- full registry validation;
- one direct command;
- one derived child stage;
- one group selection;
- one combined `ONLY` and `SCENARIO` selection;
- one clean complete record-eligible fixture;
- one local ad hoc run;
- one path comparison;
- one Git-ref comparison;
- one compatible delta;
- one incomparable environment;
- one added metric;
- one removed metric;
- one exact incremental edit and restore;
- one valid disposable mutating command.

Add mutation checks for the root rules which protect:

```text
command discovery
anchor relation
selection closure
record eligibility
cache provenance
edit restoration
observation validation
comparison compatibility
```

Deleting each rule’s effect must make its own named controls fail.

No skipped or vacuous control counts as passed.

---

# 19. Recommendations

Create `.review/M2_RECOMMENDATIONS.tsv`:

```text
id
finding
evidence_ids
observed_cost
owner
disposition
status
```

Allowed owners:

```text
M3
M4
retain
```

Allowed dispositions:

```text
audit-tool-architecture
propose-mechanical-refactor
retain-load-bearing-cost
needs-human-decision
```

Every recommendation cites stable observation metric IDs, command IDs, module IDs, or history IDs.

Do not cite source line numbers.

M2 does not implement a recommendation.

The exact M4 plan remains forbidden until M3 finishes and Rob accepts that plan.

---

# 20. Verification and freeze

Before freezing M2:

```text
make observe HELP=1
make observe LIST=1
make observe
make observe ONLY=make.prove
make observe ONLY=precommit.prover
make observe SCENARIO=project.cold.go-e2e ONLY=make.check
make observe SCENARIO=project.warm.noop ONLY=make.check
make observe COMPARE=<one local run> BASE=<one Git ref>
make observe RECORD=1

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

Run the real staged hook without bypass.

Also prove:

1. Every public Make target is classified.
2. Every anchored pre-commit stage is classified.
3. Every Docker stage is classified.
4. Full and selective runs use the same registry and runner.
5. Full and partial results use the same schema.
6. Partial results cannot record.
7. The tracked observation validates and names the exact M2 implementation candidate it measured.
8. The tracked observation can be read from its Git ref and compared with a local run.
9. Normal Make targets and the normal pre-commit hook behave the same with observation disabled.
10. Instrumentation preserves exit status and output.
11. No `.v` file changed.
12. No theorem, proof, constructor, capability, or semantic authority changed.
13. Generated `go.mod`, every generated `.go` file, and every reviewed golden remain byte-identical.
14. Runtime stdout, stderr, and exit status remain identical.
15. M2 recommendations contain no implemented optimization.
16. M3, M4, C5 Step 0, and C5 work did not begin.

The M2 implementation candidate contains:

- the permanent tool;
- suite registry;
- observation placeholder or prior tracked observation;
- anchors and inert instrumentation;
- one Make target;
- local-run ignore rule;
- exact contract and open/closing matrix;
- recommendations;
- all implementation and controls.

After committing that candidate:

1. Run the complete canonical suite against that exact committed candidate.
2. Use `RECORD=1` to replace `.review/BUILD_OBSERVATION.json`.
3. Close the evidence rows which require the observation.
4. Make one documentation-only freeze which names the candidate and requests human M2 review.
5. The freeze may change only:
   - `.review/BUILD_OBSERVATION.json`;
   - `.review/M2_OBLIGATION_MATRIX.tsv`;
   - `.review/NEXT_STEPS.md`;
   - `.review/REVIEW_REQUEST.md`;
   - `.review/M2_RECOMMENDATIONS.tsv` when its rows depend on the completed observation.
6. No commit follows the freeze.

Do not create a prose-heavy timing report. The observation, generated comparison, recommendations, matrix, raw
local bundle, and Git history are the evidence.

Only Rob accepts M2.
