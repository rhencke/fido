# M2 HUMAN DISPOSITION — THE GREAT MEASUREMENT CULLING

## 0. Authority and exact basis

Rob is the final human authority.

Rob has rejected the current M2 product architecture. The problem is not one more defect in the current
implementation. The Build Observatory became a large self-verifying measurement platform when the required
product is a tiny diagnostic timing aid.

The exact repository basis is:

```text
Uploaded snapshot:
  fido-main - 2026-08-02T213730.016.zip

Uploaded Git head / documentation-only freeze:
  f55067444e96fe8cc82aab935c9fdc89d03c136b

M2 implementation candidate named by that freeze:
  1003734e67e2f07f5a10ec931e5c5729981d4652

Accepted M1 candidate:
  6524b437bd7a7d6b2616563b8789e28a00c7af13
```

Candidate `1003734e67e2f07f5a10ec931e5c5729981d4652` is **WITHDRAWN BY HUMAN DISPOSITION**. It is
not accepted and receives no Repair 6.

Git history owns the entire Build Observatory experiment.

**The Great Measurement Culling is the sole permitted M2 work.**

C4, M0 and M1 remain accepted and are not reopened.

M3, M4, C5 Step 0, C5 and feature work remain forbidden until Rob accepts the replacement M2 result.

Use:

```text
/loop 3m
```

Continue until this exact replacement is complete or a real contract conflict blocks progress. Notify Rob with
the notification tool when complete or genuinely blocked.

---

## 1. The replacement product

M2 now delivers exactly this:

```text
one public Make target:        make perf
one small shell implementation: tools/perf.sh
one tracked result:            .review/PERFORMANCE.tsv
a handful of inert completion markers in the existing make check path
Git diff as the comparison tool
```

Nothing else.

The purpose is:

> Run the real dominant acceptance path once project-cold and once hot, serially; record cumulative elapsed
> time at a few critical completions; replace one checked-in text file; show `git diff`.

Performance timing is diagnostic evidence. It is not certified correctness, not a semantic authority, not a
benchmark framework, and not an acceptance gate.

The implementation must remain understandable in one sitting. Do not recreate any deleted abstraction under a
new name.

---

## 2. Mandatory deletion

Delete the complete live Build Observatory framework.

At minimum, delete:

```text
.review/BUILD_OBSERVATION.json
.review/BUILD_OBSERVATORY_SUITE.json
.review/M2_BUILD_OBSERVATORY.md
.review/M2_IMPLEMENTATION_REPAIR_1.md
.review/M2_IMPLEMENTATION_REPAIR_2.md
.review/M2_IMPLEMENTATION_REPAIR_3.md
.review/M2_IMPLEMENTATION_REPAIR_4.md
.review/M2_IMPLEMENTATION_REPAIR_5.md
.review/M2_REPAIR_1_CACHE_CUT_AMENDMENT.md
.review/M2_RECOMMENDATIONS.tsv
tools/build-observatory.py
```

Replace, rather than retain, `.review/M2_OBLIGATION_MATRIX.tsv`.

Delete all framework-specific code, data, prose, controls, fixtures, mutations, registry entries, Docker stages,
Make targets, hook stages and ignored local-run namespaces, including:

```text
make observe
make observatory
observatory-runner
BUILD_OBSERVATION
BUILD_OBSERVATORY_SUITE
.build-observatory
FIDO_OBSERVE
Build Observatory acquisition plans
trace-completion objects
observation bases
suite registries
scenario registries
comparison schemas and renderers
resume support
local run bundles
history analysis
module-graph acquisition added solely for the observatory
metric taxonomies
partition objects
suite self-cost accounting
observatory-specific synthetic observations
observatory-specific self-tests and mutation entries
observatory-specific FCB references and owner markers
```

Delete the `docker-cli` and `observatory-runner` Docker stages when no surviving non-observatory consumer needs
them.

Delete the `module-graph` and `module-graph-log` Docker stages when no surviving non-observatory consumer needs
them.

Remove `.build-observatory/` from `.gitignore`, `.dockerignore`, the D-24 residue set and its controls.

Remove observatory-specific logic from:

```text
Makefile
.githooks/pre-commit
Dockerfile
tools/gate-mutation-test.py
tools/fcb-reference-gate.py
tools/host-python-gate.py
tools/source-diet.py
```

Do not leave aliases, compatibility modes, deprecated wrappers, replay tools, parsers, or archived copies in the
live tree. Git is the archive.

Do not produce a deletion ledger. The Git diff is the deletion evidence.

---

## 3. What must survive

The culling deletes the measurement platform, not unrelated improvements which now have an independent current
purpose.

Preserve:

```text
the no-host-Python boundary
the pinned python-tools image
tools/host-python-gate.py after removing observatory-only assumptions
containerized Python gates and writers
tools/worktree-list.py and the exact working-tree inventory semantics
the containerized Rocq profile path and tools/rocq-profile.py
general mutation-harness speedups which preserve the same controls and failure meanings
all proof, extraction, transport, e2e, generated-byte and publication gates
all current generated Go and goldens
```

Keep general-purpose changes only when they retain one current non-observatory purpose.

Delete any code whose only consumer was the Build Observatory even if it was difficult to write.

`life.md` is untouched.

---

## 4. Canonical path

The one canonical performance subject is:

```text
make -j1 check
```

Both measurements run that same public path.

Do not implement a parallel `perf-check`, duplicate the `check` recipe, or reconstruct its dependency graph in
the script.

The script invokes the existing target with a dedicated serial Buildx builder:

```text
fido-perf-v1
```

The builder uses:

```text
BuildKit max-parallelism = 1
Make jobs = 1
```

Normal development, ordinary `make check`, and the real pre-commit hook keep their existing parallelism and
behavior.

Builder creation and one-time priming happen before the timed interval.

---

## 5. Cold and hot meaning

### Project-cold

The cold run is not an empty machine.

Before timing:

- the dedicated builder exists;
- base images are locally available;
- the pinned Python, Rocq, Dune, OCaml and Go toolchain layers are available;
- one-time builder bootstrap and registry pulls are outside the interval.

The cold invocation runs the real `make -j1 check` path while forcing the project-dependent roots required to
re-run proof and emission/e2e work.

Use the smallest explicit Make variables necessary, conceptually:

```text
FIDO_PERF_COLD=1
```

The Makefile maps that flag to the appropriate existing Buildx `--no-cache-filter` roots, expected to be
equivalent to:

```text
prover
emit
```

and the descendants required by `make check`.

Stable infrastructure ancestors and long-lived toolchain acquisition remain cached.

State this honestly in `.review/PERFORMANCE.tsv` as **project-stage cold**, not empty-cache cold.

### Hot

Immediately after the successful cold run, invoke the exact same:

```text
make -j1 check
```

using the same dedicated builder and source tree, without project invalidation.

No file may change between the cold and hot invocations.

### Publication

Write results to a temporary file outside the repository while measuring.

Replace `.review/PERFORMANCE.tsv` only after both invocations succeed.

A failed cold or hot run leaves the tracked metrics file unchanged.

---

## 6. Completion markers

Delete the general begin/end trace grammar.

Retain only a tiny optional completion-marker macro in the Makefile. It is inert unless `tools/perf.sh` supplies
a metrics log and run start.

Record cumulative elapsed milliseconds at these critical completions, using the existing real target
boundaries:

```text
pytools
hostpython
names
fcb
claims
diet
prove
e2e
check
```

A marker is a completion timestamp, not a nested span, trace, parent, partition, or proof of attribution.

Use a monotonic host clock available to the shell, preferably `/proc/uptime`. The script may record its practical
resolution in the file. Do not build a clock abstraction.

The Makefile must not parse, validate, compare, or retain timing data.

When timing is disabled, markers produce no output and do not alter order, bytes, exit status or side effects.

Remove every pre-commit timing marker. The canonical timing subject is `make check`, not the hook.

---

## 7. Shell script

Create:

```text
tools/perf.sh
```

Requirements:

- POSIX shell;
- `set -eu`;
- no Python;
- no JSON;
- no helper program added for timing;
- no registry;
- no configuration language;
- no resume;
- no partial selector;
- no comparison implementation;
- no statistical analysis;
- no self-test framework;
- no mutation tests;
- no local bundle hierarchy;
- no network pull inside a measured interval;
- no write to the tracked metrics file until both runs pass.

The script does only this:

1. Resolve the repository root.
2. Ensure the dedicated serial builder exists, creating it outside the measured interval with a temporary
   BuildKit configuration.
3. Prime stable infrastructure outside the measured interval when the builder is new.
4. Create one temporary metrics file.
5. Run project-cold `make -j1 check`.
6. Run hot `make -j1 check`.
7. Atomically replace `.review/PERFORMANCE.tsv`.
8. Run:

```text
git diff -- .review/PERFORMANCE.tsv
```

The script should be small enough that its complete behavior is obvious from direct inspection. Do not expand it
to anticipate hypothetical future benchmark needs.

Project-authored Python remains forbidden on the host. The shell script may use ordinary shell, Make, Git,
Docker, Buildx, `awk`, `sed`, `grep`, `mktemp`, `mv` and core utilities already inside the declared host boundary.

---

## 8. Tracked metrics file

Create:

```text
.review/PERFORMANCE.tsv
```

It is the sole retained performance record.

Use a plain diffable form equivalent to:

```text
# command: make -j1 check
# builder: fido-perf-v1; BuildKit max-parallelism=1
# cold: project stages forced; stable image/toolchain layers retained
# hot: immediate repeat, same source and builder
mode	checkpoint	elapsed_ms
cold	start	0
cold	pytools	...
cold	hostpython	...
cold	names	...
cold	fcb	...
cold	claims	...
cold	diet	...
cold	prove	...
cold	e2e	...
cold	check	...
hot	start	0
hot	pytools	...
hot	hostpython	...
hot	names	...
hot	fcb	...
hot	claims	...
hot	diet	...
hot	prove	...
hot	e2e	...
hot	check	...
```

Cumulative completion times are sufficient. A reader can subtract adjacent rows when needed.

Do not store:

- raw logs;
- medians;
- percentages;
- comparison verdicts;
- environment fingerprints;
- cache-stage maps;
- Git history analysis;
- module graphs;
- source inventories;
- trace IDs;
- sample IDs;
- hashes of local logs;
- validation metadata.

Git owns the historical sequence. `git diff` is the performance comparison.

Add `.review/PERFORMANCE.tsv` to `.dockerignore` so updating the record does not invalidate project Buildx layers.
It remains tracked by Git.

---

## 9. Public interface

Add one diagnostic target:

```text
make perf
```

It invokes only:

```text
sh tools/perf.sh
```

`make perf` is not a dependency of:

```text
make check
make fcb
the pre-commit hook
any correctness or publication gate
```

Remove `make observe`, `make observatory`, `HELP`, `LIST`, `PLAN`, `ONLY`, `SCENARIO`, `BASE`, `COMPARE`,
`RECORD`, `RESUME`, `REPEAT` and all related usage prose.

The only usage instruction needed is:

```text
Run `make perf`. It replaces `.review/PERFORMANCE.tsv`; inspect `git diff`.
```

---

## 10. Current M3 findings worth retaining

Delete `.review/M2_RECOMMENDATIONS.tsv`.

Before deletion, preserve only the current non-observatory work which still has a real later owner. Add a terse
section to `.review/M_SERIES_PLAN.md` or the current M3 authority, without copied timings:

1. Determine why ordinary source edits invalidate more downstream work than the proof dependency structure
   appears to require.
2. Audit policy-gate cost and repeated execution in `make check` and the pre-commit path.
3. Audit the mutation harness's repository copying and execution architecture; retain the already-landed
   named-control and parallel execution improvements when correct.
4. Measure and account for the deliberate cost of the no-host-Python boundary before changing its pinned image.
5. General Make, hook, Buildx and cache architecture remains M3/M4 work.

Delete observatory-only findings about registry duplication, metric vocabularies, observation reflexivity,
fixture schemas, stage-graph parsing, sampling policy and suite self-measurement.

Do not copy old timing numbers into prose. `.review/PERFORMANCE.tsv` owns the current numbers.

---

## 11. Replacement M2 authority

Create a short live contract:

```text
.review/M2_PERFORMANCE_SNAPSHOT.md
```

It states only:

- purpose;
- exact `make perf` interface;
- project-cold and hot definitions;
- serial builder rule;
- completion checkpoints;
- tracked TSV rule;
- diagnostic/non-gating status;
- strict scope;
- exit condition.

Delete `.review/M2_BUILD_OBSERVATORY.md`.

Update:

```text
.review/M_SERIES_PLAN.md
.review/NEXT_STEPS.md
.review/OPEN_QUESTIONS.md
.review/REVIEW_BASIS.md
.review/REVIEW_REQUEST.md
.review/fcb/current/FIDO_FCB_INDEX.md
.review/fcb/current/FIDO_FCB_ROADMAP.md
.review/fcb/current/FIDO_FCB_REFERENCES.tsv
other live FCB banners or toolchain statements which name the deleted observatory
```

Remove all three observatory open questions. Their subjects disappear or return to M3 as the terse findings above.

Retain the existing `M2-REVIEW` human act, now referring to the exact replacement candidate named by
`NEXT_STEPS`.

No new FCB amendment is required unless a fixed point explicitly requires the deleted observatory architecture.
If one does, stop, name it exactly, and propose the smallest amendment. Do not retain the framework as a
workaround.

---

## 12. Replacement obligation matrix

Replace `.review/M2_OBLIGATION_MATRIX.tsv` with these obligations:

```text
M2-01  The withdrawn observatory candidate is superseded and the culling is the sole active work.
M2-02  Every observatory implementation, data, authority, reference, target, hook stage and compatibility path is deleted.
M2-03  The no-host-Python boundary and all unrelated correctness paths remain intact.
M2-04  One `make perf` target runs the exact `make -j1 check` path project-cold and then hot on one serial builder.
M2-05  The cold interval excludes builder/bootstrap/toolchain acquisition and forces the declared project roots.
M2-06  Critical completion times are written to one temporary TSV and published atomically only after both runs pass.
M2-07  `.review/PERFORMANCE.tsv` is the sole retained timing record and `git diff` is the sole comparison mechanism.
M2-08  Proofs, assumptions, extraction, transport, generated bytes, goldens and runtime behavior remain unchanged.
M2-09  One exact replacement candidate is frozen and requests Rob's review.
```

All rows begin open.

This diagnostic facility has no observatory-specific mutation-test obligation. State that exact unsupported
boundary in the new contract and use it honestly in matrix cells where a mutation control is not applicable.

Retarget `tools/claim-matrix-gate.py` only as required for the new M2 IDs. Do not add a performance validation
framework to make the matrix look sophisticated.

---

## 13. Verification

Before freezing, run the existing project gates:

```text
make check
make regenerate
make regen-guard
make audit-fresh
make diet
make fcb
make claims
make names
make fmt
```

Run the real pre-commit hook over the exact staged snapshot without bypassing it.

Run:

```text
make perf
```

Verify:

1. The cold and hot invocations both executed the real `make -j1 check`.
2. The cold run forced the declared project roots and did not include builder creation or initial priming.
3. The hot run immediately followed on the same source and builder.
4. `.review/PERFORMANCE.tsv` contains both modes and the required completion checkpoints.
5. A forced failure leaves the previous metrics file unchanged.
6. `git diff -- .review/PERFORMANCE.tsv` shows the result.
7. `git grep` finds no live Build Observatory implementation or compatibility path.
8. No project Python runs on the host.
9. Generated `go.mod` and every generated `.go` byte remain unchanged.
10. Runtime stdout, stderr and exit status remain unchanged.
11. The whole-theory assumption audit remains green.
12. M3, M4, C5 Step 0 and C5 did not begin.

Do not add tests for the diagnostic timer beyond direct review and the successful real cold/hot run.

The existing correctness gates test the path being timed. The timing script does not need a second correctness
system around it.

---

## 14. Commit order

Use small, reviewable commits:

1. Install this human disposition and replacement authority.
2. Delete the observatory framework and references.
3. Add the tiny completion markers, shell script, Make target and metrics path.
4. Update current governance, FCB references, matrix and M3 findings.
5. Run the full correctness checks.
6. Run one real `make perf`.
7. Commit one exact implementation candidate.
8. Make one documentation-only freeze naming that candidate and requesting Rob's review.
9. Notify Rob.

Do not preserve a transitional state or compatibility bridge between the old and new systems.

---

## 15. Definition of done

The Great Measurement Culling is complete only when:

- the live Build Observatory framework is gone;
- its history exists only in Git;
- no observatory target, runner, registry, local bundle, parser, validator, comparison tool, trace object or
  compatibility path survives;
- one small POSIX shell script implements timing;
- one public `make perf` target invokes it;
- one tracked TSV holds the last project-cold and hot result;
- the canonical subject is the exact serial `make check` path;
- builder bootstrap and stable toolchain acquisition are outside the cold interval;
- critical completions are visible as cumulative elapsed milliseconds;
- the metrics file changes only after two successful runs;
- Git diff is the comparison;
- no performance-specific permanent gate or mutation framework exists;
- the no-host-Python boundary remains;
- all current correctness, proof, artifact and runtime checks remain green;
- one exact replacement candidate is frozen;
- Claude notifies Rob.

Only Rob accepts M2.
