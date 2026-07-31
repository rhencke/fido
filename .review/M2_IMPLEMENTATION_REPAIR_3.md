# M2 IMPLEMENTATION REVIEW — BLOCKING — REPAIR 3
# TRACE-BASED CANONICAL ACQUISITION AND SUITE-RUNTIME AMENDMENT

## 0. Disposition

**M2 implementation candidate `641ac9034b280ddfd0930a12635e60322a2d4686` is BLOCKING.**

It becomes the **third blocked M2 implementation candidate**.

The uploaded snapshot resolves to documentation freeze:

```text
94beac1d554290b1e2a633ac30956eac4be3be53
```

The separately authorized `life.md` commit between the candidate and freeze is character-continuity work, not
part of the M2 candidate. Preserve its content exactly in the next candidate.

C4, M0, and M1 remain accepted and are not reopened.

**M2 Repair 3 is the sole permitted work.**

M3, M4, C5 Step 0, C5, and all feature work remain forbidden.

Use:

```text
/loop 3m
```

Continue until the whole directive is complete or a real M2 contract conflict blocks progress. When complete or
genuinely blocked, notify Rob with the notification tool.

---

## 1. Exact review basis

```text
Uploaded snapshot:
  fido-main - 2026-07-31T142225.816.zip

Uploaded Git head / documentation freeze:
  94beac1d554290b1e2a633ac30956eac4be3be53

Blocked M2 candidate:
  641ac9034b280ddfd0930a12635e60322a2d4686

Previous blocked M2 candidates:
  8325ddb9ee2dcb1087dbe22d754b9a7d4c5a3b43
  e534b0ae5cc47da510e46583e47f74566589d538

Accepted M1 candidate:
  6524b437bd7a7d6b2616563b8789e28a00c7af13

M2 contract:
  .review/M2_BUILD_OBSERVATORY.md

M2 suite:
  .review/BUILD_OBSERVATORY_SUITE.json

M2 canonical observation:
  .review/BUILD_OBSERVATION.json
```

Use all code, FCB, gates, suite data, and review state from this exact ref. Do not mix refs, rewrite history, or
discard the current `life.md`.

---

## 2. What Repair 2 got right

Keep these results.

1. Project Python no longer runs on the host.
2. The host boundary is shell, Make, Git, Docker, and Buildx.
3. Working-tree Python gates use the exact mounted working source.
4. The pre-commit path uses the staged Dockerfile, staged lock, staged Python tools, and exact exported index.
5. One complete observation validator serves recording, local loading, Git loading, and comparison.
6. Source identity retains file mode, file kind, symlink identity, tracked absence, and source-view kind.
7. Samples and derived children have exact run, sample, parent, prime, command, scenario, edit, and cache-chain
   provenance.
8. Cache authorities are derived from the stages which actually touch them.
9. Cache cuts own exact invalidation-root sets and reject undeclared independent rebuilds.
10. Incremental edits must exhibit the effect they were selected to measure.
11. Metric kind, resource scope, role, parent, edit, and command all remain part of identity.
12. Zero, below-resolution intervals, untimed artifacts, aggregate step work, and wall time are distinct.
13. The observatory output no longer enters its own measured source copies and Docker contexts.
14. The finished observation validates under the current schema and recording rules.
15. The no-host-Python boundary, generated Go, proof surface, runtime output, and accepted semantic system remain
    unchanged.

The framework remains:

```text
one suite registry
one observatory tool
one Make target
one tracked canonical observation
one ignored local-run area
Git history for prior observations
```

Repair 3 changes acquisition planning, not this framework.

---

## 3. Blocking finding — the canonical suite is operationally unusable

### 3.1 Exact observed cost

The accepted candidate's canonical observation ran from:

```text
2026-07-31T13:45:42.691127Z
through
2026-07-31T17:53:11.486676Z
```

Elapsed suite time:

```text
4 h 07 m 29 s
```

The observation retains:

```text
732 total sample identities
133 direct selected executions
599 derived samples
```

The direct measured commands alone total about 3 h 54 m. The rest is priming, transitions, analysis, and suite
overhead.

Four overlapping commands account for 80 direct executions:

```text
make.check
make.prove
make.emit
make.e2e
```

Their direct measured time totals about:

```text
173.1 minutes
```

`make.check` alone ran 20 times and consumed about:

```text
142.2 minutes
```

The current fixed policy repeats every warm sample three times and every incremental edit three times for each
command. Five edit shapes across `make.check`, `make.prove`, `make.emit`, and `make.e2e` therefore create:

```text
5 edits × 4 commands × 3 repetitions = 60 direct incremental executions
```

Many of those executions repeat work already contained in another measured path.

Several failed canonical attempts made this repair round take about twenty-five hours. The current candidate's own
commit history confirms that late defects repeatedly threatened another four-hour rerun.

### 3.2 Why this blocks M2

M2 is establishing a permanent, general-purpose timing facility. A canonical run which costs four hours and
requires repeated four-hour reruns for observatory repairs is not a usable facility for tracking performance over
time.

This is inside M2's contract:

- the canonical suite and its sample policy are M2 products;
- named partial runs do not replace a practical full historical record;
- the observatory must not make performance work too expensive to perform;
- M2 cannot close with a measurement method which systematically repeats the same execution closures.

Rob explicitly amends M2 scope now. The observatory itself must be optimized before M2 can be accepted.

This does not authorize optimization of Fido's proof, policy, Docker, or acceptance graph. It authorizes only the
smallest architecture change which stops the timing suite from repeatedly executing work it already observes.

---

# 4. Human-approved M2 scope amendment

Install this named contract amendment in `.review/M2_BUILD_OBSERVATORY.md`:

```text
M2-SCOPE-AMENDMENT-TRACE-ACQUISITION
```

Settled rule:

> The canonical suite acquires a minimal set of real execution traces. Stable monotonic checkpoints and
> structured BuildKit events project every contained command and stage from those traces. The suite does not
> rerun a command-scenario-edit relation when one exact containing trace already measures that live execution
> path under the same source and cache state. Canonical acquisition uses one sample per trace. Optional repeats
> are ad hoc and never required for recording.

This amendment adopts the substance of recommendation `R07` and the canonical-sample part of `R09` into M2.

Update `.review/M_SERIES_PLAN.md` and `.review/M2_RECOMMENDATIONS.tsv` accordingly:

- `R07` becomes `implemented-in-M2` under Rob's direction.
- `R09` becomes `implemented-in-M2` for canonical multiplicity and suite self-cost visibility.
- The actual project costs reported by `R01`, `R02`, and `R03` remain M3 work.
- `R10` remains M3 except for the early trace validation and exact same-ref resume required below.
- Do not implement the project optimizations those rows discuss.

No FCB amendment is required unless a current FCB authority forbids this exact M2 contract amendment. If such a
conflict exists, stop and identify the exact governing text and proposed change. Do not work around it.

---

# 5. One acquisition model

## 5.1 Trace

A **trace** is one real execution of one root command under one exact:

```text
source view
scenario
cache cut
edit identity, when present
execution environment
concurrency configuration
```

Each trace has a stable `trace_id`.

A trace retains:

```text
trace_id
root_command_id
source_digest
scenario_id
edit_id
cache_chain_id
prime_sample_id
normal_or_serial
make_jobs
buildkit_max_parallelism
start and end
exit result
raw log
checkpoint events
BuildKit stage events
```

## 5.2 Checkpoint interval

A **checkpoint interval** is one paired monotonic begin/end event inside one trace.

Use stable IDs, never line numbers or execution order.

Checkpoint sources include:

- public Make target bodies;
- meaningful Make recipe segments which are not already public targets;
- the existing pre-commit anchors;
- structured BuildKit stage / vertex events;
- analysis steps.

## 5.3 Contained metric

A **contained metric** is a direct elapsed interval observed inside one trace.

Examples:

```text
make.fcb inside trace.working-tree.acceptance
make.prove inside trace.working-tree.acceptance
precommit.mutation inside trace.staged.acceptance
docker.prover inside a serial BuildKit trace
```

It retains the exact trace sample and checkpoint IDs which establish it.

## 5.4 Serial projection

A **serial projection** is the sum of exact non-overlapping intervals from one serial trace, chosen through the
registry's containment graph.

It is a model of command cost under the declared serial execution. It is not relabeled as normal parallel wall
time.

Every metric states one of:

```text
direct_wall_elapsed
contained_wall_elapsed
serial_projection
aggregate_step_work
untimed_artifact
```

Do not compare one kind with another as though they were the same quantity.

---

# 6. Serial acquisition

Canonical decomposition runs under a dedicated observatory-only serial configuration.

Require:

```text
Make jobs = 1
BuildKit maximum parallelism = 1
```

The normal developer builder and normal Make behavior must not change.

Use a dedicated observatory builder whose effective BuildKit parallelism is configured and then observed as one.
Do not merely set a variable and assume it worked. The suite records and validates the effective configuration.

Only the layer being decomposed must be serial:

- Make target and recipe decomposition requires Make to be serial.
- Docker stage decomposition requires BuildKit to be serial.
- Dune, Rocq, Go, and a policy tool may retain their normal internal behavior when the whole tool invocation is
  treated as one atomic checkpoint.

Do not disable internal parallelism merely to make a more detailed claim the suite does not need.

If serial execution cannot be proved for a trace, contained intervals may still be retained, but a summed serial
projection from overlapping work is forbidden.

---

# 7. Inert Make checkpoints

Extend the current inert checkpoint design to Make.

When observation is disabled:

```text
command order
source bytes
output
exit status
side effects
normal parallelism
```

must remain unchanged.

When observation is enabled, emit paired monotonic checkpoints around:

- each public Make target recipe;
- each significant unowned segment of a compound recipe;
- Python image setup;
- observatory runner setup;
- working-tree archive / generated compare;
- any other step required to partition a selected trace.

A target invoked as a prerequisite must emit the same target checkpoint as when invoked directly.

The top-level process wall time remains the parent trace. Its children plus explicit recorded overhead must
partition it without overlap in serial mode.

Do not hide gaps. Retain them under stable overhead IDs such as:

```text
trace.make.dispatch-overhead
trace.buildx-wrapper-overhead
trace.unattributed-overhead
```

A missing or unmatched checkpoint makes that trace incomplete.

Use the existing monotonic-clock discipline. Do not use wall-clock timestamps for duration.

---

# 8. Minimal canonical trace cover

The suite registry must declare:

```text
trace roots
contained commands
contained stages
checkpoint IDs
scenario applicability
edit applicability
projection definitions
standalone-only commands
```

The canonical planner computes the minimal exact trace set covering every required metric relation.

A command-scenario-edit relation may be:

```text
direct-root
contained
serial-projection
catalog-only-with-reason
```

It may not be both direct and projected in the same canonical observation unless the registry marks one as an
explicit validation spot-check.

Recording fails on redundant acquisition:

- the same relation executed directly twice;
- a direct execution retained when an exact containing trace already owns it;
- two traces claiming the same checkpoint interval;
- a projection with no owning trace;
- a command retained with no required metric and no catalog reason.

The planner must print the exact acquisition plan before running anything.

Add:

```text
make observe PLAN=1
```

This uses the same `observe` target and prints:

- direct traces which would run;
- metrics each trace will produce;
- projections;
- catalog-only commands and reasons;
- expected trace count;
- expected direct command count;
- estimated elapsed time from the current tracked observation when compatible.

`PLAN=1` runs no measured command and cannot record.

---

# 9. Required canonical trace shape

Keep the full command inventory. Change only how it is acquired.

## 9.1 Working-tree acceptance trace

Use one `make.check` trace for each required working-tree state:

```text
project cold
project cached fresh
project warm no-op
each retained incremental edit shape
```

Each trace runs once.

The Make checkpoints and BuildKit events yield the contained metrics for:

```text
hostpython
names
fcb
claims
diet
observatory
prove
e2e
generated-artifact comparison
the Make check body
the relevant Docker stages
```

Do not separately rerun a contained command for the same source / scenario / edit merely to obtain its number.

Standalone cold, cached, or warm measurements may remain for a public target only when its live path is materially
different from the interval contained in `make.check`. The registry must state that difference.

## 9.2 Staged acceptance trace

Use one `precommit.full` trace for each required staged state:

```text
project cold
project cached fresh
project warm no-op
```

Each runs once.

The existing pre-commit checkpoints yield every staged policy, proof, e2e, materialization, and comparison metric.

Do not rerun the child stages independently in the canonical suite.

## 9.3 Other trace roots

Retain one direct trace where no containing acceptance trace can establish the command:

```text
audit-fresh
regenerate
profile
module graph
builder bootstrap diagnostic
fcb-write
install-hooks
other mutating or setup commands with a current reason
```

Use one sample unless the command's result is an untimed artifact.

## 9.4 Incremental traces

Run one maximal working-tree acceptance trace per retained edit shape.

Do not run the same edit separately through:

```text
make.check
make.prove
make.emit
make.e2e
```

The one trace retains:

- actual top-level edit-feedback wall time;
- contained policy-target intervals;
- contained proof and e2e target intervals;
- Docker stage events;
- the edit's source identity and actual invalidation evidence.

This change alone replaces the current sixty direct incremental executions with one trace per edit shape.

Do not remove edit shapes merely to reduce time. A later repair may merge shapes only when the registry derives
an exact equal invalidation signature and keeps the per-edit analytical facts distinct.

---

# 10. Canonical sample policy

Delete the fixed canonical triplicate policy.

Canonical recording uses:

```text
one real trace per trace / scenario / edit identity
```

Store that one exact sample.

A one-sample comparison reports the point delta and says that no noise conclusion is available. It does not invent
a confidence judgment.

Add optional ad hoc repetition through the same Make target:

```text
make observe ONLY=<selector> REPEAT=<positive integer>
```

Rules:

- `REPEAT` is valid only for ad hoc partial runs.
- `REPEAT` cannot be used with `RECORD=1`.
- repeated samples retain distinct sample IDs and raw logs;
- comparison may report ranges when repeats exist;
- the canonical tracked observation never requires repeats.

Git history supplies long-term repeated observations. A user who needs local variance pays only for the named
target being investigated.

---

# 11. Named selection

`ONLY=` remains a first-class use case.

When a selected command is normally projected from a containing trace, the planner chooses the smallest valid
execution for the request:

- use the direct command when it is a valid ad hoc execution and cheaper than its containing acceptance trace;
- otherwise run its owning trace and retain only the selected closure plus required support;
- print which choice was made and why.

Examples which must stay useful:

```text
make observe ONLY=make.prove
make observe ONLY=make.check
make observe ONLY=precommit.mutation
make observe ONLY=working-tree.policy
make observe ONLY=make.prove SCENARIO=project.cold.prover
make observe ONLY=make.check REPEAT=3
```

A partial run can never record the canonical observation.

---

# 12. Validate before and during expensive work

The four-hour suite must never be the first time a structural rule is exercised.

Before any measured trace:

1. validate the suite registry;
2. validate the complete trace / projection coverage relation;
3. run deterministic controls;
4. run mutation controls;
5. construct a production-shaped synthetic observation only through the real producer functions;
6. validate that observation through the complete validator;
7. render and compare it;
8. print the plan.

After each real trace:

1. write the trace fragment;
2. validate every direct and contained sample in that fragment;
3. validate its checkpoints, parents, primes, cache cuts, source identities, and expected projections;
4. prove the trace closes exactly the registry relations assigned to it;
5. stop immediately on failure.

Do not wait until the final recording rule to discover a defect in an earlier trace.

The complete final validator remains pure and rerunnable without executing a command.

---

# 13. Resume

Support exact same-subject resume:

```text
make observe RESUME=<local bundle>
```

Resume is permitted only when all of these match:

```text
exact committed subject
suite digest
tool digest
registry digest
environment compatibility
serial builder configuration
source view
trace plan
```

Only complete, individually validated trace fragments may be reused.

A changed commit, changed suite, changed producer, or changed trace definition makes the old fragment incompatible.
Do not reconstruct provenance or carry a sample across incompatible definitions.

Resume remains ad hoc infrastructure for interrupted runs. Recording still validates the assembled complete
observation as one exact candidate result.

---

# 14. Suite self-cost

The observation must retain the facility's own cost:

```text
suite_started
suite_completed
suite_wall_ns
preflight_wall_ns
trace_wall_ns by trace
validation_wall_ns
direct_trace_count
contained_metric_count
projection_count
```

This is meta-evidence, not a recursively measured command.

The comparison tool reports suite-cost change between compatible observations.

The full canonical suite must make its own cost visible so another multi-hour regression cannot remain hidden
because `make.observe` is catalog-only.

---

# 15. Comparison

Two metrics are comparable only when their acquisition definitions match, including:

```text
direct / contained / projection kind
trace root
checkpoint or interval set
serial configuration
source view
scenario
edit
resource scope
effective concurrency
suite definition
```

A metric acquired directly under normal parallelism is not comparable as the same quantity to a serial projection.

The Repair 2 observation remains valid historical evidence under its schema but becomes incompatible with the new
trace-acquisition schema. Do not synthesize missing trace provenance to manufacture a delta.

The new candidate's tracked observation becomes the first canonical baseline for the trace-based suite.

---

# 16. Controls

Add must-fail controls for:

- canonical triplicate sampling;
- `REPEAT` used with `RECORD=1`;
- duplicate direct acquisition of one relation;
- a direct child retained when one exact containing trace already owns it;
- a projection with no trace;
- a projection spanning two traces;
- a projection summing overlapping intervals;
- a projection from a non-serial trace;
- Make jobs not equal to one in a serial trace;
- BuildKit effective maximum parallelism not equal to one in a serial trace;
- the serial observatory configuration altering the normal builder;
- a public Make target with no checkpoint or explicit standalone-only reason;
- unmatched or interleaved Make checkpoints;
- parent time not partitioned into child intervals plus explicit overhead;
- a missing trace fragment accepted until final recording;
- a trace fragment whose assigned coverage relation does not close;
- a synthetic fixture hand-writing a field which the real producer omits;
- `ONLY=` running unrelated traces;
- `PLAN=1` executing a command;
- resume across a changed subject, suite, producer, environment, or serial configuration;
- canonical recording with no suite self-cost;
- a contained metric compared with a normal direct metric as though they were the same kind.

Add must-accept controls for:

- one `make.check` trace yielding several contained Make and Docker metrics;
- one pre-commit trace yielding every anchored child;
- one incremental trace yielding check, proof, e2e, policy, and Docker evidence;
- one serial trace producing exact non-overlapping projections;
- a direct ad hoc `ONLY=make.prove` run;
- an ad hoc repeated selected run;
- a one-sample canonical metric with no noise conclusion;
- an interrupted exact-subject bundle resuming only its missing traces;
- the normal developer builder retaining its existing parallel behavior.

Every new root helper must be mutation-proved load-bearing. Deleting its effect must make its own named controls
fail.

---

# 17. Contract, matrix, and ledger changes

Update:

```text
.review/M2_BUILD_OBSERVATORY.md
.review/BUILD_OBSERVATORY_SUITE.json
.review/M2_OBLIGATION_MATRIX.tsv
.review/M2_RECOMMENDATIONS.tsv
.review/M_SERIES_PLAN.md
.review/NEXT_STEPS.md
.review/REVIEW_REQUEST.md
CLAUDE.md only if its terse usage pointer must change
```

The M2 contract must:

- replace the fixed triplicate policy;
- define traces, contained metrics, projections, and serial acquisition;
- define the minimal trace cover;
- define `PLAN`, `REPEAT`, and `RESUME`;
- state that normal build parallelism is unchanged;
- state that the suite validates each trace before continuing;
- state that suite self-cost is retained.

Reopen every obligation whose cited implementation or evidence changes. At minimum, review and reopen as needed:

```text
M2-02
M2-03
M2-04
M2-05
M2-08
M2-10
M2-13
M2-14
M2-15
M2-16
M2-17
M2-19
```

`M2-17` must no longer claim that M2 performs no optimization without qualification. Its current meaning becomes:

> Project build findings remain assigned to M3 or M4. M2 may optimize only its own acquisition facility under
> the accepted trace-acquisition amendment, without implementing a project performance recommendation.

Do not add a second observation tool or a second public Make target.

---

# 18. Scope limits

Repair 3 may change:

- the observatory runner;
- the suite registry;
- observatory-only builder configuration;
- inert Make checkpoints;
- pre-commit observation metadata where required;
- observation schema, planning, validation, comparison, and recording;
- M2 contracts, matrix, recommendations, usage, and current state.

Repair 3 may not:

- optimize `gate-mutation-test.py`;
- optimize `naming-gate.py`;
- merge policy gates;
- reorder normal Docker stages;
- change normal cache keys;
- change normal Make dependencies;
- change proof-module boundaries;
- alter a `.v` declaration, theorem, proof, constructor, or module;
- alter supported programs, diagnostics, generated Go, goldens, or runtime output;
- begin M3 or M4.

The normal Make and pre-commit execution paths must behave exactly as before when observation is disabled.

The no-host-Python boundary remains absolute.

---

# 19. Work order

1. Install this directive and the trace-acquisition amendment.
2. Reopen affected obligations.
3. Add an exact plan representation and `PLAN=1`.
4. Add observatory-only serial Make and BuildKit configuration.
5. Add inert Make checkpoints.
6. Model traces, containment, intervals, and projections in the registry.
7. Replace canonical triplicates with one trace sample.
8. Change incremental acquisition to one maximal trace per edit shape.
9. Add per-trace validation and exact same-subject resume.
10. Add suite self-cost.
11. Update comparison and usage.
12. Add controls and mutation coverage.
13. Run deterministic preflight and a short real smoke trace.
14. Commit one implementation candidate before any full canonical recording.
15. Run the new full canonical suite once against that exact candidate.
16. Record the observation and close the exact evidence rows.
17. Make one documentation-only freeze.
18. Notify Rob.

Do not run repeated full suites while producer or validator defects remain. Use static controls, production-shaped
fixtures, the plan, short named traces, and per-trace validation first.

---

# 20. Verification

Before the implementation candidate:

```text
make observe HELP=1
make observe LIST=1
make observe PLAN=1
make observe ONLY=make.prove
make observe ONLY=precommit.mutation
make observe ONLY=make.check REPEAT=2
make observatory
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

After committing the candidate:

```text
make observe PLAN=1
make observe RECORD=1
```

Then prove:

1. The plan has no redundant direct relation.
2. Every required command / scenario / edit metric is direct, contained, projected, or cataloged with one reason.
3. Canonical multiplicity is one trace per identity.
4. The working-tree edit use cases run once each, not once per overlapping public command.
5. Serial traces prove Make and BuildKit parallelism equal one.
6. Normal unobserved builds retain their existing parallel configuration.
7. Every trace validates before the next begins.
8. Every projection has exact non-overlapping intervals from one trace.
9. Parent trace time partitions into children plus explicit overhead.
10. `ONLY` runs the minimal selected closure.
11. `REPEAT` remains ad hoc and cannot record.
12. The observation retains suite self-cost.
13. The complete canonical observation validates and names the exact candidate.
14. Generated Go and all goldens remain byte-identical.
15. Runtime stdout, stderr, and exit status remain unchanged.
16. Whole-theory assumption evidence and every accepted M1 boundary remain unchanged.
17. M3, M4, C5 Step 0, and C5 remain forbidden.

The freeze may change only the current M2 recording overlay:

```text
.review/BUILD_OBSERVATION.json
.review/M2_OBLIGATION_MATRIX.tsv
.review/M2_RECOMMENDATIONS.tsv
.review/NEXT_STEPS.md
.review/REVIEW_REQUEST.md
```

No commit follows the freeze.

---

# 21. Definition of done

Repair 3 is complete only when:

- the suite uses a minimal trace cover;
- canonical triplicates are gone;
- one incremental trace per edit shape replaces the current cross-product;
- serial checkpoint evidence can derive contained command costs honestly;
- normal actual wall metrics and serial projections remain distinct;
- the suite validates every trace before continuing;
- exact same-subject resume works;
- `ONLY`, `PLAN`, and ad hoc `REPEAT` work through `make observe`;
- the suite records and compares its own total cost;
- the new canonical observation is produced by one full post-candidate run;
- no project build optimization has been implemented;
- all affected obligations close with exact evidence;
- one implementation candidate and one later documentation-only freeze exist;
- Claude notifies Rob.

Only Rob accepts M2.
