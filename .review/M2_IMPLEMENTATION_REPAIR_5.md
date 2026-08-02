# M2 IMPLEMENTATION REVIEW — BLOCKING — REPAIR 5

## 0. Disposition and exact review basis

**M2 implementation candidate `d41c5ed2932d2e448bda307b94cf4e268bd0d99b` is BLOCKING.**

It becomes the **fifth blocked M2 implementation candidate**.

Documentation-only freeze `bb570610058e6ef35205f08fb4d1e05db5072f48` is not a separate implementation
candidate.

Exact basis:

```text
Uploaded snapshot:
  fido-main - 2026-08-01T181536.449.zip

Uploaded Git head / documentation-only freeze:
  bb570610058e6ef35205f08fb4d1e05db5072f48

M2 implementation candidate:
  d41c5ed2932d2e448bda307b94cf4e268bd0d99b

Previous blocked M2 candidate:
  483791f73b52c134ded3414a8a744deb1151f86b

Accepted M1 candidate:
  6524b437bd7a7d6b2616563b8789e28a00c7af13
```

Use all code, data, FCB, contracts, gates, and evidence from this exact ref. Do not mix refs, reset, rebase, or
rewrite history.

C4, M0, and M1 remain accepted and are not reopened.

**M2 Repair 5 is the sole permitted implementation work.**

M3, M4, C5 Step 0, C5, and feature work remain forbidden.

Use:

```text
/loop 3m
```

Continue until this exact repair is complete or a real M2 contract conflict blocks progress. When complete or
genuinely blocked, notify Rob with the notification tool.

---

## 1. What Repair 4 got right

Keep these results:

1. Canonical acquisition remains at 27 direct traces rather than the old 133-execution cross-product.
2. The current observation retains 252 canonical metrics.
3. Every trace has a completion object.
4. Missing trace children are checked immediately during acquisition rather than only at final recording.
5. Resume carries exact primes and analysis artifacts or reruns the trace.
6. Both shell and analysis runners consult one resume rule.
7. Analysis artifacts are bound to the traces which produced them.
8. The host-class fingerprint is re-derived from retained environment fields.
9. BuildKit and Make concurrency are compared explicitly.
10. The summed `serial_projection` abstraction is deleted.
11. The current run retains parent partitions and explicit unassigned remainders.
12. The project source, proofs, generated Go, and reviewed runtime result remain unchanged.
13. The no-host-Python boundary remains intact.
14. The candidate/freeze topology is correct: the freeze changes only the observation, matrix, current state, and
    review request.
15. The freeze reports 326 observatory controls and 205 mutation entries.

The trace-cover framework remains the right product shape. Repair 5 closes the remaining authority and
self-validation defects inside it. Do not create a second observatory.

---

# 2. Root finding A — an observation does not retain the basis required to validate itself

## 2.1 Contract violated

This violates:

- M2-04 — exact selection and partial-run meaning;
- M2-05 — exact source, environment, cache, command, sample, graph, and history identity;
- M2-06 — exact cold and cache-cut semantics;
- M2-08 — exact complete canonical coverage;
- M2-13 — one schema and validator for local and tracked observations;
- M2-14 — comparison validates both sides before issuing a verdict;
- M2-15 — recording proves one exact complete run;
- M2-19 — one exact candidate carries one trustworthy canonical observation.

## 2.2 Whole-suite coverage is absent from `validate_observation`

`validate_observation` checks samples which exist. It does not derive the complete expected relation from the
suite and require exact equality in both directions.

Independently reproduced against the uploaded freeze:

1. Remove the complete `make.install-hooks/project.warm.noop` sample and trace.
2. Add `make.install-hooks` to `selection.commands_with_no_scenario_here`.
3. Recompute summaries and suite counts.

The complete validator **accepts** the mutilated observation.

Comparison also accepts it and reports the metric as removed.

The separate `check_relation_closed` function rejects the missing declared metric, but the complete validator,
loader, and comparator do not call that authority.

A selected command can therefore be reclassified after the fact to hide a lost trace.

## 2.3 The suite digest is tautological in comparison

`compare` calls:

```python
validate_observation(obs, obs.get("suite_digest", ""))
```

The observation supplies both sides of its own suite-digest equality.

Independently reproduced:

- replace `suite_digest` with 64 zeroes;
- leave every other field unchanged.

Validation and comparison both accept it.

## 2.4 Subject identity is asserted, not checked

Independently reproduced mutations which validation and comparison accept:

```text
subject.commit            replaced with 40 zeroes
subject.tree              replaced with 40 ones
subject.content_digest    replaced with arbitrary bytes
subject.inventory_digest  replaced with arbitrary bytes
```

The retained samples are not bound to that subject.

## 2.5 Environment completeness can be erased

The environment fingerprint is re-derived, which was a real Repair 4 improvement.

But `validate_observation` does not call `check_environment_complete`.

Independently reproduced:

1. Delete required `environment.cpu_model`.
2. Recompute `host_class_fingerprint` from the incomplete fields.

Validation and comparison accept the observation.

## 2.6 Cache-cut semantics are absent from complete validation

`check_cut_observed` runs during acquisition, but complete validation and comparison do not rerun it.

Independently reproduced:

1. Change the retained direct `make.prove/project.cold.prover` stage state from `rebuilt` to `hit`.
2. Recompute its `cache_after` block from the falsified stage evidence.
3. Keep all identities and summaries coherent.

The complete validator accepts the observation.

Calling `check_cut_observed` directly rejects it because the declared invalidation root stayed cached.

## 2.7 Root correction — one exact `ObservationBasis`

Design the retained causal object first.

Add one exact basis to every observation. The names may differ, but its topology must be equivalent to:

```text
Observation
  basis
    exact canonical suite-registry snapshot
    suite digest derived from that exact snapshot
    exact Docker-stage graph used by planning
    exact request
    exact selection derived from that request
    exact AcquisitionPlan built once before execution
    exact subject
    exact environment
    exact checkpoint grammar and clock identity
  traces
  measurements
  analysis artifacts
  derived views
  suite cost
```

### Captured suite versus live suite

`.review/BUILD_OBSERVATORY_SUITE.json` remains the sole live authority for planning a new run.

The observation retains the exact canonical registry snapshot used by that run as historical provenance. It is
not a second live authority.

The validator must:

1. parse the retained registry snapshot through the same suite loader used for live runs;
2. recompute its canonical digest;
3. require that digest to equal the retained `suite_digest`;
4. reject an arbitrary or malformed retained suite;
5. use that exact captured suite to interpret historical and local observations.

Do not pass a caller-supplied suite digest into `validate_observation`.

The API must become conceptually:

```python
validate_observation(observation)
```

not:

```python
validate_observation(observation, observation["suite_digest"])
```

### One plan authority

Build one exact `AcquisitionPlan` before execution and retain that exact object.

The plan must own:

- request and selection identity;
- trace IDs;
- command, scenario, edit, role, scope, and metric-kind identities;
- every expected metric;
- exact sample multiplicity;
- contained ownership;
- catalog-only exclusions and reasons;
- the stable trace order.

The planner, runner, trace completion, coverage validator, recording, resume, and final validator all consume the
same plan object.

Delete parallel semantic builders which independently reconstruct the same expected relation.

A trace completion object should retain an exact `plan_trace_id`, not a copied independent expected-metric
authority. Expected metrics are projected from the exact retained plan entry.

If a copied view remains for convenience, require byte-for-byte or structural equality to that plan projection
and never treat the copy as authority.

### Complete validation

From the retained basis, the one complete validator must prove:

- the request is valid under the retained suite;
- the retained selection is exactly the result of that request;
- the retained plan is exactly the plan built from the retained suite, stage graph, and selection;
- every plan trace has exactly one completion object;
- no completion object names a trace outside the plan;
- the union of completed trace metrics equals the plan’s required relation in both directions with exact counts;
- every direct sample belongs to one exact plan trace;
- every contained sample belongs to one exact parent trace;
- every catalog-only or unmeasured command has the exact reason the retained suite gives;
- every direct sample’s cache cut satisfies the retained scenario definition;
- environment completeness and fingerprint both hold;
- subject identity and sample source identity cohere.

For source identity:

- every unedited direct sample must use the exact subject content digest;
- every derived child must use its exact parent source digest;
- each incremental sample must retain its exact edit identity and resulting source digest;
- a Git-ref loader must verify the subject commit, tree, inventory, and content against that exact Git object when
  the repository is available;
- a dirty local run remains explicitly dirty and may not become canonical.

### One validator everywhere

The same complete validator must run for:

```text
fragment close
resume load
local observation load
Git-ref observation load
comparison baseline
comparison candidate
record eligibility
tracked canonical observation
```

No caller may choose a weaker definition of “valid.”

### Permanent canonical-observation gate

The permanent `make observatory` target and staged pre-commit observatory stage currently check only self-tests and
surface coverage.

Add a self-contained semantic validation of the tracked `.review/BUILD_OBSERVATION.json`.

A staged change to the canonical observation, suite, or validator must be checked from the staged snapshot.

A tampered canonical observation must not commit merely because its command registry still classifies every
target.

---

# 3. Root finding B — trace partition and checkpoint evidence remain self-authored

## 3.1 Contract violated

This violates:

- M2-05 — exact retained evidence;
- M2-08 — exact trace coverage;
- M2-13 — one semantic validator;
- M2-16 — measurement anchors preserve and establish the claimed execution;
- M2-19 — the candidate’s observation establishes its own metric claims.

## 3.2 A partition is optional

`TRACE_MEMBERS` requires a `partition` key, but `trace_problems` validates it only under:

```python
if part:
```

Independently reproduced:

- set a completed `make.check` partition to `null`;
- set a completed `precommit.full` partition to `null`.

The complete validator accepts both.

A key whose value may be null is not a retained partition.

## 3.3 Partition members are not bound to retained runtime events

Independently reproduced mutations which validation accepts:

- rename a partition member to `totally.not.a.real.child`;
- delete one real member and move its duration into unassigned overhead;
- shift a member so that it overlaps another member;
- make a member’s duration negative;
- add ten seconds to a member and raise the self-declared clock resolution to twenty seconds.

The current checks only recompute `covered_ns` from the partition’s own members and compare covered plus overhead
to the parent. The partition can therefore write a coherent story unrelated to the runtime checkpoint evidence.

## 3.4 The parser does not enforce the grammars its contract states

The parser uses one generic stack.

The contract states two exact grammars:

```text
Make:
  flat siblings
  at most one checkpoint open
  no enclosing root

Pre-commit:
  exactly one precommit.full root
  sibling stages one level below it
  no stage nested inside another stage
```

Independently reproduced inputs accepted by `parse_anchor_log`:

```text
nested Make checkpoint
nested pre-commit stage at depth two under the root
a later checkpoint pair whose monotonic timestamps move backwards
```

Stack balance alone does not establish either grammar.

## 3.5 Root correction — retained checkpoint sequence and one partition constructor

Each trace plan entry must state its checkpoint grammar.

Retain the exact parsed begin/end event sequence required to validate the tracked observation after local raw logs
are gone. Each event must retain:

```text
sequence index
begin or end
stable checkpoint ID
monotonic timestamp
clock identity
clock resolution
```

Use stable IDs, never line numbers or output order as identity.

The parser must receive the exact grammar from the plan and reject:

### Make grammar

- any nesting;
- more than one open checkpoint;
- an enclosing root;
- repeated pairs;
- unknown checkpoints;
- timestamps moving backwards;
- end before begin;
- open checkpoint at end.

### Pre-commit grammar

- missing or repeated `precommit.full` root;
- a child before the root begins;
- a child after the root ends;
- depth other than root depth zero and child depth one;
- one child nested inside another child;
- repeated pairs;
- unknown checkpoints;
- timestamps moving backwards;
- root not closing last.

### Other traces

An uninstrumented trace must state that it is atomic. It may not use null to mean both “not applicable” and
“evidence missing.”

Use an explicit tagged partition:

```text
kind: decomposed
```

or:

```text
kind: atomic
```

Every completed trace has one exact partition object.

### Recompute, do not trust

The final validator must:

1. re-parse or revalidate the retained checkpoint sequence under the trace grammar;
2. derive the exact interval set;
3. derive the exact top-level partition members;
4. derive clock resolution from the retained clock authority;
5. recompute covered time and exact unassigned remainder;
6. require the retained partition to equal recomputation;
7. bind every contained checkpoint metric to its exact event interval and exact child sample;
8. reject unknown member IDs, missing members, extra members, overlap, negative duration, and out-of-order events.

BuildKit aggregate step work remains outside the wall-clock partition.

The clock allowance is the instrument’s exact retained resolution. It is never an unrestricted value supplied by
the partition being judged.

---

# 4. Root finding C — suite self-cost is not closed evidence

## 4.1 Contract violated

This violates:

- M2-05 — exact timing provenance;
- M2-13 — canonical and local observations use one valid schema;
- M2-15 — recording verifies the observation it publishes;
- M2-19 — the canonical observation truthfully reports the facility’s own cost;
- Repair 4 E1/E2.

## 4.2 Current false greens

Independently reproduced mutations accepted by `validate_observation`:

```text
suite_wall_ns = 1
delete preflight validation components and adjust validation_wall_ns
retain only per_trace validation and adjust validation_wall_ns
set suite_completed one second after suite_started while suite_wall_ns remains 112 minutes
```

The validator checks:

- nonnegative durations;
- component sum;
- timestamp ordering;
- a trace-cost key set.

It does not establish that the values describe the run.

## 4.3 Required validation work was never timed

Repair 4 required timing:

```text
deterministic preflight
per-trace validation
final validation
recording checks
```

The current canonical observation retains:

```text
preflight_controls
preflight_plan
per_trace
```

It does not retain final validation or recording checks.

`check_record_eligible` and final validation execute after the suite-cost block has already been built.

## 4.4 Root correction — exact monotonic suite lifecycle

Retain:

```text
suite_started_monotonic_ns
suite_completed_monotonic_ns
suite_wall_ns
suite_started_utc
suite_completed_utc
validation components
per-trace validation costs
```

Require:

```text
suite_wall_ns =
  suite_completed_monotonic_ns - suite_started_monotonic_ns
```

UTC values are descriptive. Monotonic values own elapsed time.

The validation component vocabulary is fixed by the retained suite schema and includes at least:

```text
preflight_controls
preflight_plan
per_trace
final_validation
recording_checks
```

A component which is not applicable must carry an explicit state and reason. Do not encode “not run” as a
zero-duration measurement.

Remove duplicated suite-cost fields when the same fact already has an exact owner:

- trace wall time is owned by each direct root sample;
- direct trace count is derived from the retained plan and completions;
- contained metric count is derived from the plan and measurements.

If a summary view remains, recompute and check it.

## 4.5 Finite two-phase closeout

Avoid an infinite “validate the validation” regress.

Use this finite topology:

1. Build a provisional observation from the completed acquisition.
2. Time the final semantic validator over that provisional observation.
3. Time recording-eligibility checks without publishing.
4. Insert those exact durations and the final monotonic completion time.
5. Run one final **pure, untimed, non-mutating close verifier** over the now-closed observation.
6. Only after that verifier passes may local comparison artifacts or the canonical file be published.

The final close verifier is outside the measured suite by explicit contract. It may verify the measurement; it may
not change it.

No later writer may alter the observation after the close verifier.

Add a control proving that a post-close mutation is rejected.

---

# 5. Root finding D — the live contract still contains two acquisition policies

## 5.1 Contract violated

This violates M2’s current documentation authority and M2-03/M2-13/M2-19.

Section 3B.8 says:

```text
Canonical multiplicity is one.
The fixed triplicate policy is deleted.
REPEAT is ad hoc only.
```

Section 11 still says:

```text
warm/no-op scenarios: three samples
incremental scenarios: three samples per edit
light direct commands: three samples
```

Both cannot govern one canonical suite.

## 5.2 Required correction

Delete the stale Section 11 triplicate policy.

Replace it with one concise rule:

```text
Canonical acquisition retains one real trace per exact trace/scenario/edit identity.
Ad hoc REPEAT requires a named partial selection and cannot accompany RECORD or RESUME.
Git history supplies the repeated long-term record.
```

Do not retain both formulations “in agreement.”

Update every usage example and matrix row which still implies canonical triplicates.

---

# 6. Root finding E — a local bundle may omit its declared comparison artifacts

## 6.1 Contract violated

M2 Section 9 says every run first writes:

```text
observation.json
raw/
comparison.json
comparison.txt
```

The implementation writes the comparison files only when a compatible baseline comparison succeeds.

The current freeze reports that no comparison exists because the earlier baseline predates trace objects.

The bundle therefore does not have the shape the contract claims.

## 6.2 Required correction

Every completed local bundle writes both comparison files.

When no verdict is available, write an explicit result:

```json
{
  "status": "unavailable",
  "reason": "baseline observation uses an incompatible schema"
}
```

The plain text view states the same reason.

Do not issue metric verdicts from an invalid observation.

An incomplete run may use:

```text
status: incomplete
```

and must still retain enough state to diagnose and resume it.

---

# 7. One permanent validator, not one more gate beside it

Implement one root validator which owns observation validity.

Conceptually:

```python
validate_observation(observation)
```

It must call or subsume:

```text
suite snapshot and digest validation
request and selection validation
AcquisitionPlan validation
whole-suite relation closure
subject validation
environment completeness and fingerprint
sample rules
parent and prime identity
cache-cut validation
trace completion
checkpoint grammar
partition recomputation
analysis-artifact binding
summary recomputation
suite-cost closure
```

The following paths invoke that same root:

```text
fragment validation
resume
load local path
load Git ref
compare
record eligibility
permanent canonical-observation gate
```

Do not keep `check_relation_closed`, `check_cut_observed`, plan validation, or environment completeness as strong
rules which the complete validator may omit.

Helper functions may remain as owned subrelations. They may not be alternate validity entrypoints.

---

# 8. Exact reproduced controls

Add controls for every reproduced defect.

## 8.1 Whole-observation basis

Must fail:

- one declared trace and sample removed, then listed as unmeasured;
- one trace present which the retained plan does not schedule;
- arbitrary `suite_digest`;
- retained suite snapshot changed without the digest following;
- malformed retained suite snapshot with a matching self-authored digest;
- subject commit changed;
- subject tree changed;
- subject content digest changed;
- subject inventory digest changed;
- required environment field removed and fingerprint recomputed;
- cold invalidation root changed from rebuilt to hit;
- canonical observation changed while `make observatory` remains green.

Must accept:

- the exact canonical full selection;
- a valid partial request whose exact selection and plan derive from the retained suite;
- a historical observation whose captured suite differs from the current live suite but validates against its own
  exact retained basis;
- a comparison which reports incompatible suite definitions rather than treating them as equal.

## 8.2 Runtime checkpoints and partition

Must fail:

- null partition;
- unknown partition member ID;
- real member removed and its duration moved to overhead;
- overlapping members;
- negative member duration;
- self-declared inflated clock resolution;
- nested Make checkpoints;
- nested pre-commit child stages;
- missing pre-commit root;
- repeated pre-commit root;
- backward monotonic timestamps;
- retained partition differing by one nanosecond from recomputation;
- contained child wall time differing from its exact checkpoint interval.

Must accept:

- exact flat Make siblings;
- exact pre-commit root with sibling children;
- one-clock-tick quantization overshoot retained under the exact instrument resolution;
- an explicit atomic trace partition;
- an exact decomposed trace partition.

## 8.3 Suite self-cost

Must fail:

- `suite_wall_ns = 1`;
- monotonic start/end not matching suite wall;
- UTC duration unrelated to the retained lifecycle where the contract requires consistency;
- missing preflight component;
- missing per-trace validation;
- missing final validation;
- missing recording checks on a recording run;
- trace validation cost for no trace;
- completed trace with no validation cost;
- post-close mutation;
- a writer publishing before the pure close verifier.

Must accept:

- exact two-phase closeout;
- an ad hoc non-recording run with recording eligibility explicitly not applicable;
- the exact current trace count and self-cost derived from retained roots.

## 8.4 Bundle output

Must fail:

- a completed run with no `comparison.json`;
- a completed run with no `comparison.txt`;
- an unavailable comparison represented by missing files;
- an invalid observation producing timing verdicts.

Must accept:

- a compatible comparison;
- an explicit unavailable comparison with exact reason;
- an incomplete resumable bundle.

Every new root helper must be mutation-proved load-bearing. Deleting the exact rule must make its own named controls
fail for the intended reason.

A skipped or vacuous control cannot count as passed.

---

# 9. Candidate execution order

Do not pay for another full suite until the structure is closed.

Required order:

1. Install this Repair 5 authority.
2. Reopen the affected M2 obligation rows.
3. Correct the live M2 contract’s multiplicity and bundle rules.
4. Design and document the exact `ObservationBasis` and `AcquisitionPlan` topology.
5. Collapse planning and expected-relation production to one plan authority.
6. Implement the self-contained root validator.
7. Add the captured suite, request, selection, plan, subject, environment, and clock provenance.
8. Fix checkpoint grammar and retained event-sequence validation.
9. Make partition a required tagged object and bind it to events and contained samples.
10. Close suite self-cost with the finite two-phase design.
11. Add permanent canonical-observation validation to working-tree and staged paths.
12. Add all deterministic controls and mutations.
13. Construct a production-shaped synthetic canonical observation through the real producer and make every
    reproduced mutation fail.
14. Run `PLAN=1` and prove the canonical plan remains 27 traces and 252 metrics unless the exact registry itself
    justifies a different count.
15. Run short real smoke traces:
    - one decomposed Make trace;
    - one decomposed pre-commit trace;
    - one atomic or analysis trace;
    - one resume trace.
16. Validate each smoke immediately and inspect its bundle.
17. Only then run one complete canonical recording.
18. Freeze one exact implementation candidate with no later implementation change.
19. Notify Rob.

A smoke failure is repaired and rerun as a smoke. Do not start the full suite to test a structural rule.

---

# 10. M2 obligation matrix

Reopen at least:

```text
M2-03
M2-04
M2-05
M2-06
M2-08
M2-13
M2-14
M2-15
M2-16
M2-19
```

Reopen any other row whose exact evidence changes.

Do not keep a closed row pointing at a helper which the root validator does not invoke.

Each closed row names:

```text
one owning authority
one exact implementation surface
one positive retained evidence surface
one negative control
one mutation control
the real gate which runs it
```

The claim-matrix checker still does not judge theorem or schema strength. Human review does.

---

# 11. Allowed changes

Repair 5 may change:

- `tools/build-observatory.py`;
- the Build Observatory entries in `tools/gate-mutation-test.py`;
- `.review/BUILD_OBSERVATORY_SUITE.json`;
- `.review/BUILD_OBSERVATION.json`;
- `.review/M2_BUILD_OBSERVATORY.md`;
- `.review/M2_OBLIGATION_MATRIX.tsv`;
- `.review/M2_RECOMMENDATIONS.tsv` only for exact M3/M4 assignments;
- `.review/NEXT_STEPS.md`;
- `.review/OPEN_QUESTIONS.md` only when an existing question is answered or restated by this repair;
- `.review/REVIEW_REQUEST.md`;
- Makefile and staged-hook observatory wiring only to add the permanent canonical-observation validation and exact
  checkpoint evidence required above;
- D-24 references and owner markers required by those exact files.

It may not change:

- any `.v` declaration, theorem, proof, constructor, module, or semantic authority;
- OCaml extraction or transport behavior;
- generated Go or goldens;
- supported or rejected programs;
- diagnostics;
- normal build concurrency;
- normal Docker stage order;
- project cache keys for performance;
- the mutation or naming tools for speed;
- proof-module structure;
- general Make or hook architecture;
- the no-host-Python boundary;
- M3 or M4 implementation;
- `life.md`.

No FCB amendment is required unless a current fixed point actually conflicts with this repair. If one does, stop,
name it exactly, and propose the amendment. Do not work around it.

---

# 12. Nonblocking findings and performance signals

These do not block M2 and must not be implemented in Repair 5.

The current trace data strongly suggests:

```text
warm make.check root             about 418 s
  make.fcb contained             about 364 s
  make.names contained            about 39 s

warm precommit.full root         about 423 s
  precommit.mutation             about 364 s
  precommit.naming                about 39 s
```

Those are valuable M3/M4 signals, but the observation validator still accepts false provenance and false
partitions. Treat the figures as exploratory until Repair 5 records a self-validating canonical observation.

Keep all current M3 assignments, including:

- mutation and naming cost;
- host/container build architecture beyond the accepted no-host-Python boundary;
- duplicate or weaker gate analysis;
- fragile prose;
- claim-matrix subject factoring;
- dormant M1 replay modes;
- readable assumption-surface classification.

Keep M4 assignments for proof partitioning, module splitting, cache architecture, and approved mechanical
restructuring.

`OQ-M2-03` remains nonblocking. Keep `wall_elapsed` unless Rob decides otherwise; do not spend Repair 5 moving
hook-stage metric identities.

---

# 13. Verification

Before the full canonical run, complete all deterministic, synthetic, mutation, and smoke verification.

Before freezing, run the existing complete project checks, including:

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
make observatory
```

Run the real pre-commit hook over the exact staged snapshot without bypassing it.

Run:

```text
make observe PLAN=1
```

and retain the exact plan evidence.

Run the complete canonical suite once:

```text
make observe RECORD=1
```

Then prove:

1. the tracked observation validates through the permanent observatory gate;
2. the staged copy validates through the staged hook;
3. every plan trace has one exact completion;
4. every required metric is present exactly once;
5. every direct cold sample satisfies its exact cache cut;
6. every partition is exact recomputation from retained checkpoint events;
7. every suite-cost field follows from retained monotonic evidence;
8. every comparison file exists with either a verdict or an exact unavailable reason;
9. generated `go.mod` and every `.go` byte remain unchanged;
10. runtime stdout, stderr, and exit status remain unchanged;
11. all readable assumption surfaces remain closed;
12. the whole-theory assumption audit remains green;
13. M3, M4, C5 Step 0, and C5 did not begin.

Do not create a prose-heavy closure audit. The basis, plan, observation, controls, mutation results, gate output, Git
diff, and commit history are the evidence.

---

# 14. Definition of done

Repair 5 is complete only when:

- one exact captured suite basis makes each observation self-validating;
- one exact retained AcquisitionPlan owns the expected relation and trace acquisition;
- removing a declared trace cannot be hidden by editing the retained selection;
- arbitrary suite, subject, or environment identity fails;
- cold cache claims are revalidated on every load and comparison;
- every checkpoint log obeys its exact grammar;
- every trace has one explicit atomic or decomposed partition;
- every partition is derived from retained events and bound to exact child samples;
- suite self-cost follows from one exact monotonic lifecycle;
- final validation and recording checks are timed before one pure close verifier;
- the live M2 contract contains one multiplicity rule;
- every completed bundle contains both comparison files;
- the permanent working-tree and staged gates validate the tracked canonical observation;
- all reproduced false greens have exact controls and load-bearing mutations;
- short smoke traces pass before the full run;
- one complete canonical suite runs once and records;
- the new observation is bound to one exact implementation candidate;
- one later documentation-only freeze requests Rob’s review;
- no commit follows the freeze;
- Claude notifies Rob.

Only Rob accepts M2.
