# M2 IMPLEMENTATION REVIEW — BLOCKING — REPAIR 4

## 0. Disposition and exact review basis

**M2 implementation candidate `483791f73b52c134ded3414a8a744deb1151f86b` is BLOCKING.**

It becomes the **fourth blocked M2 implementation candidate**.

Documentation-only freeze:

```text
9539c80a22c5960fec066f1c55ddafd40f90b34d
```

Uploaded snapshot:

```text
fido-main - 2026-08-01T073751.224.zip
```

The ZIP comment resolves exactly to the freeze above.

Accepted earlier checkpoints remain accepted:

```text
C4  C4-ACCEPT-39ea7e3
M0  M0-ACCEPT-86a63db
M1  M1-ACCEPT-6524b43
```

This review does not reopen them.

**M2 Repair 4 is the sole permitted implementation work.**

M3, M4, C5 Step 0, C5, and all project performance optimization remain forbidden.

Use:

```text
/loop 3m
```

Continue until the exact repair is complete or a real M2 contract conflict blocks progress. Notify Rob with the
notification tool when complete or genuinely blocked.

Do not run another full canonical suite until the deterministic checks, exact trace-closure checks, and short
production smoke traces required below pass.

---

## 1. What Repair 3 got right

Keep these results.

The acquisition framework remains sound:

```text
one suite registry
one observatory tool
one Make target
one tracked canonical observation
one ignored local-run area
Git history for historical observations
```

Repair 3 made major real progress:

```text
previous canonical suite   133 direct executions   4 h 07 m 29 s
current candidate           27 direct executions   1 h 37 m 17 s
```

The current observation retains the same 252 canonical metrics while using 79.7% fewer direct executions and
60.7% less suite wall time.

The candidate also delivered:

- one canonical sample per direct trace identity;
- trace containment instead of rerunning overlapping public commands;
- `PLAN=1`;
- named ad hoc `ONLY=`;
- ad hoc `REPEAT=`;
- exact-subject `RESUME=`;
- observatory-only serial Make and BuildKit settings;
- Make and pre-commit checkpoints with stable IDs;
- per-sample raw logs;
- suite self-cost;
- validation after every emitted sample;
- a permanent no-host-Python boundary;
- the same generated Go bytes, goldens, proof surface, and runtime behavior.

The review independently ran the available checks against the uploaded snapshot:

```text
host-Python self-test and boundary gate
Build Observatory 276-control self-test
Build Observatory command, anchor, stage, and path coverage
D-07 human-act controls and generated view
D-24 reference controls and relation
closure-ledger generated view
claim matrix
source-diet controls and snapshot check
naming self-test
OCaml-origin gate
generated-output gate
pinned-target Go build
runtime stdout, stderr, and exit comparison
```

Observed generated hashes remain:

```text
go.mod
d8f8d4f62b5b574067a4e4bf64a298bbe2cb5bc9a28d8f9c321c776e838cf1fa

main.go
b6765619f969e7fd85b4998616d8a515c5a2c0e2d397c3ee915718f35fbc48de
```

The review environment does not contain Docker, Rocq, Dune, extraction, the plugin, or the real staged hook.
The freeze's committed run remains the execution evidence for those paths. The naming snapshot scan and mutation
harness did not complete within the review runtime.

The blockers below concern M2's own exact measurement and resume contracts. They do not erase the measured suite
cost reduction.

---

# 2. Blocking finding A — a completed sample is not a completed trace

## Contract violated

This violates:

- M2 Repair 3 §12;
- M2 contract §3B.9;
- M2-08, M2-13, M2-15, and M2-19;
- the central Repair 3 promise that a malformed early trace stops before the next expensive trace begins.

## Current defect

`checkpointer` writes and checks the partial observation after each sample. Its check is only:

```text
sample_rule_problems
+
identity_problems
```

It does not prove that the completed root trace produced the exact direct, contained, Docker-stage, and analysis
metric relation assigned to that trace by the acquisition plan.

Exact relation closure still runs only at final recording through `check_relation_closed`.

The runner calls the checkpoint when the direct root is emitted and again for each child. It has no exact
"trace complete" event after all children and artifacts have been derived.

## Independently reproduced false green

The cumulative observation prefix through the real:

```text
make.check | project.warm.noop
```

passes `fragment_problems`.

From that completed trace fragment, the reviewer removed each of these retained child samples in turn:

```text
make.prove
docker.prover
make.fcb
```

Every mutated fragment still passed `fragment_problems` with no finding.

A lost checkpoint, lost derived Docker stage, or lost contained command can therefore consume the remaining suite
and fail only at R05 after the final trace. That is the exact multi-hour failure mode Repair 3 was meant to remove.

## Required repair

Create one exact retained **trace-completion object** per real root execution.

It must retain at least:

```text
trace identity
direct root sample identity
command
scenario
edit, when present
sample index
expected metric identities from the acquisition plan
observed metric identities
exact child sample identities
prime identity
analysis-artifact identities, when present
completion state
```

After the root and every derived child and artifact have been emitted:

1. compute the exact expected metric relation for that trace from the same acquisition authority the planner uses;
2. compute the exact observed relation for that trace;
3. require equality in both directions and exact counts;
4. retain the completed trace object;
5. write and validate the partial bundle;
6. only then begin the next trace.

Keep per-sample validation. It catches a different class of defect.

Resume may reuse only a retained trace whose exact trace-completion object validates.

Do not infer completion from the presence of a successful direct root sample.

## Required controls

Must fail:

- one contained child omitted from a completed trace;
- one Docker child omitted;
- one extra child inserted;
- one child assigned to the wrong trace;
- one expected metric produced twice;
- one trace marked complete before child derivation finishes;
- one completed direct root with no trace-completion object;
- one trace-completion object whose expected relation differs from the current plan.

Must accept:

- one exact direct-only trace;
- one exact direct-plus-contained trace;
- one exact direct-plus-Docker-stage trace;
- the current `make.check/project.warm.noop` trace with its exact real child relation.

Mutation-prove every new root rule.

---

# 3. Blocking finding B — runtime checkpoint logs are not fail-closed

## Contract violated

This violates:

- M2 contract §§3B.2, 3B.6, and 3B.9;
- Repair 3 §§7, 12, 16, and 20;
- M2-05, M2-08, M2-10, M2-13, and M2-16.

## Current false greens

`parse_anchor_log` silently accepts all of these:

### End without begin

```text
end make.prove 200
```

Result:

```text
[]
```

### Duplicate begin

```text
begin make.prove 100
begin make.prove 150
end make.prove 200
```

The second begin overwrites the first. The parser reports a 50 ns interval.

### Duplicate end

```text
begin make.prove 100
end make.prove 200
end make.prove 250
```

The extra end is ignored.

Static source anchor pairing does not repair a malformed runtime log. Runtime checkpoint output is the evidence
from which contained timing is derived, and it must fail closed by itself.

## Required repair

Use one runtime checkpoint state machine.

Retain exact start and end timestamps, not only the duration.

Reject:

- begin while the same ID is already open;
- end while that ID is not open;
- a second completed pair for one single-occurrence checkpoint unless the registry explicitly permits and
  identifies the occurrence;
- an end before its begin;
- an open checkpoint at trace end;
- a checkpoint outside its parent root interval;
- an unknown checkpoint;
- an occurrence count different from the registry's declared trace relation.

Make checkpoint siblings and pre-commit nesting may have different structural rules. State each rule once and
validate each grammar against its actual execution model. Do not force Make prerequisites into a nesting model
they do not obey.

Add exact controls and mutation coverage for every rejection above.

---

# 4. Blocking finding C — the parent trace is not proved to partition

## Contract violated

This violates:

- M2 contract §3B.6;
- Repair 3 §§7, 12, 16, and 20;
- the requirement:

```text
parent elapsed
=
non-overlapping child intervals
+
explicit wrapper or unassigned overhead
```

## Current defect

The observation retains child durations, but it does not prove:

- child intervals are non-overlapping;
- every child lies inside the parent;
- the designated top-level children partition the parent;
- the uncovered remainder is retained under a stable overhead identity.

BuildKit aggregate step work is correctly a different metric kind and must not enter this wall-time partition.

For the retained warm `make.check` trace, the current values happen to be:

```text
parent wall                    362,263,112,436 ns
sum of retained Make anchors   362,220,000,000 ns
unretained remainder                43,112,436 ns
```

The near equality is useful evidence, but no current rule proves it and the remainder is not retained under one
stable identity.

## Required repair

For every decomposed parent trace:

1. retain the parent's monotonic start and end;
2. retain every child interval's monotonic start and end;
3. identify the exact top-level partition intervals through stable registry IDs;
4. prove they are inside the parent and pairwise non-overlapping;
5. compute the exact uncovered remainder;
6. retain that remainder under one stable overhead ID owned by the parent trace;
7. require:

```text
sum(partition intervals)
+
overhead
=
parent wall
```

within only the declared clock-resolution accounting.

Do not mix nested BuildKit aggregate step work into the Make or hook wall partition.

The partition is validation evidence. It does not need a second manually maintained summary.

Add controls for overlap, gap not retained, interval outside parent, double-counted nested interval, and a clean
exact partition.

---

# 5. M2 contract amendment — delete the unused serial-projection abstraction

## Finding

The current contract and Repair 3 define:

```text
serial_projection
```

The implementation produces none, hard-codes:

```text
projection_count: 0
```

and supplies none of the projection controls Repair 3 §16 requires.

`OPEN_QUESTIONS.md` acknowledges that the abstraction is defined and unused and proposes leaving the required
controls unwritten.

That is not an acceptable closed obligation. A defined capability with no current consumer, no produced value, and
no controls is speculative residue.

## Required amendment

Delete `serial_projection` from the current M2 system.

Remove it from:

- the M2 contract;
- Repair 3's live restatement;
- metric-kind vocabularies;
- acquisition-relation vocabularies;
- plan output;
- comparison identity;
- suite-cost `projection_count`;
- obligation evidence;
- controls and proposed controls;
- `OPEN_QUESTIONS.md`;
- review prose.

Retain:

```text
direct_wall_elapsed
contained_wall_elapsed
aggregate_step_work
untimed_artifact
```

Trace partition validation from §4 above remains mandatory. It is not a projected replacement metric.

A future checkpoint may introduce a projection only when one current use case needs a cost which no exact direct or
contained interval can provide, and only with its exact theorem-like validation rules and controls.

This is a proposed exact M2 contract amendment based on implementation evidence. Rob's plain-language instruction
to Claude to apply this review is the human approval of deleting the unused abstraction. No separate token is
required.

---

# 6. Blocking finding D — resume does not retain the causal state it needs

## Contract violated

This violates:

- M2 contract §3B.10;
- Repair 3 §13;
- M2-05, M2-07, M2-11, M2-12, M2-13, and M2-15.

## D1. Prime state is not restored

`run_observation` seeds resumed samples and completed trace IDs, then initializes:

```text
primes = {}
```

It does not derive the exact prime map from validated resumed cold traces.

When a cold trace is reused and a cached, warm, or incremental trace remains to run, the cold state is removed from
the chain and `sample_provenance` finds no prime. The remaining trace is skipped as unprimed.

The current real resume demonstration used a warm-only command and did not test this causal chain.

## D2. Analysis artifacts are not restored

Resume carries sample rows only.

If a completed `analysis.rocq-modules` or `analysis.history` trace is reused:

```text
graph = None
history = None
```

remain unchanged in the new run.

The resulting observation can retain the analysis samples while writing:

```text
module_graph: null
history_analysis: null
```

The validator does not bind those samples to their exact analysis artifacts.

## D3. Repeat and resume have no exact joint meaning

The CLI permits:

```text
REPEAT=<n>
RESUME=<bundle>
```

Resume identity is only:

```text
(command, scenario)
```

It does not retain or require the requested repetition count or exact repeated sample identities.

A bundle with fewer repeats can elide the whole trace in a request for more repeats.

## D4. Per-trace suite cost overwrites repeats

`suite_cost.trace_wall_ns` is a map keyed only by:

```text
command|scenario
```

Ad hoc repeated direct traces overwrite each other.

## Required repair

### Prime state

A resumed completed cold trace must either:

- restore the exact retained prime relation from its validated trace-completion object; or
- cause the cold trace to rerun.

No reconstructed equal peer is accepted.

### Analysis artifacts

A completed analysis trace must retain and resume the exact artifact object and digest which its samples establish,
or rerun that trace.

Validation must require:

```text
analysis sample present
iff
its required artifact is present and bound to that exact trace
```

for the canonical analysis commands.

### Repeat

Keep the design simple:

```text
REPEAT and RESUME are mutually exclusive.
```

Reject the combination before any measured work.

### Suite cost identity

Retain per-trace cost as an array or map keyed by exact direct sample / trace identity. Never by command and
scenario alone.

Add must-fail and must-accept controls for all four cases.

---

# 7. Blocking finding E — observation self-evidence and comparison are incomplete

## Contract violated

This violates:

- M2 contract §§3A.7, 3B.11, and 3B.12;
- Repair 3 §§14, 15, 16, and 20;
- M2-05, M2-13, M2-14, M2-15, and M2-19.

## E1. `validation_wall_ns` is absent

Repair 3 explicitly requires suite self-cost to retain:

```text
validation_wall_ns
```

The implementation and canonical observation do not contain it.

Time:

- deterministic preflight validation;
- per-trace validation;
- final validation and recording checks;

with the same monotonic clock used for the suite.

Retain their exact components or one exact total plus a component map. Do not count measured command time as
validation time.

## E2. Suite-cost data is not fully validated

The validator does not prove that:

- direct trace count equals retained completed direct traces;
- contained count equals retained contained samples;
- trace wall entries are exact and complete;
- suite timestamps and elapsed time are coherent;
- preflight and validation costs are present and nonnegative;
- every trace-cost entry names an exact trace.

Add one suite-cost validator used by recording, local loading, Git-ref loading, resume, and comparison.

After the serial-projection deletion, no projection count remains.

## E3. Environment fingerprint is stored but not re-derived

The reviewer changed only:

```text
environment.concurrency.buildkit_max_parallelism
```

from 1 to 2 while leaving the stored host-class fingerprint unchanged.

The mutated observation still passed complete observation validation.

Comparison then treated the observations as the same host class and reported normal timing verdicts because it
explicitly checks only `make_jobs`.

The environment fingerprint must be recomputed from its retained fields and compared with the stored value during
validation.

Comparison must treat all effective timing concurrency as part of compatibility, including at least:

```text
Make jobs
BuildKit maximum parallelism
```

A different serial builder configuration is `incomparable`, with the exact reason.

## E4. Analysis artifacts are not semantically validated

The observation schema requires `module_graph` and `history_analysis` members but permits null or unrelated values
even when their analysis samples are present.

Bind each artifact to:

```text
exact analysis trace
source identity
suite identity
raw artifact digest
derived view digest
```

Require the derived rebuild, critical-path, co-change, and weighted-cost views to equal recomputation from those
exact artifacts.

## Required controls

Must fail:

- missing `validation_wall_ns`;
- false direct or contained count;
- missing trace-cost entry;
- trace-cost entry naming no trace;
- changed environment field with stale fingerprint;
- changed BuildKit parallelism reported comparable;
- analysis sample with null artifact;
- artifact bound to another trace;
- tampered derived graph or history view.

Must accept:

- the repaired canonical observation;
- compatible observations with the same exact effective concurrency;
- a resumed observation carrying exact analysis artifacts.

Mutation-prove every new rule.

---

# 8. Blocking finding F — the candidate/freeze and current-state documents are not closed

## Contract violated

This violates:

- Repair 3's freeze overlay;
- M2-19;
- accepted M1 current-prose law;
- the repository's exact current-state ownership.

## F1. The freeze changed an unauthorized sixth file

Repair 3 permits the freeze to change only:

```text
.review/BUILD_OBSERVATION.json
.review/M2_OBLIGATION_MATRIX.tsv
.review/M2_RECOMMENDATIONS.tsv
.review/NEXT_STEPS.md
.review/REVIEW_REQUEST.md
```

The freeze range also changes:

```text
.review/OPEN_QUESTIONS.md
```

Any question disposition required by implementation belongs in the implementation candidate before its ref is
fixed. The next freeze must remain inside the exact closed overlay.

## F2. The review request says `state: closed`

The repository says the candidate is awaiting Rob's review while `REVIEW_REQUEST.md` says:

```text
state: closed
```

The exact freeze requesting human review must say:

```text
state: requested
```

and must name the exact candidate.

## F3. Current authority reintroduced candidate archaeology

`NEXT_STEPS.md` now retains:

- the three blocked candidate SHAs;
- their repair history;
- a superseded Repair 1 block;
- another first-candidate block.

That conflicts with the accepted M1 rule:

```text
Git owns archaeology.
Current documents state what is true now.
```

Retain one terse sentence:

```text
Earlier M2 candidates are superseded. Git history owns their refs, freezes, findings, and repair narratives.
```

Then state only the current Repair 4 work and accepted checkpoint dependencies.

## F4. The matrix closes a known unresolved contract question

All nineteen rows are marked closed while the live current documents state that `serial_projection` is an open
question and its required controls are absent.

Reopen every obligation affected by this review. Close a row only when its exact public evidence and controls
exist.

## Required freeze topology

Before the new implementation candidate:

- resolve and remove the serial-projection question;
- update every implementation-owned authority and control;
- leave no required implementation edit for after the candidate.

After committing the exact candidate, the documentation-only freeze may modify only the approved closed overlay.

No commit follows the freeze.

---

# 9. Strict-scope disposition table

| Finding | Contract violated | Blocks M2 | Owner |
|---|---|---:|---|
| Per-sample validation does not close each completed trace relation | M2 / Repair 3 trace-validation contract | **yes** | M2 Repair 4 |
| Runtime anchors accept unmatched and duplicate events | M2 checkpoint identity contract | **yes** | M2 Repair 4 |
| Parent trace is not partitioned into intervals plus retained overhead | M2 trace decomposition contract | **yes** | M2 Repair 4 |
| `serial_projection` is defined, unused, uncontrolled residue | M2 contract and one-purpose law | **yes** | M2 Repair 4 contract amendment |
| Resume loses prime state and analysis artifacts | M2 exact-resume contract | **yes** | M2 Repair 4 |
| `REPEAT` and `RESUME` can under-fulfil the requested repetitions | M2 exact-run contract | **yes** | M2 Repair 4 |
| Suite self-cost omits validation and exact trace identity | M2 suite-cost contract | **yes** | M2 Repair 4 |
| Environment fingerprint and BuildKit concurrency comparison are false-green | M2 comparison contract | **yes** | M2 Repair 4 |
| Freeze changed `OPEN_QUESTIONS` outside its allowed overlay | M2 freeze contract | **yes** | M2 Repair 4 |
| Current docs retain superseded candidate history | accepted M1 current-prose dependency | **yes** | M2 Repair 4 |
| Project policy and proof build are slow | none in M2 implementation scope | no | M3 / approved M4 |
| Fragile copied counts and positional prose | none in M2 Repair 4 | no | M3-FRAGILE-PROSE |
| Readable-assumption surface classification | none in M2 Repair 4 | no | M3 |
| General Make, Docker, and gate consolidation | none in M2 Repair 4 | no | M3 |
| Proof-module splitting and build-graph restructuring | none in M2 Repair 4 | no | M4 after plan approval |
| `life.md` | no defect | no | preserve unchanged |

Do not implement any nonblocking row.

---

# 10. Allowed changes

Repair 4 may change only what is required to complete the exact M2 acquisition, validation, resume, comparison, and
current-state contracts:

- `tools/build-observatory.py`;
- the Build Observatory suite registry;
- Make and pre-commit checkpoint instrumentation only where exact timestamps or trace completion require it;
- the M2 contract and Repair 4 authority;
- the M2 obligation matrix and recommendations;
- current M2 review state and open questions;
- mutation controls for the exact M2 rules;
- the canonical observation and final freeze overlay.

It may not:

- change any `.v` declaration, theorem, proof, or module;
- change generated Go or goldens;
- optimize a project gate;
- merge or delete project gates;
- reorder normal Docker stages;
- change normal project cache keys;
- split proof modules;
- change normal Make dependencies;
- implement an M3 or M4 recommendation;
- rewrite `life.md`.

Normal unobserved build behavior must remain unchanged.

---

# 11. Work order

1. Install this review as the sole Repair 4 authority.
2. Reopen the affected obligation rows.
3. Apply the serial-projection contract deletion and remove the resolved question.
4. Build the exact trace-completion object and relation check.
5. Replace the runtime anchor parser with the fail-closed state machine.
6. Add exact parent partition and retained overhead.
7. Repair exact resume: primes, analysis artifacts, and trace identities.
8. Refuse `REPEAT` with `RESUME`.
9. Repair suite-cost validation and add validation timing.
10. Bind environment fingerprints and all effective concurrency.
11. Bind analysis artifacts and derived views.
12. Add every required deterministic control and mutation.
13. Run `PLAN=1` and production-shaped synthetic validation.
14. Run short real smoke traces only:
    - one direct-only fast trace;
    - `make.check/project.warm.noop`;
    - one cold-to-warm prime chain;
    - one interrupted-and-resumed chain with an analysis artifact.
15. Prove each smoke trace closes before running another.
16. Only after all above pass, run one full canonical suite.
17. Commit one exact implementation candidate.
18. Make one later documentation-only freeze inside the exact overlay.
19. Notify Rob.

Do not pay for another full suite to discover a rule which a deterministic control or one short trace could have
found.

---

# 12. Verification

Before the full canonical run:

```text
make observe HELP=1
make observe LIST=1
make observe PLAN=1
make observatory
make diet
make fcb
make claims
make names
```

Run the exact short smoke tests from §11 and validate each retained trace object immediately.

Then run the full project preservation gates:

```text
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

1. Every direct trace has one exact completion object.
2. Each trace's expected and observed relation is equal in both directions.
3. Every runtime checkpoint log is structurally valid.
4. Every decomposed parent partitions into non-overlapping children plus retained overhead.
5. No serial-projection vocabulary or residue remains.
6. A resumed cold trace supplies the exact prime used by its later traces.
7. Resumed analysis traces retain their exact artifacts.
8. `REPEAT` plus `RESUME` is refused before work begins.
9. Suite cost retains and validates preflight, trace, validation, and total cost.
10. Environment fingerprints equal recomputation.
11. BuildKit or Make concurrency changes make comparisons incomparable.
12. Module and history artifacts equal recomputation from their exact retained inputs.
13. The complete registry relation closes.
14. The suite still uses the minimal direct trace cover.
15. The canonical observation names the exact candidate.
16. Generated Go, goldens, runtime behavior, theorem surfaces, and assumption evidence remain unchanged.
17. The freeze changes only the exact closed overlay.
18. M3, M4, C5 Step 0, and C5 remain forbidden.

---

# 13. Definition of done

Repair 4 is complete only when:

- a broken trace cannot survive into the next trace;
- runtime checkpoint evidence fails closed;
- every parent partition closes with explicit overhead;
- the unused serial-projection abstraction is gone;
- exact same-subject resume works across cold-to-warm chains and analysis traces;
- no repeated trace identity is overwritten;
- suite validation cost is retained;
- environment compatibility is derived rather than trusted;
- analysis artifacts are exact and load-bearing;
- current documents contain no superseded candidate narrative;
- every affected obligation closes with exact evidence;
- one complete canonical observation is produced by one repaired candidate;
- one later documentation-only freeze requests Rob's review;
- no commit follows that freeze;
- Claude notifies Rob.

Only Rob accepts M2.
