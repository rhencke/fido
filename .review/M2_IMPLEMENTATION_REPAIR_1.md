# M2 IMPLEMENTATION REVIEW — BLOCKING — REPAIR 1

## 0. Disposition

**M2 implementation candidate `8325ddb9ee2dcb1087dbe22d754b9a7d4c5a3b43` is BLOCKING.**

It becomes the **first blocked M2 implementation candidate**.

Documentation-only freeze `2222763f915285ba7de21e5659daf6456ca68214` is not a separate implementation candidate.

M1 remains accepted at `6524b437bd7a7d6b2616563b8789e28a00c7af13`. C4 and M0 remain accepted. This review does not reopen them.

**M2 repair 1 is the sole permitted implementation work.**

M3, M4, C5 Step 0, C5, and all feature work remain forbidden.

Do not optimize the build in this repair. Repair the observatory so its observations mean what they claim.

Use:

```text
/loop 3m
```

Continue until this full repair is complete or a real M2 contract conflict blocks progress. When complete or genuinely blocked, notify Rob with the notification tool.

---

## 1. Exact review basis

```text
Uploaded snapshot: fido-main - 2026-07-29T075108.693.zip
Uploaded Git head / documentation-only freeze:
  2222763f915285ba7de21e5659daf6456ca68214

Blocked M2 implementation candidate:
  8325ddb9ee2dcb1087dbe22d754b9a7d4c5a3b43

Accepted M1 implementation:
  6524b437bd7a7d6b2616563b8789e28a00c7af13

M2 authority:
  .review/M2_BUILD_OBSERVATORY.md

M2 obligation matrix:
  .review/M2_OBLIGATION_MATRIX.tsv

Accepted review basis:
  .review/REVIEW_BASIS.md
```

Use all code, policy, evidence, and documentation from this exact ref. Do not reset, rebase, rewrite history, or mix refs.

Preserve `life.md` exactly.

---

## 2. What the first candidate got right

Keep these results.

1. The permanent shape is sound:

   ```text
   one suite registry
   one observatory tool
   one Make entry point
   one tracked canonical observation
   one ignored local-run area
   Git history for old observations
   ```

2. `make observe` supports generated help, generated listings, named command and group selection, named scenario selection, comparison, and recording.
3. The registry discovers and classifies the current Make, Docker, and pre-commit surfaces in both directions.
4. Pre-commit instrumentation is inert when observation is disabled.
5. The candidate retains raw samples rather than only averages.
6. The candidate retains exact Git subject and toolchain fields.
7. The module set comes from Dune rather than a copied prose list.
8. The module graph, downstream sets, critical path, and Git history analysis are real features rather than placeholders.
9. Mutating source-tree commands already use disposable worktrees in the ordinary path.
10. Partial runs cannot record the canonical observation.
11. Help and list output are generated from the same registry used by execution.
12. The implementation found and fixed several of its own false-green controls before the freeze.
13. The implementation changed no Rocq theorem or generated Go meaning.
14. Generated `go.mod`, `main.go`, and reviewed runtime output remain unchanged.

The implementation has a real base. Do not replace it with unrelated infrastructure or a large framework.

The tracked timing data is not acceptable, because several labels, summaries, and coverage claims do not describe the work which ran.

---

# 3. Blocking finding A — scenario and cache labels do not describe the executed state

## 3.1 Contract violated

This violates M2-05, M2-06, M2-07, M2-08, M2-15, and M2-19.

The contract separates:

```text
cold versus warm session state
cached versus uncached project state
```

The implementation resets and primes once per scenario, then runs every direct command in that shared scenario state.

## 3.2 Cross-command cache contamination

The canonical `cold.uncached` samples ran in this order:

```text
make.audit-fresh   about 158 s
make.check          about 55 s
make.e2e             about 1.7 s
make.emit            about 1.8 s
make.prove           about 1.7 s
```

Only the first command started before another measured project command had populated the builder. The later commands reused work from earlier commands but were all labeled `cold.uncached`.

Every one of the 399 samples records `cache_after` equal to `cache_before`. A command which built the theory, emitted code, or filled a BuildKit layer therefore claims that no cache state changed.

The current `cold.uncached` cache record also says:

```text
buildkit_layers: empty
```

although the suite has already built the toolchain base in the same builder. A single `buildkit_layers` state cannot say both “toolchain layers are primed” and “project layers are empty.”

## 3.3 Cold and warm are not implemented as a separate session axis

The runner launches new subprocesses for all command samples and uses one persistent builder. It does not retain one explicit source session for warm runs or create a fresh source session for cold cached runs.

The current labels therefore reduce cold/warm to names around one shared sequence rather than an implemented session boundary.

## 3.4 Prime provenance is too weak

A reused cache names one run ID, but it does not retain or verify:

- the exact command and sample which populated it;
- the exact source, suite, scenario, and edit identity;
- the project-cache namespace;
- the actual builder state after an external prune or interrupted run;
- the `subject_inventory_digest` already written into the state file.

A stale JSON file can continue to call a changed or pruned cache primed.

## 3.5 Required root repair

Use one exact **measurement chain** per direct root command.

The simplest accepted design is an isolated observatory builder/cache namespace for each root command chain. An equivalent design is allowed only if it proves the same initial and transition states.

For each direct root command which uses BuildKit:

1. Create or reset its isolated measurement cache.
2. Prime only the pinned toolchain layers. This prime is retained but not counted as project build time.
3. Create a fresh exact source session.
4. Run `cold.uncached` with no reusable project result from another measured command.
5. Record the cache transition and the exact sample which produced the reusable state.
6. Create a new exact source session with the same command-chain cache.
7. Run `cold.cached` against that exact prime.
8. Keep that source session and cache identity for `warm.cached.noop`.
9. Run incremental samples against the exact named warm prime under §4.
10. Remove the isolated chain only after its observation is safely written.

A lightweight command which does not use a project cache records that authority as `not-applicable`, not `empty` or `reused`.

Replace the ambiguous cache authority with enough exact parts to state the truth. At minimum distinguish:

```text
buildkit_toolchain_layers
buildkit_project_layers
dune_build
go_build
go_module
generated_intermediate
apt_download
opam_download
```

A state may be `empty`, `primed`, `reused`, `not-applicable`, or `uncontrolled` only when the runner can establish that state.

Each sample must retain:

```text
chain_id
session_id
cache_namespace
cache_before
cache_after
prime_sample_id, when reused
```

A cold sample must never follow another measured project command in the same project-cache namespace.

Avoid cross-invocation cache-state trust where possible. The preferred design establishes the prime and every dependent sample in one observatory invocation. If cross-run reuse remains, validate the exact source, suite, command, scenario, builder, BuildKit identity, cache namespace, and actual cache existence before use.

## 3.6 Required controls

Add must-fail controls for:

- two direct commands sharing one `cold.uncached` project cache;
- a later cold sample observing a cache populated by an earlier command;
- `cache_after` unchanged after a command populates a cache;
- toolchain layers called empty after the toolchain prime;
- a cached sample naming only a run and not the exact prime sample;
- a prime from another command;
- a prime from another source or suite digest;
- a prime from another builder or cache namespace;
- a cache-state file surviving an external cache deletion;
- a cold cached run reusing the prime source session;
- a warm run using a new session while claiming the same session;
- a cache authority given a state the runner cannot establish.

Add must-accept controls for one complete root-command chain and two distinct command chains which cannot contaminate each other.

Mutation-test every new root rule.

---

# 4. Blocking finding B — incremental samples and metric identity answer the wrong question

## 4.1 Contract violated

This violates M2-05, M2-06, M2-11, M2-12, and M2-14.

## 4.2 Repeated edit text turns later samples into cache hits

For each edit shape, the runner applies the same bytes three times in three worktrees while reusing one builder cache.

Observed `make.check` samples include:

```text
edit.foundation.float    about 178 s, 50 s, 50 s
edit.proof.compilable    about 183 s, 49 s, 49 s
edit.leaf.emit           about 182 s, 51 s, 50 s
```

The first sample measured the rebuild. The next two matched the first sample’s BuildKit content and measured cache hits.

The median therefore reports about 50 seconds for edit shapes whose first rebuild cost was about 180 seconds.

This is not timing noise. It is a different cache state.

## 4.3 Edit identity is discarded from summaries

The summary key is currently:

```text
command_id | scenario_id
```

All six edit shapes and all eighteen `make.check` incremental samples are pooled into one metric.

The observation retains `edit_id` in raw samples, but the canonical summary and comparison discard it.

## 4.4 Derived parent identity is also discarded

A Docker stage can be observed under several live parents. For example, the same stage may appear while running prove, emit, e2e, regenerate, or the hook.

Raw samples retain `derived_from`. The summary key discards it and merges unlike parent contexts into one median.

A derived child selected by `ONLY` also inherits the support role of its parent, so the requested child can be reported as support rather than selected.

## 4.5 Raw log identity collides

The log path contains command, scenario, and sample index, but not edit ID or derived parent context.

Incremental samples for different edits therefore overwrite each other. The observation can retain hashes for raw logs which no longer exist in the bundle.

## 4.6 Required root repair

Define one stable metric identity:

```text
command_id
scenario_id
edit_id or none
derived_parent_id or none
resource_scope
```

Every sample, summary, comparison row, raw-log path, and recommendation evidence ID uses the same identity.

For incremental samples, choose one of these exact methods:

1. restore the same exact post-prime cache snapshot before each sample; or
2. apply a distinct deterministic inert edit for each sample so the prior sample cannot be an exact cache hit.

The second method is simpler. The registry should own the stable per-sample edit procedure and its fingerprint. The runner must verify that the expected rebuild path actually ran rather than accepting a cached no-op under an incremental label.

Comparison must require the same edit fingerprint.

Derived summaries must be per parent context. Do not merge a stage observed under different parents into one timing result.

A selected derived child is marked selected even though its live parent is support.

Raw log names must include the full stable sample identity. Recording verifies every direct raw log exists and matches its retained digest before the canonical observation can be written.

## 4.7 Required controls

Add must-fail controls for:

- three identical edit samples where samples two and three become exact cache hits;
- summaries which omit edit ID;
- summaries which merge two edits;
- summaries which omit derived parent ID;
- summaries which merge the same stage from two parents;
- a selected derived child labeled support;
- two samples mapping to one raw-log path;
- a retained raw-log digest whose file is absent;
- comparison across changed edit definitions.

Add must-accept controls for three independent samples of one edit, two edit shapes under one command, and one derived stage under two parents.

---

# 5. Blocking finding C — recording proves command presence, not complete measurement coverage

## 5.1 Contract violated

This violates M2-02, M2-08, M2-10, M2-15, and M2-19.

## 5.2 Missing canonical command-scenario pairs

The registry declares canonical measurements which the tracked observation does not contain:

```text
docker.module-graph       cold.uncached
docker.module-graph-log   cold.uncached
docker.profile            cold.uncached
docker.profile            cold.cached
docker.profile-log        cold.uncached
docker.profile-log        cold.cached
docker.sync               cold.uncached
```

`analysis.history` declares three warm no-op samples but the observation contains one.

The separate noncanonical bootstrap scenario also produced no sample in the tracked observation. It need not enter the canonical record, but it must remain selectable and must be exercised before M2 review.

## 5.3 Why recording still passed

Recording rule R05 checks that each classified command ID appears at least once. It does not check every canonical command-scenario pair, required sample count, edit multiplicity, or derived parent context.

A command measured once can therefore cover missing scenarios on paper.

Several derived children declare a scenario their parent cannot produce. Surface coverage is green, but the live execution path cannot emit the required sample.

## 5.4 Holistic command coverage is incomplete

The user requires a holistic view of every supported command.

`make.builder` and `make.install-hooks` are catalog-only even though the M2 contract says setup commands are measured separately.

Measure them safely:

- run `make.builder` with a temporary `DOCKER_CONFIG` and a unique observatory builder name, then remove it;
- run `make.install-hooks` in a standalone temporary Git repository, not a linked worktree whose config is shared;
- keep `make.observe` catalog-only to prevent recursion;
- any other catalog-only entry must be fundamentally recursive or unmeasurable and state that reason.

Diagnostic and setup measurements may remain outside the canonical default when noise or side effects make that correct. They must stay named, selectable, and covered by verification.

## 5.5 Repeated-work data is absent

The contract requires machine-readable repeated-work observations by stable command ID. The current recommendations discuss overlap, but the canonical observation does not retain a command-containment or repeated-work relation.

Add a machine-readable relation which connects:

```text
Make targets
pre-commit stages
Docker stages
analysis steps
```

It records containment and repeated execution. M2 reports it. M3 later decides whether any repeated work is safe to merge.

## 5.6 Required root repair

Derive the exact expected measurement relation from the validated registry:

```text
command
scenario
sample count
edit multiplicity
derived parent context
selected or support role
```

Recording requires exact equality between that relation and the observation:

- no missing pair;
- no extra pair;
- exact required count;
- every derived pair producible by a parent in that scenario;
- every canonical root measured;
- every support dependency accounted for;
- every selected derived child marked selected.

A noncanonical scenario is not required in the tracked record, but its named selective path must pass before review.

## 5.7 Required controls

Add must-fail controls for:

- one command measured in the wrong scenario only;
- one canonical pair absent;
- one required sample absent;
- one edit shape absent;
- one derived parent context absent;
- a child scenario its parent cannot produce;
- a command appearing once while another declared scenario is missing;
- a recorded observation with an extra undeclared pair;
- setup commands silently cataloged despite a safe isolated measurement path;
- a repeated-work conclusion with no retained relation.

---

# 6. Blocking finding D — subject, environment, resource, and duration provenance are not exact

## 6.1 Contract violated

This violates M2-05, M2-06, M2-07, M2-13, M2-14, and M2-16.

## 6.2 Dirty ad hoc runs measure two different source trees

The observation subject may describe a dirty working tree.

Nonmutating direct commands run in that dirty tree. Incremental and mutating commands use a detached worktree at `HEAD`, so they silently discard the dirty changes while retaining the dirty observation subject.

A single observation can therefore contain samples from two different source trees.

Create every disposable source from the exact selected source view:

```text
working tree
staged index
committed tree
```

Retain the exact per-sample source digest.

## 6.3 Dirty path parsing is fragile

`git status --porcelain` is sliced at character three. Rename records, quoted paths, spaces, and staged/unstaged combinations are not a stable path model.

Use `--porcelain=v2 -z` or an exact content inventory over tracked plus untracked-nonignored paths.

## 6.4 Environment identity reads the wrong builder

The environment reader inspects the ordinary `fido-builder`, while measurements run through `fido-observatory`.

The observation can therefore carry the driver, BuildKit identity, and snapshotter of a builder which did not perform the work.

Inspect the exact command-chain builder.

## 6.5 Concurrency is neither decoded nor compared

The canonical observation records:

```text
make_jobs: " -- RECORD=1"
```

That is not an effective job count.

Make and BuildKit concurrency affect time but are omitted from the compatibility fingerprint.

Record effective concurrency, CPU quota where practical, and the exact builder parallelism. Include timing-affecting concurrency in comparison compatibility.

## 6.6 Filesystem identity uses the caller directory

The tool runs `stat` on `.` rather than the supplied repository root. Record the filesystem which contains the measured root and relevant cache roots.

## 6.7 Peak RSS is cumulative, not per sample

`RUSAGE_CHILDREN.ru_maxrss` is a high-water mark across all prior children of the observatory process. Later samples can inherit the maximum of an earlier command.

Use a per-process resource result such as `wait4` or a controlled external time wrapper. If the actual worker runs in the BuildKit daemon and cannot be measured, report resource use as unavailable. Do not report wrapper RSS as container RSS.

## 6.8 Hook stage timing uses wall clock

The contract requires monotonic duration. The main wrapper uses a monotonic clock, but hook anchors use wall-clock nanoseconds.

Use a monotonic timing source for enabled observation anchors. Retain or measure instrumentation overhead. Normal hook behavior remains unchanged when observation is disabled.

## 6.9 BuildKit derived “wall” time is an aggregate

The parser adds the durations of all steps assigned to a stage. Parallel steps can overlap, so the sum is not necessarily elapsed wall time.

Either:

- derive an exact elapsed stage duration from structured events; or
- name and type the value as aggregate step work rather than `wall_ns`.

Do not publish one as the other.

`analysis.dune-graph` is currently inserted with zero duration. Instrument it or classify it as untimed evidence. Zero is a measured claim and is false when work occurred.

## 6.10 Required controls

Add must-fail controls for:

- a dirty run whose disposable sample uses committed HEAD;
- rename, space, quoted, staged-only, unstaged-only, and untracked paths collapsing to the wrong digest;
- environment identity from another builder;
- undecoded MAKEFLAGS accepted as concurrency;
- two observations with different effective concurrency classified comparable;
- filesystem identity from another directory;
- a later sample inheriting an earlier sample’s RSS high-water mark;
- a wall-clock hook duration accepted as monotonic;
- aggregate parallel step time labeled elapsed wall time;
- nonzero analysis work stored as zero duration.

---

# 7. Blocking finding E — comparison trusts stored claims and incomplete metric definitions

## 7.1 Contract violated

This violates M2-03, M2-04, and M2-14.

## 7.2 Stored summaries are trusted

`compare` does not validate either observation or recompute its summaries before using them.

A changed stored median produces a reported regression even when the retained samples are unchanged.

Validate both observations internally before comparison.

## 7.3 Scenario, edit, and parent semantics are not fingerprinted

The observation fingerprints commands only.

Two observations remain comparable when the meaning of `cold.cached`, an edit procedure, sample policy, or derived parent context changed.

Retain and compare fingerprints for:

```text
command definition
scenario definition
edit definition
metric identity
derived parent context
resource scope
```

A changed definition makes that metric incomparable rather than improved or regressed.

## 7.4 Comparison selectors do not follow run selectors

Run mode accepts command IDs and group IDs and rejects unknown selectors.

Comparison mode treats `ONLY` as a set of exact command strings. A group such as `acceptance` yields no rows. An unknown name also yields no rows and exits successfully.

Use the same registry-aware expansion and validation in run and comparison modes.

## 7.5 Resource scope can be mixed

Comparison takes the first sample’s resource scope for a metric. It does not reject a metric whose own samples mix resource scopes.

Validate one exact scope per metric identity.

## 7.6 Required controls

Add must-fail controls for:

- a tampered stored summary;
- changed scenario semantics;
- changed edit semantics;
- changed derived parent context;
- mixed resource scopes inside one metric;
- unknown comparison selector;
- empty comparison group expansion;
- group filtering which returns no rows despite matching commands;
- different effective concurrency reported comparable.

Add must-accept controls for command, group, scenario, local-path, and Git-ref comparison using one shared selector model.

---

# 8. Blocking finding F — local bundles do not retain the evidence the contract promises

## 8.1 Contract violated

This violates M2-13, M2-15, M2-16, and M2-19.

## 8.2 Interrupted runs leave no observation

The final `observation.json` is written only after the suite returns. A failed path can write an incomplete result, but a killed or interrupted suite leaves raw logs without `status: incomplete`.

Write the local observation incrementally and update it after every completed sample. Handle cancellation and signals so the bundle remains inspectable and cannot be recorded.

## 8.3 Run IDs collide

Fractional seconds are removed from the run ID. Two runs of the same subject and suite started in one second produce the same path and can overwrite each other.

Use full timestamp precision plus a collision-safe nonce or content identity. Refuse to reuse an existing bundle path.

## 8.4 Raw logs are not verified at recording

Recording checks that the local observation exists. It does not require every direct raw log to exist and match the retained digest.

Verify all direct raw logs before recording. Derived samples must name their retained parent raw log rather than invent a missing child log.

## 8.5 Required controls

Add must-fail controls for:

- SIGINT after one sample leaving no incomplete observation;
- a second run ID collision;
- a missing direct raw log;
- a changed raw log digest;
- a derived sample with no parent evidence link;
- recording a bundle whose final checkpoint was not written.

---

# 9. Blocking finding G — the registry carries parallel unchecked authorities

## 9.1 Contract violated

This violates M2-02, M2-03, M2-04, M2-06, M2-08, and M2-10.

## 9.2 Duplicate group authority

Commands list their groups and groups list their members. The current values agree, but the validator does not prove equality.

Choose one authority. Prefer command entries as the source and derive group members for listing and selection. Do not maintain both manually.

## 9.3 Unused scenario authority

`applicable_groups` is required but not used to validate or derive the command-scenario matrix.

Either make it the sole authority for applicability and derive command scenarios, or delete it. Do not keep a second inert representation.

## 9.4 Sample policy prose and numeric counts are separate

Scenario `sample_policy` text is displayed, while command `samples` values control execution. The tool does not prove they agree.

Make numeric registry data authoritative and generate usage wording from it.

## 9.5 Dependency cycles are not rejected at load time

The accepted controls require cycle rejection. The loader validates missing dependencies but not cycles. Selection can close over a cycle without reporting it.

Reject cycles as a registry defect.

## 9.6 Parent scenario production is unchecked

A derived child can declare a scenario which its live parent does not run. This caused several missing canonical pairs in the current observation.

Validate the child scenario set against the exact parent production path.

## 9.7 Counts and discovery must fail closed

Require positive integer sample counts.

Discover all public `.PHONY` targets across continuations rather than assuming one declaration. Match Docker `AS` case-insensitively. Keep stable hook anchors.

## 9.8 Generated usage is a required public surface

Preserve:

```text
make observe HELP=1
make observe LIST=1
```

The generated help must list every supported variable and exact example. The generated list must include every command and group, direct/derived/catalog status, source view, side effects, scenario matrix, sample counts, and dependencies.

Do not copy the full guide into README or `CLAUDE.md`; retain only the terse pointer.

Add controls which execute every usage example through selection or comparison parsing. Help which documents a path the tool does not support is a failure.

---

# 10. The current observation and recommendations are exploratory, not accepted evidence

The current observation contains useful raw data and helped expose these defects. Its timing conclusions cannot close M2.

Do not use its medians to design M4.

In particular, current recommendations which depend on:

- pooled incremental medians;
- contaminated cold samples;
- merged derived parents;
- incomplete command-scenario coverage;

must be removed or regenerated after the corrected canonical run.

The following current recommendations describe M2 implementation defects and must be fixed in M2 rather than deferred:

```text
M2-R02  non-independent incremental samples
M2-R08  safely measurable setup commands left catalog-only
M2-R09  derived parent contexts merged
M2-R14  measurement coverage checked only at command level
M2-R15  killed suite retains no incomplete observation
```

Valid nonmeasurement findings may remain assigned to M3, but final recommendations must cite corrected stable metric IDs from the new observation.

Add the required machine-readable repeated-work relation before deriving overlap recommendations.

---

# 11. Contract, matrix, and current-state changes

No FCB amendment is required. The accepted M2 purpose already requires exact measurements, reproducible observations, complete command coverage, and correct comparison.

Before implementation, update `.review/M2_BUILD_OBSERVATORY.md` to state the repaired model exactly:

1. per-root measurement chains;
2. separate session and cache identity;
3. exact cache transitions and prime sample identity;
4. metric identity including edit and derived parent context;
5. exact canonical pair and sample-count closure;
6. exact candidate source view per sample;
7. comparison fingerprints and internal validation;
8. incremental local-bundle checkpoints;
9. one registry authority for groups, scenarios, and sample policy;
10. generated usage as a required public surface.

Update `.review/REVIEW_BASIS.md` to match.

Create `.review/M2_IMPLEMENTATION_REPAIR_1.md` from this directive and make it the sole active repair authority.

Reopen every implementation-dependent M2 matrix row:

```text
M2-02 through M2-19
```

Keep only M2-01 closed: M1 is accepted and M2 is the sole active work.

A row closes again only when its repaired implementation, positive evidence, negative control, mutation control, and actual executing gate exist.

Update `NEXT_STEPS`, `REVIEW_REQUEST`, the FCB reference manifest, and exact owner markers. Do not copy the blocked candidate narrative into permanent current documents. One terse current-state sentence is enough; Git history owns this review.

---

# 12. Strict-scope dispositions

| Finding | Blocks M2 | Owner |
|---|---:|---|
| Scenario and cache labels do not describe the executed state | yes | M2 repair 1 |
| Incremental samples are exact cache hits and edit identity is pooled | yes | M2 repair 1 |
| Derived parent contexts are pooled | yes | M2 repair 1 |
| Canonical command-scenario and sample closure is incomplete | yes | M2 repair 1 |
| Safely measurable setup commands are catalog-only | yes | M2 repair 1 |
| Subject, builder, concurrency, resource, and duration provenance is false or incomplete | yes | M2 repair 1 |
| Comparison trusts stored summaries and incomplete definitions | yes | M2 repair 1 |
| Interrupted bundles and raw-log evidence are incomplete | yes | M2 repair 1 |
| Registry fields carry duplicated or inert authorities | yes | M2 repair 1 |
| Timing-based recommendations derive from the invalid observation | yes | M2 repair 1 |
| Build or proof dependency optimization | no | M3/M4 |
| Combining working-tree and staged acceptance paths | no | M3/M4 |
| Changing module boundaries or theorem placement | no | M4 after plan approval |
| Fragile prose audit | no | M3-FRAGILE-PROSE |
| `life.md` content | no | preserve unchanged |

Do not implement a performance recommendation in M2.

---

# 13. Allowed changes

M2 repair 1 may change:

- `.review/M2_BUILD_OBSERVATORY.md`;
- `.review/BUILD_OBSERVATORY_SUITE.json`;
- `.review/BUILD_OBSERVATION.json`;
- `.review/M2_OBLIGATION_MATRIX.tsv`;
- `.review/M2_RECOMMENDATIONS.tsv`;
- `.review/REVIEW_BASIS.md`;
- `.review/NEXT_STEPS.md`;
- `.review/REVIEW_REQUEST.md`;
- the FCB reference manifest and exact current-state pointers required by those files;
- `tools/build-observatory.py`;
- M2-specific mutation entries in `tools/gate-mutation-test.py`;
- the `observe` and permanent observatory-validator wiring in the Makefile;
- inert, observation-only pre-commit anchors and their monotonic helper;
- Docker analysis stages used only to collect M2 evidence;
- `.gitignore` entries for local observatory state;
- one small timing helper when needed for exact monotonic instrumentation.

It may not change:

- any `.v` file;
- a theorem, proof, constructor, capability, mint, program set, or diagnostic;
- extraction or transport meaning;
- generated Go or goldens;
- ordinary Make command semantics;
- ordinary pre-commit behavior when observation is disabled;
- ordinary Docker build meaning;
- M3 or M4 tool/build architecture;
- build dependencies for performance;
- `life.md`.

Do not add an external benchmark framework or a second public Make target.

---

# 14. Work order

1. Install the repair authority and reopen the matrix.
2. Mark `8325ddb...` as the first blocked M2 candidate and `2222763...` as its documentation-only freeze.
3. Treat the current observation as exploratory and remove invalid timing recommendations from current authority.
4. Fix the registry’s single-authority relations and controls first.
5. Fix metric/sample identity and raw-log identity.
6. Implement per-root scenario chains and exact cache transitions.
7. Fix exact source, environment, resource, and timing provenance.
8. Fix canonical pair/count closure and record eligibility.
9. Fix comparison validation and fingerprints.
10. Fix incremental local-bundle writes and interruption handling.
11. Measure the safely isolated setup commands.
12. Add machine-readable repeated-work observations.
13. Run deterministic self-tests and mutation tests before any multi-hour suite.
14. Run small named selections to validate each chain:

   ```text
   make observe HELP=1
   make observe LIST=1
   make observe ONLY=make.prove SCENARIO=cold.uncached
   make observe ONLY=make.prove SCENARIO=cold.cached
   make observe ONLY=make.prove SCENARIO=warm.cached.noop
   make observe ONLY=make.check SCENARIO=warm.cached.incremental
   make observe ONLY=precommit.prover
   make observe ONLY=setup
   ```

15. Compare two local selective runs and one local run against a Git-ref observation.
16. Run the noncanonical bootstrap scenario once and retain its local bundle.
17. Only after all selective evidence is green, run the complete canonical suite against one exact committed candidate.
18. Record the canonical observation from that same exact candidate.
19. Recompute recommendations from the corrected observation.
20. Create one later documentation-only freeze and notify Rob.

No arbitrary timeout. Operator cancellation leaves an incomplete local bundle.

---

# 15. Verification

Before freezing, run:

```text
make observe HELP=1
make observe LIST=1
make observe
make observe ONLY=make.prove
make observe ONLY=precommit.prover
make observe ONLY=acceptance SCENARIO=cold.uncached
make observe ONLY=make.check SCENARIO=warm.cached.noop
make observe ONLY=make.check SCENARIO=warm.cached.incremental
make observe ONLY=setup
make observe SCENARIO=bootstrap.cold.uncached ONLY=make.check
make observe COMPARE=<local-path> BASE=<git-ref>
make observe RECORD=1

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

Also prove:

1. Every supported usage example parses and resolves to the documented selection.
2. Every public Make target is discovered and classified.
3. Every pre-commit anchor is paired and classified.
4. Every Docker stage is discovered and classified.
5. Every non-recursive public command has a meaningful measured path or an approved exact reason why no timing can exist.
6. Each cold root sample has an isolated project cache.
7. Each cached sample names its exact prime sample.
8. Each warm sample retains the same source session and cache chain.
9. Every incremental sample causes the intended rebuild and uses a unique or restored prime state.
10. Every canonical command-scenario-edit-parent metric has the exact required sample count.
11. No undeclared metric exists.
12. Every direct raw log exists and matches its digest at recording time.
13. A cancelled run leaves `status: incomplete` and cannot record.
14. Dirty working-tree, staged-index, and committed-tree source views remain distinct.
15. Both observations are validated before comparison.
16. Changed command, scenario, edit, parent, scope, or concurrency definitions become incomparable.
17. The tracked observation names the exact M2 implementation candidate.
18. The tracked observation contains repeated-work facts by stable ID.
19. Recommendations cite only corrected metric IDs.
20. No timing recommendation was implemented.
21. No `.v` file changed.
22. Generated `go.mod`, every generated `.go` file, every golden, and runtime stdout/stderr/exit remain identical.
23. Normal Make targets and the hook behave identically with observation disabled.
24. M3, M4, C5 Step 0, and C5 did not begin.

The implementation candidate contains the permanent facility and all controls. The canonical observation is recorded against that exact committed candidate. The later freeze may change only:

```text
.review/BUILD_OBSERVATION.json
.review/M2_OBLIGATION_MATRIX.tsv
.review/M2_RECOMMENDATIONS.tsv
.review/NEXT_STEPS.md
.review/REVIEW_REQUEST.md
```

No commit follows the freeze.

---

# 16. Independent review evidence

The primary review independently confirmed against the uploaded freeze:

```text
build-observatory self-test: 136 controls, all executed
command-surface coverage: 58 registry commands over the current Make, hook, and Docker surfaces
source-diet permanent controls: green
D-07 human acts: green
D-24 references: green
closure-ledger generated view: green
claim matrix: 19 rows reported closed
OCaml-origin gate: green
generated-output gate: green
pinned-target Go build: green
runtime stdout/stderr/exit: exact goldens
```

The naming scan and mutation harness did not complete within the review runtime. Docker, Rocq, Dune, extraction, the plugin, and the real staged hook were not available for an independent rerun. The freeze’s committed run remains evidence for unchanged paths, but the corrected M2 suite and all new controls must run before the next freeze.

The review independently reproduced these false greens:

- later commands labeled `cold.uncached` after an earlier command populated the shared cache;
- every sample reporting identical before/after cache state;
- three identical incremental edits producing one rebuild and two cache hits;
- six edit shapes pooled into one summary;
- seven missing canonical derived command-scenario pairs;
- `analysis.history` declaring three samples but retaining one;
- a tampered stored summary producing a comparison verdict;
- comparison `ONLY=acceptance` and an unknown selector returning an empty successful result;
- two runs started in the same second producing one run ID.

These are M2 contract defects, not optional M3 improvements.

---

# 17. Definition of done

M2 repair 1 is complete only when:

- cold, warm, cached, and uncached are implemented as exact separate axes;
- root command chains cannot contaminate each other;
- cache before/after and prime sample provenance are true;
- incremental samples are independent and separately keyed by edit;
- derived samples are separately keyed by live parent;
- the exact canonical measurement relation closes in both directions;
- setup commands are measured safely;
- subject, environment, concurrency, resource, and duration provenance are exact;
- comparison validates both observations and exact metric definitions;
- local bundles survive failure and cancellation;
- raw logs are unique and digest-checked;
- registry authorities are not duplicated;
- generated help and list output remain exact;
- the canonical observation is rerun from the repaired candidate;
- recommendations are regenerated from the corrected data;
- all reopened M2 obligations close with real evidence;
- no optimization or semantic work was performed;
- one exact implementation candidate is committed;
- one later documentation-only freeze requests human M2 review;
- Claude notifies Rob.

Only Rob accepts M2. Rob may accept in ordinary language; Fido must bind that decision to the exact candidate named by the current review state.
