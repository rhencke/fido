# M2 GREAT MEASUREMENT CULLING — IMPLEMENTATION REVIEW — BLOCKING — REPAIR 1

## Disposition

**M2 replacement candidate `b1c6991943dd90128d68d5790fbf16297b469987` is BLOCKING.**

It is the **first blocked Great Measurement Culling replacement candidate**.

Documentation-only freeze `1fa17b5946a507ae3f350135b7a9ec98b10171ff` is not a separate implementation
candidate.

The culling was substantial and directionally correct, but it is incomplete. Direct Build Observatory residue
still survives in live tools and authorities, and the replacement `make perf` path does not perform several facts
its tracked TSV and closed obligation rows claim.

**M2 Culling Repair 1 is the sole permitted implementation work.**

C4, M0, and M1 remain accepted and are not reopened.

M3, M4, C5 Step 0, C5, and feature work remain forbidden.

Use:

```text
/loop 3m
```

Continue until this exact repair is complete or a real contract conflict blocks progress. When complete or
genuinely blocked, notify Rob with the notification tool.

---

## 1. Exact review basis

```text
Uploaded snapshot:
  fido-main - 2026-08-03T085317.693.zip

Uploaded Git head / documentation-only freeze:
  1fa17b5946a507ae3f350135b7a9ec98b10171ff

M2 replacement implementation candidate:
  b1c6991943dd90128d68d5790fbf16297b469987

Withdrawn Build Observatory candidate:
  1003734e67e2f07f5a10ec931e5c5729981d4652

Accepted M1 candidate:
  6524b437bd7a7d6b2616563b8789e28a00c7af13

Current contract:
  .review/M2_PERFORMANCE_SNAPSHOT.md

Human culling disposition:
  .review/M2_GREAT_MEASUREMENT_CULLING.md

Current review basis:
  .review/REVIEW_BASIS.md
```

Use every file, gate, FCB authority, and current-state document from this exact ref. Do not mix refs, reset,
rebase, or rewrite history.

Preserve `life.md` exactly.

---

## 2. Direct answer: most of `tools/` is not timing code, but the culling still missed real residue

At this exact snapshot:

```text
current tools/                 368,217 bytes   7,044 lines   18 files
tools/ at accepted M1         322,546 bytes   6,141 lines   14 files
net change since accepted M1   45,671 bytes     903 lines    4 files
```

The four new files are:

```text
tools/host-python-gate.py       27,148 bytes
tools/worktree-list.py           5,513 bytes
tools/perf.sh                    3,113 bytes
tools/python-requirements.lock     958 bytes
```

Only `tools/perf.sh` is the replacement timing implementation.

The other three have explicit current non-observatory purposes which the human culling disposition ordered
preserved:

- `host-python-gate.py` enforces Rob's no-host-Python boundary;
- `worktree-list.py` preserves the exact working-tree inventory semantics used by `make check`;
- `python-requirements.lock` pins the Python tooling image dependencies.

Most of the large remaining tools predate M2 and own current gates:

```text
source-diet.py
fcb-reference-gate.py
naming-gate.py
claim-matrix-gate.py
human-review-index.py
closure-ledger-view.py
fmt-check.py
the generated-output / mode / origin / compare gates
rocq-profile.py
regen-guard-test.sh
```

Do **not** delete those merely because they are in `tools/`.

This review does not declare their current size or architecture justified. M3 exists to review every tool under
the new complexity rule. M2 blocks only on direct culling residue and on the false claims in the replacement
performance path.

---

# 3. Blocking finding A — direct Build Observatory residue remains in live tools and comments

## Contract violated

This violates:

- M2-02 — every observatory implementation, compatibility path, control, and prose surface is deleted;
- `.review/M2_GREAT_MEASUREMENT_CULLING.md` §2;
- `.review/M2_PERFORMANCE_SNAPSHOT.md` §7;
- the rule that Git owns the deleted experiment.

## 3.1 `tools/gate-mutation-test.py` still carries an obsolete observatory commentary block

Delete the entire comment block currently surrounding the live mutation list which discusses:

```text
ONLY selectors
trace roots
checkpoint relations
resume
suite self-regression
containment
run_id
bounded metrics
root validators
suite-cost validation
bundle output
canonical-observation gates
comparison
```

The block begins around the current lines 82–116.

It describes deleted code and deleted controls. It has no current purpose and directly violates the culling.

Do not replace it with a history summary.

## 3.2 `tools/host-python-gate.py` retains a compatibility exemption for deleted repair files

Delete:

```python
DOC_EXEMPT_RE = re.compile(r'^\.review/M2_IMPLEMENTATION_REPAIR_\d+\.md$')
```

Delete the branch in `check_docs` which skips that family.

Delete the self-test which merely proves the exemption does not match `README.md`.

All `.review/M2_IMPLEMENTATION_REPAIR_*.md` files are gone. The exemption is now a live compatibility path for a
deleted architecture and permits a future file with that name to hide a host-Python instruction.

After deletion, every current Markdown file is judged by the same documentation rule.

## 3.3 `Makefile` retains observatory partition and trace prose

Rewrite or delete the stale `check` comments which currently say:

```text
parent partitions into children plus explicit overhead
```

The replacement has no parents, partitions, or overhead model.

The current sentence beginning:

```text
`check` is the canonical performance subject: its own wall time is the whole process, which `make perf` ...
```

is also grammatically incomplete. Replace the whole block with at most two current sentences:

```text
`make perf` times the complete `make -j1 check` invocation externally.
The `check` marker records only completion of this recipe body.
```

Rewrite the `prove-errors` comment which still discusses:

```text
observation on
an inner interval
a trace containing another trace
canonical acquisition
two traces claiming one checkpoint
```

Its current purpose is simply:

```text
Diagnostic wrapper which reports the File/Error lines from prover-log; it deliberately swallows the build
failure so the useful diagnostics remain visible.
```

No observatory vocabulary survives.

## 3.4 FCB Model Operations still names the deleted product

Replace the current M2 delegation text in:

```text
.review/fcb/current/FIDO_FCB_MODEL_OPERATIONS.md
```

so it says `M2 Performance Snapshot`, not `M2 Build Observatory`.

Review every live FCB and root document for the deleted product name. Historical mention is permitted only in the
current human culling disposition while that disposition remains active.

## 3.5 Required residue search

Run a full tracked-tree search and disposition every match for:

```text
Build Observatory
build-observatory
BUILD_OBSERVATION
BUILD_OBSERVATORY_SUITE
observatory-runner
make observe
make observatory
FIDO_OBSERVE
trace-completion
AcquisitionPlan
ObservationBasis
serial_projection
project.cached.fresh
project.incremental
comparison schema
local run bundle
```

Allowed surviving uses are only:

- the current human disposition describing what it withdrew;
- one terse current statement that the withdrawn experiment lives in Git history;
- this active repair directive until M2 closeout.

Everything else is deleted or rewritten as a current fact.

---

# 4. Blocking finding B — `make perf` does not use the dedicated builder it claims to use

## Contract violated

This violates:

- M2-04 — both runs use one dedicated serial builder;
- M2-05 — cold setup and cache state describe the executed builder;
- M2-06 — the tracked timing record truthfully describes the run;
- M2-07 — the sole retained performance record is honest;
- M2-09 — the frozen candidate satisfies the replacement contract.

## Reproduction

The Makefile defines:

```make
BUILDER := fido-builder
```

`tools/perf.sh` invokes:

```sh
BUILDER="$BUILDER" make -j1 pytools
...
BUILDER="$BUILDER" make -j1 check
```

That is an environment assignment.

A Makefile `:=` assignment overrides an environment value. Independently reproduced against this exact Makefile:

```text
environment BUILDER=fido-perf-v1 make ...   => fido-builder
command-line make BUILDER=fido-perf-v1 ...  => fido-perf-v1
```

The script creates and bootstraps `fido-perf-v1`, then performs the measurements with `fido-builder`.

The current `.review/PERFORMANCE.tsv` header is therefore false:

```text
# builder: fido-perf-v1; BuildKit max-parallelism=1
```

## Required correction

Pass the builder as a Make command-line variable:

```sh
make -j1 BUILDER="$BUILDER" pytools
make -j1 BUILDER="$BUILDER" check
```

Preserve the existing explicit `--builder $(BUILDER)` uses.

Do not change the ordinary default builder or normal build parallelism.

Add no builder abstraction, registry, or compatibility path.

Rerun the real performance pair after this correction.

---

# 5. Blocking finding C — the monotonic-clock conversion is wrong

## Contract violated

This violates M2-06 and the tracked TSV's exact clock statement.

## Reproduction

`/proc/uptime` supplies hundredths of a second.

Both implementations currently calculate:

```sh
seconds * 1000 + fraction / 10
```

They must calculate:

```sh
seconds * 1000 + fraction * 10
```

The defect exists in:

```text
tools/perf.sh:now_ms
Makefile:fido_mark
```

For example, an uptime fraction of `.84` is 840 ms. The current code records 8 ms.

This does not merely reduce precision. Around second boundaries it can distort a phase delta by almost one
second while the output claims 10 ms resolution.

## Required correction

Use one tiny POSIX-shell expression in both sites:

```sh
fraction=${fraction#0}
milliseconds=$((seconds * 1000 + ${fraction:-0} * 10))
```

Do not add a clock abstraction or helper program.

Keep the honest header:

```text
/proc/uptime, 10ms resolution
```

only after the implementation matches it.

Rerun the performance pair; the current TSV is invalid evidence.

---

# 6. Blocking finding D — the script claims to prime stable toolchains but primes only Python, on the wrong builder

## Contract violated

This violates M2-05 and `.review/M2_PERFORMANCE_SNAPSHOT.md` §4.

The contract requires these to be available before the timed cold interval:

```text
base images
pinned Python
Rocq
Dune
OCaml
Go toolchain layers
```

The script currently invokes only:

```sh
make pytools
```

Because of Finding B, even that invocation uses the normal builder.

A new dedicated builder can therefore pull or build Rocq/OCaml/Go infrastructure inside the measured cold run
while the TSV says those costs were excluded.

## Required correction

Prime the stable infrastructure on the exact dedicated builder before starting the clock.

Use the smallest direct Buildx path. Do not reconstruct the project graph in shell.

At minimum:

- build `python-tools` on `fido-perf-v1`;
- build the stable Rocq/OCaml base/toolchain stage on `fido-perf-v1`;
- make the pinned Go base/toolchain locally available before timing.

Prefer one explicit stable stage per toolchain authority. If the Go image currently has no reusable base stage,
introduce only the smallest named `go-base` stage and derive `go-e2e` from it; do not duplicate the pinned image
digest or restructure downstream stages.

The priming commands produce no timing rows and run before `t0`.

After priming, the cold run forces only the declared project roots:

```text
prover
emit
```

and their required descendants.

Do not clear registry, base-image, package, or toolchain caches.

---

# 7. Blocking finding E — publication is not atomic as claimed

## Contract violated

This violates M2-06 and `.review/M2_PERFORMANCE_SNAPSHOT.md` §4.

The script currently creates the final temporary file with plain:

```sh
tmp=$(mktemp)
```

then moves it into `.review/PERFORMANCE.tsv`.

A temporary file outside `.review` may be on another filesystem. In that case `mv` degrades to copy-and-remove
rather than one atomic rename.

The script also performs:

```sh
chmod 644 "$OUT"
```

after publication. A chmod failure reports failure after the tracked record has already changed.

## Required correction

Create the publication temporary file in `.review` on the same filesystem:

```sh
tmp=$(mktemp .review/.PERFORMANCE.tsv.XXXXXX)
```

Write the complete result there, set its mode before publication, then rename it over the destination:

```sh
chmod 644 "$tmp"
mv "$tmp" "$OUT"
```

The trap removes only an unpublished temporary.

A failed cold run, hot run, write, chmod, or rename leaves the prior tracked record intact.

Do not add a publication framework.

---

# 8. Blocking finding F — current review and governance documents still describe the deleted observatory

## Contract violated

This violates M2-02, M2-09, the culling's current-document requirement, and Git-owned archaeology.

## 8.1 Replace `.review/REVIEW_BASIS.md`

The opening claim names the replacement product correctly.

Almost every blocking class and required-evidence row below it still belongs to the deleted observatory:

```text
scenario registries
cache primes
incremental edits
sample medians
raw-log digests
selectors
local bundles
per-module timing
Dune adjacency
history analysis
machine-readable comparison
```

Replace the file with a short review basis for the product which exists.

It should cover only:

- one exact `make -j1 check` subject;
- one dedicated serial builder;
- honest project-cold setup and one immediate hot repeat;
- inert completion timestamps;
- one atomic tracked TSV;
- `git diff`;
- deletion of the old framework;
- preservation of every correctness and generated-artifact path;
- the complexity-fit rule in §10.

## 8.2 Shorten `.review/NEXT_STEPS.md`

Delete:

- the withdrawn candidate SHA and detailed failure narrative;
- the old no-duplicate-measurement amendment;
- `project.cached.fresh`;
- `project.incremental.<edit>`;
- the 252-to-153 metric story;
- the old trace and registry escape narrative.

Retain one terse historical sentence:

```text
The Build Observatory was withdrawn by Rob and survives only in Git history.
```

Retain the one current replacement candidate and current contract.

## 8.3 Empty `.review/OPEN_QUESTIONS.md` honestly

Replace the current historical account of three deleted observatory questions with:

```markdown
# Open questions — Claude Code to the reviewer and to Rob

**There are currently no open implementation questions.**
```

The deleted subjects need no obituary in a live question channel.

## 8.4 Rewrite the M3 findings as current findings

In `.review/M_SERIES_PLAN.md`, remove the heading and prose:

```text
Carried over from the withdrawn observatory
```

Do not explain where the findings came from.

Keep the useful findings under a current heading such as:

```text
Deferred M3 findings
```

State only what M3 must investigate now.

## 8.5 Correct the obligation matrix

Reopen at least:

```text
M2-02
M2-04
M2-05
M2-06
M2-07
M2-09
```

The current M2-02 mutation cell points at:

```text
the residue exemption in the token scan
```

That mutation proves a general D-24 residue rule. It does not prove that every Build Observatory path was deleted.

Use an honest boundary for deletion completeness:

```text
unsupported-boundary: deletion completeness is established by the exact Git diff and independent whole-tree
residue review; no performance-specific mutation framework exists
```

M2-04 through M2-06 must not close on strings which exist while their claimed behavior is false.

After repair, each closed row names the real implementation and actual retained result.

---

# 9. Standing rule — install complexity fit now

Rob explicitly ordered this rule into the next review cycle:

> **Make each component as exact and rigorous as its real job requires, but no more complicated than that job justifies.**

It is absent from the current tree.

Install it now without building a gate around it.

## 9.1 `CLAUDE.md`

Add the exact sentence once as a standing implementation rule.

## 9.2 FCB Governance

Install one concise accepted amendment:

```text
FCB-A009-COMPLEXITY-FIT
```

and one decision:

```text
D-30 — Complexity must fit the component's real job.
```

The decision owns the exact sentence above and these consequences:

- a design states the component's real job before proposing machinery;
- implementation keeps only machinery which directly serves that job;
- review reports `Complexity fit: PASS` or `Complexity fit: BLOCKED`;
- a new framework, registry, schema, validator hierarchy, compatibility layer, or governance surface not already
  required by the accepted contract needs Rob's approval before implementation;
- no automated gate is created for this judgment.

Update the accepted-amendment banners, FCB Index, Governance register, and exact affected current authorities.

Reopen no semantic fixed point. Change no theorem, language contract, or trust boundary.

Keep the amendment document short. Do not turn the simplicity rule into another framework.

## 9.3 Design and review guidance

Add the same duty tersely to:

```text
.review/fcb/current/FIDO_FCB_CHECKPOINT_AUTHORING_GUIDE.md
.review/CODEX_REVIEW_POLICY.md
```

Contract Review asks whether the proposed machinery is justified by the real job.

Implementation Review asks whether retained machinery supports the product or mainly supports itself.

Every future review includes exactly one line:

```text
Complexity fit: PASS
```

or:

```text
Complexity fit: BLOCKED — <plain reason>
```

For this candidate:

```text
Complexity fit: BLOCKED — deleted observatory machinery and claims remain, while the tiny replacement does not
yet execute the simple behavior it claims.
```

---

# 10. Tool disposition — do not turn the repair into a second indiscriminate culling

Use this disposition unless new exact evidence contradicts it:

| File or family | M2 disposition | Reason |
|---|---|---|
| `tools/perf.sh` | repair and keep | the sole performance implementation |
| observatory comments in `gate-mutation-test.py` | delete | direct dead experiment residue |
| M2 repair exemption in `host-python-gate.py` | delete | compatibility path for deleted files |
| `host-python-gate.py` otherwise | keep | current no-host-Python boundary explicitly preserved |
| `worktree-list.py` | keep | exact working-tree inventory on the live `make check` path |
| `python-requirements.lock` | keep | pinned Python tooling dependency authority |
| `rocq-profile.py` | keep | separate pre-M2 one-module proof diagnostic |
| source-diet, naming, FCB, claim, human-act, closure tools | keep for M2 | current permanent gates; M3 audits their size and factoring |
| generated-output, mode, origin, compare, regen-guard scripts | keep | current artifact / transport / publication gates |
| general mutation parallelization | keep | independent speedup preserving the same controls |

Record this exact M3 finding:

```text
Audit every retained tool under D-30. Current presence proves only that M2 does not delete it; M3 must decide
whether its exact size and architecture are justified by its real job.
```

Do not perform that general M3 audit now.

---

# 11. Strict-scope disposition table

| Finding | Contract violated | Blocks M2 | Mandatory owner |
|---|---|---:|---|
| Direct observatory comments and compatibility exemption remain | M2-02 | **yes** | M2 Culling Repair 1 |
| Make and current FCB prose still describe traces/partitions/observatory | M2-02, M2-09 | **yes** | M2 Culling Repair 1 |
| `make perf` uses the normal builder, not `fido-perf-v1` | M2-04, M2-05, M2-06 | **yes** | M2 Culling Repair 1 |
| `/proc/uptime` fraction divided rather than multiplied | M2-06 | **yes** | M2 Culling Repair 1 |
| Stable Rocq/OCaml/Go toolchains not primed on the measured builder | M2-05 | **yes** | M2 Culling Repair 1 |
| Cross-filesystem temp and post-publication chmod make atomic claim false | M2-06 | **yes** | M2 Culling Repair 1 |
| Review basis and current state retain deleted framework contracts | M2-02, M2-09 | **yes** | M2 Culling Repair 1 |
| Complexity-fit standing rule absent | Rob's explicit review-cycle instruction | **yes** | M2 Culling Repair 1 / A009 |
| General size and factoring of retained tools | no M2 contract violation | no | M3 |
| Hot `make check` policy-gate cost | no M2 contract violation | no | M3 |
| Proof/module/cache restructuring | no M2 contract violation | no | M4 after approved plan |

Do not absorb the nonblocking rows into M2.

---

# 12. Allowed changes

M2 Culling Repair 1 may change:

- `tools/perf.sh`;
- the stale comments in `tools/gate-mutation-test.py`;
- the obsolete repair exemption and its control in `tools/host-python-gate.py`;
- Makefile timing-marker arithmetic, builder invocation support, direct stable-toolchain priming, and stale comments;
- the smallest Dockerfile base-stage fact needed to prime one existing pinned toolchain without duplicating its pin;
- `.review/PERFORMANCE.tsv`;
- `.review/M2_PERFORMANCE_SNAPSHOT.md`;
- `.review/M2_OBLIGATION_MATRIX.tsv`;
- `.review/REVIEW_BASIS.md`;
- `.review/NEXT_STEPS.md`;
- `.review/OPEN_QUESTIONS.md`;
- `.review/M_SERIES_PLAN.md`;
- `.review/REVIEW_REQUEST.md`;
- `CLAUDE.md`;
- `.review/CODEX_REVIEW_POLICY.md`;
- the exact FCB Governance, Index, Guide, Model Operations, amendment register, amendment file, references, and
  generated human view required by A009/D-30;
- D-24 rows and owner markers required by those exact changes.

It may not change:

- any `.v` source;
- any theorem, proof, constructor, public type, capability, or semantic authority;
- OCaml extraction or transport behavior;
- accepted or rejected program sets;
- diagnostics;
- generated Go or goldens;
- ordinary `make check` or pre-commit parallelism;
- general tool architecture;
- the no-host-Python boundary;
- M3 or M4 implementation;
- `life.md`.

No aliases, deprecated wrappers, replay modes, or compatibility paths are permitted.

---

# 13. Work order

1. Install this repair directive as the sole active M2 repair authority.
2. Mark candidate `b1c699...` blocked and reopen the affected obligation rows.
3. Delete all direct observatory residue from live tools and comments.
4. Replace the stale review basis and current-state prose.
5. Fix the dedicated-builder invocation.
6. Fix the `/proc/uptime` conversion in both locations.
7. Prime the exact stable toolchain layers on the exact dedicated builder outside timing.
8. Fix same-filesystem atomic publication.
9. Install A009 / D-30 and the exact `CLAUDE.md`, design, and review rules.
10. Run whole-tree residue searches.
11. Run all cheap and structural controls.
12. Run the real `make perf` once from the final committed implementation candidate.
13. Inspect `.review/PERFORMANCE.tsv` directly and confirm its builder, clock, cold, and hot claims match execution.
14. Run the complete proof, artifact, regeneration, publication, and staged-hook checks.
15. Commit one exact implementation candidate.
16. Create one later documentation-only freeze which changes only current review state and exact final evidence.
17. Notify Rob.

Do not run `make perf` repeatedly to test structural edits. Shell syntax, Make-variable behavior, and timestamp
arithmetic are cheap deterministic checks. Pay for the real cold/hot pair only after those checks pass.

---

# 14. Verification

Before the real timing run, verify directly:

```text
sh -n tools/perf.sh
environment-only BUILDER assignment does not override Makefile :=
command-line BUILDER assignment does
the uptime conversion maps .84 to 840 ms
the publication temp is inside .review
all stable priming commands name fido-perf-v1
all direct observatory residue searches are clean
```

Run the permanent gates and their controls:

```text
make hostpython
make diet
make fcb
make claims
make names
make fmt
```

Run the exact performance path:

```text
make perf
```

Then inspect:

```text
.review/PERFORMANCE.tsv
git diff -- .review/PERFORMANCE.tsv
docker buildx inspect fido-perf-v1
```

Prove the performance file records:

- builder `fido-perf-v1`;
- BuildKit max-parallelism 1;
- one project-cold `make -j1 check`;
- one immediate hot `make -j1 check`;
- correct monotonic milliseconds;
- the required completion rows exactly once per mode;
- no toolchain pull or bootstrap inside the timed interval.

Run the full unchanged acceptance evidence:

```text
make check
make regenerate
make regen-guard
make audit-fresh
```

Run the real pre-commit hook against the exact staged snapshot without bypassing it.

Also prove:

1. all `.v` files are byte-identical to the accepted M1 source;
2. generated `go.mod` and every generated `.go` file remain byte-identical;
3. reviewed stdout, stderr, and exit status remain identical;
4. the whole-theory assumption audit remains green;
5. every existing non-performance mutation remains load-bearing;
6. no Build Observatory implementation or compatibility path survives;
7. `make perf` is a prerequisite of nothing and no gate reads `PERFORMANCE.tsv`;
8. M3, M4, C5 Step 0, and C5 did not begin.

Do not create a prose-heavy closure audit. The tiny script, TSV, Git diff, current contracts, gate outputs, and commit
history are the evidence.

---

# 15. Definition of done

Repair 1 is complete only when:

- direct observatory residue is gone from live tools, Make comments, FCB, and current review documents;
- no repair-family compatibility exemption survives;
- the dedicated serial builder is the builder Make actually uses;
- stable infrastructure is primed on that builder before timing;
- the monotonic milliseconds are calculated correctly;
- performance publication is a same-filesystem rename after complete write and mode setup;
- the tracked TSV is regenerated from the corrected real path;
- all closed obligation rows describe behavior which actually occurred;
- A009 / D-30 and the exact complexity-fit sentence govern design, implementation, and review;
- the general tool audit remains assigned to M3 rather than smuggled into M2;
- every proof, artifact, generated byte, and runtime result is unchanged;
- one exact replacement candidate is frozen;
- no implementation commit follows its documentation-only freeze;
- Claude notifies Rob.

Only Rob accepts M2.
