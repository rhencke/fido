# M2 GREAT MEASUREMENT CULLING — IMPLEMENTATION REVIEW — BLOCKING — REPAIR 3

## Disposition

**M2 replacement candidate `be0b569e598250449b9f131aeb8cbeaa3907860c` is BLOCKING.**

It becomes the **third blocked Great Measurement Culling replacement candidate**.

Documentation-only freeze `905d03c168357963e90172004f7ee2cc80fa5bc2` is not a separate implementation
candidate.

C4, M0 and M1 remain accepted and are not reopened.

**M2 Culling Repair 3 is the sole permitted implementation work.**

M3, M4, C5 Step 0, C5 and feature work remain forbidden.

Use:

```text
/loop 3m
```

Continue until this exact repair is complete or a real contract conflict blocks progress. When complete or
genuinely blocked, notify Rob with the notification tool.

## Exact review basis

```text
Uploaded snapshot:
  fido-main - 2026-08-03T124911.400.zip

Uploaded Git head / documentation-only freeze:
  905d03c168357963e90172004f7ee2cc80fa5bc2

M2 replacement implementation candidate:
  be0b569e598250449b9f131aeb8cbeaa3907860c

Previous blocked replacement candidate:
  3441e75aabde2f2b0932751643b56f9590b5a58b

Accepted M1 candidate:
  6524b437bd7a7d6b2616563b8789e28a00c7af13

Current M2 contract:
  .review/M2_PERFORMANCE_SNAPSHOT.md

Current review basis:
  .review/REVIEW_BASIS.md
```

Use every file, FCB document, gate and current-state document from this exact ref. Do not mix refs, reset,
rebase or rewrite history. Preserve `life.md` exactly.

---

## What is now right

Keep these results:

- the withdrawn observatory implementation is gone;
- `make perf` remains one small POSIX shell script, one Make target, one TSV and inert completion markers;
- the Make command-line builder override is correct;
- the monotonic clock conversion is correct;
- stable Python, Rocq, OCaml and Go layers are primed outside the measured interval;
- the TSV is published by same-directory rename only after both runs pass;
- the tracked pair remains cold `make check` 268.5 seconds and hot 62.2 seconds;
- no correctness gate consumes the performance record;
- every `.v`, OCaml and generated Go byte remains unchanged;
- A009 / D-30 and the exact `CLAUDE.md` complexity-fit rule remain installed;
- the generated FCB views are byte-exact and the available permanent controls are green.

The timer’s product shape is correct. Do not recreate an observatory around the remaining defects.

**Complexity fit: BLOCKED — the timer does not guarantee the serial-builder fact it publishes, mutable state is
still copied across live authorities, and superseded repair documents remain solely to say they are
superseded.**

---

# 1. Blocking finding A — an existing builder can make the TSV lie about serial execution

## Contract violated

This violates:

- M2-04 — both runs use one dedicated serial builder;
- M2-05 — the measured environment is the declared environment;
- M2-07 — the sole retained performance record is honest;
- the accepted review basis class “the tracked record claims something the run did not do.”

## Exact live path

`tools/perf.sh` creates `fido-perf-v1` with:

```text
max-parallelism = 1
```

only when this command fails:

```sh
docker buildx inspect "$BUILDER"
```

When a builder named `fido-perf-v1` already exists, the script:

1. accepts it without reading or replacing its configuration;
2. bootstraps it;
3. runs both timings on it;
4. always writes:

```text
# builder: fido-perf-v1; BuildKit max-parallelism=1
```

A pre-existing builder with default or greater parallelism therefore produces a tracked header which the script
never established.

This is not hypothetical compatibility hardening. The builder is persistent by design and the script’s public
claim applies every time `make perf` runs, not only the first time that name is created.

The reviewer reproduced the path with a pre-existing mock builder: the script issued `buildx inspect`, skipped
`buildx create`, never inspected any configuration, and still published the fixed serial header.

## Required smallest fix

Do not build a builder validator or configuration abstraction.

At the start of every `make perf` run:

1. if `fido-perf-v1` exists, remove it and fail if removal fails;
2. create it again from the script’s exact one-line BuildKit configuration;
3. bootstrap it;
4. prime the stable toolchain stages;
5. start the measured cold run.

The builder is dedicated to this diagnostic, so destroying and recreating it is the simplest honest ownership
rule. Toolchain priming remains outside the measured interval. The immediate hot run still uses the cold run’s
project cache.

Clean the temporary configuration directory on every exit path. Do not add a permanent self-test, registry,
schema or performance gate.

After this change, rerun `make perf` and replace `.review/PERFORMANCE.tsv`.

Before the real run, deliberately create `fido-perf-v1` without the serial configuration. The script must remove
it, recreate it and complete with the running BuildKit container’s own configuration showing
`max-parallelism = 1`.

---

# 2. Blocking finding B — Repair 2 removed banners but did not finish one-owner state

Repair 2 explicitly required:

```text
Governance
  owns accepted amendments and governance decisions.

NEXT_STEPS
  owns active checkpoint and candidate state.

FCB Index
  owns the live file set and consultation map, and points to those owners.
  It does not copy their current values.
```

The candidate’s own commit message claims that this is now true. It is not.

## 2.1 The FCB Index contradicts its own preamble

`FIDO_FCB_INDEX.md` says:

```text
This Index names the live file set and where to look, never their current values.
```

Its `Current project boundary` then copies:

- C4 acceptance and its disposition;
- M0 acceptance and its disposition;
- M1 acceptance, exact candidate and disposition;
- the current next permitted sequence beginning at M2;
- the current rule that M3, M4 and C5 are forbidden until M2 is accepted.

Its consultation map also hard-codes the current M2 contract and M2 obligation range under “What is being worked
on right now.”

That is the mutable state the preamble says the Index does not own.

### Required correction

The Index keeps:

- the stable bootstrap;
- the live file set and corpus roles;
- the consultation map;
- stable pointers to Governance, `NEXT_STEPS`, the Roadmap and the M-series plan.

It removes:

- the current acceptance ledger;
- the current cursor through the M-series;
- current candidate/checkpoint prohibitions;
- the hard-coded current M2 contract and obligation range.

The “What is being worked on right now” row points first to `.review/NEXT_STEPS.md`, then tells the reader to
follow the contract named there.

Update the Index table’s purpose for itself so it no longer claims to own a current boundary it has deleted.

## 2.2 The Roadmap contradicts its own ownership sentence

`FIDO_FCB_ROADMAP.md` says:

```text
It does not own the current candidate, its status, or the active work.
```

It then states:

```text
M3, M4 and C5 remain forbidden until Rob accepts M2.
```

and later names:

```text
the active M2 contract
```

It also carries accepted checkpoint labels and acceptance tokens beside entries whose job is fixed order and
dependency.

### Required correction

The Roadmap owns only:

- full checkpoint order;
- stable dependencies;
- closure, latitude and acceptance-gate assignments;
- generic exit conditions.

Remove the current cursor, active contract, current forbidden-successor statement and accepted-status labels or
tokens whose only purpose is progress reporting. Point to `NEXT_STEPS` for the current cursor and to Governance
or Git history for accepted dispositions.

Retain stable historical rationale only when it explains why the order or dependency exists.

## 2.3 The M-series plan is another active-state authority

`.review/M_SERIES_PLAN.md` still says:

```text
M2 Performance Snapshot is the sole active work.
M3 and M4 implementation are forbidden.
M2 Performance Snapshot is active.
```

The M-series plan owns the stable M0–M4 sequence and the permanent M1 source-comment law. It does not need to own
the active cursor.

Replace those mutable assertions with one pointer to `.review/NEXT_STEPS.md`.

The plan may retain the accepted M1 disposition where it is provenance for the permanent source-comment law.
Do not delete stable law in the name of removing current status.

## 2.4 Model Operations retains current-state wording in a sequence rule

`FIDO_FCB_MODEL_OPERATIONS.md` begins its post-C4 sequence with the current assertion “C4 is accepted.”

State the durable rule conditionally instead:

```text
After C4 acceptance, the sequence is ...
```

Keep the full workflow and dependency rule. Remove only the copied current cursor.

## 2.5 `NEXT_STEPS` should point to governance instead of copying its register

`NEXT_STEPS` owns the active checkpoint and candidate. It does not own the accepted amendment range or governance
decision range.

Replace:

```text
A001 through A009 are accepted; Governance owns D-01 through D-30.
```

with a pointer equivalent to:

```text
Accepted amendments and governance decisions are owned by FIDO_FCB_GOVERNANCE.md.
```

Do not delete active M2 state from `NEXT_STEPS`; that is the one place where it belongs.

## Scope of this correction

Do not add a banner generator, common-header schema, semantic prose scanner or new gate.

Do not delete stable architectural rationale merely because it cites an amendment or accepted decision. The target
is mutable progress and current-cursor state, not every historical fact.

The final semantic review must ask “does this document own this current value?” Exact-phrase searches are not
enough; Repair 2’s search passed while semantically equivalent copies remained.

---

# 3. Blocking finding C — superseded repair files remain as live archaeology

The current tree contains:

```text
.review/M2_CULLING_REPAIR_1.md   26,180 bytes
.review/M2_CULLING_REPAIR_2.md   12,211 bytes
```

`NEXT_STEPS` references Repair 1 only to say it is superseded. The D-24 manifest keeps a row only so that sentence
can resolve.

That is not a current purpose. Git already owns both directives and their findings.

## Required correction

Install this Repair 3 directive as the sole active repair authority, then:

- delete `.review/M2_CULLING_REPAIR_1.md`;
- delete `.review/M2_CULLING_REPAIR_2.md`;
- remove their `NEXT_STEPS` sentences and owner markers;
- remove their D-24 reference rows;
- add the one row and marker for `.review/M2_CULLING_REPAIR_3.md`.

At the next candidate, only the active Repair 3 directive remains. At M2 acceptance closeout, it too returns to
Git history.

Keep `.review/M2_GREAT_MEASUREMENT_CULLING.md` while the live M2 contract names that human disposition. It has a
current governing purpose and is not a repair-history peer.

---

# 4. Obligation matrix

Reopen at least:

```text
M2-01
M2-02
M2-04
M2-05
M2-06
M2-07
M2-09
```

Reopen any other row whose exact evidence changes.

Required evidence changes:

- M2-01 names Repair 3 as the sole active repair.
- M2-02 names the absence of Repairs 1 and 2 and their D-24 rows.
- M2-04 names unconditional dedicated-builder recreation plus the exact `make -j1 BUILDER=... check` path.
- M2-05 names stable-stage priming after recreation and before the clock.
- M2-06 names the newly recorded TSV from the corrected path.
- M2-07 points to that exact sole record.
- M2-09 remains open until the new candidate is frozen.

Do not add helpers solely to give the matrix a convenient token. Cite the straight-line shell and document
surfaces which actually own each fact.

The timer remains outside the permanent mutation harness.

---

# 5. Strict-scope dispositions

| Finding | Blocks M2 | Owner |
|---|---:|---|
| Existing `fido-perf-v1` can bypass the serial configuration while the TSV claims it | yes | M2 Repair 3 |
| FCB Index copies current values while saying it never does | yes | M2 Repair 3 |
| Roadmap copies active status while saying it does not own it | yes | M2 Repair 3 |
| M-series plan is a second owner of the active checkpoint | yes | M2 Repair 3 |
| Model Operations copies a current cursor into a stable sequence rule | yes | M2 Repair 3 |
| Superseded Repair 1 and Repair 2 remain in the live tree | yes | M2 Repair 3 |
| General size and factoring of retained non-performance tools | no | M3 |
| Mutation and naming gate performance | no | M3 |
| Systematic fragile-prose audit beyond the exact current-state copies above | no | M3-FRAGILE-PROSE |
| Proof splitting and build-graph restructuring | no | M4 after plan approval |

Do not perform M3 or M4 work.

---

# 6. Allowed changes

Repair 3 may change only:

- `tools/perf.sh`, only the dedicated-builder setup and its cleanup;
- `.review/PERFORMANCE.tsv`, only through one real corrected `make perf` run;
- `.review/NEXT_STEPS.md`;
- `.review/M_SERIES_PLAN.md`, only current-status ownership;
- `.review/M2_PERFORMANCE_SNAPSHOT.md`, only if needed to state unconditional builder ownership clearly;
- `.review/M2_OBLIGATION_MATRIX.tsv`;
- `.review/REVIEW_REQUEST.md`;
- the exact FCB Index, Roadmap and Model Operations current-state passages named above;
- deletion of Culling Repairs 1 and 2;
- addition of Culling Repair 3;
- D-24 rows and owner markers required by those exact changes;
- regenerated Human Review Index only if its canonical input or generated pointer changes.

It may not change:

- the Makefile;
- the Dockerfile;
- the pre-commit hook;
- any other tool;
- any `.v`, OCaml or generated Go file;
- proof, extraction, transport, diagnostics, generated bytes or runtime behavior;
- ordinary build or pre-commit parallelism;
- the no-host-Python boundary;
- the tiny performance product shape;
- M3, M4 or C5 work;
- `life.md`.

No new FCB amendment is required. A009 / D-30 and the existing one-owner laws already require this result.

---

# 7. Work order

1. Install `.review/M2_CULLING_REPAIR_3.md` as the sole repair authority.
2. Delete Culling Repairs 1 and 2 and their references.
3. Reopen the affected M2 obligation rows.
4. Make `perf.sh` recreate the dedicated builder unconditionally.
5. Remove the remaining copied mutable state from the Index, Roadmap, M-series plan, Model Operations and
   `NEXT_STEPS`.
6. Review those documents semantically, not by exact stale phrases.
7. Run all deterministic document, naming, source-diet, host-Python and mutation controls.
8. Pre-create a non-serial builder named `fido-perf-v1`.
9. Run one real `make perf`; prove that builder was replaced and the live BuildKit configuration is serial.
10. Inspect the TSV: one start and nine completion rows per mode, monotonic cumulative milliseconds, cold then
    immediate hot.
11. Run all complete correctness and publication gates.
12. Commit one exact implementation candidate.
13. Add one later documentation-only freeze requesting Rob’s review.
14. Notify Rob.

Do not run repeated performance measurements. One corrected run is enough.

---

# 8. Verification

Run:

```text
sh -n tools/perf.sh
make perf
make fcb-write
make fcb
make claims
make names
make diet
make hostpython
make fmt
make check
make regenerate
make regen-guard
make audit-fresh
```

Run the real pre-commit hook over the exact staged snapshot without bypassing it.

Also verify:

- the existing wrong builder was removed, not silently reused;
- the running `fido-perf-v1` BuildKit configuration reports `max-parallelism = 1`;
- the TSV header and executed builder agree;
- the TSV contains exactly the nine named completion rows once per mode;
- every mode’s elapsed values are monotonic and the `check` row is last;
- only `NEXT_STEPS` carries the active checkpoint and candidate;
- the FCB Index points to `NEXT_STEPS` for current work and hard-codes no M2 contract, candidate, current cursor or
  current successor prohibition;
- the Roadmap carries full order and dependencies but no active cursor or current candidate status;
- the M-series plan carries stable sequence and permanent law but no active checkpoint assertion;
- Governance remains the accepted-amendment and decision owner;
- Culling Repairs 1 and 2 and their D-24 rows are absent;
- only Culling Repair 3 remains as current repair authority;
- `.v`, OCaml, generated Go and goldens are byte-identical;
- generated hashes remain:

```text
go.mod
d8f8d4f62b5b574067a4e4bf64a298bbe2cb5bc9a28d8f9c321c776e838cf1fa

main.go
b6765619f969e7fd85b4998616d8a515c5a2c0e2d397c3ee915718f35fbc48de
```

- the whole-theory assumption audit remains green;
- the exact complexity-fit sentence remains present in `CLAUDE.md`, Governance, the authoring guide and review
  policy;
- M3, M4, C5 Step 0 and C5 did not begin.

Do not create a prose-heavy closure audit.

---

# 9. Independent review evidence

Against the uploaded freeze, the reviewer independently observed:

```text
human-act controls             24, generated view exact
D-24 controls                  64, reference relation green
claim-matrix controls          21, all 9 obligations reported closed
source-diet controls           53, 662 comments compliant
naming controls                72, snapshot scan green
host-Python controls           25, boundary green
permanent mutation entries     41, all load-bearing
OCaml-origin gate              green
generated-output gate          green
shell syntax for perf.sh       green
```

The reviewer could not run Docker, Rocq, Dune, extraction, the plugin, EditorConfig or the real staged hook in
this environment. The freeze’s committed run remains evidence for those paths.

The reviewer did reproduce the existing-builder false path with mock Docker and Make launchers: a successful
pre-existing `fido-perf-v1` caused `perf.sh` to skip creation and configuration inspection while still writing
the fixed `max-parallelism=1` header.

---

# 10. Definition of done

Repair 3 is complete only when:

- `make perf` cannot reuse a builder whose serial configuration it did not establish;
- one real corrected cold/hot pair is recorded;
- the timer remains tiny and diagnostic;
- one authority owns active checkpoint and candidate state;
- the Index, Roadmap, M-series plan and Model Operations stop copying the current cursor;
- superseded repair files live only in Git history;
- the current FCB is coherent;
- the affected obligation rows close on exact evidence;
- every correctness and publication gate remains green;
- one exact candidate and one later freeze are committed;
- no commit follows the freeze;
- Claude notifies Rob.

Only Rob accepts M2.
