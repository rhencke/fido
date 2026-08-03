# M2 GREAT MEASUREMENT CULLING — IMPLEMENTATION REVIEW — BLOCKING — REPAIR 2

## Disposition

**M2 replacement candidate `3441e75aabde2f2b0932751643b56f9590b5a58b` is BLOCKING.**

It becomes the **second blocked Great Measurement Culling replacement candidate**.

Documentation-only freeze `9ac3480fa4954b5ff02eefa27432dff05fd8ad98` is not a separate implementation
candidate.

C4, M0 and M1 remain accepted and are not reopened.

**M2 Culling Repair 2 is the sole permitted implementation work.**

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
  fido-main - 2026-08-03T111439.137.zip

Uploaded Git head / documentation-only freeze:
  9ac3480fa4954b5ff02eefa27432dff05fd8ad98

M2 replacement implementation candidate:
  3441e75aabde2f2b0932751643b56f9590b5a58b

Previous blocked replacement candidate:
  b1c6991943dd90128d68d5790fbf16297b469987

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

## Review result

The Great Measurement Culling itself now works.

Keep these results:

- the withdrawn observatory implementation is gone;
- repository bytes fell from 5,112,705 to 2,722,102;
- `tools/` fell from 1,019,145 bytes to 366,509;
- `tools/perf.sh` is an 81-line POSIX shell script;
- `make perf` is a prerequisite of nothing and no gate reads the TSV;
- the dedicated builder is passed as a Make command-line variable;
- the monotonic clock conversion is correct;
- stable Python, Rocq, OCaml and Go layers are primed before timing;
- publication uses a same-directory temporary with mode set before rename;
- the tracked pair is cold `make check` 268.5 s and hot 62.2 s;
- every `.v` file and generated Go byte remains unchanged;
- A009 / D-30 and the exact `CLAUDE.md` rule are installed.

Do not alter the timing implementation again in this repair.

**Complexity fit: BLOCKED — the tiny timer fits its job, but mutable FCB state is still copied across many
documents and is already contradictory.**

---

# 1. Blocking finding A — the live FCB carries many stale copies of mutable state

## The contradiction

The FCB Index correctly says:

```text
A001 through A009 are accepted.
M2 Performance Snapshot is active.
```

But ten other live FCB documents still say:

```text
Accepted amendments end at A008.
M1 Source Diet is the sole active work.
```

The stale sentence also lives in `tools/human-review-index.py`, so regenerating the Human Review Index faithfully
recreates the false state.

Affected current documents include:

```text
.review/fcb/current/FIDO_FCB_ACCEPTANCE_GATES.md
.review/fcb/current/FIDO_FCB_ARCHITECTURE_CHARTER.md
.review/fcb/current/FIDO_FCB_CHECKPOINT_AUTHORING_GUIDE.md
.review/fcb/current/FIDO_FCB_CLOSURE_LEDGER.md
.review/fcb/current/FIDO_FCB_FIXED_POINTS.md
.review/fcb/current/FIDO_FCB_GOVERNANCE.md
.review/fcb/current/FIDO_FCB_HUMAN_REVIEW_INDEX.md
.review/fcb/current/FIDO_FCB_LATITUDE_LEDGER.md
.review/fcb/current/FIDO_FCB_MODEL_OPERATIONS.md
.review/fcb/current/FIDO_FCB_ROADMAP.md
.review/fcb/current/FIDO_FCB_TOOLCHAIN_EVIDENCE.md
tools/human-review-index.py
```

This is not harmless prose. These are live authorities and generated views consulted at the start of every
serious task. They disagree about the active checkpoint and accepted governance.

It also demonstrates the exact complexity-fit failure D-30 exists to prevent: one mutable fact has been copied
into many documents, and every checkpoint transition has to update all of them by hand.

## Required root correction

Do not update every copied banner to the latest wording.

Delete the duplicated mutable state.

Use this ownership:

```text
FIDO_FCB_GOVERNANCE.md
  owns the accepted amendment register and governance decisions.

.review/NEXT_STEPS.md
  owns the active checkpoint and candidate state.

FIDO_FCB_INDEX.md
  owns the live file set and consultation map, and points to those owners.
  It does not copy their mutable contents.

Every other FCB document
  states only its own stable purpose and points to the owners when current state matters.
```

Required changes:

1. Remove accepted-amendment enumerations from every non-owning FCB document.
2. Remove active-checkpoint and accepted-checkpoint status sentences from every FCB document except the exact
   owner. `NEXT_STEPS` owns active work; Governance owns accepted decisions.
3. Make the FCB Index point to Governance and `NEXT_STEPS` without restating their current values.
4. Remove the mutable banner fields from `tools/human-review-index.py`.
5. Regenerate `FIDO_FCB_HUMAN_REVIEW_INDEX.md`.
6. Trim the hand-authored preambles of the generated Closure and Latitude views; their generated tables remain
   unchanged.
7. Keep the stable bootstrap, corpus role and exact-ref consultation rules.
8. Do not create a gate, schema, banner generator or shared-header framework. Deletion is the fix.

The accepted A009 record remains historical evidence. Do not rewrite accepted amendment history merely because
its decision now removes duplicated live banners.

---

# 2. Blocking finding B — `NEXT_STEPS` states the wrong obligation range

`NEXT_STEPS` says the active matrix contains:

```text
M2-01 through M2-19
```

The actual matrix and FCB Index contain exactly:

```text
M2-01 through M2-09
```

Correct `NEXT_STEPS` to `M2-01 through M2-09`.

Do not introduce a generated count or another checker. The stable IDs are the useful fact; this is one current
authority correction.

---

# 3. Blocking finding C — the live M2 contract contradicts the repaired publication path

The contract says:

```text
Results are written to a temporary file outside the repository.
```

The repaired implementation correctly creates:

```text
.review/.PERFORMANCE.tsv.XXXXXX
```

beside the destination, sets its mode, then renames it over `.review/PERFORMANCE.tsv`.

The same-directory temporary is required for an atomic rename. The live contract currently describes the
defective pre-repair topology.

Replace the publication paragraph with the current rule:

```text
Results are written to a temporary file beside `.review/PERFORMANCE.tsv`, its final mode is set before
publication, and it is renamed over the destination only after both runs succeed. A failed run leaves the
tracked record untouched.
```

The human culling disposition may retain its original wording as the historical decision which was later
repaired. The live M2 contract must describe what exists now.

---

# 4. Evidence-map cleanup

While the matrix is open, make its implementation cells name the real straight-line surfaces.

At minimum:

- `M2-05` must name the stable-toolchain priming loop, the Make cold-root selection and the timed `run`; `run`
  alone does not own the excluded acquisition work.
- `M2-06` must name `now_ms`, the Make completion marker and the same-directory publication block; `now_ms`
  alone does not own atomic publication.
- `M2-08` must name the actual proof, artifact and generated-byte paths it relies on, not only
  `worktree-list.py`.

Do not add helper functions, abstractions or controls merely to give the matrix a convenient token. Cite the
existing script, Make and gate surfaces honestly.

Reopen every affected row before editing and close it only after its exact evidence map is true.

---

# 5. Strict-scope dispositions

| Finding | Blocks M2 | Owner |
|---|---:|---|
| Live FCB documents contradict the FCB Index and `NEXT_STEPS` | yes | M2 Repair 2 |
| Duplicated mutable FCB banners caused the contradiction | yes | M2 Repair 2 |
| `NEXT_STEPS` says M2-01 through M2-19 instead of M2-09 | yes | M2 Repair 2 |
| Live M2 contract says the temporary is outside the repository | yes | M2 Repair 2 |
| Affected matrix rows name incomplete implementation surfaces | yes | M2 Repair 2 |
| Size and factoring of retained non-performance tools | no | M3 |
| Copied timing values and other fragile prose outside the exact defects above | no | M3-FRAGILE-PROSE |
| Mutation and naming gate performance | no | M3 |
| Proof splitting and build-graph restructuring | no | M4 after plan approval |

Do not perform M3 or M4 work.

---

# 6. Allowed changes

Repair 2 may change only:

- the live FCB preambles and consultation text needed to remove duplicated mutable state;
- `tools/human-review-index.py`, only its generated-view banner;
- the regenerated Human Review Index;
- the hand-authored preambles of generated FCB views;
- `.review/NEXT_STEPS.md`;
- `.review/M2_PERFORMANCE_SNAPSHOT.md`;
- `.review/M2_OBLIGATION_MATRIX.tsv`;
- `.review/REVIEW_REQUEST.md`;
- the active repair directive and D-24 reference rows required for it.

It may not change:

- `tools/perf.sh`;
- the Makefile;
- the Dockerfile;
- the pre-commit hook;
- any other tool;
- any `.v`, OCaml or generated Go file;
- `.review/PERFORMANCE.tsv`;
- proof, extraction, transport, diagnostics, generated bytes or runtime behavior;
- the no-host-Python boundary;
- M3, M4 or C5 work;
- `life.md`.

No performance rerun is required. The checked-in TSV intentionally represents the last time `make perf` ran.

---

# 7. Work order

1. Install this directive as the sole M2 repair authority.
2. Mark candidate `3441e75...` blocked and reopen the affected matrix rows.
3. Remove copied mutable state from the FCB corpus and Human Review generator.
4. Regenerate the Human Review Index.
5. Fix the M2 obligation range in `NEXT_STEPS`.
6. Fix the same-directory publication wording in the M2 contract.
7. Correct the affected matrix evidence maps without adding machinery.
8. Search the whole current corpus for:
   - `M1 Source Diet is the sole active work`;
   - accepted-amendment lists outside Governance;
   - active-checkpoint assertions outside `NEXT_STEPS`;
   - `M2-19`;
   - `temporary file outside the repository`.
9. Run all current document and repository gates.
10. Commit one exact repair candidate.
11. Add one later documentation-only freeze requesting Rob's review.
12. Notify Rob.

---

# 8. Verification

Run:

```text
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

- the Human Review Index is byte-exact regeneration from its canonical data;
- no live FCB document says M1 is active;
- Governance is the only live owner enumerating accepted amendments;
- `NEXT_STEPS` is the only live owner naming the active checkpoint and candidate;
- the FCB Index points to those owners without copying mutable state;
- `NEXT_STEPS` says M2-01 through M2-09;
- the M2 contract describes same-directory atomic publication;
- `.review/PERFORMANCE.tsv` is byte-identical to candidate `3441e75...`;
- every `.v`, OCaml and generated Go byte is unchanged;
- generated Go and runtime goldens still match;
- the complexity-fit rule remains present verbatim in `CLAUDE.md`, Governance, the authoring guide and review
  policy;
- M3, M4, C5 Step 0 and C5 did not begin.

Do not run `make perf`.

---

# 9. Definition of done

Repair 2 is complete only when:

- one authority owns accepted amendments;
- one authority owns active checkpoint and candidate state;
- all non-owning FCB banners stop copying those facts;
- the generated Human Review Index no longer recreates stale mutable state;
- every current FCB document is coherent;
- the obligation range is exact;
- the publication contract matches the implementation;
- the affected matrix rows cite the real implementation surfaces;
- no timing implementation changed;
- every required gate is green;
- one exact repair candidate and later freeze are committed;
- no commit follows the freeze;
- Claude notifies Rob.

Only Rob accepts M2.
