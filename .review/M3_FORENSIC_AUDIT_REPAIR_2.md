# M3 IMPLEMENTATION REVIEW — BLOCKING — REPAIR 2

## 0. Disposition and exact review basis

**M3 candidate `5af6bc10a811e72fed48a9a1ce09c01c8f1a9e92` is BLOCKING.**

It becomes the first blocked M3 Implementation Review candidate.

Documentation-only freeze `a7383653580e093c9ed4106938bf5be82ecf6d9b` is not a second implementation
candidate.

Exact basis:

```text
Uploaded snapshot:
  fido-main - 2026-08-04T135744.477.zip

Uploaded Git head / documentation-only freeze:
  a7383653580e093c9ed4106938bf5be82ecf6d9b

M3 implementation candidate:
  5af6bc10a811e72fed48a9a1ce09c01c8f1a9e92

M3-A1 tool-repair and measurement subject:
  a0482140384de3d8c193263c3bf5281e53ccdd8b

Accepted M3 contract:
  .review/M3_TOOL_AND_BUILD_ARCHITECTURE_AUDIT.md
  activation 0b7fd86825936c37f31ef83879574d526d548122

Accepted M3 review basis:
  .review/REVIEW_BASIS.md
  installed at 238d69ce93fb0109fd4ba8e311c95b3044575378

Accepted M2 candidate:
  9814db77ead0cfcfd8ff268303ba2afedef71197
```

Use every file, FCB document, contract, gate, audit, plan, and review-state document from this exact ref. Do
not mix refs, reset, rebase, or rewrite history.

C4, M0, M1, and M2 remain accepted.

**M3 Implementation Repair 2 is the sole permitted work.**

M4 remains forbidden. C5 Step 0, C5, and feature work remain forbidden.

Use:

```text
/loop 3m
```

Continue until this exact repair is complete or a real contract conflict blocks progress. When complete or
genuinely blocked, notify Rob with the notification tool.

---

## 1. What passes and must remain

Keep these results:

1. The forensic audit is finite and uses no permanent audit, graph, timing, inventory, or comparison system.
2. Configuration-B measurements now name immutable subject
   `a0482140384de3d8c193263c3bf5281e53ccdd8b`.
3. The naming cardinalities and profile were rerun from the source rather than counted by eye.
4. The dependency graph now comes from the pinned `rocq dep` toolchain.
5. Edit-frequency and co-change evidence use immutable, separated ranges.
6. Working-tree and staged-index paths remain distinct.
7. The hot path is correctly root-caused:
   - `names`: 22.310 s in the accepted serial record;
   - `fcb`: 28.580 s;
   - `prove`: 1.410 s;
   - `e2e`: 1.340 s.
8. M3-A1's implementation is narrow and correct:
   - one shared `renameable_declaration` predicate;
   - a `require_declaration` precondition;
   - four exact controls;
   - one load-bearing mutant.
9. All twelve matrix rows are closed without fabricated implementation surfaces.
10. M3 changed no production, proof, Make, hook, Docker, Dune, generated, or runtime path.
11. Generated Go and runtime goldens remain exact.
12. M4 has not begun.

The measurement evidence itself needs no further rerun in this repair.

---

# 2. Contract Review correction — M3-A1 and M3-A2

## 2.1 M3-A1's technical content is GREEN

The exact M3-A1 amendment and its implementation pass Contract Review.

No revert and reapplication are required. The implementation matches the narrow amendment exactly and the
independent controls pass.

## 2.2 M3-A1's authority record is false

The frozen M3 contract required a contract amendment and another Contract Review after the conflict. Governance
also says only Rob may amend a governing decision.

`.review/M3_CONTRACT_AMENDMENT_1.md` currently says:

```text
authorized by: the reviewer
```

A reviewer cannot authorize it.

Rob's plain-language approval of this Repair 2 is the human act which ratifies M3-A1. After that approval:

- change M3-A1's authority line to name Rob's approval of this exact review;
- state that this review is the required GREEN Contract Review of M3-A1;
- keep the technical amendment and tool bytes unchanged.

Do not create a token or ceremony around that decision.

## 2.3 M3-A2 — correct the claim-matrix-subject finding

The frozen contract says:

```text
M3-CLAIM-SUBJECT
  remove the need for a manually retargeted active-checkpoint constant
```

The audit instead keeps `TSV_REL` and deletes only a stale docstring. That does not satisfy the mandatory
finding.

Dynamic discovery is not the right repair either. Discovering one matching matrix file does not independently
know the exact required obligation IDs, and parsing mutable review prose would create another current-state
authority.

Install:

```text
.review/M3_CONTRACT_AMENDMENT_2.md
```

with this exact replacement:

> `M3-CLAIM-SUBJECT` requires one explicit claim-matrix subject object which owns both the active matrix path
> and the complete required obligation-ID set. The gate, its messages, and its controls read that one object.
> No docstring, parallel constant, Make recipe, hook line, or review-state parser duplicates or infers the
> subject. A checkpoint transition retargets exactly that one object.

This amendment replaces only the wording of `M3-CLAIM-SUBJECT`. No other M3 contract clause changes.

This review gives that exact amendment GREEN Contract Review. Rob's approval of this Repair 2 authorizes it.

The M4 plan then gives M4-07 one exact design:

```python
SUBJECT = ClaimMatrixSubject(
    matrix=".review/M4_OBLIGATION_MATRIX.tsv",
    required=("M4-01", ...),
)
```

The concrete form may be a frozen tuple, named tuple, or frozen dataclass already available in the standard
library. It is one object, not two authorities.

`load_rows`, diagnostics, required-row closure, controls, and the module's current-subject prose all consume
`SUBJECT`. No matrix path appears in the module docstring.

Do not add dynamic discovery, a new file, a registry, or a review-state parser.

---

# 3. Blocking finding A — `M4-14` confuses “no internal consumer” with “dead theorem”

## Contract violated

This violates:

- M3-COMPILABLE-SURFACES;
- M3-07;
- M3-09;
- the M-series requirement that public theorem guarantees remain unchanged;
- the rule that a theorem statement must expose and retain its accepted guarantee.

## The defect

The audit classifies 48 top-level `Compilable.v` theorems as dead because their names have no textual consumer
elsewhere and the module has no `Hint`.

That proves only that they are not current proof dependencies.

A top-level theorem can be its own externally visible guarantee or a standalone proof-level regression fixture.
Its statement is the product. It does not need an internal caller to have a purpose.

The proposed deletion list visibly contains such fixtures and exact guarantees, including:

```text
reorder_construction_deterministic
empty_program_report
nested_conv_erased_report
three_main_erased_report
fact_program_facts_exact
over_default_int_erased
simultaneous_failures_erased
mixed_order_erased
reordered_construction_determinism_full_determinism
```

The source comments describe several of them as exact rejected-program, ordering, determinism, and fact-table
fixtures.

`make prove` remaining green after deletion would not detect the lost guarantees; the theorem statements
themselves would be gone.

## Required correction

Delete M4-14 from the M4 plan.

Correct `M3-COMPILABLE-SURFACES` to:

```text
A/B/C/D  KEEP for the evidence already recorded.
E        KEEP / no M4 change: consumer-free exported theorem surfaces. The search proves no current internal
         dependency, not semantic deadness. Any future deletion requires a separately reviewed public-surface
         contract which names the guarantees or fixtures being retired.
```

Do not perform a 48-theorem proof-body audit in M3. The finite conclusion is that this mechanical evidence does
not authorize deletion.

Update the audit table, step count, post-M4 graph, matrix evidence, and review request accordingly.

---

# 4. Blocking finding B — M4-06 deletes the authority its retained wiring check reads

## The contradiction

M4-06 says to delete:

```text
M1_ONLY_MODES
```

while leaving:

```text
--wiring
check_permanent_wiring
the permanent M-series wiring law
```

untouched.

`check_permanent_wiring` directly iterates `M1_ONLY_MODES`. Deleting the set either breaks the permanent check
or leaves a check with no checkpoint-only names to prohibit.

## Required exact M4-06 design

Retain `M1_ONLY_MODES` as the explicit unsupported-boundary set of retired M1-only CLI spellings.

Delete:

- the argparse options for those modes;
- the implementations reachable only through them;
- the dead M1 evidence path constants;
- `--m1-self-test`;
- the 25 M1-only mutation entries;
- the mutation harness's `--m1` mode and `mutant_mode` split.

Keep:

- `M1_ONLY_MODES`;
- `PERMANENT_WIRING`;
- `diet_recipe`;
- `check_permanent_wiring`;
- `--wiring`;
- the Make and staged-hook invocations;
- the permanent M-series law.

State the surviving tuple's job plainly:

> These retired checkpoint-only spellings are unsupported and must never re-enter a permanent path.

Acceptance must prove:

- none of the spellings is accepted by argparse;
- none is invoked by Make or the hook;
- the permanent comment law and wiring result are unchanged;
- every remaining mutant is load-bearing.

Do not rename the tuple merely for tidiness.

---

# 5. Blocking finding C — prune the M4 plan again under D-30

The direct optimization plan is still larger and riskier than the measured job requires.

## 5.1 Delete M4-03

M4-03 introduces a reusable filesystem-restoration subsystem across three self-tests to save the cost of
re-copying fixtures.

Its proposed manifest records only size, `mtime_ns`, and directories. The current controls mutate:

- regular files;
- deleted paths;
- directories;
- symlinked files;
- symlinked directories.

Size and mtime do not establish file type, mode, symlink identity, or symlink target. The plan therefore does
not prove that the next control sees the pristine tree it claims.

More importantly, M4-02 removes the multiplier which makes these copies dominant: each mutant will run only its
own named controls rather than every control.

Delete M4-03. Keep the existing per-control isolation, whose simple copy topology is already correct.

Run M4-02 first and measure the remaining `make fcb` cost. Do not build a restoration framework in advance.

Revise the hot-path goal:

```text
gate-mutation-test.py   target under 6 s
make fcb                target under 15 s
```

If the second target is missed, report the result. It is not permission to reintroduce M4-03 without another
review.

## 5.2 Delete M4-13

M4-13 proposes caching a precondition inside the sealed-capability adversarial tests.

The exact shell representation and key ownership are not specified, while the current `meta_reject` controls
deliberately vary `SEALED_PRELUDE` to prove the helper does not accept false evidence.

The expected saving is secondary to the still-open 77-second readable-assumption decision, and the current
two-stage helper is simple and correct.

Delete M4-13. Record the repeated precondition as `KEEP / no M4 change` for this plan.

A later cold-path contract may reconsider it with one exact shell topology and exact adversarial controls.

## 5.3 Narrow M4-09 to the mandatory claim-matrix finding

The frozen mandatory finding is `M3-CLAIM-MUTATION`: whether the claim-matrix gate needs root mutation
coverage.

The plan also creates a new self-test interface and mutation family for `closure-ledger-view.py`. That is useful
possible work, but it is not required to close the recorded claim-matrix defect and it adds another gate surface
during an optimization checkpoint.

Remove the closure-ledger portion from M4-09.

M4-09 becomes:

```text
claim-matrix-gate.py
  subject object / required-row closure
  declaration_patterns
  check_tokens
  load_rows

gate-mutation-test.py
  one exact mutant per retained root fact not already covered
```

Use existing and narrowly added claim-matrix controls. Do not promise a mutant for every helper.

`closure-ledger-view.py` remains KEEP / no M4 change; its canonical CSV and exact `--check` relation remain
unchanged.

This also removes the plan's current contradiction: it says closure `--self-test` will run first in `make fcb`
while listing no Makefile or hook change and claiming the post-M4 graph changes neither.

---

# 6. Revised exact M4 plan

After this repair, the proposed M4 plan contains exactly six authorized steps:

```text
Wave 1   M4-06   delete dead M1 replay implementations and dormant mutants; retain the wiring boundary
         M4-07   one claim-matrix subject object; delete the stale docstring and inert naming exclusion
         M4-08   remove five duplicate readable surfaces and add four missing Complex twins

Wave 2   M4-01   compile the naming patterns once
         M4-02   run each mutant against exactly its named controls

Wave 3   M4-09   add exact claim-matrix root mutation coverage
```

`make perf` runs once after Wave 2.

M4-11 remains unauthorized and nonblocking under Q-M3-01.

The following are explicitly not in this M4 plan:

```text
M4-03 filesystem restoration
M4-04 container batching
M4-05 shared source enumeration
M4-10 narrowed Python-image cache key
M4-12 shell portability/mode cleanup
M4-13 sealed-precondition cache
M4-14 theorem deletion
```

Each receives an evidence-backed KEEP/no-current-M4-change disposition, not a deferred promise.

Replace source line numbers in the plan with stable function, target, stage, and declaration names. Current timing
and count values may remain as diagnostic baselines.

---

# 7. Blocking finding D — current review state contains false statements

## 7.1 Candidate and freeze are conflated

`NEXT_STEPS` says:

```text
M3 candidate: 5af6bc...
This commit is the documentation-only freeze...
```

The candidate is `5af6bc...`.

The documentation-only freeze is `a738365...`.

Record both exact objects correctly.

## 7.2 The scope statement contradicts M3-A1

`NEXT_STEPS` first correctly says M3 implemented no M4 step and no production, proof, Make, hook, Docker, Dune,
generated, or runtime path moved.

It then says:

```text
M3 implemented nothing ... no ... tool ... path moved.
```

That is false. M3-A1 changed two tool files.

Keep one sentence:

> M3 implemented no M4 step. Its sole project-tool change is the M3-A1 claim-matrix self-test precondition
> repair; no production, proof, Make, hook, Docker, Dune, generated, or runtime path moved.

Delete the duplicate.

## 7.3 Review request must pin the exact objects

Set:

```text
candidate: 5af6bc10a811e72fed48a9a1ce09c01c8f1a9e92
freeze: a7383653580e093c9ed4106938bf5be82ecf6d9b
```

The next repair candidate and freeze will replace those values before the next review request.

## 7.4 Amendment authority

After Rob approves this review:

- M3-A1 says Rob authorized it;
- M3-A2 says Rob authorized it;
- this review is named as the GREEN Contract Review for both exact amendments.

No model is recorded as accepting or amending the contract.

---

# 8. Audit, matrix, and review corrections

Update:

- `M3-COMPILABLE-SURFACES`;
- `M3-CLAIM-SUBJECT`;
- `M3-MUTATION-ARCHITECTURE`;
- `M3-CLAIM-MUTATION`;
- `M3-TOOL-COMPLEXITY`;
- the unit-disposition tables;
- the proposed M4 step count and order;
- the post-M4 graph;
- the M3 obligation matrix;
- `NEXT_STEPS`;
- `REVIEW_REQUEST`;
- `REVIEW_BASIS` only to cite M3-A2 and this review;
- `OPEN_QUESTIONS` only to correct M3-A1 authority and keep Q-M3-01 open.

Reopen at least:

```text
M3-06
M3-07
M3-09
M3-10
M3-12
```

Reopen any row whose exact evidence changes. Close each with its actual evidence after the corrections.

M3-11 remains the exact M3-A1 tool exception and no more.

---

# 9. Strict-scope dispositions

| Finding | Blocks M3 | Owner |
|---|---:|---|
| M3-A1 lacks the required human authority and recorded Contract Review | yes | M3 Repair 2 |
| M3-CLAIM-SUBJECT is not satisfied | yes | M3-A2 / M3 Repair 2 |
| M4-14 would delete exported theorem guarantees and fixtures on insufficient evidence | yes | M3 Repair 2 |
| M4-06 deletes the set its retained permanent wiring rule reads | yes | M3 Repair 2 |
| M4-03 adds an incomplete restoration subsystem | yes | delete from current M4 plan |
| M4-13 is not exact enough for an adversarial proof gate | yes | delete from current M4 plan |
| Closure-ledger mutation coverage | no | KEEP now; reconsider only under a later exact requirement |
| Q-M3-01 readable assumption placement | no | Rob; default no change |
| Container-start batching, shared enumeration, cache-key narrowing, portability | no | KEEP / no current M4 change |
| General proof-module splitting | no | later evidence and separate approval |

Do not implement any M4 step during this repair.

---

# 10. Allowed changes

This repair may change only:

```text
.review/M3_CONTRACT_AMENDMENT_1.md       authority and review attribution only
.review/M3_CONTRACT_AMENDMENT_2.md       new, exact M3-A2
.review/M3_FORENSIC_AUDIT_REPAIR_2.md    this review installed as the sole repair authority
.review/M3_AUDIT.md
.review/M4_MECHANICAL_REFACTOR_PLAN.md
.review/M3_OBLIGATION_MATRIX.tsv
.review/NEXT_STEPS.md
.review/OPEN_QUESTIONS.md
.review/REVIEW_REQUEST.md
.review/REVIEW_BASIS.md                  citations only
.review/fcb/current/FIDO_FCB_REFERENCES.tsv and exact owner markers required by those files
```

It may not change:

- any project tool;
- Makefile;
- the hook;
- Dockerfile;
- Dune;
- any `.v` or OCaml file;
- generated Go;
- fixtures or goldens;
- `tools/perf.sh` or `.review/PERFORMANCE.tsv`;
- `life.md`;
- any M4 production path.

No measurement rerun is required.

---

# 11. Work order

1. Wait for Rob's plain-language approval of M3-A1 and M3-A2 as stated here.
2. Install this file as `.review/M3_FORENSIC_AUDIT_REPAIR_2.md`, the sole active repair authority.
3. Correct M3-A1's authority and Contract Review record.
4. Install M3-A2.
5. Reopen the affected M3 obligation rows.
6. Correct the audit dispositions.
7. Replace the M4 plan with the six-step exact plan.
8. Correct `NEXT_STEPS`, `REVIEW_REQUEST`, `OPEN_QUESTIONS`, and the basis citation.
9. Run all current gates.
10. Commit one exact documentation-only repair candidate.
11. Add one later documentation-only freeze requesting M3 Implementation Review.
12. Notify Rob.

No project source or tool byte should change in this repair.

---

# 12. Verification

Run:

```text
make claims
make fcb
make names
make diet
make hostpython
make fmt
make check
```

Run the real pre-commit hook over the exact staged snapshot without bypass.

Also verify:

- M3-A1 and M3-A2 name Rob, not a model, as human authority;
- the review record is the bounded GREEN Contract Review for both;
- the candidate and freeze SHAs are distinct and correct;
- no review-state sentence says no tool changed;
- M4-14, M4-03, and M4-13 are absent;
- M4-06 retains the explicit retired-mode set and permanent wiring check;
- M4-07 has one exact subject object and no dynamic discovery;
- M4-09 covers claim-matrix root facts only;
- the plan has exactly six authorized steps and no unresolved alternative or fallback;
- every mandatory finding maps to an existing step or an evidence-backed KEEP;
- all twelve M3 obligations are closed with exact current evidence;
- every file outside `.review` is byte-identical to candidate `5af6bc10a811e72fed48a9a1ce09c01c8f1a9e92`;
- generated hashes remain:

```text
go.mod
d8f8d4f62b5b574067a4e4bf64a298bbe2cb5bc9a28d8f9c321c776e838cf1fa

main.go
b6765619f969e7fd85b4998616d8a515c5a2c0e2d397c3ee915718f35fbc48de
```

- runtime stdout, stderr, and exit status still match the reviewed goldens;
- M4, C5 Step 0, and C5 did not begin.

Do not create another audit, inventory, path checker, plan validator, or review-state schema.

---

# 13. Definition of done

M3 Repair 2 is complete only when:

- Rob has ratified M3-A1 and M3-A2;
- the contract-amendment process is recorded truthfully;
- consumer-free public theorems are not deleted as dead internal helpers;
- the mandatory claim-subject finding is closed by one explicit subject object;
- the source-diet wiring authority remains coherent;
- the M4 plan contains only six justified, exact steps;
- the plan adds no filesystem-restoration subsystem and no sealed-test cache;
- the audit, matrix, current state, and review request agree;
- every current gate is green;
- one exact repair candidate is followed by one documentation-only freeze;
- no commit follows the freeze;
- Claude notifies Rob.

Only Rob accepts M3 and separately approves the final exact M4 plan.

**Complexity fit: BLOCKED — the forensic evidence is strong, but the proposed M4 plan still deletes public
proof surfaces and introduces machinery whose measured jobs do not justify it.**
