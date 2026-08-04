# M4 — Mechanical Refactor Plan

status: proposed — M4 is FORBIDDEN until Rob accepts M3 and separately approves this exact plan
(`M4-PLAN-APPROVAL`)

Produced by M3 under `.review/M3_TOOL_AND_BUILD_ARCHITECTURE_AUDIT.md`, activation
`0b7fd86825936c37f31ef83879574d526d548122`, as amended by `.review/M3_CONTRACT_AMENDMENT_1.md` (`M3-A1`) and
`.review/M3_CONTRACT_AMENDMENT_2.md` (`M3-A2`), both authorized by Rob. Evidence: `.review/M3_AUDIT.md`.
Pruned under `.review/M3_FORENSIC_AUDIT_REPAIR_1.md` §6 and `.review/M3_FORENSIC_AUDIT_REPAIR_2.md` §5.

**M3 recorded the baselines below. M3 implemented no step and produced no after value.** Every "after" here
is an **acceptance criterion M4 must meet**, never an observation. Where a step names a target, it is a
target.

**Six steps. No step contains an alternative, a fallback, or a "decide during M4".** Each names one exact
design and identifies its subjects by stable name — function, target, stage, declaration — never by line
number. `M4-11` is written up at the end and is **not** one of the six: it is unauthorized pending Rob's
answer to `Q-M3-01`.

---

## 0. How every step is measured and verified

```text
BASELINE (already recorded; do not re-derive):  .review/M3_AUDIT.md §1.1, §1.2, §3.1
AFTER, configuration A (serial diagnostic):     make perf     -> rewrites .review/PERFORMANCE.tsv
AFTER, configuration B (one target, host idle, builder fido-builder, default concurrency):
                                                make <target> -> wall time, at the step's own commit
```

`make perf` runs **once, after Wave 2**. Configuration A and configuration B numbers are never pooled.

**Verification per step, and no more than this:**

```text
1. during development: run only the directly affected target or control
2. before the step commit:   make check
                             make fmt
3. commit through the real pre-commit hook over the staged snapshot, without --no-verify
```

`make check` already runs `fcb`, `claims`, `names`, `diet` and `hostpython`; invoking them separately repeats
the same working-tree work without adding a source view — the waste this audit exists to remove.
`make regenerate`, `make regen-guard` and `make audit-fresh` run **only at wave boundaries**, unless a step
directly changes those paths. None of the six does.

**Byte-invariance per step:** `git diff <wave baseline> -- '*.v' plugin/ e2e/ go.mod '**/*.go'` is EMPTY
except for `M4-08`, which touches `gate/Assumptions.v` alone. **No step changes any `.v` under `dune`'s
`(modules …)`, the Makefile, the hook, the Dockerfile or a Dune file.**

**Rollback boundary, every step:** one commit per step, reverted with `git revert` of that single commit if
any gate fails. No step depends on an uncommitted predecessor, and waves are ordered so reverting a later
step never invalidates an earlier one.

---

## Wave 1 — deletions and corrections

No performance claim. These remove dead surface and close two mandatory findings.

### M4-06 — delete the dead M1 replay implementations, keep the boundary that names them

**Root cause** (`M3-SOURCE-DIET-REPLAY`): seven CLI modes in `tools/source-diet.py` are invoked by no
Makefile recipe and no hook line, name six repository paths that no longer exist, and are guarded by 25
mutants routed to `--m1-self-test`, which nothing invokes.

**The trap this step must not fall into.** `check_permanent_wiring` — the permanent M-series law, run by
`make diet --wiring` and by the hook on every commit — *iterates* `M1_ONLY_MODES` to prove no permanent path
invokes a checkpoint-only mode. Deleting that tuple would either break the retained check or leave it with
nothing to prohibit. An earlier draft of this step did exactly that.

**Delete**

```text
tools/source-diet.py         the argparse options for --against-baseline, --disposition-exact,
                             --code-identical, --verify-m1-evidence, --write-metrics-table,
                             --write-disposition and --m1-self-test
                             the implementations reachable only through them: verify_m1_evidence,
                             m1_self_test, m1_topology_repo, and their helpers
                             the six dead M1 evidence path constants
tools/gate-mutation-test.py  the 25 M1-only mutation entries, the --m1 mode, and the mutant_mode split;
                             MUTANTS becomes one list in which every entry is selected
.review/M_SERIES_PLAN.md     restate what survives, if it names a deleted mode
```

**Keep**

```text
tools/source-diet.py         M1_ONLY_MODES, PERMANENT_WIRING, diet_recipe, check_permanent_wiring, --wiring
Makefile / .githooks         their existing invocations, unchanged
                             the permanent M-series law itself
```

`M1_ONLY_MODES` survives with its job stated plainly in the source:

> These retired checkpoint-only spellings are unsupported and must never re-enter a permanent path.

**Do not rename the tuple for tidiness.** Its name is what the wiring check and its controls refer to.

**Deletions made legal by:** Rob's M1 acceptance, `M1-ACCEPT-6524b43`. M1's exit evidence was consumed at its
review and the ledgers these modes read were deleted then; Git owns them.

**Baseline:** `tools/source-diet.py` 2 294 lines; `tools/gate-mutation-test.py` 68 entries, 43 selected.
**Acceptance:**

```text
none of the seven spellings is accepted by argparse (each must exit as an unrecognized argument)
none is invoked by Make or the hook
make diet output byte-identical, including the wiring line's permanent-path count
every remaining mutant reported load-bearing by name
no M1_ path constant remains that does not resolve
```

### M4-07 — one claim-matrix subject object

**Root cause** (`M3-CLAIM-SUBJECT`, as replaced by `M3-A2`): the active matrix path and the required
obligation-ID set are two hand-retargeted constants, and a third copy of the path had already drifted into
the module docstring naming a matrix deleted at M2 closeout.

**Exact design.** One object owns both facts:

```python
SUBJECT = ClaimMatrixSubject(
    matrix=".review/M4_OBLIGATION_MATRIX.tsv",
    required=("M4-01", ...),
)
```

A frozen tuple, named tuple or frozen dataclass from the standard library — a thin domain wrapper, which the
collection law allows. **One object, not two authorities.**

```text
consume SUBJECT   load_rows, the diagnostics and error messages, the required-row closure, every control,
                  and the module's own current-subject prose
delete            the separate matrix-path and required-ID constants
delete            the matrix path from the module docstring; no second copy anywhere
also delete       the third EXCLUDED_FILES entry in tools/naming-gate.py, which names a C4 review document
                  that is not in the tree, so it excludes nothing and would cover the next file to take
                  that name
```

**Not authorized:** dynamic discovery, a new file, a registry, a schema, or a review-state parser. A
checkpoint transition retargets exactly one object.

**Invariants preserved:** the matrix relation checks exactly what it checks today; the A005 policy is
unchanged; the deleted exclusion excluded nothing, so no file changes classification.

**Baseline:** two hand-retargeted constants plus one dangling docstring path; one dangling naming exclusion.
**Acceptance:** exactly one occurrence of the matrix path in the module; `make claims` green with the same
reported obligation counts; `make names` reports the same file count and the same empty violation set; a
control proving a required ID absent from `SUBJECT.required` is still detected.

### M4-08 — repair the readable assumption surface

**Root cause** (`M3-ASSUMPTION-DUPLICATES`, `M3-ASSUMPTION-SURFACES`): 540 `Print Assumptions` lines for 535
distinct surfaces, and four Complex real/imaginary pairs gated on the real half only.

**Exact change** — `gate/Assumptions.v` only:

```text
delete 5 duplicates   Compilable.capability_is_compile_outcome
                      Compilable.capability_source
                      Compilable.forest_count_source
                      Compilable.member_at_in_forest
                      Compilable.occurrence_expr_diags_conv_sound
add 4 missing twins   Complex.typed_runtime_imaginary_coherent
                      Complex.typed_runtime_imaginary_not_inf
                      Complex.typed_runtime_imaginary_not_nan
                      Complex.typed_runtime_imaginary_not_neg_zero
```

**This edits the gate module, never a certified one.** `dune`'s `(modules …)` does not include `gate/`, and
the certified-module coverage check compares tracked **root** `.v` against that list, so the theory is
untouched and no `Fido` `.vo` changes.

**Invariants preserved:** the `prover` stage's fail-closed pair — zero `^Axioms:` **and** `want == got` —
holds by construction: 540 − 5 + 4 = 539 declared, each of which must print `Closed under the global
context`. The whole-theory `Fido Audit Assumptions` is unchanged and remains the authority.

**Baseline:** 540 declared / 535 distinct; the stage prints "540/540 surfaces closed".
**Acceptance:** 539 declared / 539 distinct; the stage prints "539/539"; `make prove` green; each of the four
new surfaces reports closed.

---

## Wave 2 — the hot path

Baseline **`make check` hot = 63 680 ms (A)**, of which `names` 22 310 and `fcb` 28 580; at the subject ref
(B) `make names` 23 440 ms and `make fcb` 33 330 ms.

### M4-01 — compile the naming gate's patterns once

**Root cause** (`M3-PERF-NAMES`): `check_prose` and `check_code` in `tools/naming-gate.py` build a pattern
**string** per line per retired name, so a 160-name table makes 9 371 786 `re.escape` and 10 207 628
`re.search` calls.

**Exact change:** build the 160 core patterns and the 20 compound patterns **once** at module import into a
compiled table, and search with the compiled objects inside the loop. The loop, its order, its per-name
messages and its results are unchanged.

```python
# module level, once
RETIRED_PATTERNS = tuple(
    (old, re.compile(r"(?<![\w.'/-])" + re.escape(old) + r"(?![\w'])"))
    for old in OLD_MODULES + OLD_NAMES + OLD_FILES + DELETED_SURFACES)
# inside check_prose / check_code
for old, pat in RETIRED_PATTERNS:
    if pat.search(line):
        ...
```

The `digits` special case keeps its own compiled pattern and its `continue`, so the prose path still performs
one fewer escape than the code path — that asymmetry is preserved exactly, not tidied.

**Not proposed:** collapsing the 160 patterns into one alternation. Where one retired name is a substring of
another the loop reports **both**, and an alternation reports only the first alternative matching at a
position. That is a behaviour change and is not part of this step.

**Files changed:** `tools/naming-gate.py` only.

**Invariants preserved:** identical violation set, identical messages, identical exit status, identical
`N files examined`; all 72 controls pass unchanged. The gate's own self-test is the differential.

**Baseline:** `names` 22 310 ms (A hot), 23 440 ms (B, subject ref, host idle); 9 371 786 `re.escape` calls.
**Acceptance:** under 1 000 `re.escape` calls under the exact cProfile command recorded in
`.review/M3_AUDIT.md` `M3-PERF-NAMES`; `make names` (B, host idle) **target under 5 000 ms**; zero change in
reported violations on the tree or on the gate's own fixtures.

### M4-02 — run each mutant against exactly its named controls

**Root cause** (`M3-PERF-FCB`): `run_mutant` in `tools/gate-mutation-test.py` runs each gate's **entire**
self-test while `main` only asserts that the mutant's own `expected` controls fired — 43 mutants, 2 019
nested control executions, 26 220 ms, 79% of `fcb`.

**Exact design:**

```text
selector        every gate that has mutation entries accepts --only <label>, repeatable
unknown label   fails closed: the gate exits nonzero naming the unknown label
empty selection an empty selected set fails closed; selecting nothing must never pass
harness         run_mutant passes exactly the mutant's expected control labels, one --only each
unfiltered      with no --only, the self-test is the ordinary complete gate self-test, unchanged
assertions      unchanged: the mutant must exit nonzero AND every expected label must appear among the
                reported failures
```

**Why the evidence does not weaken.** The current assertion is: the self-test fails, and every label in
`expected` is among the failures. Running only the `expected` controls preserves both halves — a mutant whose
named controls still pass still fails the step. What is lost was never asserted: noticing that a mutation
*also* broke unrelated controls.

**This step, not a restoration subsystem, is what removes the copy cost.** The whole-tree copies inside
`fcb-reference-gate`, `human-review-index` and `claim-matrix-gate` are dominant only because every mutant
runs every one of their controls. Removing the multiplier is the smaller change and it comes first.

**Files changed:** `tools/gate-mutation-test.py`, plus one `--only` argument in each gate that has mutants.

**Baseline:** `gate-mutation-test` 26 220 ms (B, subject ref), 43 mutants, 2 019 nested control executions.
**Acceptance:**

```text
every mutant still reported load-bearing by name
gate-mutation-test   target under 6 000 ms
make fcb             target under 15 000 ms
two new controls: an unknown label fails closed, and an empty selection fails closed
```

If the `make fcb` target is missed, **report the measured result**. That is not permission to reintroduce a
restoration subsystem without another review.

`make perf` runs once at the end of this wave.

---

## Wave 3 — coverage

### M4-09 — claim-matrix root mutation coverage

**Root cause** (`M3-CLAIM-MUTATION`): `tools/claim-matrix-gate.py` has eighteen root helpers and two mutants,
and the precondition defect `M3-A1` repaired is exactly what missing coverage looks like — a rule nothing
proved load-bearing, which reached a freeze.

**Scope: this gate's root facts only.** Not every helper that exists, and not another gate.

```text
tools/claim-matrix-gate.py
  the subject object      the active matrix and its complete required-ID set are one authority; a required
                          ID absent from SUBJECT.required must be detected
                          control: 'a required obligation row is missing'
  declaration_patterns    a surface is DECLARED, never merely mentioned; a bare mention in a comment must
                          not satisfy an implementation cell
                          control: 'a named implementation surface never existed'
  check_tokens            an evidence token must occur LITERALLY in the file it names
                          control: 'an evidence token that does not occur in the file it names'   (new)
  load_rows               no duplicate row, no malformed row, no unknown status
                          control: 'a duplicated obligation row'                                  (new)

tools/gate-mutation-test.py
  one exact mutant per retained root fact above that is not already covered
```

Existing controls are used where they exist; two are added narrowly. **No mutant is promised for a helper
merely because it exists.**

**`tools/closure-ledger-view.py` is not in this step.** It has no `--self-test` at all, which the audit
records — but giving it a self-test interface and a mutation family adds a gate surface during an
optimization checkpoint, to close a defect no mandatory finding names. It is **KEEP, no M4 change**; its
canonical CSV and its exact `--check` relation are unchanged. This also removes an earlier draft's
contradiction, which promised a new gate would run first in `make fcb` while listing no Makefile change.

**Files changed:** `tools/claim-matrix-gate.py`, `tools/gate-mutation-test.py`.

**Baseline:** 2 claim-gate mutants over 18 root helpers.
**Acceptance:** each named root fact has one mutant, each proved load-bearing by name; the two new controls
present and passing; `make claims` and `make fcb` green.

---

## 5. Not in this plan

### M4-11 — the readable Print-Assumptions gate's 77 s — UNAUTHORIZED

`rocq c gate/Assumptions.v` costs ≈77 s: 59% of the cold `prover` stage and 29% of the whole 270 s cold
`make check`, while the strictly stronger whole-theory `Fido Audit Assumptions` costs 1.72 s.
`M3-EDIT-WEIGHT` shows this is the path semantic work actually walks — `Compilable.v` co-changes with
`gate/Assumptions.v` in 12 of 25 commits.

Reducing a readable proof surface changes what a human can check by eye, and `CLAUDE.md` makes those surfaces
a standing public claim. That is not mechanical. It is `Q-M3-01` in `.review/OPEN_QUESTIONS.md`, owned by
Rob, non-blocking, default "change nothing". **No M4 step proceeds from it without an explicit decision, and
it is not counted among the six.**

### Considered and not in this plan, each with an evidence-backed disposition

```text
M4-03  filesystem restoration        its manifest recorded size, mtime_ns and directories, which do not
                                     establish file type, mode, symlink identity or symlink target — while
                                     the controls mutate all of those. It would not have proved the property
                                     it claimed, and M4-02 removes the multiplier that made copies dominant.
                                     KEEP the existing per-control isolation.        (M3-MUTATION-ARCHITECTURE)
M4-04  container batching            restructures the Makefile and the hook to recover a floor that shrinks
                                     anyway once M4-01 and M4-02 land.               (M3-NO-HOST-PYTHON-COST)
M4-05  shared source enumeration     the five Python gates differ in SELECTION, not just traversal — 102,
                                     113 and 111 files at the same ref.               (M3-SOURCE-ENUMERATION)
M4-10  narrowed PYTAG cache key      needs a fail-closed Dockerfile-stage parser in both the Makefile and the
                                     hook, and inverts the risk to a stale image.           (M3-INVALIDATION)
M4-12  shell portability and modes   the host boundary is as declared; no current requirement asks for BSD
                                     portability or a tidier mode bit.           (M3-HOST-CONTAINER-OTHER)
M4-13  sealed-precondition cache     a cache inside an adversarial proof gate needs an exact shell topology
                                     and key ownership this plan does not have, while the meta_reject
                                     controls deliberately vary the prelude.                        (§3.1)
M4-14  theorem deletion              consumer-freeness proves no current internal dependency, not semantic
                                     deadness; a top-level theorem can be its own guarantee or a standalone
                                     fixture whose statement IS the product.      (M3-COMPILABLE-SURFACES)
       closure-ledger coverage       useful, but not required by any mandatory finding, and it would add a
                                     gate surface during an optimization checkpoint.      (M3-CLAIM-MUTATION)
       a tool-prose path checker     a weak path scanner to catch strings M4-07 deletes.    (M3-FRAGILE-PROSE)
       proof-module splitting        Compilable.v's downstream rebuild set is already 3.      (M3-DUNE-FANOUT)
```

Each is a `KEEP / no current M4 change` with its measured evidence recorded in the audit. **None is a
deferred promise.**

---

## 6. Post-M4 execution graph

Unchanged in shape: the same nine completion markers, the same full-acceptance join, the same partial
targets, the same Docker DAG, the same six caches, the same two source views and two entry points. **No
Makefile recipe, no hook line, no Docker stage, no cache key and no Dune file changes.** What changes:

```text
make check   names  22.3 s              ->  target < 5 s              (M4-01)
             fcb    28.6 s              ->  target < 15 s             (M4-02)
prover       unchanged; gate/Assumptions.v needs a decision           (M4-11, unauthorized)
tools        the M1 replay implementations and 25 dormant mutants     ->  deleted
             two hand-retargeted claim-matrix constants               ->  one subject object
             one dangling naming exclusion, one stale docstring path  ->  deleted
gate         540 Print Assumptions / 535 distinct  ->  539 / 539, four missing twins added
coverage     claim-matrix root facts gain mutants and two controls
```

No target is removed, no gate is removed, no source view is collapsed, no partial result is presented as full
acceptance, and no exported theorem is deleted.

## 7. Step order

```text
Wave 1   M4-06  M4-07  M4-08      deletions and corrections; no performance claim
Wave 2   M4-01  M4-02             hot path
Wave 3   M4-09                    claim-matrix root coverage
```

`make perf` runs once at the end of Wave 2. The §0 verification runs after **every** step.
