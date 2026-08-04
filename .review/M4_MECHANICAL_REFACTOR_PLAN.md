# M4 — Mechanical Refactor Plan

status: proposed — M4 is FORBIDDEN until Rob accepts M3 and separately approves this exact plan
(`M4-PLAN-APPROVAL`)

Produced by M3 under `.review/M3_TOOL_AND_BUILD_ARCHITECTURE_AUDIT.md`, activation
`0b7fd86825936c37f31ef83879574d526d548122`, as amended by `.review/M3_CONTRACT_AMENDMENT_1.md`.
Evidence: `.review/M3_AUDIT.md`. Pruned under `.review/M3_FORENSIC_AUDIT_REPAIR_1.md` §6.

**M3 recorded the baselines below. M3 implemented no step and produced no after value.** Every "after" here
is an **acceptance criterion M4 must meet**, never an observation. Where a step names a target, it is a
target.

**Nine steps. No step contains an alternative, a fallback, or a "decide during M4".** Each names one exact
design. `M4-11` is written up at the end and is **not** one of the nine: it is unauthorized pending Rob's
answer to `Q-M3-01`.

---

## 0. How every step is measured and verified

```text
BASELINE (already recorded; do not re-derive):  .review/M3_AUDIT.md §1.1, §1.2, §3.1
AFTER, configuration A (serial diagnostic):     make perf     -> rewrites .review/PERFORMANCE.tsv
AFTER, configuration B (one target, host idle, builder fido-builder, default concurrency):
                                                make <target> -> wall time, at the step's own commit
AFTER, cold prover internals:                   make prover-log FIDO_PERF_COLD=1
```

`make perf` runs **once at the end of a wave**, never per step. Configuration A and configuration B numbers
are never pooled or compared.

**Verification per step, and no more than this:**

```text
1. during development: run only the directly affected target or control
2. before the step commit:   make check
                             make fmt
3. commit through the real pre-commit hook over the staged snapshot, without --no-verify
```

`make check` already runs `fcb`, `claims`, `names`, `diet` and `hostpython`; invoking them separately repeats
the same working-tree work without adding a source view, which is the waste this audit exists to remove.
`make regenerate`, `make regen-guard` and `make audit-fresh` run **only at wave boundaries**, unless a step
directly changes those paths — none of the nine does.

**Byte-invariance per step:** `git diff <wave baseline> -- '*.v' plugin/ e2e/ go.mod '**/*.go'` is EMPTY
except for `M4-08` (`gate/Assumptions.v` only) and `M4-14` (`Compilable.v` only).

**Rollback boundary, every step:** one commit per step, reverted with `git revert` of that single commit if
any gate fails. No step depends on an uncommitted predecessor, and waves are ordered so reverting a later
step never invalidates an earlier one.

---

## Wave 1 — deletions and corrections

No performance claim. These remove dead surface so later waves edit less.

### M4-06 — delete the dead M1 replay path

**Root cause** (`M3-SOURCE-DIET-REPLAY`): seven CLI modes in `tools/source-diet.py` are invoked by no
Makefile recipe and no hook line, name six repository paths that no longer exist, and are guarded by 25
mutants that `mutant_mode` routes to `--m1-self-test`, which nothing invokes.

**Exact change**

```text
tools/source-diet.py         delete M1_ONLY_MODES and each mode it names — --against-baseline,
                             --disposition-exact, --code-identical, --verify-m1-evidence,
                             --write-metrics-table, --write-disposition, --m1-self-test — the six dead
                             path constants at lines 41-44 and 50, and the code reachable only from those
                             modes (verify_m1_evidence:997, m1_self_test:1523, m1_topology_repo:2108)
tools/gate-mutation-test.py  delete the 25 --m1-self-test entries and the mutant_mode indirection;
                             MUTANTS becomes one list in which every entry is selected
.review/M_SERIES_PLAN.md     restate what survives, if it names a deleted mode
```

**Authority removed:** none. The `.v` comment law, the exception relation and `--wiring` are untouched —
those are what `make diet` and the hook invoke.

**Deletions made legal by:** Rob's M1 acceptance, `M1-ACCEPT-6524b43`. M1's exit evidence was consumed at its
review and the ledgers these modes read were deleted then; Git owns them.

**Source-view / cache-key consequences:** none.

**Baseline:** `tools/source-diet.py` 2 294 lines; `tools/gate-mutation-test.py` 68 entries, 43 selected.
**Acceptance:** both files smaller; `make diet` output byte-identical; every remaining mutant reported
load-bearing by name; no `M1_` path constant remains that does not resolve.

### M4-07 — delete two stale strings

**Root cause** (`M3-CLAIM-SUBJECT`, `M3-NAMING-EXCLUSION`): the claim gate's docstring names a matrix deleted
at M2 closeout, and the naming gate excludes a C4 review document that is not in the tree.

**Exact change**

```text
tools/claim-matrix-gate.py  delete the stale matrix path from the module docstring, so exactly one place
                            (TSV_REL) names the current matrix
tools/naming-gate.py        delete the third EXCLUDED_FILES entry, which names a file not in the tree
```

`TSV_REL` **stays** the one current claim-matrix subject authority. Deriving it from review state would
couple the gate to a document it must not read, and the drift that actually happened was the prose, not the
constant. **No generic "tool prose path" checker is added**: that would be a weak path scanner built to catch
two strings this step deletes.

**Invariants preserved:** the A005 policy and the claim-matrix relation keep their exact meaning. The deleted
exclusion excluded nothing, so no file changes classification.

**Baseline:** one dangling path in the claim gate's docstring, one dangling exclusion in the naming gate.
**Acceptance:** both gone; `make names` reports the same file count and the same (empty) violation set;
`make claims` unchanged.

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

### M4-14 — delete the 48 consumer-free `Compilable.v` declarations

**Root cause** (`M3-COMPILABLE-SURFACES`): 48 top-level `Theorem`/`Lemma`/`Corollary` in `Compilable.v` have
no consumer anywhere — not the readable gate, not another module, not `e2e/` or `plugin/`, and not elsewhere
in `Compilable.v` itself. `Compilable.v` declares no `Hint`, so nothing there can be applied without being
named; a name that occurs only at its own declaration site is dead.

**Exact change** — `Compilable.v` only. Delete these 48 declarations and their proofs:

```text
erase_diagnostic_code                erase_diagnostic_primary             erase_diagnostic_related
erase_diagnostic_related_length      occurrences_expr_head_ex             expression_conv_target_some
const_info_child_some                conversion_operand_ref_tot_view      occurrence_type_name_fact_none
outcome_dom_exact_skip               conv_target_table_type               expression_ref_view_eq
local_conv_failure_sound             occurrence_emits_none_pure_typename  semantic_diagnostics_nonempty
is_version_element_spec              selected_count_empty                 selected_one_dir
dir_component_neq_gomod              dir_component_neq_filename           filename_ok_neq_gomod
preflight_fails_dir                  source_spec_valid_files_equal        package_import_path_input_equal
reorder_construction_deterministic   empty_program_report                 nested_conv_erased_report
three_main_erased_report             missing_main_erased_report           fact_program_facts_exact
fact_program_inner_literal           fact_program_inner_conversion        fact_program_outer_arg
fact_program_outer_fact              dup_lit_facts_exact                  nested_use_single_resolution
inner_fail_one_inner_no_outer        over_default_int_erased              over_default_float_erased
over_default_complex_erased          bad_int8_erased                      frac_f2i_erased
nz_c2s_erased                        wrongkind_erased                     dup_across_files_erased
simultaneous_failures_erased         mixed_order_erased
reordered_construction_determinism_full_determinism
```

**Deletions made legal by:** the project's standing law — ruthless correctness or ruthless deletion, no
middle state — and by the measured absence of any consumer. Nothing gated, exported, extracted or fixtured
refers to them.

**Invariants preserved:** every gated surface, every proof that survives, the whole-theory assumption audit,
the generated bytes and the goldens. **`gate/Assumptions.v` names none of the 48** — that is group A, and
these are group E — so the readable gate's count is unchanged by this step.

**Rollback boundary:** if `make prove` fails, some deleted declaration was in fact a proof dependency the
name search missed. Revert the single commit; the finding reopens with that counter-example named.

**Baseline:** `Compilable.v` 10 156 lines, 623 top-level `Theorem`/`Lemma`/`Corollary`.
**Acceptance:** 575 remain; `make prove` green including the whole-theory audit; readable gate still 539/539;
`make check` green with generated bytes and goldens byte-identical.

---

## Wave 2 — the hot path

Baseline **`make check` hot = 63 680 ms (A)**, of which `names` 22 310 and `fcb` 28 580; at the subject ref
(B) `make names` 23 440 ms and `make fcb` 33 330 ms.

### M4-01 — compile the naming gate's patterns once

**Root cause** (`M3-PERF-NAMES`): `tools/naming-gate.py:336` (and `:290`, `:342`) build a pattern **string**
per line per retired name, so a 160-name table makes 9 371 786 `re.escape` and 10 207 628 `re.search` calls.

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

**Files changed:** `tools/naming-gate.py` only. **Cache-key consequences:** none — `PYTAG` does not cover
`tools/`.

**Invariants preserved:** identical violation set, identical messages, identical exit status, identical
`N files examined`; all 72 controls pass unchanged. The gate's own self-test is the differential.

**Baseline:** `names` 22 310 ms (A hot), 23 440 ms (B, subject ref, host idle); 9 371 786 `re.escape` calls.
**Acceptance:** under 1 000 `re.escape` calls under the exact cProfile command recorded in
`.review/M3_AUDIT.md` `M3-PERF-NAMES`; `make names` (B, host idle) **target under 5 000 ms**; zero change in
reported violations on the tree or on the gate's own fixtures.

### M4-03 — one pristine fixture per self-test, restored between controls

**Root cause** (`M3-MUTATION-ARCHITECTURE`): three gates copy the whole tree per control —
`fcb-reference-gate.py:scenario` 704 copies per `make fcb`, `human-review-index.py` 48,
`claim-matrix-gate.py` 50 — and the mutation harness multiplies them.

**Exact design.** One design, named in full:

```text
pristine fixture owner   each gate's self_test() makes ONE copy of the tree, PRISTINE, before any control,
                         and one WORK copy that every control runs against
manifest                 immediately after the copies, walk WORK once and record (relative path -> size,
                         mtime_ns) for every file, plus the set of directories
what a control may       anything under WORK; controls are not restricted, because restricting them would
mutate                   change what they test
restoration              after each control, walk WORK against the manifest:
                           path absent from the manifest        -> delete it (a created path)
                           path in the manifest but missing     -> re-copy from PRISTINE (a deleted path)
                           size or mtime_ns differs             -> re-copy from PRISTINE (a modified path)
                           directories created by a control     -> removed after their contents
                         PRISTINE is never written; WORK is never re-created
```

`mtime_ns` changes whenever a file is written, so it detects a same-size rewrite. A control that rewrote
identical bytes would be restored unnecessarily, which is harmless. Nothing in these fixtures restores an
mtime.

**The control that proves it.** One new control per affected gate, run in the middle of the sequence:

```text
'a control's mutations do not leak into the next one'
  step 1  delete one known file, modify a second, create a third
  step 2  return, letting the harness restore
  step 3  assert all three match PRISTINE byte for byte, and that the created path is gone
```

Without this the restoration could silently degrade and every later control would be judging a dirty tree.

**Files changed:** `tools/fcb-reference-gate.py`, `tools/human-review-index.py`,
`tools/claim-matrix-gate.py`. `tools/source-diet.py`, `tools/host-python-gate.py` and
`tools/naming-gate.py` build small fixtures rather than copying and are **not** touched.

**Invariants preserved:** each control still runs against a tree containing exactly its own mutation and
nothing else. That isolation is the evidence.

**Baseline:** `fcb-reference-gate.py --self-test` 3 710 ms (B, subject ref), 64 controls; 802 whole-tree
copies per `make fcb` across the three gates.
**Acceptance:** the same control counts with the same per-control pass/fail in all three gates;
`fcb-reference-gate.py --self-test` **target under 1 500 ms**; the new leak control present and passing in
each of the three.

### M4-02 — run each mutant against the controls it names

**Root cause** (`M3-PERF-FCB`): `run_mutant` runs each gate's **entire** self-test while `main` only asserts
that the mutant's own `expected` controls fired — 43 mutants, 2 019 nested control executions, 26 220 ms,
79% of `fcb`.

**Ordering:** strictly after `M4-03`, so the per-control copy cost is already gone when this is measured.

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

**Files changed:** `tools/gate-mutation-test.py`, plus one `--only` argument in each gate that has mutants.

**Baseline:** `gate-mutation-test` 26 220 ms (B, subject ref), 43 mutants, 2 019 nested control executions.
**Acceptance:** every mutant still reported load-bearing by name; **target under 6 000 ms**; two new controls
— an unknown label fails closed, and an empty selection fails closed.

---

## Wave 3 — coverage

### M4-09 — mutation coverage for the two least-covered gates

**Root cause** (`M3-CLAIM-MUTATION`): `claim-matrix-gate.py` has 18 root helpers and 2 mutants;
`closure-ledger-view.py` has 6 root helpers, **no `--self-test` at all**, and publishes a generated FCB view.
The precondition defect `M3-A1` repaired is exactly what missing coverage looks like.

**This step covers root facts accepted claims depend on, not every helper that exists.**

```text
tools/claim-matrix-gate.py
  declaration_patterns   a surface is DECLARED, never merely mentioned; a bare mention in a comment must
                         not satisfy an implementation cell
                         control: 'a named implementation surface never existed'
  check_tokens           an evidence token must occur LITERALLY in the named file
                         control: 'an evidence token that does not occur in the file it names'  (new)
  load_rows              every required obligation present exactly once, no duplicate, no absence
                         control: 'a required obligation row is missing'

tools/closure-ledger-view.py
  FIRST add --self-test with its own controls; a mutant against a gate with no controls proves nothing.
  load                   the canonical CSV parses fail-closed: a malformed row is an error, never a skip
                         control: 'a malformed canonical row'                                    (new)
  render                 the published view is a total function of the canonical rows
                         control: 'a row present in the CSV is absent from the rendered view'    (new)
  split_header           the human header is preserved across a rewrite
                         control: 'the current header is dropped on rewrite'                     (new)
```

Five mutants, one per named helper, each asserting its own named control fails.

**Files changed:** `tools/claim-matrix-gate.py`, `tools/closure-ledger-view.py`,
`tools/gate-mutation-test.py`.

**Baseline:** 2 claim-gate mutants, 0 closure-ledger controls, 0 closure-ledger mutants.
**Acceptance:** `closure-ledger-view.py --self-test` exists and runs first in `make fcb`, as every other
document gate already does; the mutant total rises by five, each proved load-bearing by name; `make fcb`
green.

---

## Wave 4 — the cold path

Baseline **`make check` cold = 270 020 ms (A)**, of which `prove` 133 980 — and inside that,
`gate/Assumptions.v` ≈77 000 ms and the sealed self-tests ≈33 000 ms (`.review/M3_AUDIT.md` §3.1).

### M4-13 — hoist the sealed self-tests' recomputed precondition

**Root cause** (§3.1 result 2): `Dockerfile:sealed()` runs two `rocq c` invocations per call. Stage 1
compiles `SEALED_PRELUDE + Definition sentinel := <sentinel>.` and must succeed. There are 25 sealed calls
but only **four** distinct `(prelude, sentinel)` pairs, so stage 1 is recomputed 21 times.

**Exact change:** in the `prover` stage's heredoc, compile stage 1 once per distinct `(prelude, sentinel)`
pair before the sealed calls, record each result, and have `sealed()` assert against the recorded result for
its own pair instead of recompiling.

**Files changed:** `Dockerfile`, inside the `prover` stage's heredoc only. No stage, COPY set or cache key
changes.

**Why no control weakens:** stage 1 asserts "the module under test loaded and its public sentinel resolved",
a property of `(prelude, sentinel)` alone — the probe is not in the compiled file. Each sealed call still
requires that fact before its stage-2 rejection counts.

**The failure mode to test first:** the two `meta_reject` controls deliberately pass a *different*
`SEALED_PRELUDE`, so they must resolve to their own stage-1 result and never to a hoisted one. The keying is
therefore on the `(prelude, sentinel)` pair, not the sentinel alone. If those two controls can be made to
pass by accident, the hoist is wrong.

**Baseline:** 25 sealed calls at 1.10 s each; 33.1 s and 32.0 s across two runs; ≈0.55 s per `rocq c`.
**Acceptance:** all 25 sealed labels printed, all 3 meta-controls rejecting for their exact stated reasons,
all 3 mint controls unchanged; **target: the sealed block under 20 000 ms**, measured with
`make prover-log FIDO_PERF_COLD=1`.

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
it is not counted among the nine.**

### Deleted from an earlier draft of this plan, under D-30

```text
one container start per source view   restructures the Makefile and the hook to recover a floor that
                                      shrinks anyway once M4-01/02/03 land        (M3-NO-HOST-PYTHON-COST)
one enumeration owner                 the five Python gates differ in SELECTION, not just traversal —
                                      102, 113 and 111 files at the same ref       (M3-SOURCE-ENUMERATION)
narrow the PYTAG cache key            needs a fail-closed Dockerfile-stage parser in both the Makefile and
                                      the hook, and inverts the risk to a stale image  (M3-INVALIDATION)
host-shell portability and modes      the host boundary is as declared; no current requirement asks for
                                      BSD portability or a tidier mode bit      (M3-HOST-CONTAINER-OTHER)
a generic tool-prose path checker     a weak path scanner to catch two strings M4-07 deletes  (M3-FRAGILE-PROSE)
```

Each is recorded as measured evidence in the audit with a `KEEP` disposition. None is a deferred promise.

---

## 6. Post-M4 execution graph

Unchanged in shape: the same nine completion markers, the same full-acceptance join, the same partial
targets, the same Docker DAG, the same six caches, the same two source views and two entry points. **No
Makefile recipe, no hook line, no Docker stage, no cache key and no Dune file changes.** What changes:

```text
make check   names  22.3 s              ->  target < 5 s              (M4-01)
             fcb    28.6 s              ->  target < 10 s             (M4-02, M4-03)
prover       sealed block 33 s          ->  target < 20 s             (M4-13)
             gate/Assumptions.v 77 s    ->  unchanged; needs a decision (M4-11, unauthorized)
tools        the M1 replay path, 25 dormant mutants, 2 stale strings  ->  deleted
Compilable.v 48 consumer-free declarations                            ->  deleted
gate         540 Print Assumptions / 535 distinct -> 539 / 539, four missing twins added
coverage     claim-matrix +3 mutants, closure-ledger gains controls and +2 mutants
```

No target is removed, no gate is removed, no source view is collapsed, and no partial result is presented as
full acceptance.

## 7. Step order

```text
Wave 1   M4-06  M4-07  M4-08  M4-14      deletions and corrections; no performance claim
Wave 2   M4-01  M4-03  M4-02             hot path; M4-03 strictly before M4-02
Wave 3   M4-09                           coverage
Wave 4   M4-13                           cold path
```

`make perf` runs once at the end of Waves 2 and 4. The §0 verification runs after **every** step.
