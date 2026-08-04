# M4 — Mechanical Refactor Plan

status: proposed — M4 is FORBIDDEN until Rob accepts M3 and separately approves this exact plan
(`M4-PLAN-APPROVAL`)

Produced by M3 under `.review/M3_TOOL_AND_BUILD_ARCHITECTURE_AUDIT.md`, activation
`0b7fd86825936c37f31ef83879574d526d548122`. Evidence: `.review/M3_AUDIT.md`.

**M3 recorded the baselines below. M3 implemented no step and produced no after value.** Every "after" here
is an **acceptance criterion M4 must meet**, never an observation. Where a step names a target, it is a
target.

---

## 0. How every step is measured

One procedure, used by every step, so the numbers stay comparable:

```text
BASELINE (already recorded by M3; do not re-derive):  .review/M3_AUDIT.md §1.1 and §3.1
AFTER, configuration A (the accepted serial diagnostic):
    make perf                            # rewrites .review/PERFORMANCE.tsv; `git diff` is the comparison
AFTER, configuration B (one target in isolation, host idle, builder fido-builder):
    make <target>                        # wall time; name the target and state the host was idle
AFTER, cold prover internals:
    make prover-log FIDO_PERF_COLD=1     # read the --progress=plain timestamps
```

`make perf` runs **once at the end of a wave**, never per step. Configuration A and configuration B numbers
are never pooled or compared with each other.

**Correctness acceptance is identical for every step and is not negotiable per step:**

```text
make check      green
make fcb        green      (every remaining mutant still proved load-bearing, by name)
make claims     green
make names      green
make diet       green
make hostpython green
make fmt        green
the real pre-commit hook over the exact staged snapshot, without --no-verify
git diff <wave baseline> -- '*.v' plugin/ e2e/ go.mod '**/*.go'     EMPTY, except M4-08
```

`M4-08` is the only step that touches a `.v` file, and it touches `gate/Assumptions.v` alone.

**Rollback boundary, every step:** one commit per step. A step that fails any gate is reverted with
`git revert` of that single commit; no step depends on an uncommitted predecessor. Waves are ordered so that
reverting a later step never invalidates an earlier one.

---

## Wave 1 — deletions and corrections

No performance claim. These remove dead surface and repair drifted prose, so later waves edit less.

### M4-06 — delete the dead M1 replay path

**Root cause** (`M3-SOURCE-DIET-REPLAY`): seven CLI modes in `tools/source-diet.py` are invoked by no
Makefile recipe and no hook line, reference six repository paths that no longer exist, and are guarded by 25
mutants that `mutant_mode` routes to `--m1-self-test` — which nothing invokes.

**Files changed**

```text
tools/source-diet.py         remove M1_ONLY_MODES (:1165) and every mode it names —
                             --against-baseline --disposition-exact --code-identical
                             --verify-m1-evidence --write-metrics-table --write-disposition
                             --m1-self-test — the six dead path constants (:41-44, :50) and the code
                             reachable only from those modes (verify_m1_evidence:997,
                             m1_self_test:1523, m1_topology_repo:2108)
tools/gate-mutation-test.py  remove the 25 --m1-self-test mutants and the mutant_mode indirection;
                             MUTANTS becomes one list in which every entry is selected
.review/M_SERIES_PLAN.md     if it names a deleted mode, restate what survives
```

**Authority removed:** none. The permanent `.v` comment law, the exception relation and `--wiring` are
untouched — they are what `make diet` and the hook actually invoke.

**Deletions made legal by:** Rob's M1 acceptance, `M1-ACCEPT-6524b43`. M1's exit evidence was consumed at
its review and the ledgers these modes read were deleted then. Git owns them.

**Source-view / cache-key consequences:** none.

**Invariants preserved:** `make diet`'s three invocations and the hook's three keep their exact behaviour
and messages; every remaining mutant is still load-bearing.

**Baseline:** `tools/source-diet.py` 2 294 lines; `tools/gate-mutation-test.py` 67 entries, 42 selected.
**Acceptance:** both files smaller; `make diet` output byte-identical; `make fcb` reports every remaining
mutant load-bearing; no `M1_` path constant remains that does not resolve.

### M4-07 — stop hand-maintaining subjects; make a tool's own prose checkable

**Root cause** (`M3-CLAIM-SUBJECT`, `M3-NAMING-EXCLUSION`, `M3-FRAGILE-PROSE` class 1): the claim gate's
subject is a hand-edited constant whose docstring has already drifted to a deleted path, and the naming gate
carries an exclusion for a file that is not in the tree.

**Files changed**

```text
tools/claim-matrix-gate.py  derive the matrix path from the active review state instead of the
                            hand-edited TSV_REL — or, if that couples the gate to a document it should
                            not read, keep the constant and delete the duplicated path from the
                            docstring (:20) so exactly one place names it
tools/naming-gate.py        delete '.review/C4_IMPLEMENTATION_REPAIR_21.md' from EXCLUDED_FILES (:42)
tools/host-python-gate.py   NEW rule: every '.review/…' or 'tools/…' path a tracked tool NAMES must
                            resolve in the tree under test — the tools' analogue of D-24, added to the
                            gate that already enumerates and reads every tool file
```

**Where the new rule goes matters.** It is one predicate in a gate that already reads every tool; it is not a
new gate, tool, registry or schema. If review judges it a new authority, the fallback inside this step is to
delete the stale strings only and record the class in `PAINFUL_LESSONS.md`. Stated here so the step cannot
silently grow.

**Invariants preserved:** the A005 policy, the claim-matrix relation and the no-host-Python boundary keep
their current meaning. The deleted exclusion excluded nothing, so no file changes classification.

**New controls required:** one must-fail control for the new rule, one must-accept twin, and one mutant
proving it load-bearing.

**Baseline:** 1 dangling tool-prose path in `claim-matrix-gate.py`, 6 in `source-diet.py` (removed by
`M4-06`), 1 dangling exclusion in `naming-gate.py`.
**Acceptance:** zero dangling tool-named paths; the new rule fails on an injected dangling path and passes
once it is removed.

### M4-08 — repair the readable assumption surface

**Root cause** (`M3-ASSUMPTION-DUPLICATES`, `M3-ASSUMPTION-SURFACES`): `gate/Assumptions.v` has 540
`Print Assumptions` lines for 535 distinct surfaces, and four Complex real/imaginary pairs are gated on the
real half only.

**Files changed**

```text
gate/Assumptions.v   delete the 5 duplicate lines —
                       Compilable.capability_is_compile_outcome
                       Compilable.capability_source
                       Compilable.forest_count_source
                       Compilable.member_at_in_forest
                       Compilable.occurrence_expr_diags_conv_sound
                     add the 4 missing imaginary twins —
                       Complex.typed_runtime_imaginary_coherent
                       Complex.typed_runtime_imaginary_not_inf
                       Complex.typed_runtime_imaginary_not_nan
                       Complex.typed_runtime_imaginary_not_neg_zero
```

**This is the only step that edits a `.v` file, and it edits the gate module, never a certified one.**
`dune`'s `(modules …)` does not include `gate/`, and the certified-module coverage check compares tracked
**root** `.v` against that list, so the theory is untouched and no `Fido` `.vo` changes.

**Invariants preserved:** the `prover` stage's fail-closed pair — zero `^Axioms:` **and** `want == got` —
holds by construction: 540 − 5 + 4 = 539 declared, each of which must print `Closed under the global
context`. The whole-theory `Fido Audit Assumptions` is unchanged and remains the authority for zero
assumptions.

**Baseline:** 540 declared / 535 distinct; the stage prints "540/540 surfaces closed".
**Acceptance:** 539 declared / 539 distinct; the stage prints "539/539"; `make prove` green; each of the four
new surfaces reports closed.

### M4-12 — host-shell portability and mode honesty

**Root cause** (`M3-HOST-CONTAINER-OTHER`, audit §4.1): `Makefile:212` and `Makefile:221` use GNU-only
`find … -printf '%P\n'`; three `tools/*.sh` are `100755` and three are `100644` although all six are invoked
as `sh tools/<name>.sh`, so the bit decides nothing while reading as though it does.

**Files changed**

```text
Makefile                 replace `find . -type f -printf '%P\n'` with a POSIX construct, in fcb-write
tools/*.sh (six files)   one consistent Git mode
```

**Invariants preserved:** `fcb-write`'s publication ordering is untouched — both writers still complete into
an isolated directory, the complete output set is still validated there, and only then is any byte published
through `cat >` (which writes through the existing inode and preserves ownership and mode). Only the path
enumeration inside that loop changes.

**Baseline:** `make fcb-write` publishes 2 validated views. **Acceptance:** identical message, identical
published bytes, and the recipe runs where `find` has no `-printf`.

---

## Wave 2 — the hot path

This wave is what shortens ordinary feedback. Baseline **`make check` hot = 63 680 ms (A)**, of which
`names` 22 310 and `fcb` 28 580.

### M4-01 — compile the naming gate's patterns once

**Root cause** (`M3-PERF-NAMES`): `tools/naming-gate.py:336` (and `:290`, `:342`) build a pattern **string**
per line per retired name, so a 170-name table over ~53 000 lines makes 9 003 383 `re.escape` and
9 790 568 `re.search` calls.

**Change:** build the 170 + 20 patterns **once** at module import into a compiled table and search with the
compiled objects inside the loop. The loop, its order, its per-name messages and its results are unchanged.

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

**Explicitly NOT proposed:** collapsing the 170 patterns into one alternation. It is faster still, but where
one retired name is a substring of another the loop reports **both** and an alternation reports only the
first alternative matching at a position. That is a behaviour change and would need its own equivalence
argument. The exact-preserving change is the whole of this step.

**Files changed:** `tools/naming-gate.py` only. **Authority removed:** none. **Cache-key consequences:** none
— `PYTAG` does not cover `tools/`.

**Invariants preserved:** identical violation set, identical messages, identical exit status, identical
`N files examined`; all 72 controls pass unchanged. The gate's own self-test is the differential.

**Baseline:** `names` 22 310 ms (A hot) / 22 490 ms (B, host idle); 9 003 383 `re.escape` calls.
**Acceptance:** under 1 000 `re.escape` calls under the same cProfile procedure recorded in
`M3_AUDIT.md` `M3-PERF-NAMES`; `make names` (B, host idle) **target under 5 000 ms**; zero change in reported
violations on the current tree or on the gate's fixtures.

### M4-03 — stop copying the tree once per control

**Root cause** (`M3-MUTATION-ARCHITECTURE`): `tools/fcb-reference-gate.py:584 scenario` does a full
`shutil.copytree` for each of its 64 controls, and the mutation harness runs that whole self-test 11 more
times — ~704 tree copies from that one gate per `make fcb`.

**Change:** build **one** pristine working copy per self-test run and restore only what a control mutated (or
copy-on-write the single file it edits). Every control keeps its own isolated view; what is removed is
re-copying 163 unchanged files 64 times.

**Files changed:** `tools/fcb-reference-gate.py`, which carries 704 of the ≈815 full tree copies. The same
shape exists at smaller scale in `tools/human-review-index.py` (48) and `tools/claim-matrix-gate.py` (21) and
is part of this step. `tools/source-diet.py`, `tools/host-python-gate.py` and `tools/naming-gate.py` build
small fixtures rather than copying, and are **not** touched by this step.

**Invariants preserved:** each control still runs against a tree containing exactly its own mutation and
nothing else. That isolation *is* the evidence. Any restore-based design must be proved by a control that
mutates, restores, and then asserts the **next** control sees a clean tree — without that, this step is not
done.

**Baseline:** `fcb-reference-gate.py --self-test` 3 680 ms (B, host idle), 64 controls.
**Acceptance:** same 64 controls with the same per-control pass/fail; **target under 1 500 ms**; plus the new
cross-control isolation control.

### M4-02 — run each mutant against the controls it names

**Root cause** (`M3-PERF-FCB`, `M3-MUTATION-ARCHITECTURE`): `run_mutant` runs each gate's **entire**
self-test while `main` only ever asserts that the mutant's own `expected` controls fired — 42 mutants ×
whole self-tests ≈ 1 990 nested control executions, 22 400 ms, 78% of `fcb`.

**Change, in dependency order:**

1. Land `M4-03` first, so the per-control copy cost is already down and this measurement is clean.
2. Give each gate's self-test an exact `--only <control-label>` selection, and have `run_mutant` pass the
   mutant's `expected` labels.
3. Keep the `returncode != 0` assertion **and** the `missing` assertion exactly as they stand.

**Why the evidence does not weaken.** The current assertion is: the self-test fails, and every label in
`expected` is among the failures. Running only the `expected` controls preserves both halves — a mutant
whose named controls still pass still fails the step. What is lost is incidental and was never asserted:
noticing that a mutation *also* broke unrelated controls.

**If review judges that loss unacceptable**, the fallback inside this step is to keep whole self-tests and
take the win from `M4-03` alone. Stated here so the step cannot quietly trade evidence for speed.

**Files changed:** `tools/gate-mutation-test.py`, plus one `--only` argument in each gate that has mutants.

**Baseline:** `gate-mutation-test` 22 400 ms (B, host idle), 42 mutants.
**Acceptance:** 42 mutants, each still reported load-bearing by name; **target under 6 000 ms**; and a
control proving `--only` fails closed when it selects nothing — selecting zero controls must never pass.

### M4-10 — key the Python tooling image on what defines it

**Root cause** (`M3-INVALIDATION`): `Makefile:20` keys `PYTAG` on the whole Dockerfile. Demonstrated — one
comment edit ~776 lines from the stage flips `6e65f59ae32bd774` → `b5562f3bf16ae2a8` and forces a full
`--load` rebuild. The hook computes the same tag the same way, so the cost is paid twice.

**Change:** key the tag on the `python-tools` stage's own definition plus the lock. The extraction must be
**exact and fail-closed**: if the stage delimiters are not found, the recipe fails, rather than hashing
nothing or silently hashing everything.

**Files changed:** `Makefile` and `.githooks/pre-commit`. **They must change together and identically** — the
hook computing a different tag than `make check` would mean the two entry points judge with different
images, which is precisely what the content-addressed tag exists to prevent.

**Cache-key consequence, stated plainly:** this **narrows** a cache key, so the risk inverts. A change that
genuinely affects the Python image but lands outside the extracted region would no longer rebuild it. This
step therefore requires a control that an edit **inside** the stage changes the tag and an edit **outside**
it does not, plus a review check that nothing outside the extracted region can affect that image. **If that
cannot be shown, drop this step** — a stale tooling image is worse than a slow one.

**Baseline:** any Dockerfile edit rebuilds `python-tools`; `make pytools` 170–210 ms on a tag hit.
**Acceptance:** an edit to the `go-e2e` stage leaves `PYTAG` unchanged; an edit inside `python-tools` changes
it; `make check` and the hook compute the same tag for the same tree.

---

## Wave 3 — structure

### M4-05 — one enumeration owner for the Python gates

**Root cause** (`M3-SOURCE-ENUMERATION`): five Python components each re-derive the tracked-file set with
different primitives (`git ls-files` plus `os.walk` / `rglob` / `scandir` / `iterdir`), each having to get
fail-closed behaviour right independently, while `Makefile:59` names `tools/worktree-list.py` as the owner of
the inventory — which it is, for the tar export only.

**Change:** make `tools/worktree-list.py` the single enumeration owner for the Python gates in both
working-tree and snapshot mode, and have the gates consume it.

**Explicitly retained as distinct:** `tools/generated-mode-gate.sh` reads `git ls-files -s` from the **real
index** to see file *modes*, which an exported tree cannot show — a different question, not a duplicate
answer, and merging it would destroy the check. `tools/staged-generated-compare.sh` is shell and keeps its
own enumeration for the same reason.

**Invariants preserved:** every gate's current *selection* — which files it judges — must be unchanged. This
changes who enumerates, never what is examined.

**Baseline:** 5 independent Python enumerations; `naming-gate` reports 100 files examined,
`fcb-reference-gate` 111, `source-diet` 111.
**Acceptance:** identical per-gate counts and identical judgements; every gate's fail-closed enumeration
control still passes; one owner; `worktree-list.py`'s own controls extended to cover snapshot mode.

### M4-04 — one container start per source view

**Root cause** (`M3-NO-HOST-PYTHON-COST`, `M3-ACCEPTANCE-DUPLICATION`): `make check` starts the pinned
Python container 16 times and the hook 14, at roughly 0.6–0.7 s each — about 10 s of the 63.7 s hot run — for
what is one read-only mount of one tree by one image.

**Change:** one container start per source view, running the gate sequence inside it. The boundary is
unchanged and is the point: **project Python still never runs on the host.** What changes is that it starts
once rather than once per gate.

**Files changed:** `Makefile` (the `hostpython`, `names`, `fcb`, `claims`, `diet` recipes and `check`) and
`.githooks/pre-commit`.

**What must not change, and must be shown not to have changed:**

- every gate keeps a separately invocable public target (`make names`, `make fcb`, …), so partial feedback
  stays partial feedback and `M3-ACCEPTANCE-DUPLICATION`'s distinction is preserved;
- the hook still runs the **staged** copy of every gate against the **exported index**;
- a failure in gate *k* still fails the run with that gate's own message, never a batched summary;
- the `$(call fido_mark,…)` completion markers stay exactly where they are, so `make perf` keeps measuring
  the same nine completions and the record stays comparable across M4.

**Ordering:** last of the mechanical steps, because it touches the recipes every earlier step measures
through.

**Baseline:** 16 container starts (`make check`), 14 (hook); ≈10 s of the hot run.
**Acceptance:** at most 3 container starts per source view; every gate's message and exit status unchanged;
`make perf` (A) at the end of the wave; the real hook green over a staged snapshot.

---

## Wave 4 — the cold path

Baseline **`make check` cold = 270 020 ms (A)**, of which `prove` 133 980 — and inside that,
`gate/Assumptions.v` ≈77 000 and the sealed self-tests ≈33 000 (`M3_AUDIT.md` §3.1).

### M4-13 — hoist the sealed self-tests' recomputed precondition

**Root cause** (§3.1 result 2): `Dockerfile:156 sealed()` runs two `rocq c` invocations per call. Stage 1
compiles `SEALED_PRELUDE + Definition sentinel := <sentinel>.` and must succeed. There are 25 sealed calls
but only **four** distinct `(prelude, sentinel)` pairs, so stage 1 is recomputed 21 times.

**Change:** compile stage 1 once per distinct pair, before the sealed calls, and have each call assert
against that recorded result rather than recompiling it.

**Files changed:** `Dockerfile`, inside the `prover` stage's heredoc only.

**Why no control weakens:** stage 1 asserts "the module under test loaded and its public sentinel resolved",
which is a property of `(prelude, sentinel)` alone — the probe is not in the compiled file. Each sealed call
still requires that fact before its stage-2 rejection counts. **The failure mode to test first:** the two
`meta_reject` controls deliberately pass a *different* `SEALED_PRELUDE`, so they must resolve to their own
stage-1 result and never to the hoisted one. If they can be made to pass by accident, the hoist is wrong.

**Cache-key consequence:** editing the Dockerfile invalidates `prover` — and today also `PYTAG`, which is why
`M4-10` lands first.

**Baseline:** 25 sealed calls at 1.10 s each; ≈33.1 s and ≈32.0 s across two runs; ≈0.55 s per `rocq c`.
**Acceptance:** all 25 sealed labels still printed, all 3 meta-controls still rejecting for their exact
stated reasons, all 3 mint controls unchanged; **target: the sealed block under 20 000 ms**, measured with
`make prover-log FIDO_PERF_COLD=1`.

### M4-11 — the readable Print-Assumptions gate's 77 s — NOT AUTHORIZED BY THIS PLAN

**Root cause** (§3.1 result 1): `rocq c gate/Assumptions.v` costs ≈77 s — 59% of the cold `prover` stage and
29% of the whole 270 s cold `make check` — while the strictly stronger whole-theory `Fido Audit Assumptions`
costs 1.72 s. 540 `Print Assumptions` commands each re-walk one constant's closure with no sharing.

**Written down and deliberately not planned as mechanical work.** Reducing a readable proof surface changes
what a human can check by eye, and `CLAUDE.md` makes the axiom-free surfaces a standing public claim. M4 is a
*mechanical* refactor; this is not mechanical.

Recorded in `.review/OPEN_QUESTIONS.md` for Rob, with the options and the default if nobody answers.

**No M4 step proceeds from this finding without an explicit decision.**

---

## 5. Post-M4 execution graph

Unchanged in shape: the same nine completion markers, the same full-acceptance join, the same partial
targets, the same Docker DAG, the same six caches, the same two source views and two entry points. What
changes:

```text
make check   16 container starts       ->  <=3 per source view          (M4-04)
             names  22.3 s             ->  target < 5 s                 (M4-01)
             fcb    28.6 s             ->  target < 10 s                (M4-02, M4-03)
             PYTAG keyed on 1245 Dockerfile lines -> on the stage that defines it   (M4-10)
prover       sealed block 33 s         ->  target < 20 s                (M4-13)
             gate/Assumptions.v 77 s   ->  unchanged; needs a decision  (M4-11)
tools        the M1 replay path, 25 dormant mutants, 7 dangling paths, 1 dead exclusion -> deleted
```

No target is removed, no gate is removed, no source view is collapsed, no partial result is presented as full
acceptance, and no proof, artifact or generated byte changes.

## 6. Step order

```text
Wave 1   M4-06  M4-07  M4-08  M4-12       deletions and corrections; no performance claim
Wave 2   M4-01  M4-03  M4-02  M4-10       hot path; M4-03 strictly before M4-02
Wave 3   M4-05  M4-04                     structure; M4-04 last of the mechanical steps
Wave 4   M4-13                            cold path
         M4-11                            BLOCKED pending Rob's decision
```

`make perf` runs once at the end of Waves 2, 3 and 4. The full correctness set in §0 runs after **every**
step.
