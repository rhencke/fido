# M3 — Tool and Build Architecture Audit — findings

status: complete

Contract: `.review/M3_TOOL_AND_BUILD_ARCHITECTURE_AUDIT.md`, activation
`0b7fd86825936c37f31ef83879574d526d548122`. Accepted basis: `.review/REVIEW_BASIS.md`.

This is one temporary table, not a registry. The Makefile, hook, Dockerfile, Dune files and tools remain the
authorities for what executes. M3 changes none of them.

---

# 1. Measured configurations

Four configurations, never pooled. Every measured fact below names the one that produced it.

```text
A  serial diagnostic       make -j1 check, builder fido-perf-v1, BuildKit max-parallelism=1
                           source: .review/PERFORMANCE.tsv at 9814db7 (the accepted M2 record)
B  ordinary working tree   make <target>, builder fido-builder, default make parallelism, this host
C  staged acceptance       .githooks/pre-commit over the exported Git index
D  partial feedback        one named public target run alone (a subset of B)
```

A and B answer different questions and their numbers are not interchangeable. A B measurement taken while a
background build held CPU is marked **(contended)** and is an upper bound only.

## 1.1 Configuration A — the accepted serial baseline

Adjacent-row deltas of `.review/PERFORMANCE.tsv` (the record stores cumulative completions; a reader
subtracts adjacent rows).

| phase | cold ms | hot ms |
|---|---:|---:|
| pytools | 180 | 210 |
| hostpython | 2 950 | 2 920 |
| names | 22 210 | 22 310 |
| fcb | 28 150 | 28 580 |
| claims | 1 690 | 1 720 |
| diet | 2 300 | 2 690 |
| prove | 133 980 | 1 410 |
| e2e | 45 170 | 1 340 |
| check body | 33 390 | 2 500 |
| **total** | **270 020** | **63 680** |

**The dominant hot cost is not the proof.** On the hot path `names` (22.3 s) + `fcb` (28.6 s) = **50.9 s of
63.7 s — 80%** — while `prove` and `e2e` are 1.4 s and 1.3 s because Buildx returns cached stages. Neither
`names` nor `fcb` reads a `.v`, a `.vo`, or any Docker layer.

Cold inverts the ranking: `prove` 134.0 s (50%) and `e2e` 45.2 s (17%) dominate; `names`+`fcb` are 19%.

Two different problems, then. Cold is a Rocq/Docker problem; hot is a Python problem; and hot is the
ordinary edit loop.

---

# 2. Current execution graph

## 2.1 Working-tree entry — `make check`

```text
make check : pytools hostpython names fcb claims diet prove e2e builder
  builder      docker buildx inspect|create fido-builder                    [no source view]
  pytools      docker image inspect $(PYTAG) -> buildx --target python-tools if absent
  hostpython   PYRUN host-python-gate.py --self-test                \  working tree, read-only mount
               PYRUN host-python-gate.py                            /
  names        PYRUN naming-gate.py          (runs its own controls first, then scans)
  fcb          PYRUN human-review-index.py --self-test
               PYRUN human-review-index.py --check
               PYRUN fcb-reference-gate.py --self-test
               PYRUN fcb-reference-gate.py
               PYRUN closure-ledger-view.py --check
               PYRUN gate-mutation-test.py
  claims       PYRUN claim-matrix-gate.py --self-test ; PYRUN claim-matrix-gate.py
  diet         PYRUN source-diet.py --self-test ; --check ; --wiring
  prove        buildx --target prover                             [source view: the Buildx context]
  e2e          buildx --target go-e2e
  check body   PYRUN worktree-list.py --self-test ; PYRUN worktree-list.py
               tar export of the listed working-tree paths -> $tree
               sh ocaml-origin-gate.sh $tree ; sh generated-output-gate.sh $tree
               buildx --target generated-artifact --output local=$pristine
               sh staged-generated-compare.sh $tree $pristine
```

**16 container starts** of the pinned Python image, plus 3 Buildx invocations.

## 2.2 Staged entry — `.githooks/pre-commit`

```text
git checkout-index --ignore-skip-worktree-bits --all --prefix=$ctx   (the index, exported ONCE)
PYTAG recomputed from the STAGED Dockerfile + lock; image built if that tag is absent
sh $ctx/tools/ocaml-origin-gate.sh $ctx
sh $ctx/tools/generated-output-gate.sh $ctx
sh $ctx/tools/generated-mode-gate.sh          (from the repo cwd: reads the real Git index)
PYRUN naming-gate.py --snapshot
PYRUN human-review-index.py --self-test ; --check
PYRUN fcb-reference-gate.py --self-test ; (check)
PYRUN closure-ledger-view.py --check
PYRUN gate-mutation-test.py
PYRUN claim-matrix-gate.py --self-test ; (check)
PYRUN source-diet.py --snapshot --self-test ; --snapshot --check ; --wiring
PYRUN host-python-gate.py --self-test ; (check)
buildx --target prover ; buildx --target go-e2e         (context = $ctx, the exported index)
buildx --target generated-artifact --output local=$tmp/pristine
sh $ctx/tools/staged-generated-compare.sh $ctx $tmp/pristine
```

**14 container starts**, plus 3 Buildx invocations.

**This is required different-view work, not duplication.** The hook judges the proposed commit with the
staged copy of every gate; `make check` judges the working tree with the working-tree copy. A staged bad
gate must be the version that runs. That distinction is load-bearing and M4 must not collapse it. What is
genuinely repeated over *one* source view is isolated in `M3-ACCEPTANCE-DUPLICATION`.

## 2.3 Docker DAG and persistent caches

```text
python:3.12-slim-bookworm@sha256:d50fb76…  ── python-tools     cache fido-apt-pytools  (locked)
ocaml/opam:debian-12-ocaml-5.3@sha256:bbaac5… ── rocq-builder  cache fido-apt-builder  (locked)
                                                               cache fido-opam         (locked)
debian:12-slim@sha256:60eac75…  ── rocq-base                   cache fido-apt-base     (locked)
     rocq-base ── prover    COPY dune-project dune, *.v, gate/, plugin/
     rocq-base ── profile   COPY (same four)                    ARG PROFILE_FILE
     rocq-base ── emit      COPY (same four) + e2e/
                            cache fido-dune-rocq-9.2.0-$arch  (locked; SHARED by all three)
                            cache fido-crossmnt-$arch         (private; emit only)
     profile ── profile-log (scratch)
     emit ── generated-module (scratch) ── generated-artifact (scratch)
     generated-module ─┐
     emit ─────────────┴── go-e2e  ← golang:1.23-alpine@sha256:383395b…  (go-base)
     emit + go-e2e:/fresh-build-ok + generated-module ── sync   [make regenerate; validate-before-publish]
```

Six persistent caches. `prover`, `profile` and `emit` share one `_build` cache with `sharing=locked`, so a
run that does `prove` then `e2e` serializes on that lock and `emit`'s `dune build` is a cache hit inside it
rather than a second compile.

`.dockerignore` excludes `/go.mod` and `**/*.go`, so the pristine `generated-module` layer cannot be
contaminated by the committed bytes. That exclusion is what makes the byte-compare mean anything.

**Always-run controls** (never cached, by design): every gate's `--self-test`, the `prover` stage's
assumption audit and self-tests A–E/F–AA, and the emit-stage provenance rejections. These are the
adversarial half of the evidence and M4 must keep them always-run.

---

# 3. Findings

Twenty mandatory stable IDs, each ending in exact M4 step IDs or an evidence-backed
`KEEP / no M4 change`.

## M3-PERF-NAMES — `names` on the accepted hot path

**22.3 s (A, hot) / 22.49 s (B, host idle).** One container, one process, 100 files.

Root cause, from a one-off cProfile run inside the pinned image — the same container entry the Makefile
uses, with the gate loaded under the profiler. Nothing tracked, nothing added to any recipe:

```text
docker run --rm -u $(id -u):$(id -g) -e PYTHONDONTWRITEBYTECODE=1 -e HOME=/tmp -w /repo -v "$PWD":/repo:ro "$PYTAG" python3 -c '<cProfile wrapper around runpy.run_path("tools/naming-gate.py")>'
```

```text
72 482 119 function calls in 35.938 s (profiled; 22.5 s unprofiled)
  check_prose            166 calls   23.942 s cumulative
  re.search          9 790 568 calls  17.756 s
  re.escape          9 003 383 calls  12.194 s   (8.911 s of it in str.translate)
```

`tools/naming-gate.py:336` (and `:290`, `:342`) build a **new pattern string per line per retired name**:

```python
if re.search(r"(?<![\w.'/-])" + re.escape(old) + r"(?![\w'])", line):
```

The tables hold 170 retired names (`OLD_MODULES` 18 + `OLD_NAMES` 78 + `OLD_FILES` 5 +
`DELETED_SURFACES` 69) plus 20 `RETIRED_COMPOUNDS`. 170 names × ~53 000 scanned lines = the 9.0 M calls.
Every one of those patterns is a **constant**. `re`'s internal cache holds 512 entries and is thrashed, so
each call re-escapes and re-looks-up.

Disposition: **SIMPLIFY** → `M4-01`.

## M3-PERF-FCB — `fcb`, including the mutation harness

**28.6 s (A, hot).** Per-line timestamps of `make fcb` (B, host idle) attribute it:

| sub-invocation | ms |
|---|---:|
| human-review-index `--self-test` | (start) |
| human-review-index `--check` | 580 |
| fcb-reference-gate `--self-test` | 3 680 |
| fcb-reference-gate (check) | 1 590 |
| closure-ledger-view `--check` | 2 080 |
| **gate-mutation-test** | **22 400** |

`gate-mutation-test` is **78% of `fcb`** and **35% of the entire hot `make check`**.

Disposition: **SIMPLIFY** → `M4-02`, `M4-03`. Root cause under `M3-MUTATION-ARCHITECTURE`.

## M3-MUTATION-ARCHITECTURE — copying, isolation, control selection, parallelism, cost

The harness nests two control layers, and the product is the cost.

`tools/gate-mutation-test.py:434 run_mutant` — per mutant: a full `shutil.copytree` of the tree, then a
subprocess running that gate's **entire** `--self-test`. `main` runs them on
`ThreadPoolExecutor(max_workers=min(len(selected), os.cpu_count()))` — 4 here.

**Three** of the gates then copy the tree *again*, per control — the others build small fixtures instead, and
the difference is where M4 should aim:

```text
copies the whole tree per control   fcb-reference-gate.py:584 scenario   human-review-index.py   claim-matrix-gate.py
builds a small temp fixture         source-diet.py   host-python-gate.py   naming-gate.py
```

Selected mutants by tool (measured by importing the module in the pinned image):

```text
source-diet          16      × 53 controls  =  848
fcb-reference-gate   11      × 64 controls  =  704
host-python-gate      9      × 25 controls  =  225
naming-gate           2      × 72 controls  =  144
human-review-index    2      × 24 controls  =   48
claim-matrix-gate     1      × 21 controls  =   21
worktree-list         1
                     42 mutants           ≈ 1 990 nested control executions per `make fcb`
```

Of those, the ones that copy the whole tree are the 704 from `fcb-reference-gate`, the 48 from
`human-review-index` and the 21 from `claim-matrix-gate` — **≈773 full tree copies**, plus the 42 the harness
itself makes, so **≈815**. The other ~1 217 executions build small fixtures and are comparatively cheap.
The copy cost is therefore concentrated almost entirely in one gate, which is where `M4-03` aims.

**The nesting is not redundant evidence** — a mutant proves the rule is load-bearing, a control proves the
gate detects a defect — but the harness re-runs the *whole* self-test when it only ever asserts that the
mutant's own `expected` controls fired (`main`: `missing = [c for c in expected if …]`).

Disposition: **SIMPLIFY** → `M4-02`, `M4-03`.

## M3-SOURCE-DIET-REPLAY — dormant M1 replay modes

Not merely dormant — **broken, and guarded by mutants that never run.**

1. `tools/source-diet.py:1165 M1_ONLY_MODES` names seven CLI modes: `--against-baseline`,
   `--disposition-exact`, `--code-identical`, `--verify-m1-evidence`, `--write-metrics-table`,
   `--write-disposition`, `--m1-self-test`. **No Makefile recipe and no hook line invokes any of them**
   (`git grep -n 'source-diet' -- Makefile .githooks`).
2. Those modes reference six repository paths that **no longer exist**:

```text
.review/M1_BASELINE.tsv                source-diet.py:41
.review/M1_METRICS.tsv                 source-diet.py:42
.review/M1_FILE_DISPOSITION.tsv        source-diet.py:43, 1912, 1949
.review/M1_DECLARATION_DELETIONS.tsv   source-diet.py:44
.review/M1_OBLIGATION_MATRIX.tsv       source-diet.py:50, 1435
.review/M2_PERFORMANCE_SNAPSHOT.md     source-diet.py:1444
```

3. **25 of the 67 mutants** in `tools/gate-mutation-test.py` are `--m1-self-test` mutants (all
   `source-diet.py`). `mutant_mode` routes them there, and `--m1` is invoked nowhere, so they never run.

So the dead mode is protected by dead mutants, and the pair has been keeping each other alive.

Disposition: **DELETE** → `M4-06`.

## M3-CLAIM-SUBJECT — the manually retargeted active-checkpoint constant

The retarget has already drifted. `tools/claim-matrix-gate.py:44` reads
`TSV_REL = '.review/M3_OBLIGATION_MATRIX.tsv'`, while its own docstring at line 20 still says:

```text
Matrix: `.review/M2_OBLIGATION_MATRIX.tsv`.
```

`.review/M2_OBLIGATION_MATRIX.tsv` does not exist. No gate catches it: D-24 scans *authority documents*
and a tool is not one; the naming gate scans retired *names*, not retired *paths*.

Disposition: **SIMPLIFY** → `M4-07` (make the subject follow the review state instead of a hand-edited
constant, and give the tools the same not-a-dangling-path check the authorities already have).

## M3-NAMING-EXCLUSION — the inert exclusion

`tools/naming-gate.py:42 EXCLUDED_FILES` holds three entries. One does not resolve:

```text
.review/fcb/amendments/                    EXISTS   (an amendment must quote the names it retires)
tools/naming-gate.py                       EXISTS   (spells every retired name by necessity)
.review/C4_IMPLEMENTATION_REPAIR_21.md     MISSING
```

An exclusion for a file that is not in the tree excludes nothing and hides the next file that takes that
name. Every retained exclusion must resolve.

Disposition: **DELETE** the third entry → `M4-07`.

## M3-ASSUMPTION-DUPLICATES — duplicate `Print Assumptions` in `gate/Assumptions.v`

540 `Print Assumptions` lines; **535 distinct**. Five exact duplicates:

```text
Compilable.capability_is_compile_outcome
Compilable.capability_source
Compilable.forest_count_source
Compilable.member_at_in_forest
Compilable.occurrence_expr_diags_conv_sound
```

The count check in the `prover` stage is `want=$(grep -c '^Print Assumptions')` versus
`got=$(grep -c '^Closed under the global context')`, and a duplicate raises both sides equally, so the gate
still passes — but its message says "540/540 surfaces closed" when 535 surfaces are closed.

Disposition: **DELETE** the five duplicate lines → `M4-08`.

## M3-ASSUMPTION-SURFACES — omitted Complex imaginary-component readable surfaces

`Complex.v` declares 11 `_real` and 11 `_imaginary` lemmas. The readable gate carries 16 Complex surfaces.
Four real/imaginary pairs are asymmetric — the real half is gated, the imaginary half is not:

```text
typed_runtime_real_coherent      gated  /  typed_runtime_imaginary_coherent      NOT
typed_runtime_real_not_inf       gated  /  typed_runtime_imaginary_not_inf       NOT
typed_runtime_real_not_nan       gated  /  typed_runtime_imaginary_not_nan       NOT
typed_runtime_real_not_neg_zero  gated  /  typed_runtime_imaginary_not_neg_zero  NOT
```

(`typed_runtime_real_shape` / `typed_runtime_imaginary_shape` are both gated, so the asymmetry is an
omission rather than a policy.) The whole-theory `Fido Audit Assumptions` already covers them; what is
missing is the *readable* surface a human checks.

Disposition: **KEEP the lemmas, add the four missing readable lines** → `M4-08`.

## M3-HOST-CONTAINER-OTHER — what the no-host-Python boundary does not settle

The boundary is exact about Python and silent about shell. Five shell gates execute **on the host**:

```text
Makefile:73   sh tools/ocaml-origin-gate.sh          make check
Makefile:74   sh tools/generated-output-gate.sh      make check
Makefile:77   sh tools/staged-generated-compare.sh   make check
Makefile:137  sh tools/regen-guard-test.sh           make regen-guard
Makefile:185  sh tools/perf.sh                       make perf
```

plus `ocaml-origin-gate.sh`, `generated-output-gate.sh` and `generated-mode-gate.sh` from the hook. Between
them they invoke host `git`, `find`, `sed`, `grep`, `diff`, `awk`, `tar`, `cmp` and `mktemp`, none pinned.

One concrete exposure, not hypothetical: the `fcb-write` recipe uses `find … -printf '%P\n'` twice
(`Makefile:212`, `Makefile:221`). `-printf` is GNU findutils only, so that recipe cannot run on a BSD or
busybox host.

This is a **declared-scope** question, not a defect: the project's declared host boundary is "shell, Make,
Git, Docker and Buildx", so host shell is inside the trusted base by design.

Disposition: **KEEP, no M4 change** — the boundary is as declared. Recorded so the exposure is stated
rather than assumed away; widening it is a scope decision for Rob, not an M4 refactor.

## M3-CLAIM-MUTATION — does the claim-matrix gate need mutation coverage?

**Yes, and `closure-ledger-view.py` needs it more.** Mutation coverage against top-level helper count:

| tool | top-level defs | selected mutants |
|---|---:|---:|
| source-diet.py | 67 | 16 (+25 that never run) |
| fcb-reference-gate.py | 59 | 11 |
| host-python-gate.py | 26 | 9 |
| claim-matrix-gate.py | 17 | **1** |
| naming-gate.py | 15 | 2 |
| human-review-index.py | 12 | 2 |
| closure-ledger-view.py | 6 | **0** |
| worktree-list.py | 5 | 1 |

`claim-matrix-gate.py` runs 21 of its own controls, but only one of its rules has been shown load-bearing.
`closure-ledger-view.py` has no mutant at all, and it publishes a generated FCB view.

**And while auditing it, its own self-test failed — on a defect a mutant would have caught.** M3 closed all
twelve obligations with `unsupported-boundary` implementation cells, because M3 implements nothing by
contract §1 and so declares no surface. `make claims` then reported:

```text
FAIL  a named implementation surface was renamed: could not construct the scenario
      (no closed row with a locatable declaration to rename)
```

The mechanism is exact:

```text
tools/claim-matrix-gate.py:468 rename_named_surface
  -> :470 ensure_closed_row(work)          guarantees only that SOME closed row exists
  -> :472 scans closed rows for a first implementation entry that is `path:symbol`
          AND whose file the rename regex at :486/:488 can match — `.v` declaration kinds,
          or Python `def`/`class`.  A Makefile target or a `.sh` function passes
          check_implementation but is not renameable, so it is skipped.
  -> :492 raise AssertionError('no closed row with a locatable declaration to rename')
```

`ensure_closed_row` at `:413` appends `SYNTHETIC_CLOSED` — which names `Compilable.v:deep_nested_compile_fixture`,
a real declaration — but **only if no closed row already serves**. Its own docstring says the flag exists
because "a documentation checkpoint legitimately has neither". The author saw this class and covered the
*builder* scenario with `require_builder`; the *rename* scenario has no equivalent, so the precondition it
establishes is weaker than the one it needs.

It has never fired before because some closed row always happened to name a Python `def`. At M2 that was
`M2-08 → tools/worktree-list.py:tracked_and_untracked`, and it only worked because that cell was reordered
during M2 Repair so the locatable entry came first. This is therefore the **second** time the defect has been
worked around in data.

M3 is the first checkpoint where no honest such entry exists, because M3 wrote no Rocq and no Python.

**This blocks M3's exit** (`M3-11`, `M3-12`, contract §11) and M3 may not repair it: contract §9 forbids
changing a project tool. Reported as an architectural conflict rather than worked around a third time.

Disposition: **KEEP the harness, extend coverage, and repair `ensure_closed_row`** → `M4-09`, and the
blocking conflict in `.review/OPEN_QUESTIONS.md` `Q-M3-02`.

## M3-SOURCE-ENUMERATION — every independent enumeration and its one right owner

Seven independent enumerations of the repository:

```text
tools/worktree-list.py          git ls-files --cached --others --exclude-standard   (declared owner)
tools/naming-gate.py            git ls-files … + iterdir + rglob
tools/fcb-reference-gate.py     git ls-files … + os.walk + rglob + scandir
tools/source-diet.py            git ls-files … + os.walk
tools/host-python-gate.py       git ls-files … + rglob
tools/generated-mode-gate.sh    git ls-files -s        (index-authoritative, deliberately distinct)
tools/staged-generated-compare.sh  git ls-files --cached --others --exclude-standard
```

`Makefile:59` names `tools/worktree-list.py` as the one that "owns the inventory" — but it owns it only for
the `make check` tar export. Six other components enumerate for themselves.

**Not all six are wrong.** `generated-mode-gate.sh` must read `git ls-files -s` from the real index to see
file *modes*, which an exported tree cannot show; that is a different question, not a duplicate answer. The
Python gates, however, each re-derive the same tracked-file set with different traversal primitives, and
each must independently get the fail-closed behaviour right.

Disposition: **MERGE** the Python-side enumeration behind one owner → `M4-05`; **KEEP**
`generated-mode-gate.sh` distinct with its reason recorded.

## M3-NO-HOST-PYTHON-COST — the deliberate cost of the accepted boundary

`make check` starts the pinned Python container **16 times**; the hook starts it **14 times**.

Floor cost per start, configuration B, host idle: `make pytools` (a bare `docker image inspect`) is 170 ms;
`make fmt` (that prerequisite plus exactly one container start plus a scan of 111 files) is 980 ms. Cross-
checking against configuration A — `claims` 1 720 ms for 2 starts, `diet` 2 690 ms for 3, `hostpython`
2 920 ms for 2 — puts container start plus interpreter start at roughly **0.6–0.7 s**.

So **≈10 s of the 63.7 s hot `make check` is container startup** — about 16%, paid 16 times for what is one
read-only mount of one tree by one image.

This is the *price of a boundary worth having*: project Python never touching the host is a permanent
accepted invariant and M4 must not weaken it. But the boundary requires Python to run **in the image**, not
to run **once per gate**.

Disposition: **MERGE** the per-gate invocations into one container start per source view → `M4-04`.

## M3-INVALIDATION — why ordinary edits rebuild more than the proof graph requires

`Makefile:20` keys the Python tooling image on the **whole** Dockerfile:

```make
PYTAG := fido-python-tools:$(shell cat Dockerfile tools/python-requirements.lock | sha256sum | cut -c1-16)
```

Only lines 23–27 of 1 245 define that image. Demonstrated (one-off, no tree modified — the edit was applied
to a pipe):

```text
current PYTAG suffix                                              6e65f59ae32bd774
after one comment edit in the go-e2e stage (~line 803)            b5562f3bf16ae2a8
```

A comment 776 lines away from the stage that defines it forces a full `--load` rebuild of the tooling
image. The pre-commit hook computes the same tag the same way, so the cost is paid twice.

Disposition: **SIMPLIFY** → `M4-10`.

## M3-BUILDX-CACHE — stage boundaries, COPY sets, cache mounts and false invalidation

Six persistent caches; the DAG is in §2.3. Two structural facts:

1. `prover`, `profile` and `emit` COPY the **same** four inputs (`dune-project dune`, `*.v`, `gate/`,
   `plugin/`), so BuildKit content-addresses those layers once and shares them. `emit` adds `e2e/` last, so
   an `e2e/` edit invalidates only `emit`, not `prover`. That ordering is correct and deliberate.
2. All three mount the **same** `fido-dune-rocq-9.2.0-$arch` `_build` cache with `sharing=locked`. So a
   theory compile is done once and reused across stages — but the stages also **serialize** on it, which is
   why parallel `make check` gains little on the Rocq half.

**A cache-mount is not a Docker layer.** `--no-cache-filter prover` re-runs the stage's `RUN` but leaves
`_build` populated, so even a "cold" `prove` does not recompile the theory from nothing. That is what
`.review/PERFORMANCE.tsv`'s cold column measures, and §1.1's cold numbers must be read that way.

Disposition: **KEEP the cache topology, no M4 change**; the COPY ordering and the shared `_build` are both
doing their job. The invalidation defect is `M3-INVALIDATION`, which is a Make-level key, not a Buildx one.

## M3-ACCEPTANCE-DUPLICATION — repeated work across `make check`, partial targets and the hook

Working-tree versus staged-index work is **not** duplication and is not counted here.

What is genuinely repeated over one source view:

1. **Every gate's `--self-test` is source-view independent.** The controls build their own fixtures in
   `tempfile.TemporaryDirectory()`; they do not read the tree under test. Running them in `make check` and
   again in the hook is therefore the *same computation twice*, not two views. Cost: the full self-test set
   is the dominant part of both `names` and `fcb`.
2. **`gate-mutation-test` re-runs those same self-tests 42 more times** (`M3-MUTATION-ARCHITECTURE`), inside
   the run that already ran each of them once.
3. `make check` runs `prove` and then `e2e`; `e2e`'s `emit` stage repeats `dune build @install @all`. This
   one is **already cheap** — the shared `_build` cache makes it a re-check, not a recompile.

Disposition: **SIMPLIFY** (1) and (2) → `M4-02`, `M4-03`, `M4-04`; **KEEP** (3).

## M3-DUNE-FANOUT — the real Dune/Rocq graph, critical path and rebuild set

Root `.v` modules, size and their `From Fido Require` edges:

```text
Decimal 116   FilePath 219   Integer 102   Float 477   Version 18   ModulePath 279   Names 214   (no Fido deps)
Complex 186      <- Float
Collections 178  <- FilePath
Syntax 282       <- Collections Complex FilePath Float Integer ModulePath Names Version
Index 3525       <- Collections FilePath Syntax
Typing 644       <- Complex Float Integer Syntax
Compilable 10156 <- Collections Complex FilePath Float Index Integer ModulePath Syntax Typing
Safe 343         <- Compilable Complex Float Integer Syntax Typing
Render 1458      <- Compilable Complex Decimal Float Integer ModulePath Safe Syntax Typing Version
Emit 279         <- Collections Compilable FilePath ModulePath Render Safe Syntax Version
```

**`Compilable.v` is 10 156 of ~18 500 lines — 55% of the theory — and every remaining module depends on
it.** Editing it rebuilds `Safe`, `Render`, `Emit` and re-runs every downstream gate.

But the compile itself is not the problem. `make profile FILE=Compilable.v` (configuration B):

```text
Compilable.v recompiled alone in 6.5 s (deps already built)
8962 sentences, 3.83 s of measured elaboration
slowest single sentence 0.239 s (the Stdlib Require), then 0.210 s (the Fido Require)
```

No lemma dominates; the cost is spread across 8 962 sentences. A module split would reduce the *rebuild
set* after an edit, not the total compile time, and it would be a change to certified source — outside
M4's mechanical remit and requiring its own contract.

Disposition: **KEEP, no M4 change.** The measured fan-out does not justify splitting a certified module;
`M3-EDIT-WEIGHT` below shows why the edit frequency does not either.

## M3-EDIT-WEIGHT — files edited, over separated named ranges

Three exact ranges, kept apart, because pooling them predicts neither kind of work.

**Range 1 — whole history to C4 acceptance, `.v` only: `git log 39ea7e3 -- '*.v'`, 1 829 commits.**
Top files, all deleted: `main.v` 369, `builtins.v` 297, `GoSem.v` 216.
Also deleted, next in rank: `GoCompile.v` 211, `GoPrint.v` 180.
This range describes an architecture that no longer exists and predicts nothing about the current tree.
Recorded so nobody reaches for it.

**Range 2 — the current module set: `git log 20c5ad5..39ea7e3`, 55 commits.** `20c5ad5` (2026-07-26) is the
commit that introduced the whole current module set. This is the only range that describes today's files:

```text
Compilable.v 22   gate/Assumptions.v 18   Emit.v 8   Safe.v 4   Render.v 3
e2e/Witness*.v 3 each   Typing/Syntax/Index/Float/Complex 2 each   the seven leaf modules 1 each
```

Relevance to M4: `Compilable.v` and `gate/Assumptions.v` are together 40 of 76 `.v` touches, so the cold
path — which is `Compilable`'s compile plus the assumptions gate — is exactly the path semantic work pays.

**Range 3 — the M-series: `git log 39ea7e3..HEAD`, 168 commits.**

```text
tools/build-observatory.py 101   tools/gate-mutation-test.py 86   .review/NEXT_STEPS.md 46
.review/REVIEW_REQUEST.md 40     .review/BUILD_OBSERVATORY_SUITE.json 29   Makefile 19
```

The top entry and three others are **files Rob withdrew and that no longer exist**. This range measures the
M2 culling, not future work. It must not be pooled with Range 2, and it is not evidence for any M4 decision
about the certified tree.

Disposition: **KEEP the ranges as recorded, no M4 change**; they are the input to
`M3-DUNE-FANOUT`'s KEEP and to `M4-01`/`M4-02`'s ordering.

## M3-COMPILABLE-SURFACES — ungated `Compilable.v` surfaces

`Compilable.v` declares 623 top-level `Theorem`/`Lemma`/`Corollary`. `gate/Assumptions.v` names 249 of them.

The 374 remainder are **not** unproved or unaudited: the whole-certified-theory `Fido Audit Assumptions`
seeds from every Fido constant, mutual inductive and surviving named assumption, so it covers all 623 plus
every internal definition. What the readable gate adds is a *human-readable* list, and it is a strict subset
by construction.

The finding asks whether each is "required guarantee, proof dependency, or dead". Answering that for 374
lemmas one at a time is exactly the per-theorem inventory §3 of the contract forbids. The auditable question
is the **rule**: which classes of surface belong in the readable gate.

Disposition: **KEEP, no M4 change to the lemma set.** The readable gate's *cost* is the real issue and it is
§3.1 below. No lemma is deleted on this evidence.

## M3-TOOL-COMPLEXITY — every retained tool under D-30

Per-file dispositions are the table in §4.1. The summary across all eighteen tracked tool files:

```text
KEEP      12   ocaml-origin / generated-output / generated-mode / staged-generated-compare /
               regen-guard / perf.sh, host-python-gate, human-review-index, closure-ledger-view,
               fmt-check, rocq-profile, python-requirements.lock
SIMPLIFY   5   naming-gate, gate-mutation-test, source-diet, fcb-reference-gate, claim-matrix-gate
MERGE      1   worktree-list  (into one enumeration owner)
DELETE     0   at file granularity
```

**No tool file is deleted, and that is a finding rather than a shrug.** Each of the eighteen owns a distinct
policy fact and is invoked by a live target or hook line. What is over-built is *inside* five of them —
`source-diet.py`'s dead M1 replay path, the mutation harness's re-run of whole self-tests, the naming
gate's per-line pattern construction, the reference gate's per-control tree copy, and the claim gate's
hand-maintained subject. Those are `M4-01` … `M4-07`.

Two observations that a current gate invocation does **not** by itself justify:

- `tools/source-diet.py` is 2 294 lines, the largest tool in the repository, and enforces one rule (the `.v`
  comment law). The rest is M1 exit-evidence machinery that no longer has ledgers to read
  (`M3-SOURCE-DIET-REPLAY`).
- `tools/gate-mutation-test.py` is invoked by two live lines, but 25 of its 67 entries are unreachable from
  either (`M3-SOURCE-DIET-REPLAY` item 3).

Disposition: as tabulated in §4.1 → `M4-01`, `M4-02`, `M4-03`, `M4-05`, `M4-06`, `M4-07`, `M4-09`, `M4-12`.

## M3-FRAGILE-PROSE — mutable counts, line-number identity, list-position identity

Three classes found, each with a live instance:

1. **A tool's prose naming a path that no longer exists** — `tools/claim-matrix-gate.py:20` and the six
   `source-diet.py` M1 ledger paths (`M3-CLAIM-SUBJECT`, `M3-SOURCE-DIET-REPLAY`). Nothing checks tool
   prose; D-24 checks authority documents only.
2. **A count in a gate's own success message that is not the quantity it claims** — the `prover` stage
   prints "540/540 surfaces closed" for 535 distinct surfaces (`M3-ASSUMPTION-DUPLICATES`).
3. **List-position identity** — none found in the current normative documents. The mandatory findings use
   stable IDs, the obligation matrix uses `M3-nn` keys, and the FCB registries are keyed TSVs. This class is
   already closed; recorded so its absence is stated rather than assumed.

Disposition: (1) **SIMPLIFY** → `M4-07`; (2) **DELETE** the duplicates → `M4-08`; (3) **KEEP, no M4
change**.

---

# 3.1 Cold-path decomposition — inside the `prover` stage

Not a mandatory stable ID; the forensic account the mandatory performance findings depend on. Two
independent runs of `make prover-log FIDO_PERF_COLD=1` (configuration B), reading `--progress=plain`
timestamps:

| step | run 1 s | run 2 s | share |
|---|---:|---:|---:|
| `dune build @install @all` (theory + plugin) | 16.4 | 16.4 | 13% |
| **`rocq c gate/Assumptions.v` — the readable gate** | **77.6** | **76.9** | **59%** |
| certified-module coverage (shell) | 0.01 | 0.01 | — |
| `Fido Audit Assumptions` — whole certified theory | 1.72 | 1.72 | 1% |
| assumption self-tests A–E | 2.23 | 2.11 | 2% |
| sealed F–AG + meta-controls + mint AB–AD + positive | 33.1 | 32.0 | 25% |
| **stage total** | **131.1** | **130.3** | |

Two results worth stating plainly.

**1. The readable Print-Assumptions gate costs 77 s; the strictly stronger whole-theory audit costs 1.7 s.**
`gate/Assumptions.v` issues 540 `Print Assumptions` commands, each re-walking one constant's assumption
closure with no sharing between them; `Fido Audit Assumptions` walks the whole theory once. The readable
gate's guarantee is a **subset** of the audit's — it covers 535 distinct declared surfaces, the audit covers
every constant, mutual inductive and surviving named assumption. 77 s is 59% of the cold prover stage and
**29% of the entire 270 s cold `make check`**.

That is a proof-gate architecture question, not a mechanical refactor. It is written up as `M4-11` with the
preservation argument stated, and flagged in `.review/OPEN_QUESTIONS.md` because deleting a readable proof
surface is Rob's call, not mine.

**2. The sealed-capability self-tests recompute their own precondition 25 times.**
`Dockerfile:156 sealed()` runs **two** `rocq c` invocations per call: stage 1 compiles
`SEALED_PRELUDE + Definition sentinel := <sentinel>.` and must succeed (proving the module loaded), then
stage 2 adds the hidden term and must fail. There are 25 sealed calls but only **four distinct
(prelude, sentinel) pairs**:

```text
Compilable.compile   F G H I J K L M N O P Q R S T U V W X   (19 calls)
Emit.Mint.issue      Y Z                                     ( 2 calls)
Emit.of_safe         AA                                      ( 1 call )
Safe.certify         AE AF AG                                ( 3 calls)
```

Measured 1.10 s per sealed call (F at 99.09 s → AG at 126.7 s), so ~0.55 s per `rocq c`, each loading the
whole theory. Stage 1 is a property of `(prelude, sentinel)` and nothing else — the probe cannot affect
whether the module loaded. Hoisting it to one run per distinct pair is 4 loads instead of 25, saving
~21 × 0.55 ≈ **11.6 s** with **no** control weakened: every sealed call still proves its own module loaded,
because the hoisted stage-1 result is exactly the fact it asserted.

**3. A cache-mount is not a Docker layer, and the accepted baseline's "cold" reflects that.**
`dune build` took 16.4 s in *both* runs, with the `fido-dune-rocq-9.2.0-$arch` `_build` cache warm
throughout. `--no-cache-filter prover` re-runs the stage's `RUN` but does not clear a cache mount. So the
270 s cold column of `.review/PERFORMANCE.tsv` is **project-stage cold with the theory's `_build`
warm** — it is a faithful measure of "I edited a `.v` and re-ran acceptance", which is the loop that
matters, and it is not a from-nothing build. §1.1 must be read that way, and `M4` must not quote it as one.

---

# 4. Audit table

The seven accepted audit-unit classes. Every row carries one disposition from
`KEEP / SIMPLIFY / MERGE / DELETE / MOVE` and either an `M4` step ID or a retain reason. Sibling surfaces
share a row only where the row lists every path and they have one job, owner, source view and disposition.

## 4.1 Unit class 1 — tracked tool files

Seventeen files. Git mode is recorded because three `.sh` are `100755` and three are `100644` while **all**
are invoked as `sh tools/<name>.sh`; the mode decides nothing and reads as though it does.

| # | file | mode | real job / owner | source view | disposition | M4 / reason |
|---|---|---|---|---|---|---|
| T-01 | `tools/naming-gate.py` | 644 | A005 scoped-name policy; the only verifier prose gets | working tree or export | **SIMPLIFY** | `M4-01` — 9.0 M `re.escape` calls; 22.3 s, the largest single hot cost |
| T-02 | `tools/gate-mutation-test.py` | 644 | proves each gate's root helpers load-bearing | copies of the tree | **SIMPLIFY** | `M4-02`, `M4-03` — 22.4 s, 78% of `fcb`; 25 of 67 mutants never run |
| T-03 | `tools/source-diet.py` | 644 | the permanent `.v` comment law + exception relation | working tree or export | **SIMPLIFY** | `M4-06` — 2 294 lines, of which the M1 replay path is dead and references six deleted files |
| T-04 | `tools/fcb-reference-gate.py` | 644 | D-24: the complete authority↔manifest reference relation | working tree or export | **SIMPLIFY** | `M4-03`, `M4-05` — 64 controls each copying the tree; own enumeration |
| T-05 | `tools/host-python-gate.py` | 644 | the permanent no-host-Python boundary | working tree or export | **KEEP** | boundary is a permanent accepted invariant; cost 2.9 s is proportionate |
| T-06 | `tools/claim-matrix-gate.py` | 644 | every completion claim names a surface that exists | working tree or export | **SIMPLIFY** | `M4-07`, `M4-09` — hand-retargeted subject already drifted; 1 mutant for 17 helpers |
| T-07 | `tools/human-review-index.py` | 644 | D-07 human-act data + its generated view | working tree or export | **KEEP** | 0.6 s; one canonical source, one generated view, controls load-bearing |
| T-08 | `tools/closure-ledger-view.py` | 644 | the generated closure-ledger view of its canonical CSV | working tree or export | **KEEP** | 2.1 s; **but** `M4-09` adds the mutation coverage it entirely lacks |
| T-09 | `tools/worktree-list.py` | 644 | the declared inventory owner for the `make check` export | working tree | **MERGE** | `M4-05` — it owns the tar path only; five other components enumerate for themselves |
| T-10 | `tools/fmt-check.py` | 644 | `.editorconfig` whitespace report (reports, never gates) | working tree | **KEEP** | 0.98 s, not on the `check` path, delegates property resolution to the reference implementation |
| T-11 | `tools/rocq-profile.py` | 644 | ranks a `rocq c -time` log; diagnostic only | a profile log | **KEEP** | 100 lines, no gate depends on it, earned its keep in this audit (`M3-DUNE-FANOUT`) |
| T-12 | `tools/perf.sh` | 644 | the M2 diagnostic timing aid | its own builder | **KEEP** | accepted M2 product, frozen by contract §9; 88 lines |
| T-13 | `tools/ocaml-origin-gate.sh` | 755 | transport-only OCaml boundary, every depth | exported tree | **KEEP** | 61 lines, host shell, one job |
| T-14 | `tools/generated-output-gate.sh` | 755 | tracked Go is Fido-headed, no nested `go.mod`, no `.fido` | exported tree | **KEEP** | 57 lines, one job |
| T-15 | `tools/generated-mode-gate.sh` | 755 | Git **mode** of generated entries, index-authoritative | the real Git index | **KEEP** | 30 lines; its distinct source view is required, not duplicate (`M3-SOURCE-ENUMERATION`) |
| T-16 | `tools/staged-generated-compare.sh` | 644 | staged/working bytes vs the pristine layer, both directions | exported tree + pristine | **KEEP** | 54 lines, one shared implementation for `make check` and the hook |
| T-17 | `tools/regen-guard-test.sh` | 644 | proves `sync` is unbuildable when `go-e2e` fails | Docker DAG | **KEEP** | 48 lines; the only control on validate-before-publish |
| T-18 | `tools/python-requirements.lock` | 644 | states the stdlib-only closure `host-python-gate` proves | — | **KEEP** | data, not code |

`M4-12` normalizes the six `.sh` modes so the bit stops implying an execution path that does not exist.

## 4.2 Unit class 2 — public Make targets

Twenty-one targets (`.PHONY` plus `.DEFAULT_GOAL`).

| target | job | partial or full | disposition | M4 / reason |
|---|---|---|---|---|
| `check` | **full working-tree acceptance** | full | **KEEP** | the one full join; `M4-04` changes how it invokes gates, not what it asserts |
| `prove` | the complete proof gate | partial | **KEEP** | `M4-11` addresses its dominant internal cost |
| `emit` | materialize witnesses + exercise the sink | partial | **KEEP** | |
| `e2e` | emit + pinned `go build ./...` + goldens | partial | **KEEP** | |
| `regenerate` | validate-before-publish republication | full (publication) | **KEEP** | |
| `regen-guard` | proves `regenerate` cannot publish unvalidated | partial | **KEEP** | |
| `audit-fresh` | forces `prover` + `go-e2e` to run, not report a cache hit | partial | **KEEP** | this audit used the same mechanism via `FIDO_PERF_COLD` |
| `fcb`, `claims`, `diet`, `names`, `hostpython` | one gate family each | **partial** | **KEEP** | `M4-04` batches their container starts; each stays separately invocable |
| `fcb-write` | regenerate every generated FCB view | writer | **SIMPLIFY** | `M4-12` — GNU-only `find -printf` twice |
| `fmt` | whitespace report | partial, non-gate | **KEEP** | |
| `perf` | the M2 serial diagnostic | diagnostic | **KEEP** | frozen by contract §9 |
| `profile` | rank one module's sentences | diagnostic | **KEEP** | |
| `prover-log`, `prove-errors` | readable proof diagnostics | diagnostic | **KEEP** | `prover-log` is what produced §3.1 |
| `pytools`, `builder` | image/builder prerequisites | infrastructure | **KEEP** | `M4-10` fixes `pytools`' key |
| `install-hooks` | one `git config` | setup | **KEEP** | |

Every partial target prints a scoped success line naming what it checked; none claims full acceptance. That
distinction holds today and `M4` preserves it.

## 4.3 Unit class 3 — named pre-commit stages

| stage | source view | disposition | reason |
|---|---|---|---|
| export the index once (`git checkout-index --ignore-skip-worktree-bits --all`) | — | **KEEP** | one export, then everything reads it; `--ignore-skip-worktree-bits` is load-bearing |
| recompute `PYTAG` from the **staged** Dockerfile + lock | staged | **SIMPLIFY** | `M4-10` — same over-keying as `make check` |
| three shell policy gates on the export | exported index | **KEEP** | |
| `generated-mode-gate.sh` from the repo cwd | the real Git index | **KEEP** | mode is invisible in an export |
| the seven Python gate families on the export | exported index | **MERGE** | `M4-04` — 14 container starts for one mount |
| `buildx --target prover`, `--target go-e2e` | staged Buildx context | **KEEP** | |
| `--target generated-artifact` + `staged-generated-compare.sh` | staged + pristine | **KEEP** | |

## 4.4 Unit class 4 — Docker/Buildx stages, caches, source-view boundaries

| unit | disposition | reason |
|---|---|---|
| `python-tools` | **KEEP** | 5 Dockerfile lines; the *tag* is the defect (`M4-10`), not the stage |
| `rocq-builder` → `rocq-base` | **KEEP** | digest-pinned, builder/runtime split is right |
| `prover` | **KEEP** | `M4-11` addresses its internals, not the stage |
| `profile` / `profile-log` | **KEEP** | diagnostic; export surface is the raw log only |
| `emit` | **KEEP** | |
| `generated-module` → `generated-artifact` | **KEEP** | content-addressed pristine layer; the whole byte-compare rests on it |
| `go-base` → `go-e2e` | **KEEP** | `go-base` exists so the digest appears once and can be primed outside a timed interval |
| `sync` | **KEEP** | the validate-before-publish DAG edge; `regen-guard` proves it |
| caches `fido-apt-pytools`, `-builder`, `-base`, `fido-opam` | **KEEP** | apt/opam layer caches, correctly `sharing=locked` |
| cache `fido-dune-rocq-9.2.0-$arch` (locked, shared by 3 stages) | **KEEP** | one compile reused; serialization is the price and it is the right one |
| cache `fido-crossmnt-$arch` (private, emit) | **KEEP** | it *is* the cross-device test fixture |
| `.dockerignore` excluding `/go.mod` and `**/*.go` | **KEEP** | the exclusion is what makes the pristine independent of the committed bytes |

## 4.5 Unit class 5 — Dune aliases and proof-build units

| unit | disposition | reason |
|---|---|---|
| `dune build @install @all` | **KEEP** | one command builds theory and plugin; 16.4 s, 13% of the cold stage |
| `(rocq.theory (name Fido) (modules …))` — 16 modules | **KEEP** | `M3-DUNE-FANOUT`: no split justified by measured cost or edit weight |
| `(library (name fido_emit) (private_modules sink))` | **KEEP** | `sink` private is the reason no external consumer can publish |
| `(rocq.pp (modules materialize))` | **KEEP** | |
| the certified-module coverage check (tracked root `.v` == `(modules …)`) | **KEEP** | costs 0.01 s and closes a real hole |

## 4.6 Unit class 6 — distinct gates

| gate | disposition | M4 / reason |
|---|---|---|
| readable `Print Assumptions` (`gate/Assumptions.v`, 540 lines / 535 distinct) | **SIMPLIFY** | `M4-08` duplicates + omissions; `M4-11` its 77 s cost |
| whole-theory `Fido Audit Assumptions` | **KEEP** | 1.7 s for a strictly stronger guarantee |
| assumption self-tests A–E | **KEEP** | 2.2 s; each proves the audit is not fail-open |
| sealed-capability self-tests F–AG + meta + mint AB–AD + positive | **SIMPLIFY** | `M4-13` — hoist the 25 recomputed stage-1 loads to 4 |
| emit-time provenance rejection (6 forged-image classes) | **KEEP** | rejects before any effect; transiently generated, never tracked |
| the internal sink exercise (`sink_test`) | **KEEP** | dirty/adversarial trees; the only control on the publication sink |
| `go build ./...` e2e + goldens + differentials | **KEEP** | 45 s cold, the last-mile integration alarm |
| generated-byte compare (working tree and staged) | **KEEP** | one shared implementation, two source views |
| validate-before-publish DAG edge + `regen-guard` | **KEEP** | |
| the six Python document gates | see §4.1 | |

## 4.7 Unit class 7 — internal helpers that qualify

A helper qualifies only if it owns a distinct policy fact, source enumeration, cache key, production edge or
dominant measured cost. Five do:

| helper | why it qualifies | disposition | M4 |
|---|---|---|---|
| `naming-gate.py:318 check_prose` | dominant measured cost — 23.9 s of 35.9 s profiled | **SIMPLIFY** | `M4-01` |
| `gate-mutation-test.py:434 run_mutant` | owns the per-mutant tree copy and control selection | **SIMPLIFY** | `M4-02`, `M4-03` |
| `fcb-reference-gate.py:584 scenario` | owns the per-control tree copy | **SIMPLIFY** | `M4-03` |
| `Makefile:20 PYTAG` | owns a cache key, and keys it on 1 245 lines instead of 5 | **SIMPLIFY** | `M4-10` |
| `Dockerfile:156 sealed()` | owns a production proof-gate edge and recomputes its precondition 25× | **SIMPLIFY** | `M4-13` |

No other helper is inventoried. Functions, theorems and proof bodies are explicitly out of scope.
