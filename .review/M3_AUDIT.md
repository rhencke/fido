# M3 — Tool and Build Architecture Audit — findings

status: complete

Contract: `.review/M3_TOOL_AND_BUILD_ARCHITECTURE_AUDIT.md`, activation
`0b7fd86825936c37f31ef83879574d526d548122`, as amended by `.review/M3_CONTRACT_AMENDMENT_1.md` (`M3-A1`) and
`.review/M3_CONTRACT_AMENDMENT_2.md` (`M3-A2`), both authorized by Rob.
Accepted basis: `.review/REVIEW_BASIS.md`. Repair authority: `.review/M3_FORENSIC_AUDIT_REPAIR_2.md`.

This is one temporary table, not a registry. The Makefile, hook, Dockerfile, Dune files and tools remain the
authorities for what executes. M3's only project-tool change is the one `M3-A1` authorizes.

---

# 1. Measured configurations

Four configurations, never pooled. Every measured fact names the one that produced it.

```text
A  serial diagnostic       make -j1 check, builder fido-perf-v1, BuildKit max-parallelism=1
                           subject 9814db77ead0cfcfd8ff268303ba2afedef71197 (the accepted M2 record)
B  ordinary working tree   subject a0482140384de3d8c193263c3bf5281e53ccdd8b
                           builder fido-builder, default Make concurrency, host idle unless stated
C  staged acceptance       .githooks/pre-commit over the exported Git index
D  partial feedback        one named public target run alone (a subset of B)
```

**Every configuration-B figure below was taken at `a0482140384de3d8c193263c3bf5281e53ccdd8b`** — the commit
that landed the `M3-A1` claim-matrix repair — so the tools, build files and tree under measurement are one
immutable snapshot rather than a tree that was still being edited.

A and B answer different questions. Their numbers are not interchangeable and are never pooled.

## 1.1 Configuration A — the accepted serial baseline

Adjacent-row deltas of `.review/PERFORMANCE.tsv` at `9814db77ead0cfcfd8ff268303ba2afedef71197` (the record
stores cumulative completions; a reader subtracts adjacent rows).

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

Two different problems. Cold is a Rocq/Docker problem; hot is a Python problem; hot is the ordinary loop.

## 1.2 Configuration B — at the subject ref, host idle

```text
ref        a0482140384de3d8c193263c3bf5281e53ccdd8b
builder    fido-builder            Make concurrency  default
cache      warm (image tag hit, Buildx stages cached)
host       idle
```

| command | observed |
|---|---:|
| `make names` | 23 440 ms |
| `make fcb` | 33 330 ms |
| `make claims` | 2 580 ms |
| `make fmt` | 1 240 ms |

`make fcb` is larger here than in configuration A because this ref carries 43 mutants and two more tracked
documents, not because the configurations are comparable. They are not, and are not compared.

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
assumption audit and self-tests A–E/F–AG, and the emit-stage provenance rejections. These are the
adversarial half of the evidence and M4 must keep them always-run.

---

# 3. Findings

Twenty mandatory stable IDs, each ending in exact M4 step IDs or an evidence-backed `KEEP / no M4 change`.

## M3-PERF-NAMES — `names` on the accepted hot path

**22 310 ms (A, hot) / 23 440 ms (B, subject ref, host idle).** One container, one process.

Root cause, from a cProfile run at the subject ref inside the pinned image. The exact command, reproducible
as written:

```text
docker run --rm -u $(id -u):$(id -g) -e PYTHONDONTWRITEBYTECODE=1 -e HOME=/tmp -e GIT_CONFIG_COUNT=1 -e GIT_CONFIG_KEY_0=safe.directory -e GIT_CONFIG_VALUE_0=/repo -w /repo -v "$PWD":/repo:ro "$PYTAG" python3 -c "
import cProfile, pstats, sys, runpy, contextlib
sys.argv = ['tools/naming-gate.py']
def go():
    with contextlib.suppress(SystemExit):
        runpy.run_path('tools/naming-gate.py', run_name='__main__')
pr = cProfile.Profile(); pr.enable(); go(); pr.disable()
st = pstats.Stats(pr)
want = {'escape': 're.escape', 'search': 're.search', 'check_prose': 'check_prose', 'check_code': 'check_code'}
for f, v in st.stats.items():
    if f[2] in want and ('re/__init__' in f[0] or 'naming-gate' in f[0]):
        print(f'{want[f[2]]:12s} calls={v[0]:>10d}  tottime={v[2]:.3f}  cumtime={v[3]:.3f}')
print(f'profiled total {st.total_tt:.3f} s')
"
```

with `PYTAG` as the Makefile computes it. Observed at `a0482140384de3d8c193263c3bf5281e53ccdd8b`:

```text
files examined                 102
check_prose      calls=       168   tottime= 3.039   cumtime=25.398
check_code       calls=       131   tottime= 1.403   cumtime=12.080
re.escape        calls=   9371786   tottime= 2.841   cumtime=12.960
re.search        calls=  10207628   tottime= 3.333   cumtime=18.485
profiled total   37.630 s            (unprofiled wall: 23 440 ms)
```

`tools/naming-gate.py:336` (and `:290`, `:342`) build a **new pattern string per line per retired name**:

```python
if re.search(r"(?<![\w.'/-])" + re.escape(old) + r"(?![\w'])", line):
```

Table cardinalities, read from the module itself rather than counted by eye:

```text
OLD_MODULES        13     OLD_QUALIFIED       5   (substring test, no regex)
OLD_NAMES          73     RETIRED_COMPOUNDS  20   (searched, not escaped)
OLD_FILES           5
DELETED_SURFACES   69
core retired names 160    all distinct
```

160 constant patterns, rebuilt for every candidate line in both `check_prose` and `check_code`. `re`'s
internal cache holds 512 entries and is thrashed, so each call re-escapes and re-looks-up. No line count is
claimed here: the measured facts are the call counts, and deriving a line total from them would mix the
159-escape prose path with the 160-escape code path.

Disposition: **SIMPLIFY** → `M4-01`.

## M3-PERF-FCB — `fcb`, including the mutation harness

**28 580 ms (A, hot) / 33 330 ms (B, subject ref, host idle).** Per-line timestamps of `make fcb` at the
subject ref, reading `/proc/uptime` per output line:

| sub-invocation | ms |
|---|---:|
| human-review-index `--self-test` | 1 210 |
| human-review-index `--check` | 650 |
| fcb-reference-gate `--self-test` | 3 710 |
| fcb-reference-gate (check) | 750 |
| closure-ledger-view `--check` | 560 |
| **gate-mutation-test** | **26 220** |
| target teardown | 230 |

`gate-mutation-test` is **79% of `fcb`**.

Disposition: **SIMPLIFY** → `M4-02`. Root cause under `M3-MUTATION-ARCHITECTURE`.

## M3-MUTATION-ARCHITECTURE — copying, isolation, control selection, parallelism, cost

The harness nests two control layers, and the product is the cost.

`tools/gate-mutation-test.py:run_mutant` — per mutant: a full `shutil.copytree` of the tree, then a
subprocess running that gate's **entire** `--self-test`. `main` runs them on
`ThreadPoolExecutor(max_workers=min(len(selected), os.cpu_count()))` — 4 on this host.

**Three** gates then copy the tree again per control; the other three build small fixtures. The difference is
where M4 aims:

```text
copies the whole tree per control   fcb-reference-gate.py:scenario   human-review-index.py   claim-matrix-gate.py
builds a small temp fixture         source-diet.py   host-python-gate.py   naming-gate.py
```

Measured at the subject ref by importing the harness in the pinned image and multiplying by each gate's own
control count:

```text
source-diet          16 mutants x 53 controls =  848
fcb-reference-gate   11 mutants x 64 controls =  704     <- copies
host-python-gate      9 mutants x 25 controls =  225
naming-gate           2 mutants x 72 controls =  144
claim-matrix-gate     2 mutants x 25 controls =   50     <- copies
human-review-index    2 mutants x 24 controls =   48     <- copies
worktree-list         1 mutant
                     43 mutants, 2 019 nested control executions per `make fcb`
                     of which 802 copy the whole tree, plus 43 mutant-level = 845 full tree copies
```

**The nesting is not redundant evidence** — a mutant proves a rule load-bearing, a control proves the gate
detects a defect — but the harness re-runs the *whole* self-test when `main` only ever asserts that the
mutant's own `expected` controls fired.

Disposition: **SIMPLIFY** → `M4-02` alone.

An earlier draft also proposed replacing the per-control tree copy with a manifest-and-restore scheme
(`M4-03`). It is **withdrawn**, for two reasons. Its manifest recorded size, `mtime_ns` and directories, which
do not establish file type, mode, symlink identity or symlink target — and these controls mutate regular
files, deleted paths, directories, symlinked files and symlinked directories. So it would not have proved the
property it claimed. And `M4-02` removes the multiplier that makes the copies dominant in the first place:
each mutant runs only its own named controls. Measure after `M4-02`; do not build a restoration framework in
advance of knowing whether anything still needs one.

The existing per-control isolation — one copy, discarded — is simple and correct, and is **KEEP, no M4
change**.

## M3-SOURCE-DIET-REPLAY — dormant M1 replay modes

Not merely dormant — **broken, and guarded by mutants that never run.**

1. `tools/source-diet.py:M1_ONLY_MODES` names seven CLI modes: `--against-baseline`,
   `--disposition-exact`, `--code-identical`, `--verify-m1-evidence`, `--write-metrics-table`,
   `--write-disposition`, `--m1-self-test`. **No Makefile recipe and no hook line invokes any of them**
   (`git grep -n 'source-diet' -- Makefile .githooks`).
2. Those modes reference six repository paths that **no longer exist** — the M1 baseline, metrics, file
   disposition, declaration-deletion and obligation ledgers, and the retired M2 checkpoint document. Their
   exact spellings are in `tools/source-diet.py` at lines 41–44, 50, 1435, 1444, 1912 and 1949; they are not
   repeated here because this file must not name paths that are gone.
3. **25 of the 68 mutants** in `tools/gate-mutation-test.py` are `--m1-self-test` mutants (all
   `source-diet.py`). `mutant_mode` routes them there, and `--m1` is invoked nowhere, so they never run.

The dead mode is protected by dead mutants, and the pair has been keeping each other alive.

Disposition: **DELETE** → `M4-06`.

## M3-CLAIM-SUBJECT — the manually retargeted active-checkpoint constant

The retarget has already drifted. `tools/claim-matrix-gate.py` sets `TSV_REL` to the current matrix while its
own docstring still names the previous checkpoint's matrix, which was deleted at M2 closeout. No gate catches
it: D-24 scans *authority documents* and a tool is not one; the naming gate scans retired *names*, not
retired *paths*.

**Deleting the stale string does not satisfy this finding, and recording it as satisfied was wrong.** The
contract asks to remove the *need* for a hand-retargeted constant; deleting the docstring copy leaves the
constant exactly as hand-retargeted as before. Dynamic discovery does not satisfy it either — finding one
matching matrix file still does not know the required obligation IDs, and reading them out of review prose
would create a second current-state authority.

Amendment `M3-A2` (`.review/M3_CONTRACT_AMENDMENT_2.md`) replaces the finding's wording with what actually
closes it: **one explicit subject object owning both the matrix path and the complete required obligation-ID
set**, read by the gate, its messages and its controls, with no second copy anywhere.

Disposition: **SIMPLIFY** → `M4-07`, which builds that one object and deletes the stale docstring path with
it.

## M3-NAMING-EXCLUSION — the inert exclusion

`tools/naming-gate.py:EXCLUDED_FILES` holds three entries. Two resolve — the FCB amendments tree, which must
quote the names it retires, and the gate itself, which spells every retired name by necessity. The third
names a C4 review document that is **not in the tree**.

An exclusion for a file that is not there excludes nothing and hides the next file to take that name.

Disposition: **DELETE** that entry → `M4-07`.

## M3-ASSUMPTION-DUPLICATES — duplicate `Print Assumptions` in `gate/Assumptions.v`

540 `Print Assumptions` lines; **535 distinct**. Five exact duplicates:

```text
Compilable.capability_is_compile_outcome
Compilable.capability_source
Compilable.forest_count_source
Compilable.member_at_in_forest
Compilable.occurrence_expr_diags_conv_sound
```

The `prover` stage compares `want=$(grep -c '^Print Assumptions')` against
`got=$(grep -c '^Closed under the global context')`, and a duplicate raises both sides equally, so the gate
passes — while reporting "540/540 surfaces closed" when 535 surfaces are closed.

Disposition: **DELETE** the five duplicate lines → `M4-08`.

## M3-ASSUMPTION-SURFACES — omitted Complex imaginary-component readable surfaces

`Complex.v` declares 11 `_real` and 11 `_imaginary` lemmas; the readable gate carries 16 Complex surfaces.
Four real/imaginary pairs are asymmetric — the real half gated, the imaginary half not:

```text
typed_runtime_real_coherent      gated  /  typed_runtime_imaginary_coherent      NOT
typed_runtime_real_not_inf       gated  /  typed_runtime_imaginary_not_inf       NOT
typed_runtime_real_not_nan       gated  /  typed_runtime_imaginary_not_nan       NOT
typed_runtime_real_not_neg_zero  gated  /  typed_runtime_imaginary_not_neg_zero  NOT
```

`typed_runtime_real_shape` / `typed_runtime_imaginary_shape` are both gated, so this is an omission rather
than a policy. The whole-theory audit already covers them; what is missing is the *readable* surface.

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

plus three from the hook. Between them they invoke host `git`, `find`, `sed`, `grep`, `diff`, `awk`, `tar`,
`cmp` and `mktemp`, none pinned. One concrete consequence: the `fcb-write` recipe uses `find … -printf`
twice, which is GNU findutils only, so that recipe cannot run on a BSD or busybox host.

This is a **declared-scope** fact, not a defect: the project's declared host boundary is "shell, Make, Git,
Docker and Buildx", so host shell is inside the trusted base by design, and nothing in the current
requirement set asks for BSD portability.

Disposition: **KEEP, no M4 change.** Recorded so the exposure is stated rather than assumed away. Widening
the host boundary is a scope decision for Rob, not an M4 refactor, and tidying a mode bit is not a
requirement.

## M3-CLAIM-MUTATION — does the claim-matrix gate need mutation coverage?

**Yes — and the audit proved it the hard way.** Mutation coverage against top-level helper count at the
subject ref:

| tool | top-level defs | selected mutants |
|---|---:|---:|
| source-diet.py | 67 | 16 (+25 that never run) |
| fcb-reference-gate.py | 59 | 11 |
| host-python-gate.py | 26 | 9 |
| claim-matrix-gate.py | 18 | 2 |
| naming-gate.py | 15 | 2 |
| human-review-index.py | 12 | 2 |
| closure-ledger-view.py | 6 | **0** |
| worktree-list.py | 5 | 1 |

While closing the matrix, `tools/claim-matrix-gate.py` failed its own self-test on a matrix that was correct:

```text
FAIL  a named implementation surface was renamed: could not construct the scenario
      (no closed row with a locatable declaration to rename)
```

`rename_named_surface` needed a closed row naming a movable `.v` declaration or Python `def`/`class`;
`ensure_closed_row` guaranteed only that *some* row was closed. Every closed row of a documentation-only
checkpoint honestly carries `unsupported-boundary`, so the control could not be built. It had never fired
because some closed row always happened to name a Python `def` — at M2 only after that cell was reordered so
the locatable entry came first.

That defect is repaired under Amendment `M3-A1` (`.review/M3_CONTRACT_AMENDMENT_1.md`): one shared
`renameable_declaration` predicate, a `require_declaration` flag mirroring the existing `require_builder`,
four new controls, and one mutation entry. `closure-ledger-view.py` still has no mutant at all and it
publishes a generated FCB view.

Disposition: **the precondition repair is done under `M3-A1`; the remaining claim-matrix coverage** →
`M4-09`, scoped to that gate's root facts alone.

**`closure-ledger-view.py` is KEEP, no M4 change.** Its zero controls are a real observation and it is
recorded here, but the mandatory finding asks about the *claim-matrix* gate. Giving the ledger view a new
self-test interface and a mutation family would add a gate surface during an optimization checkpoint, to
close a defect nobody recorded. Its canonical CSV and its exact `--check` relation are unchanged. A later
exact requirement can reconsider it.

## M3-SOURCE-ENUMERATION — every independent enumeration and its one right owner

Seven independent enumerations of the repository:

```text
tools/worktree-list.py             git ls-files --cached --others --exclude-standard  (declared owner)
tools/naming-gate.py               git ls-files … + iterdir + rglob
tools/fcb-reference-gate.py        git ls-files … + os.walk + rglob + scandir
tools/source-diet.py               git ls-files … + os.walk
tools/host-python-gate.py          git ls-files … + rglob
tools/generated-mode-gate.sh       git ls-files -s        (index-authoritative, deliberately distinct)
tools/staged-generated-compare.sh  git ls-files --cached --others --exclude-standard
```

`Makefile:59` names `tools/worktree-list.py` as the one that "owns the inventory" — but it owns it only for
the `make check` tar export.

**They do not all ask the same question.** `generated-mode-gate.sh` must read `git ls-files -s` from the real
index to see file *modes*, invisible in an export. And the Python gates differ in *selection*, not just
traversal: the naming gate examined 102 files at the subject ref while the reference gate inventoried 113 and
source-diet 111. A shared owner would have to preserve three different selections through one API, and this
audit has not shown that it can.

Disposition: **KEEP each enumeration, no M4 change.** Recorded as a real duplication with a real cost, and
retained because unifying it is a redesign this evidence does not justify. It needs its own contract if it is
ever wanted.

## M3-NO-HOST-PYTHON-COST — the deliberate cost of the accepted boundary

`make check` starts the pinned Python container **16 times**; the hook starts it **14 times**.

Floor cost per start, configuration B at the subject ref, host idle: `make pytools` (a bare
`docker image inspect`) is 170–210 ms; `make fmt` (that prerequisite plus exactly one container start plus a
scan of 111 files) is 1 240 ms. Cross-checking against configuration A — `claims` 1 720 ms for 2 starts,
`diet` 2 690 ms for 3, `hostpython` 2 920 ms for 2 — puts container start plus interpreter start at roughly
**0.6–0.7 s**, so **≈10 s of the 63.7 s hot `make check`**, about 16%.

This is the price of a boundary worth having, and it is paid 16 times for what is one read-only mount of one
tree by one image.

Disposition: **KEEP, no M4 change.** Batching the gates into one container start would have to preserve
separate public targets, exact staged copies, gate-specific failure messages, the completion markers `make
perf` measures, and the two source views — a restructuring of both the Makefile and the hook to recover a
floor that shrinks anyway once `M4-01` and `M4-02` land. Re-measure after M4 and reconsider then;
this is recorded evidence, not a deferred promise.

## M3-INVALIDATION — why ordinary edits rebuild more than the proof graph requires

`Makefile:20` keys the Python tooling image on the **whole** Dockerfile:

```make
PYTAG := fido-python-tools:$(shell cat Dockerfile tools/python-requirements.lock | sha256sum | cut -c1-16)
```

Only lines 23–27 of 1 245 define that image. Demonstrated at the subject ref, with the edit applied to a pipe
so no tracked file changed:

```text
current PYTAG suffix                                              6e65f59ae32bd774
after one comment edit in the go-e2e stage (~line 803)            b5562f3bf16ae2a8
```

A comment 776 lines from the stage that defines it forces a full `--load` rebuild, and the hook computes the
same tag the same way.

Disposition: **KEEP, no M4 change.** A tag hit costs 170–210 ms and the miss is rare. Narrowing the key means
a fail-closed Dockerfile-stage extractor duplicated in the Makefile *and* the hook, and it inverts the risk
from "rebuilds too often" to "runs a stale tooling image" — the worse failure. Under `D-30` that parser is
not justified by this benefit. Recorded as measured evidence; the over-keying is real and cheap.

## M3-BUILDX-CACHE — stage boundaries, COPY sets, cache mounts and false invalidation

Six persistent caches; the DAG is §2.3. Two structural facts:

1. `prover`, `profile` and `emit` COPY the **same** four inputs (`dune-project dune`, `*.v`, `gate/`,
   `plugin/`), so BuildKit content-addresses those layers once and shares them. `emit` adds `e2e/` last, so
   an `e2e/` edit invalidates only `emit`. That ordering is correct and deliberate.
2. All three mount the **same** `fido-dune-rocq-9.2.0-$arch` `_build` cache with `sharing=locked`. A theory
   compile is done once and reused across stages — and the stages also **serialize** on it, which is why
   parallel `make check` gains little on the Rocq half.

**A cache mount is not a Docker layer.** `--no-cache-filter prover` re-runs the stage's `RUN` but leaves
`_build` populated, so even a "cold" `prove` does not recompile the theory from nothing. That is what
`.review/PERFORMANCE.tsv`'s cold column measures, and §1.1's cold numbers must be read that way.

Disposition: **KEEP, no M4 change.** The COPY ordering and the shared `_build` both do their job.

## M3-ACCEPTANCE-DUPLICATION — repeated work across `make check`, partial targets and the hook

Working-tree versus staged-index work is **not** duplication and is not counted here.

What is genuinely repeated over one source view:

1. **Every gate's `--self-test` is source-view independent.** The controls build their own fixtures in
   `tempfile.TemporaryDirectory()`; they do not read the tree under test. Running them in `make check` and
   again in the hook is therefore the same computation twice, not two views.
2. **`gate-mutation-test` re-runs those same self-tests 43 more times** (`M3-MUTATION-ARCHITECTURE`), inside
   the run that already ran each of them once. 2 019 nested control executions, 845 full tree copies.
3. `make check` runs `prove` then `e2e`; `e2e`'s `emit` stage repeats `dune build @install @all`. Already
   cheap — the shared `_build` cache makes it a re-check, not a recompile.

Disposition: **SIMPLIFY** (2) → `M4-02`. **KEEP** (1) and (3): the self-tests are the adversarial
half of the evidence and must stay always-run in both views, and (3) costs nothing.

## M3-DUNE-FANOUT — the real Dune/Rocq graph, critical path and rebuild set

**Authority: the pinned toolchain's own dependency output**, not source imports. Obtained at the subject ref
with a temporary diagnostic image (no Dockerfile stage added, nothing tracked):

```text
docker buildx build --builder fido-builder --platform linux/amd64 --target prover --load -t fido-m3-diag .
docker run --rm fido-m3-diag sh -c 'rocq dep -Q . Fido *.v'
```

Normalized adjacency, transitive closure and downstream rebuild set, computed from that raw output:

```text
module        direct  transitive  downstream rebuild set (transitive dependents)
FilePath           0      0        8  Collections Compilable Emit Index Render Safe Syntax Typing
Float              0      0        8  Compilable Complex Emit Index Render Safe Syntax Typing
Collections        1      1        7  Compilable Emit Index Render Safe Syntax Typing
Complex            1      1        7  Compilable Emit Index Render Safe Syntax Typing
Integer            0      0        7  Compilable Emit Index Render Safe Syntax Typing
ModulePath         0      0        7  Compilable Emit Index Render Safe Syntax Typing
Names              0      0        7  Compilable Emit Index Render Safe Syntax Typing
Version            0      0        7  Compilable Emit Index Render Safe Syntax Typing
Syntax             8      8        6  Compilable Emit Index Render Safe Typing
Index              3      9        4  Compilable Emit Render Safe
Typing             4      9        4  Compilable Emit Render Safe
Compilable         9     11        3  Emit Render Safe
Decimal            0      0        2  Emit Render
Safe               6     12        2  Emit Render
Render            10     14        1  Emit
Emit               8     15        0  (none)

critical path, depth 8:
  FilePath/Float -> Collections/Complex -> Syntax -> Typing/Index -> Compilable -> Safe -> Render -> Emit
```

The `From Fido Require` declarations agree with the toolchain graph edge for edge at this ref. That is a
useful fact — the imports are a faithful projection here — but the toolchain is the authority and the
imports are not.

**The decisive number is Compilable's downstream set: 3.** `Compilable.v` is 10 156 of ~18 500 lines, 55% of
the theory, and it sits *low* in the dependents order: editing it rebuilds only `Safe`, `Render` and `Emit`.
Editing a leaf like `FilePath` or `Float` rebuilds 8. So the largest module already has one of the smallest
rebuild sets.

Cost, configuration B at the subject ref (`make profile FILE=Compilable.v`):

```text
Compilable.v recompiled alone in 6.5 s (deps already built)
8962 sentences, 3.83 s of measured elaboration
slowest single sentence 0.239 s (the Stdlib Require), then 0.210 s (the Fido Require)
```

Disposition: **KEEP, no M4 change** — and the rationale is measured, not categorical. A split is *permitted*
to M4 under Governance `D-27` when M3 evidence and Rob's approved plan justify it. This evidence does not:
the fan-out a split would reduce is already 3, no sentence dominates the 6.5 s, and the change would be
substantial certified-source churn for a rebuild set that is nearly minimal.

## M3-EDIT-WEIGHT — files edited and co-change groups, over separated immutable ranges

Three exact ranges with full immutable endpoints, kept apart because pooling them predicts neither kind of
work.

**Range 1 — whole history to C4 acceptance, `.v` only.**
`git log 39ea7e3b012ec798c6a756c971c10bb363557ef8 -- '*.v'`, 1 829 commits.
Top files, all deleted: `main.v` 369, `builtins.v` 297, `GoSem.v` 216.
Also deleted, next in rank: `GoCompile.v` 211, `GoPrint.v` 180.
This range describes an architecture that no longer exists. Recorded so nobody reaches for it.

**Range 2 — the current module set (the semantic/proof range).**
`git log 20c5ad5c499d5046563471624117b80c737c7157..39ea7e3b012ec798c6a756c971c10bb363557ef8 -- '*.v'`,
25 commits. `20c5ad5c…` is the commit that introduced the whole current module set.

```text
per-file touches   Compilable.v 22   gate/Assumptions.v 18   Emit.v 8   Safe.v 4   Render.v 3
                   e2e/Witness*.v 3 each   Typing/Syntax/Index/Float/Complex 2 each   leaves 1 each

co-change groups   12  Compilable.v + gate/Assumptions.v
                    4  Compilable.v alone
                    2  Emit.v + gate/Assumptions.v
                    2  Compilable.v + Emit.v + gate/Assumptions.v
                    1  Compilable.v + Render.v + Safe.v
                    1  the five e2e witnesses + Emit.v + Safe.v
                    1  a whole-tree rename touching every module
```

**The dominant group is `Compilable.v` with `gate/Assumptions.v`, 12 of 25 commits**, and 16 of 25 touch the
assumptions gate alongside a certified module. This is the single most decision-relevant fact in the range:
semantic work almost always edits the readable assumption gate, and the readable assumption gate is the 77 s
cold cost in §3.1. The cold path hurts exactly where proof work walks — which is why `M4-11` is written down
and why `Q-M3-01` is worth Rob answering.

**Range 3 — the M-series tooling/documentation campaign.**
`git log 39ea7e3b012ec798c6a756c971c10bb363557ef8..a0482140384de3d8c193263c3bf5281e53ccdd8b`, restricted to
`tools Makefile Dockerfile .githooks dune`.

```text
co-change groups   63  the withdrawn observatory tool + gate-mutation-test.py
                   24  the withdrawn observatory tool alone
                    3  Makefile + those two
                    3  the hook + Makefile + those two
                    2  source-diet.py alone
                    2  gate-mutation-test.py + source-diet.py
```

The top two groups are dominated by a tool Rob withdrew, which is no longer in the tree. This range measures
the M2 culling, not future work. It is **not** pooled with Range 2 and is not evidence for any M4 decision
about the certified tree. Its one usable signal is the third and fourth groups: a Makefile or hook change
travels with the gate tools, which is why `M4` keeps Makefile and hook edits out of the retained steps.

Disposition: **KEEP the ranges as recorded, no M4 change.** They are the input to `M3-DUNE-FANOUT`'s KEEP and
to the ordering of `M4-01`/`M4-02`.

## M3-COMPILABLE-SURFACES — ungated `Compilable.v` surfaces

`Compilable.v` declares **623** top-level `Theorem`/`Lemma`/`Corollary`, all distinct names.

**Method, exactly.** For each name, search for `(?<![\w'])(?:Compilable\.)?<name>(?![\w'])` — bare or
module-qualified — in `gate/Assumptions.v`, then the other root `.v` modules, then `e2e/` and `plugin/`, then
elsewhere within `Compilable.v` itself excluding its own declaration site. First hit wins; the groups are
disjoint and sum to 623. Run in the pinned image at the subject ref.

```text
A  named in gate/Assumptions.v — readable public surface        200
B  referenced by another root .v module                           3
D  referenced by e2e/ or plugin/                                  1
C  referenced only inside Compilable.v — proof dependency        371
E  no consumer found anywhere                                    48
                                                                ---
                                                                623
```

**Why "no textual consumer" means "no consumer" here.** A Rocq lemma can normally be used without being
named, through a hint database. `Compilable.v` contains **no `Hint` declaration of any kind**, so nothing is
registered into a database and the 19 `auto`/`eauto` uses can only reach stdlib's core hints. A lemma in this
module therefore cannot be applied without appearing by name. The method's residual error is in the safe
direction: a name mentioned only in a comment counts as a consumer, so group E is a *lower bound* on what is
genuinely dead.

Group C is the honest answer to "required guarantee, proof dependency, or dead": 371 are proof dependencies —
load-bearing, just not readable surfaces — and the whole-theory `Fido Audit Assumptions` covers all 623
regardless.

**Group E is NOT dead, and reading it that way was an error.** The search establishes exactly one thing:
those 48 are not *current internal proof dependencies*. It does not establish that they have no purpose. A
top-level theorem can be its own externally visible guarantee, or a standalone proof-level regression fixture
whose **statement is the product** — such a theorem has no caller by design. The list visibly contains
several: the reordering and determinism fixtures, the rejected-program report fixtures, and the exact
fact-table guarantees. Their own source comments describe them that way.

And `make prove` staying green after a deletion would not have caught it. The lost guarantees would be the
deleted statements themselves; there would be nothing left to fail.

No 48-theorem proof-body audit is performed here — that is the per-theorem inventory §3 forbids. The finite
conclusion is the one this evidence supports and no more: **mechanical consumer-freeness does not authorize
deleting an exported theorem.**

Disposition: **A, B, C and D KEEP, no M4 change. E KEEP, no M4 change** — consumer-free exported theorem
surfaces, retained. Any future deletion needs a separately reviewed public-surface contract naming the exact
guarantees or fixtures being retired.

## M3-TOOL-COMPLEXITY — every retained tool under D-30

Per-file dispositions are §4.1. The summary across all eighteen tracked tool files:

```text
KEEP      13   ocaml-origin / generated-output / generated-mode / staged-generated-compare /
               regen-guard / perf.sh, host-python-gate, human-review-index, closure-ledger-view,
               fmt-check, rocq-profile, worktree-list, python-requirements.lock
SIMPLIFY   5   naming-gate, gate-mutation-test, source-diet, fcb-reference-gate, claim-matrix-gate
MERGE      0
DELETE     0   at file granularity
```

**No tool file is deleted, and that is a finding rather than a shrug.** Each of the eighteen owns a distinct
policy fact and is invoked by a live target or hook line. What is over-built is *inside* five of them:
`source-diet.py`'s dead M1 replay path, the mutation harness's re-run of whole self-tests, the naming gate's
per-line pattern construction, the reference gate's per-control tree copy, and the claim gate's two stale
strings. Those are `M4-01`, `M4-02`, `M4-06`, `M4-07` and `M4-09`.

Two observations a current gate invocation does **not** by itself justify:

- `tools/source-diet.py` is 2 294 lines, the largest tool here, and enforces one rule — the `.v` comment law.
  The rest is M1 exit-evidence machinery with no ledgers left to read (`M3-SOURCE-DIET-REPLAY`).
- `tools/gate-mutation-test.py` is invoked by two live lines, but 25 of its 68 entries are unreachable from
  either.

## M3-FRAGILE-PROSE — mutable counts, line-number identity, list-position identity

Three classes; each with its live instance and its disposition:

1. **A tool's prose naming a path that no longer exists** — the claim gate's docstring and the six
   `source-diet.py` M1 ledger constants. Nothing checks tool prose: D-24 checks authority documents only.
   → **DELETE the strings** (`M4-06`, `M4-07`). A generic "tool prose path" checker is *not* proposed: it
   would be a weak path scanner built to catch two strings that deletion already removes.
2. **A count in a gate's success message that is not the quantity it claims** — the `prover` stage prints
   "540/540 surfaces closed" for 535 distinct surfaces. → **DELETE the duplicates** (`M4-08`).
3. **List-position identity** — none found. Mandatory findings use stable IDs, the matrix uses `M3-nn` keys,
   the FCB registries are keyed TSVs. → **KEEP, no M4 change**; recorded so its absence is stated rather than
   assumed.

---

# 3.1 Cold-path decomposition — inside the `prover` stage

Not a mandatory stable ID; the forensic account the mandatory performance findings rest on. Two independent
runs of `make prover-log FIDO_PERF_COLD=1` (configuration B), reading `--progress=plain` timestamps:

| step | run 1 s | run 2 s | share |
|---|---:|---:|---:|
| `dune build @install @all` (theory + plugin) | 16.4 | 16.4 | 13% |
| **`rocq c gate/Assumptions.v` — the readable gate** | **77.6** | **76.9** | **59%** |
| certified-module coverage (shell) | 0.01 | 0.01 | — |
| `Fido Audit Assumptions` — whole certified theory | 1.72 | 1.72 | 1% |
| assumption self-tests A–E | 2.23 | 2.11 | 2% |
| sealed F–AG + meta-controls + mint AB–AD + positive | 33.1 | 32.0 | 25% |
| **stage total** | **131.1** | **130.3** | |

**1. The readable Print-Assumptions gate costs 77 s; the strictly stronger whole-theory audit costs 1.7 s.**
`gate/Assumptions.v` issues 540 `Print Assumptions` commands, each re-walking one constant's assumption
closure with no sharing; `Fido Audit Assumptions` walks the whole theory once. The readable gate covers 535
distinct declared surfaces; the audit covers every constant, mutual inductive and surviving named assumption.
77 s is 59% of the cold `prover` stage and **29% of the entire 270 s cold `make check`** — and
`M3-EDIT-WEIGHT` shows this is the path semantic work actually walks.

That is a proof-gate architecture question, not a mechanical refactor. It is `M4-11`, written up with its
preservation argument and deliberately left **unauthorized**, and `Q-M3-01` in `.review/OPEN_QUESTIONS.md`.

**2. The sealed-capability self-tests recompute their own precondition 21 times.**
`Dockerfile:sealed()` runs **two** `rocq c` invocations per call: stage 1 compiles
`SEALED_PRELUDE + Definition sentinel := <sentinel>.` and must succeed, then stage 2 adds the hidden term and
must fail. There are 25 sealed calls but only **four distinct (prelude, sentinel) pairs**:

```text
Compilable.compile   F G H I J K L M N O P Q R S T U V W X   (19 calls)
Emit.Mint.issue      Y Z                                     ( 2 calls)
Emit.of_safe         AA                                      ( 1 call )
Safe.certify         AE AF AG                                ( 3 calls)
```

Measured 1.10 s per sealed call (F at 99.09 s → AG at 126.7 s), so ≈0.55 s per `rocq c`, each loading the
whole theory. Stage 1 is a property of `(prelude, sentinel)` alone — the probe is not in the compiled file.
Hoisting it would be 4 loads instead of 25, ≈21 × 0.55 ≈ **11.6 s**. **No M4 step does it.** The saving is
secondary to the still-open 77 s readable-assumption decision above, and a cache inside an adversarial
proof gate needs an exact shell topology and exact key ownership this plan does not have — while the two
`meta_reject` controls deliberately vary `SEALED_PRELUDE` precisely to prove the helper rejects false
evidence. The current two-stage helper is simple and correct. **KEEP, no M4 change**; a later cold-path
contract may reconsider it with that topology named.

**3. A cache mount is not a Docker layer, and the accepted baseline's "cold" reflects that.**
`dune build` took 16.4 s in *both* runs with the `_build` cache warm throughout. `--no-cache-filter prover`
re-runs the stage's `RUN` but does not clear a cache mount. So the 270 s cold column of
`.review/PERFORMANCE.tsv` is **project-stage cold with the theory's `_build` warm** — a faithful measure of
"I edited a `.v` and re-ran acceptance", not a from-nothing build. §1.1 must be read that way and `M4` must
not quote it as one.

---

# 4. Audit table

The seven accepted audit-unit classes. Every row carries one disposition from
`KEEP / SIMPLIFY / MERGE / DELETE / MOVE` and either an `M4` step ID or a retain reason. Sibling surfaces
share a row only where the row lists every path and they have one job, owner, source view and disposition.

## 4.1 Unit class 1 — tracked tool files

Eighteen files.

| # | file | real job / owner | source view | disposition | M4 / reason |
|---|---|---|---|---|---|
| T-01 | `tools/naming-gate.py` | A005 scoped-name policy; the only verifier prose gets | working tree or export | **SIMPLIFY** | `M4-01` — 9 371 786 `re.escape` calls; 23.4 s, the largest single hot cost |
| T-02 | `tools/gate-mutation-test.py` | proves each gate's root helpers load-bearing | copies of the tree | **SIMPLIFY** | `M4-02`, `M4-06` — 26.2 s, 79% of `fcb`; 25 of 68 entries never run |
| T-03 | `tools/source-diet.py` | the permanent `.v` comment law + exception relation | working tree or export | **SIMPLIFY** | `M4-06` — 2 294 lines, of which the M1 replay path is dead and names six deleted ledgers |
| T-04 | `tools/fcb-reference-gate.py` | D-24: the complete authority↔manifest reference relation | working tree or export | **KEEP** | its 64 controls each copy the tree, 704 copies per `make fcb` — but `M4-02` removes the multiplier that makes that dominant. Re-measure after it |
| T-05 | `tools/host-python-gate.py` | the permanent no-host-Python boundary | working tree or export | **KEEP** | a permanent accepted invariant; 2.9 s is proportionate to it |
| T-06 | `tools/claim-matrix-gate.py` | every completion claim names a surface that exists | working tree or export | **SIMPLIFY** | `M4-07` one subject object (`M3-A2`); `M4-09` root-fact coverage. The precondition defect is already repaired under `M3-A1` |
| T-07 | `tools/human-review-index.py` | D-07 human-act data + its generated view | working tree or export | **KEEP** | 1.9 s; one canonical source, one generated view, controls load-bearing |
| T-08 | `tools/closure-ledger-view.py` | the generated closure-ledger view of its canonical CSV | working tree or export | **KEEP** | 0.6 s; it has no controls at all, which is recorded — but adding a self-test interface is not this checkpoint's job |
| T-09 | `tools/worktree-list.py` | the declared inventory owner for the `make check` export | working tree | **KEEP** | `M3-SOURCE-ENUMERATION`: the five Python enumerations differ in *selection*, not only traversal, so one owner is a redesign this evidence does not justify |
| T-10 | `tools/fmt-check.py` | `.editorconfig` whitespace report (reports, never gates) | working tree | **KEEP** | 1.24 s, off the `check` path, delegates property resolution to the reference implementation |
| T-11 | `tools/rocq-profile.py` | ranks a `rocq c -time` log; diagnostic only | a profile log | **KEEP** | 100 lines, no gate depends on it, and it produced `M3-DUNE-FANOUT`'s cost evidence |
| T-12 | `tools/perf.sh` | the M2 diagnostic timing aid | its own builder | **KEEP** | accepted M2 product, frozen by contract §9; 88 lines |
| T-13 | `tools/ocaml-origin-gate.sh` | transport-only OCaml boundary, every depth | exported tree | **KEEP** | 61 lines, host shell, one job |
| T-14 | `tools/generated-output-gate.sh` | tracked Go is Fido-headed, no nested `go.mod`, no `.fido` | exported tree | **KEEP** | 57 lines, one job |
| T-15 | `tools/generated-mode-gate.sh` | Git **mode** of generated entries, index-authoritative | the real Git index | **KEEP** | 30 lines; its distinct source view is required, not duplicate |
| T-16 | `tools/staged-generated-compare.sh` | staged/working bytes vs the pristine layer, both directions | exported tree + pristine | **KEEP** | 54 lines, one shared implementation for `make check` and the hook |
| T-17 | `tools/regen-guard-test.sh` | proves `sync` is unbuildable when `go-e2e` fails | Docker DAG | **KEEP** | 48 lines; the only control on validate-before-publish |
| T-18 | `tools/python-requirements.lock` | states the stdlib-only closure `host-python-gate` proves | — | **KEEP** | data, not code |

## 4.2 Unit class 2 — public Make targets

Twenty-one targets (`.PHONY` plus `.DEFAULT_GOAL`). **No Makefile change is proposed by M4.**

| target | job | partial or full | disposition | reason |
|---|---|---|---|---|
| `check` | **full working-tree acceptance** | full | **KEEP** | the one full join |
| `prove` | the complete proof gate | partial | **KEEP** | no M4 step touches it |
| `emit` | materialize witnesses + exercise the sink | partial | **KEEP** | |
| `e2e` | emit + pinned `go build ./...` + goldens | partial | **KEEP** | |
| `regenerate` | validate-before-publish republication | full (publication) | **KEEP** | |
| `regen-guard` | proves `regenerate` cannot publish unvalidated | partial | **KEEP** | |
| `audit-fresh` | forces `prover` + `go-e2e` to run, not report a cache hit | partial | **KEEP** | this audit used the same mechanism via `FIDO_PERF_COLD` |
| `fcb`, `claims`, `diet`, `names`, `hostpython` | one gate family each | **partial** | **KEEP** | each stays separately invocable; M4 changes only what runs inside them |
| `fcb-write` | regenerate every generated FCB view | writer | **KEEP** | its GNU-only `find -printf` is inside the declared host boundary |
| `fmt` | whitespace report | partial, non-gate | **KEEP** | |
| `perf` | the M2 serial diagnostic | diagnostic | **KEEP** | frozen by contract §9 |
| `profile` | rank one module's sentences | diagnostic | **KEEP** | |
| `prover-log`, `prove-errors` | readable proof diagnostics | diagnostic | **KEEP** | `prover-log` produced §3.1 |
| `pytools`, `builder` | image/builder prerequisites | infrastructure | **KEEP** | `PYTAG`'s over-keying is recorded and retained |
| `install-hooks` | one `git config` | setup | **KEEP** | |

Every partial target prints a scoped success line naming what it checked; none claims full acceptance. That
distinction holds today and no M4 step touches it.

## 4.3 Unit class 3 — named pre-commit stages

**No hook change is proposed by M4.**

| stage | source view | disposition | reason |
|---|---|---|---|
| export the index once (`git checkout-index --ignore-skip-worktree-bits --all`) | — | **KEEP** | one export, then everything reads it; the flag is load-bearing |
| recompute `PYTAG` from the **staged** Dockerfile + lock | staged | **KEEP** | over-keyed, cheap on a hit, and narrowing it inverts the risk |
| three shell policy gates on the export | exported index | **KEEP** | |
| `generated-mode-gate.sh` from the repo cwd | the real Git index | **KEEP** | mode is invisible in an export |
| the seven Python gate families on the export | exported index | **KEEP** | 14 container starts is the boundary's price; `M4-01/02/03` shrink what runs inside them |
| `buildx --target prover`, `--target go-e2e` | staged Buildx context | **KEEP** | |
| `--target generated-artifact` + `staged-generated-compare.sh` | staged + pristine | **KEEP** | |

## 4.4 Unit class 4 — Docker/Buildx stages, caches, source-view boundaries

**No Dockerfile stage, heredoc, COPY set or cache key changes.**

| unit | disposition | reason |
|---|---|---|
| `python-tools` | **KEEP** | 5 Dockerfile lines; the tag is over-keyed and retained (`M3-INVALIDATION`) |
| `rocq-builder` → `rocq-base` | **KEEP** | digest-pinned; builder/runtime split is right |
| `prover` | **KEEP** | unchanged by M4 |
| `profile` / `profile-log` | **KEEP** | diagnostic; export surface is the raw log only |
| `emit` | **KEEP** | |
| `generated-module` → `generated-artifact` | **KEEP** | content-addressed pristine layer; the byte-compare rests on it |
| `go-base` → `go-e2e` | **KEEP** | `go-base` exists so the digest appears once and can be primed outside a timed interval |
| `sync` | **KEEP** | the validate-before-publish DAG edge; `regen-guard` proves it |
| caches `fido-apt-pytools`, `-builder`, `-base`, `fido-opam` | **KEEP** | apt/opam layer caches, correctly `sharing=locked` |
| cache `fido-dune-rocq-9.2.0-$arch` (locked, shared by 3 stages) | **KEEP** | one compile reused; serialization is the right price |
| cache `fido-crossmnt-$arch` (private, emit) | **KEEP** | it *is* the cross-device test fixture |
| `.dockerignore` excluding `/go.mod` and `**/*.go` | **KEEP** | the exclusion makes the pristine independent of the committed bytes |

## 4.5 Unit class 5 — Dune aliases and proof-build units

| unit | disposition | reason |
|---|---|---|
| `dune build @install @all` | **KEEP** | one command builds theory and plugin; 16.4 s, 13% of the cold stage |
| `(rocq.theory (name Fido) (modules …))` — 16 modules | **KEEP** | `M3-DUNE-FANOUT`: `Compilable`'s downstream set is already 3; a split reduces nothing measured |
| `(library (name fido_emit) (private_modules sink))` | **KEEP** | `sink` private is why no external consumer can publish |
| `(rocq.pp (modules materialize))` | **KEEP** | |
| the certified-module coverage check (tracked root `.v` == `(modules …)`) | **KEEP** | costs 0.01 s and closes a real hole |

## 4.6 Unit class 6 — distinct gates

| gate | disposition | M4 / reason |
|---|---|---|
| readable `Print Assumptions` (`gate/Assumptions.v`, 540 lines / 535 distinct) | **SIMPLIFY** | `M4-08` duplicates and the four missing twins. Its 77 s cost is `M4-11`, unauthorized |
| whole-theory `Fido Audit Assumptions` | **KEEP** | 1.7 s for a strictly stronger guarantee |
| assumption self-tests A–E | **KEEP** | 2.2 s; each proves the audit is not fail-open |
| sealed-capability self-tests F–AG + meta + mint AB–AD + positive | **KEEP** | the 21 recomputed stage-1 loads are recorded in §3.1; the two-stage helper is simple and correct, and a cache in an adversarial gate needs an exact topology this plan does not have |
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
| `naming-gate.py:check_prose` | dominant measured cost — 25.4 s of 37.6 s profiled | **SIMPLIFY** | `M4-01` |
| `gate-mutation-test.py:run_mutant` | owns per-mutant tree copy and control selection | **SIMPLIFY** | `M4-02` |
| `fcb-reference-gate.py:scenario` | owns the per-control tree copy — 704 of 845 | **KEEP** | measured; `M4-02` removes the multiplier first |
| `claim-matrix-gate.py:ensure_closed_row` | owns the self-test precondition that blocked M3 | **SIMPLIFY** | repaired under `M3-A1` |
| `Dockerfile:sealed()` | owns a production proof-gate edge, recomputes its precondition 21× | **KEEP** | §3.1; no M4 change in this plan |

`Makefile:PYTAG` owns a cache key and was inventoried, but its disposition is **KEEP** (`M3-INVALIDATION`).

No other helper is inventoried. Functions, theorems and proof bodies are explicitly out of scope.
