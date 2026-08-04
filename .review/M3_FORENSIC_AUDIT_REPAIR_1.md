# M3 FORENSIC AUDIT REVIEW — BLOCKING — REPAIR 1

## 0. Disposition and exact review basis

**M3 audit state `9420ae0062fea315d1f63f996044886f2655dd2d` is BLOCKING.**

This is not an implementation candidate or a documentation-only freeze. Claude Code stopped correctly after
discovering a conflict between the frozen M3 contract and the claim-matrix gate.

Exact basis:

```text
Uploaded snapshot:
  fido-main - 2026-08-04T110930.220.zip

Uploaded Git head / stopped M3 audit state:
  9420ae0062fea315d1f63f996044886f2655dd2d

Accepted M3 contract activation:
  0b7fd86825936c37f31ef83879574d526d548122

Accepted M3 review-basis installation:
  238d69ce93fb0109fd4ba8e311c95b3044575378

Accepted M2 implementation candidate:
  9814db77ead0cfcfd8ff268303ba2afedef71197
```

Use every code, FCB, contract, gate, audit, plan, and current-state document from this exact ref. Do not mix
refs, reset, rebase, or rewrite history.

C4, M0, M1, and M2 remain accepted.

**M3 Forensic Audit Repair 1 is the sole permitted work.**

M4 remains forbidden. C5 Step 0, C5, and feature work remain forbidden.

Use:

```text
/loop 3m
```

Continue until this exact repair is complete or a real contract conflict blocks progress. When complete or
genuinely blocked, notify Rob with the notification tool.

---

## 1. What the audit established well

Keep the forensic findings and their evidence where corrected below.

The audit found the dominant costs:

```text
accepted serial hot make check:   63.680 s
  names:                          22.310 s
  fcb:                            28.580 s
  prove:                           1.410 s
  e2e:                             1.340 s
```

It correctly showed that ordinary hot feedback is dominated by Python policy work rather than Rocq.

It also found strong root causes:

1. `naming-gate.py` constructs constant regexes inside the line/name loop.
2. `gate-mutation-test.py` runs entire gate self-tests for mutants whose acceptance checks only named controls.
3. Three self-test implementations repeatedly copy the whole tree.
4. Twenty-five source-diet replay mutants protect M1 modes no live command invokes.
5. The source-diet replay path names deleted evidence files.
6. `gate/Assumptions.v` contains five duplicate `Print Assumptions` commands.
7. Four Complex imaginary-component readable surfaces are absent.
8. The readable assumption gate costs about 77 seconds while the whole-theory audit costs about 1.7 seconds.
9. Sealed-capability tests recompute a stage-one load/sentinel precondition for repeated identical pairs.
10. Working-tree and staged-index execution are distinct source views and must not be collapsed.
11. Project Python remains containerized.
12. M3 changed no production, proof, build, tool, generated, or runtime path before it encountered the contract
    conflict.

The audit and the proposed M4 plan are useful drafts. They are not yet accepted M3 deliverables.

---

## 2. Contract Amendment M3-A1 — exact claim-matrix acceptance-dependency repair

### 2.1 Conflict

The frozen M3 contract requires:

```text
all twelve M3 obligations closed
all current gates green
```

It also forbids M3 from changing any project tool.

Those requirements are jointly unsatisfiable because `tools/claim-matrix-gate.py` cannot construct its
`rename_named_surface` self-test when every closed row legitimately has an `unsupported-boundary`
implementation cell.

`ensure_closed_row` guarantees only that some row is closed. The rename control needs a closed row whose
implementation names a renameable `.v` declaration or Python `def`/`class`. The synthetic row already exists
for this purpose, but the helper does not append it when a non-renameable closed row exists.

Claude correctly stopped rather than fabricating an implementation surface or accepting M3 with an open matrix.

### 2.2 Accepted amendment

Install:

```text
.review/M3_CONTRACT_AMENDMENT_1.md
```

with the following exact effect:

> M3 may change `tools/claim-matrix-gate.py` and the claim-matrix entries in
> `tools/gate-mutation-test.py` only to repair the self-test precondition which prevents a documentation-only
> checkpoint from closing its obligation matrix. No other project-tool change is authorized in M3.

This amendment supersedes only:

- M3 contract §9’s prohibition on project-tool changes, for these exact files and this exact defect;
- M3-11’s absolute “no tool change” claim.

Replace M3-11 with a claim equivalent to:

> M3 changes no production, proof, Make, hook, Docker, Dune, generated, or runtime path. Its only project-tool
> change is the reviewed claim-matrix self-test precondition repair required to close a documentation-only
> matrix.

No other contract clause changes.

### 2.3 Exact implementation

Use the existing topology. Do not invent a second fixture system.

A suitable shape is:

```python
def ensure_closed_row(
    work: Path,
    *,
    require_builder: bool = False,
    require_declaration: bool = False,
) -> None:
    ...
```

A closed row serves `require_declaration=True` only when its implementation field contains a current,
renameable `.v` declaration or Python `def`/`class` under the same rule `rename_named_surface` uses.

`rename_named_surface` calls:

```python
ensure_closed_row(work, require_declaration=True)
```

The synthetic row is appended only when no live closed row satisfies the exact required shape.

The helper and rename control must share one predicate for “renameable implementation entry.” Do not duplicate
the regex and path-selection meaning in two places.

### 2.4 Controls and mutation

Add exact controls for:

- closed rows exist but every implementation cell is `unsupported-boundary`: the synthetic row is appended and
  the rename scenario executes;
- one closed row carries a renameable declaration: no synthetic row is added;
- one closed row carries a Make target or shell symbol: it does not satisfy the declaration precondition;
- a documentation-only all-closed matrix passes the complete claim-matrix self-test;
- a genuinely renamed referenced declaration still fails for the intended reason.

Add one exact mutation entry which removes the `require_declaration` effect. Its named control must fail for the
intended reason.

Do not broaden this amendment into general claim-gate redesign.

---

# 3. Blocking finding A — measured evidence is not tied to exact refs and reproducible commands

## 3.1 Contract violated

This violates M3-04, M3-05, M3-09, M3-10, the accepted review basis, and the M3 contract requirement that
every measured fact name:

```text
exact Git ref or range
exact command
source view
cache condition
observed result
```

## 3.2 Configuration B has no exact subject ref

The audit defines configuration B as:

```text
make <target>, builder fido-builder, default Make parallelism, this host
```

but does not name the exact Git ref whose tools and build files were measured.

Some measurements were taken while the audit documents were still changing. Tool bytes may have been unchanged,
but that is not recorded as evidence.

### Required correction

After landing the narrow claim-matrix repair in one commit, use that exact full SHA as the subject of all
configuration-B measurements retained in the final audit.

For each measurement, state:

```text
ref
command
source view
builder
Make concurrency
cache condition
host idle or contended
observed result
```

Rerun only the targeted measurements the final M4 steps actually need. Do not rerun the full serial performance
snapshot.

## 3.3 The naming profile command is a placeholder

The recorded command contains:

```text
<cProfile wrapper around runpy.run_path("tools/naming-gate.py")>
```

That is not an executable command another reviewer can reproduce.

Replace it with the exact command actually used.

## 3.4 The naming counts are wrong

The current source has:

```text
OLD_MODULES          13
OLD_NAMES            73
OLD_FILES             5
DELETED_SURFACES     69
core retired names  160
OLD_QUALIFIED         5
RETIRED_COMPOUNDS    20
```

The audit states `OLD_MODULES 18`, `OLD_NAMES 78`, and 170 core names.

An independent profile of the current code also produced counts different from the audit’s recorded totals.

Rerun and correct:

```text
table cardinalities
scanned file and line counts
re.escape call count
re.search call count
wall time
```

Do not retain hand-copied counts which disagree with the exact ref.

## 3.5 A mutable Git range is not exact evidence

Replace:

```text
git log 39ea7e3..HEAD
```

with a full immutable end SHA.

Every history range in the final audit must use full immutable endpoints.

---

# 4. Blocking finding B — the real dependency and co-change evidence is incomplete

## 4.1 The Dune/Rocq graph was reconstructed from source imports

The audit calls its table “the real Dune/Rocq graph” and derives edges from `From Fido Require` declarations.

The frozen M3 contract explicitly forbids reconstructing a build graph from a weaker source when Dune or the
toolchain can report it.

### Required correction

Use the pinned Dune/Rocq toolchain’s own dependency output from the exact measurement ref.

A temporary diagnostic command is allowed. Do not add a permanent graph tool or Docker stage.

Record:

```text
exact command
exact ref
raw toolchain output location during the run
normalized adjacency in the audit
critical path
downstream rebuild set for each current module
```

The final audit may explain how source imports relate to the toolchain graph, but the imports are not the graph’s
authority.

## 4.2 Co-change groups are absent

The contract requires edit frequency **and co-change groups** over separated exact ranges.

The audit supplies per-file touch counts only.

### Required correction

For each accepted exact Git range, add a concise co-change result:

```text
files or units changed together
count
what current M4 decision, if any, the group supports
```

Keep semantic/proof development separate from the M-series tooling/documentation campaign.

Do not build a permanent history analyzer. Use one temporary command in the pinned environment and record the
exact command and immutable range.

---

# 5. Blocking finding C — the proposed M4 plan is not complete or implementation-ready

## 5.1 `M4-09` is missing

The audit assigns these findings to `M4-09`:

- claim-matrix mutation coverage;
- closure-ledger-view mutation coverage;
- tool-complexity disposition.

`OPEN_QUESTIONS` also calls the blocking claim-matrix repair work pulled forward from `M4-09`.

The M4 plan contains no `M4-09` step.

It claims thirteen steps but defines twelve headings.

### Required correction

Add one real `M4-09` step.

Because the narrow `ensure_closed_row` repair is pulled into M3 by Amendment M3-A1, M4-09 owns only the broader
load-bearing coverage work which remains after that repair.

The revised step must name the exact root helpers to mutate in:

```text
tools/claim-matrix-gate.py
tools/closure-ledger-view.py
```

For each helper, name the invariant it owns and the existing or new control expected to fail when that invariant
is removed.

Do not promise mutation coverage for every helper merely because it exists. Cover the root facts on which accepted
claims depend.

## 5.2 Multiple steps contain unresolved design alternatives

An implementation-ready plan cannot tell Claude to choose during M4.

Current unresolved alternatives include:

- M4-07: derive the matrix path or keep the constant;
- M4-07: add a new tool-path checker or fall back to deleting stale prose;
- M4-03: restore files or use copy-on-write;
- M4-02: selective controls or keep whole self-tests;
- M4-10: implement the cache-key narrowing if it can be shown safe, otherwise drop it;
- M4-12: choose one unspecified shell-file mode.

Select one exact design for every retained step before M3 review.

No fallback branch survives in the accepted M4 plan.

---

# 6. Blocking finding D — prune M4 to the smallest justified mechanical plan

Apply D-30 to the proposed plan now, before implementation.

## 6.1 Delete M4-04 from this M4 plan

“One container start per source view” requires restructuring both Make and the staged hook while preserving:

- separate public targets;
- exact staged copies;
- gate-specific failures;
- current performance checkpoint boundaries;
- source-view separation.

The plan does not contain the exact new graph which establishes those requirements. It proposes a framework-sized
batching change to recover an estimated container-start floor after the two dominant gates are already being
optimized directly.

Delete M4-04 from M4.

Record the container-start cost as measured evidence for a later optimization only if the post-M4 hot path still
justifies it.

## 6.2 Delete M4-05 from this M4 plan

The five Python tools do not all ask the same enumeration question or select the same files. Making the
hyphenated `worktree-list.py` the shared owner requires a new import/API topology which the audit has not proved
preserves each gate’s exact source view and selection.

Delete M4-05 from M4.

Retain each current enumeration unless a later contract proves one exact shared relation.

## 6.3 Delete M4-10 from this M4 plan

`PYTAG` currently hashes the whole Dockerfile. A hit costs about 170–210 ms. Narrowing the key requires a
fail-closed Dockerfile-stage extractor in both Make and the hook and creates the greater risk of a stale Python
image.

The current plan itself says to drop the step if safety cannot be shown. Under D-30, do not build that parser for
this measured benefit.

Delete M4-10.

## 6.4 Delete M4-12 from this M4 plan

The audit disposition for the host-shell boundary is:

```text
KEEP, no M4 change
```

M4-12 then changes GNU `find` usage and normalizes modes for host portability not required by the accepted host
boundary.

Delete M4-12.

Mode or portability work requires its own current requirement, not visual tidiness.

## 6.5 Narrow M4-07

Keep only:

- delete the stale M2 matrix path from the claim-gate docstring;
- delete the nonexistent naming-gate exclusion.

Keep `TSV_REL` as the one current claim-matrix subject authority for now.

Do not add a generic “tool prose path” rule to `host-python-gate.py`. That would create a weak path scanner to
support two stale strings which deletion already fixes.

## 6.6 Keep the direct, justified steps

The revised M4 plan may retain, after correction:

```text
M4-01  compile naming patterns once
M4-02  run each mutant against its exact named controls
M4-03  remove repeated whole-tree copies with one selected isolation design
M4-06  delete dead M1 replay modes and dormant mutants
M4-07  delete the two exact stale strings/exclusions only
M4-08  repair readable-assumption duplicates and four missing twins
M4-09  add exact root-helper mutation coverage
M4-13  hoist the repeated sealed-test load/sentinel precondition
```

`M4-11` remains unauthorized pending Rob’s answer to Q-M3-01 and is not counted as an approved M4 step.

## 6.7 Select the exact M4-02 and M4-03 designs

For M4-02, select the filtered-control design and state it exactly:

- every gate with mutation entries accepts an exact repeated control-label selector;
- an unknown label and an empty selected set fail closed;
- the mutation harness passes only the mutant’s named expected controls;
- the unfiltered self-test remains the ordinary complete gate self-test;
- each mutant still must exit nonzero and report every expected control label.

For M4-03, inspect each affected self-test and select one restoration design. The plan must name:

```text
the one pristine fixture owner
which paths each control may mutate
how those paths are restored
how created and deleted paths are handled
the control proving the next scenario sees the pristine state
```

Do not leave “restore or copy-on-write” to M4.

---

# 7. Blocking finding E — verification repeats the exact work the audit calls waste

The plan says every step runs:

```text
make check
make fcb
make claims
make names
make diet
make hostpython
make fmt
real pre-commit hook
```

`make check` already runs `fcb`, `claims`, `names`, `diet`, and `hostpython`.

The separate invocations repeat the same working-tree work without adding a source view.

### Required correction

For each M4 step:

1. run the directly affected target or control during development;
2. before the step commit, run:
   ```text
   make check
   make fmt
   ```
3. commit through the real pre-commit hook over the staged snapshot.

Run `make regenerate`, `make regen-guard`, and `make audit-fresh` only at the wave or final boundaries named by
the revised plan, unless a step directly changes those paths.

This preserves working-tree and staged-index evidence without paying twice for the same working-tree target.

---

# 8. Blocking finding F — two audit conclusions need a finite, stronger classification

## 8.1 `M3-COMPILABLE-SURFACES`

The audit concludes that all 374 ungated `Compilable.v` theorem-like declarations stay because the whole-theory
assumption audit covers them.

Assumption closure does not establish that each declaration is a required public guarantee, proof dependency,
or live internal fact. The finding’s original question was broader than axiom freedom.

Do not inventory 374 theorems one by one.

Use a finite group-level classification:

```text
named by a public theorem or capability contract
reachable as a proof dependency from retained public surfaces
used by production/extraction/fixtures/gates
otherwise consumer-free candidate for deletion
```

Record group counts and exact search method. Any consumer-free candidates become exact M4 deletion entries or an
evidence-backed retained boundary.

Do not keep an entire theorem family merely because it is axiom-free.

## 8.2 Dune split rationale

The audit says splitting a certified module is outside M4’s mechanical remit.

Governance D-27 explicitly allows M4 to refactor proof units when M3 evidence and Rob’s approved plan justify it.

The current KEEP conclusion may remain because:

- `Compilable.v` recompiles in about 6.5 seconds;
- no sentence dominates;
- higher-value hot-path changes exist;
- a split would create substantial proof-source churn.

Correct the rationale. Do not claim the change is categorically outside M4.

---

# 9. Q-M3-01 — nonblocking human decision

Keep Q-M3-01 open and nonblocking.

The default remains no change.

The reviewer’s recommendation, if Rob chooses to decide now, is:

```text
Option 2:
keep the readable gate, but move it from ordinary make prove / make check to audit-fresh and checkpoint-freeze
verification; keep the strictly stronger whole-theory audit on ordinary acceptance.
```

Do not place M4-11 into the approved M4 plan without Rob’s explicit disposition.

M3 can close without this answer.

---

# 10. Obligation matrix

After Amendment M3-A1 and the forensic corrections, close the twelve rows with exact evidence.

Each row must name its actual evidence rather than repeating one generic sentence.

At minimum:

```text
M3-01  Governance/NEXT_STEPS exact active state
M3-02  finite audit table classes and source-view ownership
M3-03  exact working-tree, staged, Buildx, Dune/Rocq, proof, e2e and publication graph
M3-04  corrected exact-ref timing evidence
M3-05  toolchain dependency graph, immutable edit ranges, co-change groups, cache evidence
M3-06  D-30 dispositions for every accepted audit unit
M3-07  every stable finding mapped to an existing exact M4 step or KEEP reason
M3-08  preserved source-view and full/partial distinctions
M3-09  revised exact, pruned, implementation-ready M4 plan
M3-10  exact baseline and post-change procedure for every retained M4 optimization
M3-11  exact reviewed claim-gate repair as the sole M3 tool change; every other path unchanged
M3-12  one exact candidate and later documentation-only freeze; M4 forbidden
```

For documentation-only evidence cells, use honest current evidence surfaces. Do not fabricate code declarations.

---

# 11. Allowed changes

This repair may change:

```text
.review/M3_CONTRACT_AMENDMENT_1.md
.review/M3_AUDIT.md
.review/M4_MECHANICAL_REFACTOR_PLAN.md
.review/M3_OBLIGATION_MATRIX.tsv
.review/NEXT_STEPS.md
.review/OPEN_QUESTIONS.md
.review/REVIEW_REQUEST.md
.review/REVIEW_BASIS.md, only to cite the accepted amendment and this review
FCB/human-act references required by those files
tools/claim-matrix-gate.py, only the exact self-test precondition repair
tools/gate-mutation-test.py, only the exact mutation entry for that repair
```

Temporary untracked diagnostics are permitted.

It may not change:

- Makefile recipes or dependencies;
- pre-commit behavior;
- Dockerfile stages or cache keys;
- Dune files;
- any other tool;
- Rocq code or proof structure;
- OCaml transport;
- generated Go;
- fixtures or goldens;
- the no-host-Python boundary;
- `tools/perf.sh` or `.review/PERFORMANCE.tsv`;
- `life.md`;
- any M4 production step.

If corrected evidence exposes another conflict with the frozen contract, stop and name it. Do not edit around it.

---

# 12. Required work order

1. Install this file as the sole active M3 repair authority.
2. Install and record M3 Contract Amendment M3-A1.
3. Reopen or retain open every affected obligation.
4. Implement the exact claim-matrix self-test precondition repair and mutation.
5. Commit that narrow amendment/repair so targeted measurements have one immutable subject ref.
6. Rerun only the required exact-ref configuration-B measurements.
7. Correct naming cardinalities and replace the profile placeholder with the real command.
8. Replace every mutable Git range endpoint.
9. Obtain the real Dune/Rocq dependency graph from the pinned toolchain.
10. Add separated co-change evidence.
11. Finish the finite group-level `Compilable.v` surface classification.
12. Rewrite the M4 plan:
    - add exact M4-09;
    - remove M4-04, M4-05, M4-10, and M4-12;
    - narrow M4-07;
    - select exact M4-02 and M4-03 designs;
    - remove fallback branches;
    - remove duplicated per-step verification;
    - keep M4-11 unauthorized.
13. Close every matrix row with its real evidence.
14. Run all required gates.
15. Commit one exact M3 implementation candidate.
16. Add one later documentation-only freeze requesting M3 Implementation Review.
17. Notify Rob.

Do not start any M4 step.

---

# 13. Verification

Before the candidate:

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

- the claim-matrix self-test passes when all twelve M3 rows are closed and all implementation cells are honest
  documentation-only boundaries;
- the new claim-gate mutant is load-bearing;
- no other tool byte differs from the accepted M3 contract activation;
- every measurement names its exact ref and executable command;
- the Dune/Rocq graph comes from the pinned toolchain;
- co-change groups are present over immutable ranges;
- every M4 step ID cited by the audit exists in the plan;
- the plan contains no “or,” “fallback,” “if review judges,” or “drop this step” design branch;
- the plan contains only the retained exact steps;
- Q-M3-01 remains nonblocking and M4-11 remains unauthorized;
- every `.v`, OCaml, generated Go, fixture, golden, Makefile, Dockerfile, Dune file, hook, perf script, and TSV byte
  is unchanged;
- generated hashes remain:

```text
go.mod
d8f8d4f62b5b574067a4e4bf64a298bbe2cb5bc9a28d8f9c321c776e838cf1fa

main.go
b6765619f969e7fd85b4998616d8a515c5a2c0e2d397c3ee915718f35fbc48de
```

- the whole-theory assumption audit remains green;
- M4, C5 Step 0, and C5 did not begin.

Docker, Rocq, Dune, extraction, and the staged hook must be run in the repository’s pinned environment before the
freeze. Do not substitute a host toolchain.

---

# 14. Definition of done

M3 Forensic Audit Repair 1 is complete only when:

- Amendment M3-A1 makes the matrix closable without fabricated implementation evidence;
- the exact claim-matrix repair is the only M3 project-tool change;
- all retained measurements are reproducible at immutable refs;
- the naming evidence matches the current source;
- the dependency graph comes from Dune/Rocq;
- edit frequency and co-change evidence are both present over separated immutable ranges;
- every mandatory finding has an existing exact M4 owner or an evidence-backed KEEP disposition;
- the M4 plan contains no missing step, unresolved alternative, fallback, or placeholder;
- the M4 plan is pruned to machinery its real jobs justify;
- the `Compilable.v` surfaces receive a finite group-level current-purpose classification;
- all twelve M3 obligations close;
- every current gate is green;
- one exact M3 candidate is followed by one documentation-only freeze;
- no commit follows the freeze;
- Claude notifies Rob.

Only Rob accepts M3 and separately approves the final exact M4 plan.

**Complexity fit: BLOCKED — the forensic findings are valuable, but the evidence is not yet fully reproducible
and the proposed M4 plan contains missing, alternative, and unjustified machinery.**
