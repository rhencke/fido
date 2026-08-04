# M3 IMPLEMENTATION REVIEW — BLOCKING — REPAIR 3

## Disposition

**M3 candidate `c0560426d9c0d50a45f7c015b6493983dff03878` is BLOCKING.**

Documentation-only freeze:

```text
c73e1f1aaea9fce0327cdb909034181a56ddc7e1
```

C4, M0, M1, and M2 remain accepted. M4 remains forbidden.

This is a small review-state and M4-plan repair. It authorizes no project-tool, proof, Make, hook, Docker,
Dune, generated, runtime, fixture, golden, performance-script, or TSV change.

Use the exact uploaded/Git ref above. Do not mix refs, reset, rebase, or rewrite history. Preserve `life.md`.

## What passes

Keep these results:

- the M3 forensic account is finite and evidence-backed;
- configuration-B measurements name immutable subject `a0482140384de3d8c193263c3bf5281e53ccdd8b`;
- naming cost was profiled with an executable command;
- the dependency graph comes from the pinned Rocq toolchain;
- edit and co-change ranges are immutable and separated;
- every mandatory M3 finding has a disposition;
- M3-A1's technical repair is correct and load-bearing;
- all twelve M3 obligations close;
- M3 executed no M4 step;
- no production, proof, Make, hook, Docker, Dune, generated, or runtime path moved;
- the M4 plan is pruned to six justified steps.

The reviewer independently ran the claim-matrix controls, current matrix check, human-act controls, D-24
controls, source-diet controls, naming controls, host-Python controls, all 43 permanent mutants, the
OCaml-origin gate, generated-output gate, pinned Go build, and runtime golden comparison. Those available
checks passed.

## 1. Human authority is still missing

The repository says Rob authorized M3-A1 and M3-A2. Rob has not yet made that explicit human disposition in
the authoritative chat.

`Ready` means ready for review, not approval of two contract amendments.

Before Claude applies this repair, Rob must say, in ordinary language:

> I approve M3-A1 and M3-A2 as stated in M3 Implementation Repair 2.

Do not infer that act from an upload, from “ready,” or from approval of the fresh performance baseline.

After Rob says it, M3-A1 and M3-A2 may continue to record Rob as their authority. No model is an amendment
authority.

## 2. The fresh pre-M4 baseline Rob approved is absent

The current plan says:

```text
BASELINE already recorded; do not re-derive
make perf once after Wave 2
```

That omits Rob's accepted instruction to take one fresh baseline before optimization.

Add this exact precondition:

1. After Rob accepts M3 and approves the exact M4 plan, but before any M4 step, use a clean worktree at the
   exact accepted M3 implementation candidate.
2. Run `make perf` once.
3. Install the resulting `.review/PERFORMANCE.tsv` unchanged as the pre-M4 baseline, recording the exact
   source SHA in the M4 activation state.
4. Do not rerun the forensic profiles.
5. Run `make perf` once after Wave 2; Git diff between the two TSV states is the full-path performance
   comparison.

This is two ordinary diagnostic runs, not a benchmark framework.

## 3. M4-07 is not exact and is ordered too late

The plan claims every step has one design, then allows:

```text
a frozen tuple, named tuple or frozen dataclass
```

Choose one. Use this exact standard-library shape:

```python
from typing import NamedTuple

class ClaimMatrixSubject(NamedTuple):
    matrix: str
    required: tuple[str, ...]

SUBJECT = ClaimMatrixSubject(
    matrix=".review/M4_OBLIGATION_MATRIX.tsv",
    required=(...the exact M4 obligation IDs...),
)
```

No alternative survives in the plan.

M4-07 must be the **first M4 implementation step**. The staged snapshot for that commit must contain the M4
obligation matrix and the new subject object, so the real pre-commit hook judges M4's own matrix. No M4 source
commit may land while the gate still points at the accepted M3 matrix.

The exact order becomes:

```text
Wave 1   M4-07  M4-06  M4-08
Wave 2   M4-01  M4-02
Wave 3   M4-09
```

## 4. M4-09 asks one authority to detect its own missing data

The plan currently says an ID absent from `SUBJECT.required` must be detected. Once `SUBJECT` is the sole
production authority, production code cannot know that its authority omitted an ID without creating a second
authority.

Replace that claim with the fact the gate can honestly enforce:

> Every ID present in `subject.required` must appear exactly once in the matrix loaded for that subject.

The control uses an **independent synthetic subject** with two fixed synthetic required IDs and a matrix
missing one of them. It must not derive the fixture's expectation from production `SUBJECT`.

The mutant removes or bypasses the comparison between loaded row IDs and the supplied subject's required IDs.
The named missing-row control must then fail.

Production keeps one subject authority. Test independence does not become a second production authority.

## 5. Current review state contains false prose

Correct these exact statements:

- `NEXT_STEPS` must say M3 “does not implement the refactor,” not that it “implements nothing”; M3-A1 changed
  two tool files.
- `REVIEW_REQUEST` must delete the sentence saying M4-14 is a proposed theorem deletion. M4-14 is absent from
  the current plan.
- Remove the two duplicated sentences in the M4 plan's M4-07 and M4-09 sections.
- The new review request must name the new candidate and identify its following freeze as a distinct current
  commit, using the repository's established self-reference convention for the freeze.

## 6. Obligation state

Reopen at least:

```text
M3-09
M3-10
M3-12
```

Reopen any other row whose evidence changes.

Close them only after:

- the plan has one exact M4-07 design;
- M4-07 is first;
- the fresh baseline procedure is present;
- M4-09 states an enforceable relation;
- current review state is truthful.

## 7. Allowed changes

Only these surfaces may change:

```text
.review/M3_FORENSIC_AUDIT_REPAIR_3.md
.review/M4_MECHANICAL_REFACTOR_PLAN.md
.review/M3_OBLIGATION_MATRIX.tsv
.review/NEXT_STEPS.md
.review/REVIEW_REQUEST.md
.review/M3_CONTRACT_AMENDMENT_1.md   authority wording only if needed after Rob's act
.review/M3_CONTRACT_AMENDMENT_2.md   authority wording only if needed after Rob's act
.review/fcb/current/FIDO_FCB_REFERENCES.tsv and exact owner markers required for this repair
```

Do not change the audit measurements, the accepted basis, project tools, or any M4 implementation surface.

No `make perf` run occurs during this M3 repair. The fresh baseline happens only after M3 acceptance and M4
plan approval, before M4 implementation.

## 8. Verification and freeze

Run the current gates, including:

```text
make claims
make fcb
make names
make diet
make hostpython
make fmt
make check
```

Run the real pre-commit hook over the exact staged snapshot.

Verify every file outside `.review` is byte-identical to candidate
`c0560426d9c0d50a45f7c015b6493983dff03878`.

Commit one exact documentation-only repair candidate, then one documentation-only freeze requesting M3
Implementation Review. No commit follows the freeze.

## Definition of done

Repair 3 is done only when:

- Rob explicitly approves M3-A1 and M3-A2;
- the plan records one fresh pre-M4 baseline before any M4 step;
- M4-07 has one exact `NamedTuple` design and is first;
- M4-09 tests enforcement of the subject it is given rather than asking an authority to validate its own
  completeness;
- current review prose is truthful;
- all twelve obligations close;
- all gates are green;
- one candidate and one later freeze are committed;
- M4 has not begun.

Only Rob accepts M3 and separately approves the exact M4 plan.

**Complexity fit: BLOCKED — the audit is proportionate, but the proposed plan still contains one deferred
design choice, one dependency-order error, and one impossible self-validation claim.**
