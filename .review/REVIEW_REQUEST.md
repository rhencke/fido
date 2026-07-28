# Review Request

state: requested
review: Implementation Review
confirmation: no
confirmation_used: no
human_override: (M1 repair 5, authorized by Rob's upload of the fifth blocking implementation review)
result: awaiting Rob's human M1 review
candidate: 6524b437bd7a7d6b2616563b8789e28a00c7af13

contract: .review/M1_SOURCE_DIET.md
review_basis: .review/REVIEW_BASIS.md

**A human M1 review is requested for candidate `6524b437bd7a7d6b2616563b8789e28a00c7af13`.** C4 is ACCEPTED under `C4-ACCEPT-39ea7e3` and M0
under `M0-ACCEPT-86a63db`. Every required obligation in `.review/M1_OBLIGATION_MATRIX.tsv` is closed.

Repair 4's evidence map is unchanged. Repair 5 removed the last prose that violated M1's own rule that Git
owns archaeology: `NEXT_STEPS` recited four superseded candidates, their freezes and their failure narratives
while asserting in the same block that Git owns them, and the current unsupported boundary opened SR-005 and
SR-006 by narrating how an earlier draft had been wrong. Current documents now state what is true now. Neither
restriction was weakened, and the SR-009 float boundary is bounded by ADR-0002's resolution rather than by a
C4 repair that ended two checkpoints ago.

**Permanent, run by every build and every commit:**

```text
make diet          # --self-test, --check, --wiring
```

**M1 exit evidence, run explicitly for this review only:**

```text
python3 tools/source-diet.py --m1-self-test
python3 tools/gate-mutation-test.py --m1
python3 tools/source-diet.py --verify-m1-evidence \
  --baseline-ref 068d3371ac3300303d6c7c99a97ed884182c81e4 \
  --candidate-ref 6524b437bd7a7d6b2616563b8789e28a00c7af13
```

The verifier proves: the baseline seal and every sealed metric reproduce; the candidate's metric table is
header-only; the four candidate-owned ledgers are byte-identical in the candidate and here; every change
since the candidate lies inside the five-file freeze overlay; every metric row equals recomputation; every
disposition row is exact in both trees; and every surviving top-level Rocq command is identical after
removing exactly the eight ledgered declaration units.

Measured against the sealed baseline `068d3371ac3300303d6c7c99a97ed884182c81e4`, generated from `.review/M1_METRICS.tsv`:

| metric | baseline | candidate | delta |
|---|---:|---:|---:|
| repository bytes | 3,272,574 | 2,663,850 | -18.60% |
| deterministic archive bytes | 801,677 | 583,297 | -27.24% |
| `.v` comment bytes | 408,155 | 59,370 | -85.45% |
| `.v` comment blocks | 1,464 | 662 | -54.78% |
| `.review` bytes outside the live FCB | 490,345 | 172,015 | -64.92% |

The canonical numbers are that table. Prose copying them is not authority — recorded as `M3-FRAGILE-PROSE`.

After acceptance the closeout can retire `M1_BASELINE.tsv`, `M1_METRICS.tsv`, `M1_FILE_DISPOSITION.tsv`,
`M1_DECLARATION_DELETIONS.tsv`, `M1_OBLIGATION_MATRIX.tsv` and this repair directive to Git history with no
functional gate edit. `M1_COMMENT_EXCEPTIONS.tsv` stays, because the permanent comment gate consumes it.

M2, M3, M4, C5 Step 0 and C5 remain forbidden until Rob accepts M1. Automatic Codex review is disabled.
