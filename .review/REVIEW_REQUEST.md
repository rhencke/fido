# Review Request

state: requested
review: Implementation Review
confirmation: no
confirmation_used: no
human_override: (M1 repair 4, authorized by Rob's upload of the fourth blocking implementation review)
result: awaiting Rob's human M1 review
candidate: de6cf13f215e6c630fb267413315f584f675b264

contract: .review/M1_SOURCE_DIET.md
review_basis: .review/REVIEW_BASIS.md

**A human M1 review is requested for candidate `de6cf13f215e6c630fb267413315f584f675b264`.** C4 is ACCEPTED under `C4-ACCEPT-39ea7e3` and M0
under `M0-ACCEPT-86a63db`. Every required obligation in `.review/M1_OBLIGATION_MATRIX.tsv` is closed, and each
row now names the command that actually runs its evidence.

Repair 3's lifetime separation is unchanged. Repair 4 corrected the evidence map that separation invalidated:
six exit-only obligations still named `make diet`, `make fcb` or `make check` as the gate establishing them
after those paths deliberately stopped running that evidence. `Makefile:diet` now appears only on the four
permanent comment-policy rows it genuinely runs.

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
  --candidate-ref de6cf13f215e6c630fb267413315f584f675b264
```

The verifier proves: the baseline seal and every sealed metric reproduce; the candidate's metric table is
header-only; the four candidate-owned ledgers are byte-identical in the candidate and here; every change
since the candidate lies inside the five-file freeze overlay; every metric row equals recomputation; every
disposition row is exact in both trees; and every surviving top-level Rocq command is identical after
removing exactly the eight ledgered declaration units.

Measured against the sealed baseline `068d3371ac3300303d6c7c99a97ed884182c81e4`, generated from `.review/M1_METRICS.tsv`:

| metric | baseline | candidate | delta |
|---|---:|---:|---:|
| repository bytes | 3,272,574 | 2,667,378 | -18.49% |
| deterministic archive bytes | 801,677 | 584,157 | -27.13% |
| `.v` comment bytes | 408,155 | 59,370 | -85.45% |
| `.v` comment blocks | 1,464 | 662 | -54.78% |
| `.review` bytes outside the live FCB | 490,345 | 175,770 | -64.15% |

The canonical numbers are that table. Prose copying them is not authority — recorded as `M3-FRAGILE-PROSE`.

After acceptance the closeout can retire `M1_BASELINE.tsv`, `M1_METRICS.tsv`, `M1_FILE_DISPOSITION.tsv`,
`M1_DECLARATION_DELETIONS.tsv`, `M1_OBLIGATION_MATRIX.tsv` and this repair directive to Git history with no
functional gate edit. `M1_COMMENT_EXCEPTIONS.tsv` stays, because the permanent comment gate consumes it.

M2, M3, M4, C5 Step 0 and C5 remain forbidden until Rob accepts M1. Automatic Codex review is disabled.
