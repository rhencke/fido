# Review Request

state: requested
review: Implementation Review
confirmation: no
confirmation_used: no
human_override: (M1 repair 1, authorized by Rob's upload of the blocking implementation review)
result: awaiting Rob's human M1 review
candidate: 71e70de20e11495ccb829130b6c021d9b00ce59c

contract: .review/M1_SOURCE_DIET.md
review_basis: .review/REVIEW_BASIS.md

**A human M1 review is requested for candidate `71e70de20e11495ccb829130b6c021d9b00ce59c`.** C4 is ACCEPTED under `C4-ACCEPT-39ea7e3` and M0
under `M0-ACCEPT-86a63db`. `.review/M1_OBLIGATION_MATRIX.tsv` reads 15 of 15 closed; `make claims` refuses to
let this file request review while any row is absent, duplicate, malformed or open.

Measured against the sealed baseline `068d3371ac3300303d6c7c99a97ed884182c81e4`:

| metric | baseline | candidate | delta |
|---|---:|---:|---:|
| repository bytes | 3,272,574 | 2,622,715 | -19.86% |
| deterministic archive bytes | 801,677 | 570,395 | -28.85% |
| `.v` comment bytes | 408,155 | 61,676 | -84.89% |
| `.v` comment physical lines | 4,332 | 708 | -83.66% |
| `.v` comment blocks | 1,464 | 708 | -51.64% |
| `.review` bytes outside the live FCB | 490,345 | 156,904 | -68.00% |
| root Markdown bytes | 158,291 | 142,981 | -9.67% |
| ledgered comment exceptions | — | 0 | the goal was zero |

The ledgers are the evidence, and one command reproduces every one of them from Git:

```text
python3 tools/source-diet.py --verify-m1-evidence \
  --baseline-ref 068d3371ac3300303d6c7c99a97ed884182c81e4 \
  --candidate-ref 71e70de20e11495ccb829130b6c021d9b00ce59c
```

It exports both trees and checks: the baseline seal and every sealed metric reproduce; every metric row equals
recomputation; every disposition row is byte-exact in both trees; every surviving Rocq declaration is identical
after removing exactly the ledgered ones; and every required metric moved the right way.

The repair the review asked for was to the evidence model, not to one row. The checker that accepted the first
candidate could not see an edit inside a surviving proof, a false ledger value or a false metric. It can now,
and each of those defects is a named control that fails when its rule is deleted.

M2, M3, M4, C5 Step 0 and C5 remain forbidden until Rob accepts M1. Automatic Codex review is disabled.
