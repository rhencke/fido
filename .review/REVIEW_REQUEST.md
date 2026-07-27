# Review Request

state: requested
review: Implementation Review
confirmation: no
confirmation_used: no
human_override: (repair 20 — see .review/C4_IMPLEMENTATION_REPAIR_20.md)
result: awaiting Rob's human C4 Implementation Review
candidate: 0d0036c23195b3996d957f9872ad0188666a3677

contract: .review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md
review_basis: .review/REVIEW_BASIS.md

**A human C4 Implementation Review is requested for candidate `0d0036c23195b3996d957f9872ad0188666a3677`.**
Both repair-20 blocker classes are closed: D-24 corpus membership is now data rather than a Python constant,
and A005 is judged over Rocq statements rather than physical lines. The whole-system closure audit is
`.review/C4_REPAIR_20_CLOSURE_AUDIT.md` and the obligation matrix is
`.review/C4_REPAIR_20_OBLIGATION_MATRIX.tsv`, which reads 12 of 12 closed — `make claims` refuses to let this
file request review while any obligation is open.

Both defects were reproduced against the previous candidate before anything was edited, and both repairs were
mutation-tested by reverting them, so every control covering them has been watched failing.

C4 is NOT accepted; only Rob accepts it. C5, checkpoint-definition Step 0, M1–M4 implementation, post-C4
features, the broad source cleanup and proof-module partitioning remain forbidden. Automatic Codex review is
disabled.
