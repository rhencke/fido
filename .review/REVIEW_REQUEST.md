# Review Request

state: closed
review: Implementation Review
confirmation: no
confirmation_used: no
human_override: (M1 repair 4, authorized by Rob's upload of the fourth blocking implementation review)
result: M1 candidate c73925c BLOCKED by the fourth M1 implementation review
candidate: (none — M1 repair 4 is in progress)

contract: .review/M1_SOURCE_DIET.md
review_basis: .review/REVIEW_BASIS.md

**No review is requested.** The fourth M1 implementation candidate is blocked and its documentation freeze is
stale. C4 remains accepted under `C4-ACCEPT-39ea7e3` and M0 under `M0-ACCEPT-86a63db`.

Repair 3's lifetime separation was right and is unchanged. What was wrong is the evidence map: several
exit-only obligations still named `make diet`, `make fcb` or `make check` as the gate establishing them,
after repair 3 moved that evidence off those paths. The claim-matrix checker verifies that a named string
exists; it cannot verify that the named command runs the check. A human review had to catch it, and did.

The M1 exit evidence runs explicitly, and these are the exact commands:

```text
python3 tools/source-diet.py --m1-self-test
python3 tools/gate-mutation-test.py --m1
python3 tools/source-diet.py --verify-m1-evidence \
  --baseline-ref 068d3371ac3300303d6c7c99a97ed884182c81e4 \
  --candidate-ref <the M1 candidate>
```

`.review/M1_OBLIGATION_MATRIX.tsv` has the reopened rows; `make claims` refuses to let this file request
review while any row is open.

M2, M3, M4, C5 Step 0 and C5 remain forbidden. Automatic Codex review is disabled.
