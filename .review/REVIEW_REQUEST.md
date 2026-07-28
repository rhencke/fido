# Review Request

state: closed
review: Implementation Review
confirmation: no
confirmation_used: no
human_override: (M1 repair 3, authorized by Rob's upload of the third blocking implementation review)
result: M1 candidate 8ad80e6 BLOCKED by the third M1 implementation review
candidate: (none — M1 repair 3 is in progress)

contract: .review/M1_SOURCE_DIET.md
review_basis: .review/REVIEW_BASIS.md

**No review is requested.** The third M1 implementation candidate is blocked and its documentation freeze is
stale. C4 remains accepted under `C4-ACCEPT-39ea7e3` and M0 under `M0-ACCEPT-86a63db`.

The blocking finding is a lifetime defect, not a source defect: the permanent `make diet` path enforced the
M1 baseline, file disposition and code identity forever, so no later checkpoint could add a file or a Rocq
declaration. A checkpoint-exit proof is not a permanent language law. Repair 3 separates the permanent
source-comment policy from the M1 exit evidence.

`.review/M1_OBLIGATION_MATRIX.tsv` has the reopened rows; `make claims` refuses to let this file request
review while any row is open.

M2, M3, M4, C5 Step 0 and C5 remain forbidden. Automatic Codex review is disabled.
