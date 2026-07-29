# Review Request

state: closed
review: Implementation Review
confirmation: no
confirmation_used: no
human_override: (M2 Build Observatory, authorized by Rob's acceptance token `M1-ACCEPT-6524b43`)
result: M1 accepted; M2 implementation in progress
candidate: (none — the M2 candidate is named by its documentation-only freeze)

contract: .review/M2_BUILD_OBSERVATORY.md
review_basis: .review/REVIEW_BASIS.md

`.review/NEXT_STEPS.md` owns mutable checkpoint and candidate state. This file may pin the exact candidate
under human review, but it does not own mutable state. Canonical data rows carry no candidate identity.

M1 Source Diet is **ACCEPTED** at `6524b437bd7a7d6b2616563b8789e28a00c7af13` under Rob's disposition
`M1-ACCEPT-6524b43`. C4 is accepted under `C4-ACCEPT-39ea7e3` and M0 under `M0-ACCEPT-86a63db`. Git history
owns M1's contract, its obligation matrix and its evidence.

M2 Build Observatory is the sole active implementation work. Its contract is `.review/M2_BUILD_OBSERVATORY.md`
and its nineteen obligations are open in `.review/M2_OBLIGATION_MATRIX.tsv`. No review is requested: a review
cannot be requested while any required obligation is open, which the claim gate enforces rather than asserts.

M3, M4, C5 Step 0 and C5 remain forbidden. Automatic Codex review is disabled. Only Rob accepts M2.
