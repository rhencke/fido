# Review Request

state: closed
review: Contract Review
confirmation: no

contract: .review/NEXT_STEPS.md
contract_sha: REPLACE_WITH_COMMIT_SHA
review_basis: .review/REVIEW_BASIS.md

# Implementation Review only:
base_sha: N/A
head_sha: N/A

# Bounded confirmation only:
confirmation_of: N/A
prior_findings: N/A
repair_base_sha: N/A
repair_head_sha: N/A

## Rules

- Set `state: requested` only at an intentional review barrier.
- Use only `Contract Review` or `Implementation Review` in `review`.
- A confirmation keeps the same review type and sets `confirmation: yes`.
- Close the request after recording the review result.
- Ordinary Claude turns leave this file closed, so the stop hook returns immediately.
