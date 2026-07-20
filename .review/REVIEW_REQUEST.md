# Review Request

state: closed
review: Implementation Review
confirmation: no

contract: .review/NEXT_STEPS.md
contract_sha: 83c3989
review_basis: .review/REVIEW_BASIS.md

# Implementation Review only:
base_sha: fea649389ee52d442373c43ea2bdb3be2eca47db
head_sha: 1180b49ea0aef4ca0f17af257d5008763391ca7c
# Implementation Review #1 verdict: BLOCKING (5 findings F1-F5, recorded in
# .review/C3_IMPL_REVIEW_FINDINGS.md). Closed while repairing all as ONE batch; a
# bounded confirmation (confirmation: yes) will be requested after full re-verification.

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
