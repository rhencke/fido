# Review Request

state: requested
review: Implementation Review
confirmation: yes

contract: .review/NEXT_STEPS.md
contract_sha: 83c3989
review_basis: .review/REVIEW_BASIS.md

# Implementation Review only:
base_sha: fea649389ee52d442373c43ea2bdb3be2eca47db
head_sha: 42c536e33a70f6e3a6973190eca3086a23f3dc91

# Bounded confirmation only:
confirmation_of: bounded confirmation #2 (BLOCKING — F4 closed, F1/F2/F3 residual + F5) over 29872f5..b48b542
prior_findings: .review/C3_IMPL_REVIEW_FINDINGS.md
repair_base_sha: b48b542228e6164b04c1496809b780a186eb9485
repair_head_sha: 42c536e33a70f6e3a6973190eca3086a23f3dc91

## Rules

- Set `state: requested` only at an intentional review barrier.
- Use only `Contract Review` or `Implementation Review` in `review`.
- A confirmation keeps the same review type and sets `confirmation: yes`.
- Close the request after recording the review result.
- Ordinary Claude turns leave this file closed, so the stop hook returns immediately.
