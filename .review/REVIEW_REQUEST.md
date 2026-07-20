# Review Request

state: requested
review: Implementation Review
confirmation: yes

contract: .review/NEXT_STEPS.md
contract_sha: 83c3989
review_basis: .review/REVIEW_BASIS.md

# Implementation Review only:
base_sha: fea649389ee52d442373c43ea2bdb3be2eca47db
head_sha: b48b542228e6164b04c1496809b780a186eb9485

# Bounded confirmation only:
confirmation_of: bounded confirmation #1 (BLOCKING — F4 closed, F1/F2/F3 open deeper + F5) over 1180b49..29872f5
prior_findings: .review/C3_IMPL_REVIEW_FINDINGS.md
repair_base_sha: 29872f5f17555da378f7744905c74482b782540f
repair_head_sha: b48b542228e6164b04c1496809b780a186eb9485

## Rules

- Set `state: requested` only at an intentional review barrier.
- Use only `Contract Review` or `Implementation Review` in `review`.
- A confirmation keeps the same review type and sets `confirmation: yes`.
- Close the request after recording the review result.
- Ordinary Claude turns leave this file closed, so the stop hook returns immediately.
