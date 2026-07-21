# Review Request

state: closed
review: Implementation Review
confirmation: yes
confirmation_used: no
human_override: C3-semantic-prose-closeout-1

contract: .review/C3_FRESH_IMAGE_LITERAL_BUILD_PLAN.md
contract_sha256: a13779c2e55c679e461e857d019eeae6adef27b0666876ed0cac92833814f212
repair_directive: .review/C3_SEMANTIC_PROSE_CLOSEOUT.md
review_basis: .review/REVIEW_BASIS.md

# Prior result: the C3-final-cleanup-1 bounded confirmation returned BLOCKING on the tracked-tree prose sweep
# alone (the runner, package-import proofs, gate 386, architecture, and size were closed).  Rob's
# `.review/C3_SEMANTIC_PROSE_CLOSEOUT.md` (human_override C3-semantic-prose-closeout-1) authorizes ONE prose-only
# repair batch + ONE final bounded confirmation.  This file stays `state: closed` during the repair; it is set
# to `requested` (confirmation_used: yes) only once the candidate is frozen and every required check is GREEN.

## Rules

- Set `state: requested` only at an intentional review barrier, after the candidate is frozen and verified.
- Use only `Contract Review` or `Implementation Review` in `review`.
- `confirmation_used: yes` records that the bounded confirmation for this override has been requested; a further
  round runs ONLY under a new explicit `human_override` token.
- A BLOCKING confirmation (or ARCHITECTURAL CONFLICT) ENDS autonomous work: close, record compactly, notify Rob,
  STOP — no repair or re-request without a new explicit human override.
- Close the request after recording the review result.
- Ordinary Claude turns leave this file closed, so the stop hook returns immediately.
