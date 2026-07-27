# Review Request

state: requested
review: Implementation Review
confirmation: no
confirmation_used: no
human_override: (M1 — see .review/M1_SOURCE_DIET.md)
result: awaiting Rob's human M1 review
candidate: 7dc9ff3bb3450cc3bcc41abfb7c5c24154967f3d

contract: .review/M1_SOURCE_DIET.md
review_basis: .review/REVIEW_BASIS.md

**A human M1 review is requested for candidate `7dc9ff3bb3450cc3bcc41abfb7c5c24154967f3d`.**
C4 is ACCEPTED under `C4-ACCEPT-39ea7e3` and M0 under `M0-ACCEPT-86a63db`.
`.review/M1_OBLIGATION_MATRIX.tsv` reads 15 of 15 closed with all fifteen required obligations present —
`make claims` refuses to let this file request review while any row is absent, duplicate, malformed or open.

Measured against the sealed baseline `068d3371ac3300303d6c7c99a97ed884182c81e4`:

| metric | baseline | candidate | delta |
|---|---|---|---|
| repository bytes | 3,272,574 | 2,922,857 | −10.69% |
| deterministic archive bytes | 801,677 | 676,765 | −15.58% |
| `.v` comment bytes | 408,155 | 125,934 | −69.15% |
| `.v` comment physical lines | 4,332 | 1,443 | −66.69% |
| multiline comment blocks | 875 | 0 | — |
| over-120 comment blocks | 133 | 0 | — |
| archaeology comment blocks | 25 | 0 | — |
| ledgered comment exceptions | — | 0 | the goal was zero |

No surviving Rocq code changed: across all 23 `.v` files, 0 code tokens added and 424 removed, and the
declarations that vanished are exactly the eight in `.review/M1_DECLARATION_DELETIONS.tsv`. Twenty-two of
the twenty-three files have byte-identical code token streams. `make diet` checks this rather than asserting
it.

Generated `go.mod` and `main.go`, and every reviewed golden, are byte-identical to the baseline.
`make regenerate` reproduces them exactly. `make audit-fresh` observed 540 of 540 gated surfaces axiom-free
and the whole-tree `go build ./...` uncached.

Three scoping calls are recorded in `.review/OPEN_QUESTIONS.md` with their defaults rather than guessed:
a dead exclusion row in the naming gate, whether M1 may trim the campaign master plan against its own
instruction not to, and the COLLECTION LAW being stated at full length in two documents.

M2, M3, M4, C5 Step 0 and C5 remain forbidden until Rob accepts M1. Automatic Codex review is disabled.
