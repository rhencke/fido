# Review Request

state: requested
review: Implementation Review
confirmation: no
confirmation_used: no
human_override: (M1 repair 2, authorized by Rob's upload of the second blocking implementation review)
result: awaiting Rob's human M1 review
candidate: 8ad80e6614bff64b493bbdd1db937f4640eda252

contract: .review/M1_SOURCE_DIET.md
review_basis: .review/REVIEW_BASIS.md

**A human M1 review is requested for candidate `8ad80e6614bff64b493bbdd1db937f4640eda252`.** C4 is ACCEPTED under `C4-ACCEPT-39ea7e3` and M0
under `M0-ACCEPT-86a63db`. `.review/M1_OBLIGATION_MATRIX.tsv` reads 15 of 15 closed; the nine the second review
reopened close on evidence this repair built, and none reuses a control from an unrelated obligation.

Measured against the sealed baseline `068d3371ac3300303d6c7c99a97ed884182c81e4`:

| metric | baseline | candidate | delta |
|---|---:|---:|---:|
| repository bytes | 3,272,574 | 2,671,433 | -18.37% |
| deterministic archive bytes | 801,677 | 585,422 | -26.98% |
| `.v` comment bytes | 408,155 | 59,370 | -85.45% |
| `.v` comment blocks | 1,464 | 662 | -54.78% |
| `.review` bytes outside the live FCB | 490,345 | 191,339 | -60.98% |
| root Markdown bytes | 158,291 | 135,452 | -14.43% |
| ledgered comment exceptions | — | 0 | the goal was zero |

One command establishes the whole evidence topology from two exact Git refs:

```text
python3 tools/source-diet.py --verify-m1-evidence \
  --baseline-ref 068d3371ac3300303d6c7c99a97ed884182c81e4 \
  --candidate-ref 8ad80e6614bff64b493bbdd1db937f4640eda252
```

It proves: the baseline seal and every sealed metric reproduce; the candidate's metric table is HEADER-ONLY,
so it states no other candidate's results; the four candidate-owned ledgers are byte-identical in the
candidate and here, so this freeze rewrote none of them; every change since the candidate lies inside the
five-file freeze overlay; every metric row equals recomputation; every disposition row is exact in both
trees; and every surviving top-level Rocq command is identical after removing exactly the eight ledgered
declaration units.

That last check is the one the second review blocked on. The old model gave a declaration every command after
it, and tested terminators by equality, so a proof ending `} Qed.` was invisible and the declaration swallowed
what followed — in this repository, a `Transparent` directive in `Render.v`. Ownership is now decided per
command, by what FOLLOWS a declaration rather than by whether its text contains `:=`, and a shape the model
cannot classify raises instead of guessing.

M2, M3, M4, C5 Step 0 and C5 remain forbidden until Rob accepts M1. Automatic Codex review is disabled.
