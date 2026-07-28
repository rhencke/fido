# Review Request

state: requested
review: Implementation Review
confirmation: no
confirmation_used: no
human_override: (M1 repair 3, authorized by Rob's upload of the third blocking implementation review)
result: awaiting Rob's human M1 review
candidate: c73925c6b7c432a8265bdb052388efaf57d96f6f

contract: .review/M1_SOURCE_DIET.md
review_basis: .review/REVIEW_BASIS.md

**A human M1 review is requested for candidate `c73925c6b7c432a8265bdb052388efaf57d96f6f`.** C4 is ACCEPTED under `C4-ACCEPT-39ea7e3` and M0
under `M0-ACCEPT-86a63db`. Every required obligation in `.review/M1_OBLIGATION_MATRIX.tsv` is closed; `make
claims` refuses to let this file request review otherwise.

The blocking finding was a lifetime defect. `make diet` had grown the M1 baseline, file-disposition and
code-identity checks, so the permanent build path enforced one checkpoint's exit evidence forever: M2 could
not add a report, no later checkpoint could add a Rocq declaration, and the temporary evidence could never
retire. That is now separated.

**The permanent path** runs `--self-test`, `--check` and `--wiring`. It reads the `.v` files and
`M1_COMMENT_EXCEPTIONS.tsv`, and no baseline, metric table, file disposition, deletion ledger, obligation
matrix, candidate ref or freeze state. `--wiring` reads the `diet` recipe and the staged hook and fails if
either regains a checkpoint-only mode, so the boundary is enforced by the build it protects.

**The M1 exit evidence** runs explicitly and only for this review:

```text
python3 tools/source-diet.py --m1-self-test
python3 tools/gate-mutation-test.py --m1
python3 tools/source-diet.py --verify-m1-evidence \
  --baseline-ref 068d3371ac3300303d6c7c99a97ed884182c81e4 \
  --candidate-ref c73925c6b7c432a8265bdb052388efaf57d96f6f
```

It proves the same things it proved before: the baseline seal and every sealed metric reproduce; the
candidate's metric table is header-only; the four candidate-owned ledgers are byte-identical in the candidate
and here; every change since the candidate lies inside the five-file freeze overlay; every metric row equals
recomputation; every disposition row is exact in both trees; and every surviving top-level Rocq command is
identical after removing exactly the eight ledgered declaration units.

The canonical numbers are `.review/M1_METRICS.tsv`, generated from those two refs. Prose that copies them is
not authority — a lesson this repair records as `M3-FRAGILE-PROSE`, and one my own previous freeze commit
demonstrated by reporting byte counts that disagree with the generated table.

After acceptance, the closeout can retire `M1_BASELINE.tsv`, `M1_METRICS.tsv`, `M1_FILE_DISPOSITION.tsv`,
`M1_DECLARATION_DELETIONS.tsv`, `M1_OBLIGATION_MATRIX.tsv` and this repair directive to Git history with no
functional gate edit. `M1_COMMENT_EXCEPTIONS.tsv` stays, because the permanent comment gate consumes it.

M2, M3, M4, C5 Step 0 and C5 remain forbidden until Rob accepts M1. Automatic Codex review is disabled.
