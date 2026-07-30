# Review Request

state: closed
review: Implementation Review
confirmation: no
confirmation_used: no
human_override: (M2 repair 1, authorized by Rob's upload of the first blocking M2 implementation review)
result: repair 1 complete and frozen; awaiting Rob
candidate: e534b0ae5cc47da510e46583e47f74566589d538

contract: .review/M2_BUILD_OBSERVATORY.md
review_basis: .review/REVIEW_BASIS.md

`.review/NEXT_STEPS.md` owns mutable checkpoint and candidate state. This file pins the exact candidate under
human review; it does not own mutable state. Canonical data rows carry no candidate identity.

Repair 1 answers `.review/M2_IMPLEMENTATION_REPAIR_1.md` as amended by
`.review/M2_REPAIR_1_CACHE_CUT_AMENDMENT.md`. The first M2 candidate was blocked because its observation
labelled work that had already been done by an earlier command, pooled unlike samples into single metrics, and
recorded coverage it did not measure. The permanent shape is kept; the measurements are now true.

Every defect this repair closed was found by running the tool and reading what it wrote, not by re-reading
code. Seven canonical runs were attempted; six were discarded, each because the tool refused its own output
or because a number did not mean what its label said. The seventh is recorded. In particular the incremental
samples were measuring cache hits in three separate ways — one command reading another's tree, one run
reading an earlier run's build, and a cold claim resting on no stage evidence at all — and each is now
refused by a control with a mutant proving the rule load-bearing.

209 controls (109 must-fail with the reason pinned), 111 mutation entries, every registry relation closed in
both directions. `.review/M2_RECOMMENDATIONS.tsv` assigns four findings to M3; M2 implements none of them.
R04 is recorded as an unresolved TENSION with a candidate reconciliation attached, because whether a
well-tested duplication is acceptable is a judgement for Rob and the reviewer rather than something the
ledger should settle.

M1 is ACCEPTED under `M1-ACCEPT-6524b43`, C4 under `C4-ACCEPT-39ea7e3` and M0 under `M0-ACCEPT-86a63db`.
M3, M4, C5 Step 0 and C5 remain forbidden. Only Rob accepts M2.
