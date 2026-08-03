# Review Request

state: requested
review: Implementation Review
confirmation: no
confirmation_used: no
human_override: (M2 Culling Repair 2, authorized by Rob's upload of the blocking implementation review installed at `.review/M2_CULLING_REPAIR_2.md`)
result: (pending)
candidate: be0b569e598250449b9f131aeb8cbeaa3907860c

contract: .review/M2_PERFORMANCE_SNAPSHOT.md
review_basis: .review/REVIEW_BASIS.md

`.review/NEXT_STEPS.md` owns mutable checkpoint and candidate state. This file pins the exact candidate under
human review; it does not own mutable state. Canonical data rows carry no candidate identity.

Candidate `be0b569e598250449b9f131aeb8cbeaa3907860c` completes M2 Culling Repair 2. All nine obligations close
against evidence that resolves.

The repair deleted duplicated mutable state rather than updating it. Governance owns the accepted amendments
and decisions; `.review/NEXT_STEPS.md` owns the active checkpoint and candidate; the FCB Index names where to
look rather than what is currently there; every other document states its own stable purpose. The Human
Review Index generator no longer emits the stale banner, and regeneration is byte-exact and idempotent.

No timing implementation changed. `tools/perf.sh`, the Makefile, the Dockerfile, the pre-commit hook and
`.review/PERFORMANCE.tsv` are byte-identical to the previous candidate `3441e75aabde`, and no `.v`, OCaml or
generated Go byte moved.

Complexity fit: PASS.

M1 is ACCEPTED under `M1-ACCEPT-6524b43`, C4 under `C4-ACCEPT-39ea7e3` and M0 under `M0-ACCEPT-86a63db`.
M3, M4, C5 Step 0 and C5 remain forbidden. Only Rob accepts M2.
