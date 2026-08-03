# Review Request

state: requested
review: Implementation Review
confirmation: no
confirmation_used: no
human_override: (M2 Culling Repair 4, authorized by Rob's upload of the blocking implementation review installed at `.review/M2_CULLING_REPAIR_4.md`)
result: (pending)
candidate: 9814db77ead0cfcfd8ff268303ba2afedef71197

contract: .review/M2_PERFORMANCE_SNAPSHOT.md
review_basis: .review/REVIEW_BASIS.md

`.review/NEXT_STEPS.md` owns mutable checkpoint and candidate state. This file pins the exact candidate under
human review; it does not own mutable state. Canonical data rows carry no candidate identity.

Candidate `9814db77ead0cfcfd8ff268303ba2afedef71197` completes M2 Culling Repair 4. All nine obligations close
against evidence that resolves.

`.review/M_SERIES_PLAN.md` now owns the stable M0–M4 order, the M4 approval act, the permanent
source-comment law with `M1-ACCEPT-6524b43` as its provenance, the M2 product description and the M3
assignments. It asserts nothing about which checkpoint is under way. `.review/NEXT_STEPS.md` alone owns the
active candidate and the successor prohibition; Governance alone owns accepted amendments and decisions.

The previous request claimed this was already true and it was not. That claim is corrected rather than
repeated: the check that matters is whether the next transition needs one edit or several, not whether
today's copies happen to agree.

No implementation changed. `tools/perf.sh`, `.review/PERFORMANCE.tsv`, the Makefile, the Dockerfile and the
pre-commit hook are byte-identical to `d44a69dd5f53`, and no `.v`, OCaml or generated Go byte moved.

Complexity fit: PASS.

M1 is ACCEPTED under `M1-ACCEPT-6524b43`, C4 under `C4-ACCEPT-39ea7e3` and M0 under `M0-ACCEPT-86a63db`.
M3, M4, C5 Step 0 and C5 remain forbidden. Only Rob accepts M2.
