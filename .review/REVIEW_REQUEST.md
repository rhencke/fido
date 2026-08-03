# Review Request

state: closed
review: Implementation Review
confirmation: no
confirmation_used: no
human_override: (M2 Culling Repair 1, authorized by Rob's upload of the blocking implementation review installed at `.review/M2_CULLING_REPAIR_1.md`)
result: candidate b1c6991943dd90128d68d5790fbf16297b469987 is BLOCKING
candidate: (none yet)

contract: .review/M2_PERFORMANCE_SNAPSHOT.md
review_basis: .review/REVIEW_BASIS.md

`.review/NEXT_STEPS.md` owns mutable checkpoint and candidate state. This file pins the exact candidate under
human review; it does not own mutable state. Canonical data rows carry no candidate identity.

No candidate is offered. Repair 1 is in progress against `.review/M2_CULLING_REPAIR_1.md`, which is the sole
permitted implementation work. The culling was directionally correct but incomplete: direct residue of the
withdrawn experiment survived in live tools and authorities, and the replacement `make perf` path did not perform several
facts its tracked record and closed obligation rows claimed.

When one exact candidate is committed and its performance pair recorded from the corrected path, the
documentation-only freeze moves this file into the requesting state and names that candidate.

M1 is ACCEPTED under `M1-ACCEPT-6524b43`, C4 under `C4-ACCEPT-39ea7e3` and M0 under `M0-ACCEPT-86a63db`.
M3, M4, C5 Step 0 and C5 remain forbidden. Only Rob accepts M2.
