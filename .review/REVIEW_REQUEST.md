# Review Request

state: requested
review: Implementation Review
confirmation: no
confirmation_used: no
human_override: (M2 repair 5, authorized by Rob's upload of the blocking M2 implementation review installed at `.review/M2_IMPLEMENTATION_REPAIR_5.md`)
result: (pending)
candidate: 1003734e67e2f07f5a10ec931e5c5729981d4652

contract: .review/M2_BUILD_OBSERVATORY.md
review_basis: .review/REVIEW_BASIS.md

`.review/NEXT_STEPS.md` owns mutable checkpoint and candidate state. This file pins the exact candidate under
human review; it does not own mutable state. Canonical data rows carry no candidate identity.

Candidate `1003734e67e2f07f5a10ec931e5c5729981d4652` closes M2 Repair 5's five root findings and its fourteen
reopened obligations. The canonical observation in the freeze commit measures that exact ref.

**Read `.review/M2_BUILD_OBSERVATORY.md` §1C first.** Rob amended M2's scope during this repair and
authorized it explicitly: the timing suite measures each phase exactly once cold and exactly once hot, and
must finish inside one hour. `project.cached.fresh` and the five `project.incremental.<edit>` scenarios are
withdrawn with their edits; the canonical relation falls from 252 required metrics to 153. That supersedes
Repair 5 §9 step 14's fixed 27 traces / 252 metrics, through that step's own registry escape, and amends
contract §3A.2 and §3A.6 in place. The reviewer authored none of it.

M1 is ACCEPTED under `M1-ACCEPT-6524b43`, C4 under `C4-ACCEPT-39ea7e3` and M0 under `M0-ACCEPT-86a63db`.
M3, M4, C5 Step 0 and C5 remain forbidden. Only Rob accepts M2.
