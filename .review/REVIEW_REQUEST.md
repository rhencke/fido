# Review Request

state: requested
review: Implementation Review
confirmation: no
confirmation_used: no
human_override: (M2 Culling Repair 3, authorized by Rob's upload of the blocking implementation review installed at `.review/M2_CULLING_REPAIR_3.md`)
result: (pending)
candidate: d44a69dd5f538cf9888303f579e766d889348018

contract: .review/M2_PERFORMANCE_SNAPSHOT.md
review_basis: .review/REVIEW_BASIS.md

`.review/NEXT_STEPS.md` owns mutable checkpoint and candidate state. This file pins the exact candidate under
human review; it does not own mutable state. Canonical data rows carry no candidate identity.

Candidate `d44a69dd5f538cf9888303f579e766d889348018` completes M2 Culling Repair 3. All nine obligations close
against evidence from the corrected path.

`make perf` now removes and recreates its dedicated builder every run, so the header states a configuration
the script established. Proved against a decoy: a `fido-perf-v1` with no BuildKit configuration at all was
created first in container `638d4e82a26e`; the run removed it, and the replacement `87089f1e1ed2` reports
`max-parallelism = 1` from its own config file.

Repair 2's one-owner work was verified by exact-phrase search, which missed semantically equivalent copies.
This pass asked each document what it owns: the Index, Roadmap, M-series plan and Model Operations no longer
carry the current cursor, and `NEXT_STEPS` points at Governance for the amendment register.

Culling Repairs 1 and 2 are deleted with their D-24 rows; only the active directive remains.

Complexity fit: PASS.

M1 is ACCEPTED under `M1-ACCEPT-6524b43`, C4 under `C4-ACCEPT-39ea7e3` and M0 under `M0-ACCEPT-86a63db`.
M3, M4, C5 Step 0 and C5 remain forbidden. Only Rob accepts M2.
