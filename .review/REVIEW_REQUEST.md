# Review Request

state: requested
review: Implementation Review
confirmation: no
confirmation_used: no
human_override: (M2 Culling Repair 1, authorized by Rob's upload of the blocking implementation review installed at `.review/M2_CULLING_REPAIR_1.md`)
result: (pending)
candidate: 3441e75aabde2f2b0932751643b56f9590b5a58b

contract: .review/M2_PERFORMANCE_SNAPSHOT.md
review_basis: .review/REVIEW_BASIS.md

`.review/NEXT_STEPS.md` owns mutable checkpoint and candidate state. This file pins the exact candidate under
human review; it does not own mutable state. Canonical data rows carry no candidate identity.

Candidate `3441e75aabde2f2b0932751643b56f9590b5a58b` completes M2 Culling Repair 1. All nine obligations
close against evidence from the corrected path.

The two findings worth verifying directly are the ones where a tracked file asserted something the code did
not do. `tools/perf.sh` exported `BUILDER`, which `BUILDER := fido-builder` overrides, so every measurement
ran on the ordinary builder while the header named `fido-perf-v1`. And `/proc/uptime`'s hundredths were
divided by ten rather than multiplied, so `.84` recorded as 8 ms under a header claiming 10 ms resolution.
Both are reproducible in one line and both are fixed.

Deleting the `DOC_EXEMPT_RE` compatibility path exposed a defect it had been concealing: the documentation
scanner read a fenced ```` ```python ```` delimiter as a host-Python instruction, which made the boundary
unstatable in its own prose. Fixed with controls both ways and a mutant.

Two deliberate non-changes are recorded in the candidate's commit message: `FCB_AMENDMENT_A007` is an
accepted human act and was not edited, and the repair directive is typed `reference` because it quotes every
deleted path.

Complexity fit: PASS.

M1 is ACCEPTED under `M1-ACCEPT-6524b43`, C4 under `C4-ACCEPT-39ea7e3` and M0 under `M0-ACCEPT-86a63db`.
M3, M4, C5 Step 0 and C5 remain forbidden. Only Rob accepts M2.
