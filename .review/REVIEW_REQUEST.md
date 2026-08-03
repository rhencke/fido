# Review Request

state: requested
review: Implementation Review
confirmation: no
confirmation_used: no
human_override: (M2 Great Measurement Culling, authorized by Rob's human disposition installed at `.review/M2_GREAT_MEASUREMENT_CULLING.md`)
result: (pending)
candidate: b1c6991943dd90128d68d5790fbf16297b469987

contract: .review/M2_PERFORMANCE_SNAPSHOT.md
review_basis: .review/REVIEW_BASIS.md

`.review/NEXT_STEPS.md` owns mutable checkpoint and candidate state. This file pins the exact candidate under
human review; it does not own mutable state. Canonical data rows carry no candidate identity.

Candidate `b1c6991943dd90128d68d5790fbf16297b469987` completes the Great Measurement Culling. Rob withdrew the
Build Observatory candidate `1003734e67e2f07f5a10ec931e5c5729981d4652` by human disposition; it is not
accepted and received no Repair 6. Git history owns that experiment in full.

M2 now delivers one `make perf` target, one 68-line POSIX shell script, one tracked
`.review/PERFORMANCE.tsv`, and nine inert completion markers in the existing `make check` path. `git diff` is
the comparison. Timing is diagnostic evidence, not an acceptance gate, and no gate consults it.

The diff is 1,021 insertions against 50,972 deletions. Two changes in it are worth reading directly rather
than by summary: the claim-matrix gate now accepts an explicit `unsupported-boundary:` on an OPEN row, and
removing `.build-observatory/` from `.gitignore` revealed 76 MB of local run bundles that an ignore rule had
been hiding.

M1 is ACCEPTED under `M1-ACCEPT-6524b43`, C4 under `C4-ACCEPT-39ea7e3` and M0 under `M0-ACCEPT-86a63db`.
M3, M4, C5 Step 0 and C5 remain forbidden. Only Rob accepts M2.
