# Review Request

state: requested
review: Contract Review
confirmation: no
confirmation_used: no
human_override: (none required; Rob's M2 acceptance authorizes installing the M3 contract)
result: (pending)
candidate: (the M3 contract commit named by `.review/NEXT_STEPS.md`)

contract: .review/M3_TOOL_AND_BUILD_ARCHITECTURE_AUDIT.md
review_basis: .review/REVIEW_BASIS.md

`.review/NEXT_STEPS.md` owns mutable checkpoint and candidate state. This file pins what is under review; it
does not own mutable state.

**Contract Review is requested over the M3 contract installed by this commit.** M3 implementation is
forbidden until that review passes.

M2 is ACCEPTED under `M2-ACCEPT-9814db7` at `9814db77ead0cfcfd8ff268303ba2afedef71197`. Its permanent result
— `make perf`, `tools/perf.sh`, `.review/PERFORMANCE.tsv` and the inert completion markers — outlives the
checkpoint and is owned by `.review/M_SERIES_PLAN.md`. Git history owns M2's contract, obligation matrix,
repairs and the human culling narrative.

This commit is authority-only. Every M3 obligation is open, `.review/M3_AUDIT.md` and
`.review/M4_MECHANICAL_REFACTOR_PLAN.md` carry a heading and `status: pending` and nothing else, and no
audit conclusion or proposed refactor has been invented ahead of the audit.

The one question worth putting to a Contract Review: this contract asks for an audit of every tool and build
surface, and the previous checkpoint was withdrawn for building a platform where a script would do. The
guard here is that `M3_AUDIT.md` is one temporary table, not a registry, and that §5 forbids a permanent
timing or audit tool. Whether that guard is strong enough is the reviewer's call, not mine.

M1 is ACCEPTED under `M1-ACCEPT-6524b43`, C4 under `C4-ACCEPT-39ea7e3` and M0 under `M0-ACCEPT-86a63db`.
M4, C5 Step 0 and C5 remain forbidden. Only Rob accepts M3.
