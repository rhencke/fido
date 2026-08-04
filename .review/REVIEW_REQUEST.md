# Review Request

state: requested
review: Contract Review
confirmation: yes
confirmation_used: yes
human_override: (none required; the Contract Review that blocked this contract orders exactly this repair)
result: (pending)
candidate: (this contract-repair candidate; `.review/NEXT_STEPS.md` owns the active state)

contract: .review/M3_TOOL_AND_BUILD_ARCHITECTURE_AUDIT.md
contract_activation_sha: 9d7ad8175134026ff5683e7b3c10062b48608064
review_basis: .review/REVIEW_BASIS.md
prior_finding_record: .review/M3_CONTRACT_REVIEW_REPAIR_1.md

`.review/NEXT_STEPS.md` owns mutable checkpoint and candidate state. This file pins what is under review; it
does not own mutable state.

**The single bounded Contract Review confirmation is requested.** The initial Contract Review over contract
activation `9d7ad8175134026ff5683e7b3c10062b48608064` returned BLOCKING with six findings. This candidate
repairs all six as one batch. The confirmation is limited to those findings and the clauses they directly
changed; it does not reopen contract design. Once it is GREEN the revised contract activation SHA is this
candidate's, and the reviewer's accepted output is installed as `.review/REVIEW_BASIS.md`.

What changed, by finding:

1. **Contract freeze.** §9 no longer lets M3 edit its own contract. After Contract Review the contract and
   accepted basis are frozen; a contract found defective is a stop and an amendment request, not an edit.
2. **M3 records baselines; M4 produces after values.** §8 and `M3-10` had asked M3 for after measurements of a
   refactor M3 is forbidden to perform. M3 now records exact current baselines and the plan names the exact
   post-change procedure M4 runs. "Under one minute" stays a goal in §2 and is never evidence.
3. **A finite audit unit.** §3 replaces "every surface" with seven closed audit units, the row field set and
   five allowed dispositions, and forbids inventorying every function, theorem or proof body. §7 drops
   "meaningful helper" for the §3.7 rule, and `M3-HOST-CONTAINER-OTHER` is narrowed to what exists today.
4. **Four distinct configurations.** §5 separates the serial diagnostic baseline, ordinary working-tree
   acceptance, staged acceptance and partial feedback, and forbids pooling them. §2 no longer lets
   `.review/PERFORMANCE.tsv` read as developer wall time.
5. **Reproducible measured facts.** §5 requires every measured fact to name its ref or range, command, source
   view, cache condition and result, and requires edit-frequency evidence to keep semantic/proof ranges and
   M-series tooling ranges separate.
6. **Review state.** This request names the binding activation SHA and the prior finding record.
   `.review/REVIEW_BASIS.md` no longer calls itself accepted before a review accepted it. The `M3-REVIEW`
   human act no longer claims a candidate exists; it is deferred until one is frozen.

This candidate is authority-only. No production, proof, build, tool, generated or runtime path moved, and no
audit or M4 step was executed. Every M3 obligation stays open; `.review/M3_AUDIT.md` and
`.review/M4_MECHANICAL_REFACTOR_PLAN.md` still carry a heading and `status: pending` and nothing else.

M2 is ACCEPTED under `M2-ACCEPT-9814db7` at `9814db77ead0cfcfd8ff268303ba2afedef71197`, M1 under
`M1-ACCEPT-6524b43`, C4 under `C4-ACCEPT-39ea7e3` and M0 under `M0-ACCEPT-86a63db`. M4, C5 Step 0 and C5
remain forbidden. Only Rob accepts M3.
