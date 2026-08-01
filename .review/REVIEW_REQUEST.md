# Review Request

state: requested
review: Implementation Review
confirmation: no
confirmation_used: no
human_override: (M2 repair 4, authorized by Rob's upload of the blocking M2 implementation review installed at `.review/M2_IMPLEMENTATION_REPAIR_4.md`)
result: repair 4 complete and frozen; awaiting Rob
candidate: d41c5ed2932d2e448bda307b94cf4e268bd0d99b

contract: .review/M2_BUILD_OBSERVATORY.md
review_basis: .review/REVIEW_BASIS.md

`.review/NEXT_STEPS.md` owns mutable checkpoint and candidate state. This file pins the exact candidate under
human review; it does not own mutable state. Canonical data rows carry no candidate identity.

Repair 4 answers `.review/M2_IMPLEMENTATION_REPAIR_4.md`, findings A through F and the §5 contract amendment.

**Measured at this candidate: 27 traces, 27 completion objects all closed, 252 canonical metrics, 112 m 41 s.**
Every decomposed parent partitions into its children plus a retained remainder — 11.7–44.7 ms across the eight
`make.check` traces, 5.0–20.7 ms across the three `precommit.full` traces, against parents of seven to nine
minutes. The suite's own validation cost is 1.7 s, of which per-trace closure is 130 ms over 27 traces.

**A** — a completed sample is not a completed trace. Your reproduction deleted `make.prove`, `docker.prover`
and `make.fcb` from a real completed fragment and every mutilated fragment passed. The rule that catches it is
the binding to the record, not the object's internal consistency: an object's own lists stay perfectly
self-consistent when a sample vanishes from beside it. Ordering is load-bearing — an omitted child first
surfaced as a metric-count mismatch, so a control asserting the real reason passed on a message about
something else.

**B** — the runtime checkpoint log fails closed by itself. One stack serves both grammars because both obey
stack discipline for their own reasons: Make is flat siblings with no enclosing anchor, since prerequisites run
before the recipe; the hook is one root with sibling stages inside. So an end must close the INNERMOST open
checkpoint, which rejects interleaving without assuming Make nests.

**C** — the parent partitions into non-overlapping children plus one retained remainder. Your 43,112,436 ns is
now computed, retained under a stable identity, and asserted by a control using your exact numbers.

**§5** — the summed projection is deleted. One instruction I did not follow literally: the retain-list spells
the first kind `direct_wall_elapsed`, and that kind is carried by every hook stage measured INSIDE its parent —
roughly twenty-five intervals per pre-commit trace. Adopting the spelling would put the word DIRECT on all of
them. The contract names what the code emits and `OQ-M2-03` records the discrepancy, my default, and the real
question underneath: a hook stage is contained by any honest reading, so the principled fix is making those
children contained rather than renaming the direct kind, which moves ~25 metric identities per trace.

**D** — resume carries the causal state or the trace reruns. Your D1 was precise: the resume demonstrated
before could not have shown the defect, because a warm-only command has no cold trace and so no prime to lose.

**E** — self-evidence is checked, not asserted. `concurrency` was already IN the fingerprint fields; the hole
was that nothing recomputed the hash. Comparison now names the concurrency change instead of reporting
"different fingerprints", which withholds the one thing that explains the timings.

Four defects were found by real runs and by nothing else, all invisible to a canonical run:

- the declared checkpoint vocabulary was the command ids alone, so `make.check-body` — the `<command>-body`
  form your §4 requires to be NAMED — was refused as undeclared work;
- a trace's expectation was taken from the planner's per-trace list, which is FILTERED by selection and states
  every role as `selected`, so an ad hoc run disagreed on identity alone;
- the resume filter lived inside the shell chain loop and the analysis runner never consulted it, so a resumed
  analysis chain carried its traces and ran them again;
- §4's "within only the declared clock-resolution accounting" was under-implemented: a real `precommit.full`
  overshot its parent by 3.04 ms because checkpoints are timestamped at 10 ms and the parent is not.

The last is worth the most. The allowance is one tick of the instrument's own declared resolution and it is
RETAINED in the partition, so a reader sees what was permitted. That is the difference between accounting for
an instrument and widening a bound until the data fit. The remainder stays exact, negative-from-quantisation
included, rather than clamped.

326 controls, 205 mutation entries. All nineteen obligations closed against evidence in the observation.
`R07` and `R09` are delivered; `R01`–`R06`, `R08`, `R10`–`R12` remain assigned to M3 and visible under D-28,
and none is implemented here.

There is again no comparison: the tracked baseline predates the `traces` member, so it does not validate and
the tool refuses to rest a verdict on it. The recorded observation is the baseline the next candidate is
compared against.

M1 is ACCEPTED under `M1-ACCEPT-6524b43`, C4 under `C4-ACCEPT-39ea7e3` and M0 under `M0-ACCEPT-86a63db`.
M3, M4, C5 Step 0 and C5 remain forbidden. Only Rob accepts M2.
