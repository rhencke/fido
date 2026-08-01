# Review Request

state: closed
review: Implementation Review
confirmation: no
confirmation_used: no
human_override: (M2 repair 3, authorized by Rob's upload of the blocking M2 implementation review carrying the accepted amendment `M2-SCOPE-AMENDMENT-TRACE-ACQUISITION`)
result: repair 3 complete and frozen; awaiting Rob
candidate: 483791f73b52c134ded3414a8a744deb1151f86b

contract: .review/M2_BUILD_OBSERVATORY.md
review_basis: .review/REVIEW_BASIS.md
fcb_tree: 983eba409a29d5dc785cd40f160d514fbb5eb671

`.review/NEXT_STEPS.md` owns mutable checkpoint and candidate state. This file pins the exact candidate under
human review; it does not own mutable state. Canonical data rows carry no candidate identity.

Repair 3 answers `.review/M2_IMPLEMENTATION_REPAIR_3.md`. The third candidate was not blocked for a false
measurement — it was blocked because the facility was unusable. The canonical suite cost **4 h 07 m 29 s over
133 direct executions**, because a fixed triplicate policy crossed with five edit shapes over four overlapping
commands kept re-running execution closures the suite had already observed. Rob's amendment lets M2 optimize
its OWN acquisition and nothing else.

**Measured at this candidate: 27 direct executions, 1 h 37 m 17 s, establishing the same 252 canonical
metrics.** 79.7% fewer executions, 60.7% less wall time, identical coverage. 225 of those metrics are derived
inside traces that were already paying for them: `make.prove` went from twenty samples to one, and `make.fcb`
— sixteen minutes of it — disappears entirely into the `make.check` traces that always ran it.

The mechanism is that acquisition became a RELATION over command, state and root rather than a property of a
command. One rule, `contained_here`, is read by the expected relation, the planner, the runner and the child
derivation. `make.prove` is contained under the canonical states and direct when asked for by name, so
`ONLY=make.prove SCENARIO=project.cold.prover` is still a real execution rather than an impossible request.

Three defects are worth naming, because the interesting thing is what found each one.

**The plan and the runner disagreed, and the plan was right.** `PLAN=1` scheduled one `make.prove` trace; a
live run was executing six. The runner walked every scenario a command declares without asking whether a
containing trace already measured it — a second authority, heading for a duplicate-acquisition refusal after
another hour of building. Found in seconds by comparing a printed plan against a running log, which is the
whole argument for requiring the plan to be inspectable before anything executes.

**A contained command is measured, not missing.** A fully contained command reaches the observation through
child derivation, so it HAS samples. The runner decided whether a command was unmeasurable AFTER containment
emptied its chain, so six gates were one run away from being written into the same bundle twice: once as
measured, once among the commands this selection could not measure. Found by reading the runner rather than
running it. The validator now REFUSES an observation that says both — avoiding a bad write in the producer
leaves the bad state writable.

**A command is contained only in a state it DECLARES.** R05 refused a 97-minute run over 44 metrics the
registry never declared, every one a warm-only gate minted under a `make.check` state it does not declare.
The rule asked whether the ROOT ran in this state and never whether the COMMAND was measured in it; its own
docstring stated the rule intended while the code implemented half of it. Three of the rule's four readers
iterate a command's own scenarios and could never ask the question — the child derivation asks about every
command under one parent state, and that is the reader that was wrong.

That last one carries the lesson of this repair. A control added the same morning pinned the plan against the
runner and passed, because **scheduling and derivation are different projections of one rule**. Pinning one
proves nothing about the other. Both are now pinned before anything builds, and the second answers in under a
second what cost 97 minutes to learn.

One interaction is worth recording: the new check MASKED an existing control, whose fixture then returned the
right answer for the wrong reason and could no longer detect its own rule being deleted. The mutation harness
said so immediately. Each rule now has a fixture only IT can decide.

276 controls, 173 mutation entries, each proved load-bearing by deleting its effect and watching its own named
controls fail. The observation retains 252 sample identities and all fourteen recording rules passed. All
nineteen obligations are closed against evidence in it.

Three things this candidate does NOT claim.

`serial_projection` is defined and unused: `projection_count` is 0, the open question about it stands, and no
number here rests on summing intervals. `.review/M2_RECOMMENDATIONS.tsv` adds `R12` — the self-test prints a
must-fail/must-accept partition it does not compute, verified by inspection rather than estimated, and
assigned to M3 rather than repaired here. And there is again no comparison: the tracked baseline predates
`suite_cost`, so it does not validate and the tool refuses to rest a verdict on it. Manufacturing the missing
provenance to produce a delta was available and is not a trade this project makes. The 4 h 07 m figure above
is read from the prior observation's own retained samples, not from a comparison the tool would not sign.

`R07` and `R09` are delivered and closed. `R01`–`R06`, `R08`, `R10`–`R12` remain assigned to M3 and visible
under D-28; M2 implements none of them.

M1 is ACCEPTED under `M1-ACCEPT-6524b43`, C4 under `C4-ACCEPT-39ea7e3` and M0 under `M0-ACCEPT-86a63db`.
M3, M4, C5 Step 0 and C5 remain forbidden. Only Rob accepts M2.
