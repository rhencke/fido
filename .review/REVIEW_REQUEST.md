# Review Request

state: closed
review: Implementation Review
confirmation: no
confirmation_used: no
human_override: (M2 repair 2, authorized by Rob's upload of the consolidated blocking M2 implementation review)
result: repair 2 complete and frozen; awaiting Rob
candidate: 641ac9034b280ddfd0930a12635e60322a2d4686

contract: .review/M2_BUILD_OBSERVATORY.md
review_basis: .review/REVIEW_BASIS.md

`.review/NEXT_STEPS.md` owns mutable checkpoint and candidate state. This file pins the exact candidate under
human review; it does not own mutable state. Canonical data rows carry no candidate identity.

Repair 2 answers `.review/M2_IMPLEMENTATION_REPAIR_2.md`: Rob's accepted scope amendment, under which project
Python never runs on the host, and blocking findings A through M. Every Python gate, writer, profiler,
comparison and self-test now runs in the pinned image, with sources MOUNTED read-only from the exact declared
source view rather than copied into a policy image — which makes a stale-green layer unrepresentable rather
than merely unlikely. The host boundary is shell, Make, Git, Docker and Buildx, and one gate enforces it.

Several complete canonical runs were discarded before this one. Every defect that discarded a run was found by
running the tool and reading what it wrote. Four are worth naming, because they share a shape.

A hook stage finishing inside one 10 ms clock tick carried its own measurement kind, and measurement kind is
part of the seven-part metric identity — so a stage changed identity by being fast, and the registry was told
it had declared metrics nobody measured and measured metrics nobody declared. Precision is not identity; it
belongs to the read, not to the metric.

The FCB view writer bind-mounts a temporary directory that the HOST daemon resolves, so a path existing only
inside the observatory runner was silently replaced by an empty one. That bug had already been met, diagnosed
and commented in the pre-commit hook — and the fix was scoped to the one command being debugged. It had been
failing every run invisibly, because an earlier recording rule always raised first.

Three Docker stages were derived children of commands that are cataloged, because each is an idempotent guard
that never rebuilds once its tag exists. A derived child is observed inside a parent's run; when every parent
never runs, the child is selected forever and measured never.

The run identity was required by the identity relations, named by no member list, emitted by the producer
never, and supplied BY HAND in the self-test fixture. The fixture is what hid it: every control passed against
a shape the tool had never once emitted.

The last two were found without a run, by pointing the complete observation validator at a finished
observation — thirty seconds against four hours. Each of the four is now a rule rather than an edit, because
each was first repaired as an instance while its class stayed open.

252 controls, 151 mutation entries, each proved load-bearing by deleting its effect and watching its own named
controls fail. The canonical observation retains 732 sample identities; all fourteen recording rules passed.
`.review/M2_RECOMMENDATIONS.tsv` assigns ten findings to M3; M2 implements none of them. R04 remains an
unresolved TENSION with a candidate reconciliation attached, because whether a well-tested duplication is
acceptable is a judgement for Rob and the reviewer rather than something the ledger should settle.

No comparison accompanies this observation. The tracked baseline predates the sample fields this repair
introduced, so it does not validate, and the tool refuses to rest a verdict on it. Synthesizing the missing
provenance to manufacture a delta was available and is not a trade this project makes; the recorded
observation is the baseline the next candidate is compared against.

M1 is ACCEPTED under `M1-ACCEPT-6524b43`, C4 under `C4-ACCEPT-39ea7e3` and M0 under `M0-ACCEPT-86a63db`.
M3, M4, C5 Step 0 and C5 remain forbidden. Only Rob accepts M2.
