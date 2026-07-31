# Open questions — Claude Code to the reviewer and to Rob

## OQ-M2-01 — should the residue set derive from `.gitignore` instead of being hand-maintained?

**Owner:** reviewer, for M3. **Blocks M2:** no. **Default if unanswered:** keep the hand-maintained set.

M2 installs the first current authority that names a deliberately-ignored namespace: the M2 contract specifies
local run bundles under `.build-observatory/runs`, and `.gitignore` tells Git never to hold them. The D-24
reference gate demanded a typed row for that path, and there is no honest row to write — a `repository-file`
or `repository-directory` row must resolve in every committed snapshot, and typing a repository-relative path
as off-tree is the exact laundering the gate already refuses by name.

The acceptance commit resolves it at the smallest correct scope: `tools/fcb-reference-gate.py` already owns
one residue authority, `RESIDUE_DIRS`, described as "residue that cannot be part of a committed snapshot", and
its inventory already consults it. The token scan now consults the same set, so a residue-rooted token is not
an operational reference. The exemption is bounded by two controls — a must-accept for a residue namespace and
a must-fail proving `.build-observatory-notes/` is still flagged, so the exemption binds the exact directory
name and not a prefix — and one mutation entry proving the skip is load-bearing.

The question is one layer up. `RESIDUE_DIRS` and `.gitignore` now state overlapping facts about what Git never
holds, maintained by hand in two places. That is a duplicate-authority smell of exactly the kind this project
otherwise refuses. Deriving the set from `.gitignore` would make it one authority, at the cost of teaching a
policy tool to parse ignore syntax — which has its own precedence and negation rules, and would be a real
parser rather than a lookup.

M3 owns tool and build architecture and is the right place to decide. Until then the hand-maintained set
stands: it is small, exact, machine-checked in both directions, and a wrong entry cannot hide a tracked file,
only exempt a namespace that Git already refuses to carry.

**Recommended M3 disposition, recorded by the reviewer in Repair 2 §18:** do not write an ad hoc `.gitignore`
parser. If M3 derives ignored residue, use Git's own ignore engine through exact Git queries such as
`git check-ignore`. Until M3, retain the small explicit residue set with exact controls. Repair 2 implements
none of this beyond the narrow observatory containment §12 required.

## OQ-M2-02 — should the observatory run inside buildx, so the host needs no Python?

**ANSWERED by Rob, in the M2 Repair 2 scope amendment.** The no-host-Python half is settled and implemented:
project Python runs only in the pinned image, `make observe` runs in a pinned runner container that drives
the host daemon through the mounted socket, and `tools/host-python-gate.py` holds the boundary permanently.
Docker-socket trust was decided deliberately rather than inherited — §8 requires the runner to address the
same builder and cache authorities the real project commands use, so an independent daemon was rejected.

The second half below stands and remains M3's: "no Python on the host" and "no host-side MEASUREMENT" are
different goals, and only the first is bought. The hook's anchors are still written by `/bin/sh` on the host,
which is where the hook itself runs, so its instrumentation is still host-side. Whether the whole harness
should move inside buildx is tool architecture, which M3 owns.

**Owner:** Rob, for M3. **Blocks M2:** no. **Default if unanswered:** the host keeps only the launcher
boundary — shell, Make, Git, Docker, Buildx — and the hook's own instrumentation stays with the hook.

Rob's direction, recorded here so it is not lost with the chat. `tools/build-observatory.py` runs on the
host and requires Python there, which makes the measurement environment the developer's machine rather than
a pinned one. Everything else in this repository is hermetic: the proof, the emission, the e2e and the
generated-byte compare all run inside pinned images, and `make check` states plainly that a local host Rocq
is not supported. The timing facility is the exception.

The shape Rob described: an OUTER harness that can talk to buildx and drives an INNER harness, both in
buildx. The objection I had raised — that a containerised harness would perturb the timings it collects —
does not apply, because the harness does not measure itself. Its own cost only has to stay small relative
to the work under measurement, not be accounted for.

Rob's amendment moved the no-host-Python part into M2 and it is implemented. What it did NOT settle is
whether the measurement harness itself belongs inside buildx, which remains tool architecture and M3's.

Of the two things I said a decision would have to settle, one is settled and one is not. The Docker-socket
trust posture was decided deliberately: the runner drives the host daemon through the mounted socket so it
addresses the same builder and cache authorities the real commands use, because an independent daemon would
make the timings mean nothing. The other stands — the pre-commit anchors are written by `/bin/sh` inside the
hook on the host, and while the hook itself is host-side its instrumentation stays host-side with it. "No
Python on the host" and "no host-side measurement" are not the same goal, and only the first is bought here.

## Acquisition is a property of the RELATION, not of the command

Repair 3 §8 says a command-scenario-edit relation may be direct-root, contained, serial-projection or
catalog-only. I first modelled acquisition as a property of the COMMAND — a `measurement: contained` row
naming its trace root — which is adequate for a gate like `make names` that has one warm state and no reason
to run standalone. It is NOT adequate for `make.prove` and `make.e2e`, and the directive says so itself: §11
lists `make observe ONLY=make.prove SCENARIO=project.cold.prover` among the examples that must stay useful,
and a per-command `contained` classification erases exactly that capability. Converting those two turned
sixteen controls red, one of them the documented-example check, which is the directive telling me the model
is wrong rather than the fixtures being inconvenient.

So the same command is acquired two ways: contained inside a `make.check` trace under the canonical cold,
cached, warm and incremental states, and direct when someone asks for it ad hoc under a state of its own. The
planner §11 requires — "use the direct command when it is a valid ad hoc execution and cheaper than its
containing acceptance trace" — is the thing that chooses between them, and it does not exist yet. Converting
`prove` and `e2e` before it does would mean either breaking a documented requirement or pretending the
example still resolves.

The six warm-only gates — `hostpython`, `names`, `fcb`, `claims`, `diet`, `observatory` — are converted and
green, because for them the per-command form is honest: they have one state, and an ad hoc `ONLY=` on any of
them can simply run the owning trace.

**Owner:** reviewer. **Blocks M2:** no — it blocks only the order of work inside Repair 3, and the work order
already puts the plan representation (§19 step 3) before the registry model (step 6). **Default if
unanswered:** build the planner first, then express `prove` and `e2e` as contained CANONICALLY while
retaining their direct rows for ad hoc selection, so §11's examples keep resolving. If a reviewer would
rather `SCENARIO=project.cold.prover` be replaced in §11 by the compound `project.cold.acceptance` this
repair introduced, that is a smaller change and I will take it — but I am not going to make it silently.
