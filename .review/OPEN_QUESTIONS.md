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

## OQ-M2-02 — should the observatory run inside buildx, so the host needs no Python?

**Owner:** Rob, for M3. **Blocks M2:** no. **Default if unanswered:** the observatory stays a host-side
Python tool.

Rob's direction, recorded here so it is not lost with the chat. `tools/build-observatory.py` runs on the
host and requires Python there, which makes the measurement environment the developer's machine rather than
a pinned one. Everything else in this repository is hermetic: the proof, the emission, the e2e and the
generated-byte compare all run inside pinned images, and `make check` states plainly that a local host Rocq
is not supported. The timing facility is the exception.

The shape Rob described: an OUTER harness that can talk to buildx and drives an INNER harness, both in
buildx. The objection I had raised — that a containerised harness would perturb the timings it collects —
does not apply, because the harness does not measure itself. Its own cost only has to stay small relative
to the work under measurement, not be accounted for.

This is tool architecture, which M3 owns. The accepted M2 repair may not change it: §13 forbids changes to
M3 or M4 tool and build architecture, and the cache-cut amendment does not authorize Make or hook
architecture refactoring. So M2 records the direction and implements none of it.

Two things a decision will have to settle. The outer harness needs the Docker socket to drive buildx, which
is a different trust posture from the current host tool and should be stated deliberately rather than
inherited. And the pre-commit anchors are written by `/bin/sh` inside the hook on the host; if the hook
itself remains host-side, its instrumentation stays host-side with it, so "no Python on the host" and "no
host-side measurement" are not the same goal and the decision should say which one it is buying.
