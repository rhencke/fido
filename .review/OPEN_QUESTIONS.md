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
