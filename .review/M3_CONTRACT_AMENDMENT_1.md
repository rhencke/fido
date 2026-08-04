# M3 Contract Amendment 1 — `M3-A1`

status: ACCEPTED
amends: .review/M3_TOOL_AND_BUILD_ARCHITECTURE_AUDIT.md, activation 0b7fd86825936c37f31ef83879574d526d548122
specified by: .review/M3_FORENSIC_AUDIT_REPAIR_1.md §2
green contract review: .review/M3_FORENSIC_AUDIT_REPAIR_2.md §2.1
authorized by: **Rob**, 2026-08-04 — approving M3-A1 and M3-A2 as stated in M3 Implementation
Repair 2. Recorded because he said so, not inferred from an upload, from "ready", or from any
other act.

**Authority correction.** This document previously recorded the reviewer as having authorized the amendment.
That was false and it was mine: a reviewer specifies an amendment, and Rob alone accepts one. The technical
content below and the tool bytes it describes are unchanged — `.review/M3_FORENSIC_AUDIT_REPAIR_2.md` §2.1
gave them GREEN Contract Review — and only the authority line changed.

## The conflict

The frozen M3 contract requires all twelve obligations closed and all gates green (§11), and forbids M3 from
changing any project tool (§9). Those are jointly unsatisfiable.

`tools/claim-matrix-gate.py` cannot construct its `rename_named_surface` control when every closed row
legitimately carries an `unsupported-boundary` implementation cell — which is what a documentation-only
checkpoint honestly has, because it declares no code surface. `ensure_closed_row` guaranteed only that *some*
row was closed; the control needed one naming a movable `.v` declaration or Python `def`/`class`. The
synthetic row exists for exactly this case but was never appended while any other closed row existed.

M3 stopped rather than fabricate an implementation surface or accept an open matrix.

## The amendment

> M3 may change `tools/claim-matrix-gate.py` and the claim-matrix entries in `tools/gate-mutation-test.py`
> only to repair the self-test precondition which prevents a documentation-only checkpoint from closing its
> obligation matrix. No other project-tool change is authorized in M3.

This supersedes exactly two things and nothing else:

1. M3 contract §9's prohibition on project-tool changes — **for these two files and this one defect only**;
2. obligation `M3-11`'s absolute "no tool change" claim, which is replaced by:

> M3 changes no production, proof, Make, hook, Docker, Dune, generated, or runtime path. Its only
> project-tool change is the reviewed claim-matrix self-test precondition repair required to close a
> documentation-only matrix.

No other contract clause changes. The frozen contract text itself is not edited; this document is the
instrument that supersedes those two points, and the obligation matrix carries the revised `M3-11` claim.

## What was changed under it

```text
tools/claim-matrix-gate.py    renameable_declaration()  — the ONE meaning of "a declaration the rename
                              control can move", read-only, shared by the precondition and the control so
                              they cannot drift apart again
                              ensure_closed_row(..., require_declaration=False) — mirrors the existing
                              require_builder flag; appends the synthetic row when no live closed row
                              satisfies the required shape
                              rename_named_surface() — calls it with require_declaration=True and reuses
                              the shared predicate instead of re-deriving the regex
                              four new controls (25 total, was 21)
tools/gate-mutation-test.py   one mutation entry removing the require_declaration effect (43 total, was 42)
```

Nothing else in either file changed, and no other tool changed.

## Controls

```text
closed rows are all documentation-only boundaries              synthetic row appended, control constructible
a closed row already names a movable declaration               no synthetic row added
a Makefile target is not a movable declaration                 synthetic row appended (a Make target and a
                                                               shell function are declarations the matrix
                                                               accepts but this control cannot move)
a documentation-only all-closed matrix still constructs        run() accepts it, the rename fires, and the
  the rename control                                           gate notices for the intended reason
a named implementation surface was renamed                     unchanged; still fails for its stated reason
```

The mutation entry `the movable-declaration precondition for the rename control` removes the new condition;
the first and fourth controls above must then fail, by name.

## Scope this amendment does NOT grant

It is not authority for a general claim-gate redesign, a new fixture system, a second predicate for
declaration shape, mutation coverage of other helpers (that stays `M4-09`), or any other tool change.
