# M3 Contract Amendment 2 — `M3-A2`

status: ACCEPTED
amends: .review/M3_TOOL_AND_BUILD_ARCHITECTURE_AUDIT.md, activation 0b7fd86825936c37f31ef83879574d526d548122
specified by: .review/M3_FORENSIC_AUDIT_REPAIR_2.md §2.3
green contract review: .review/M3_FORENSIC_AUDIT_REPAIR_2.md §2.3
authorized by: **Rob**, 2026-08-04 — approving M3-A1 and M3-A2 as stated in M3 Implementation
Repair 2. Recorded because he said so, not inferred from an upload, from "ready", or from any
other act.

## Why

The frozen contract's mandatory finding read:

```text
M3-CLAIM-SUBJECT   remove the need for a manually retargeted active-checkpoint constant
```

My audit kept `TSV_REL` and proposed deleting only a stale docstring path. That closes the drift I found but
does not satisfy the finding as written — the constant is still hand-retargeted at every checkpoint. I
recorded it as satisfied, and it was not.

Dynamic discovery is not the repair either. A gate that finds one matching matrix file still does not know
the exact required obligation IDs, and parsing review prose to learn them would create a second current-state
authority — the very shape this project forbids.

## The amendment

`M3-CLAIM-SUBJECT` is replaced, in full, by:

> `M3-CLAIM-SUBJECT` requires one explicit claim-matrix subject object which owns both the active matrix path
> and the complete required obligation-ID set. The gate, its messages, and its controls read that one object.
> No docstring, parallel constant, Make recipe, hook line, or review-state parser duplicates or infers the
> subject. A checkpoint transition retargets exactly that one object.

This replaces only the wording of `M3-CLAIM-SUBJECT`. **No other M3 contract clause changes**, and this
amendment authorizes no tool change by itself — the work is `M4-07`, which M4 performs only after Rob
approves the plan.

## What satisfies it

Two constants become one object, with one place to retarget:

```python
SUBJECT = ClaimMatrixSubject(
    matrix=".review/M4_OBLIGATION_MATRIX.tsv",
    required=("M4-01", ...),
)
```

The concrete form is a frozen tuple, named tuple or frozen dataclass from the standard library — a thin
domain wrapper, which the collection law allows. It is one object, not two authorities.

`load_rows`, the diagnostics, the required-row closure, the controls, and the module's own current-subject
prose all consume `SUBJECT`. No matrix path appears in the module docstring.

**Not authorized by this amendment:** dynamic discovery, a new file, a registry, a schema, or a review-state
parser.

## Scope this amendment does NOT grant

It is not authority to redesign the claim gate, to change what the matrix relation checks, or to alter any
other tool. `M3-A1` remains the only project-tool change M3 itself makes.
