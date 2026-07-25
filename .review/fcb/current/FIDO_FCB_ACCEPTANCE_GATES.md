# Fido FCB Acceptance Gates

> **Derived reference, not implementation authority.** The code and its gated theorems are the sole implementation authority.  
> **Living document.** Its identity is its Git blob at the exact ref resolved for the task; its
> history is the commit log. No version suffixes, no checksum manifest.  
> **Accepted amendments:** `FCB-A001-INTRINSIC-STATIC-CAPABILITY-PROVENANCE`; `FCB-A002-GIT-CANONICAL-FCB-STORAGE`; `FCB-A003-LIVING-DOCUMENTATION`.
> **Proposed, awaiting Rob:** `FCB-A004-GIT-RESOLVABLE-LIVING-CORPUS`.  
> **Canonical live location:** `.review/fcb/current/` in the exact Git ref used for the task.  
> **Stable bootstrap:** `.review/fcb/current/INDEX.md`  
> Project libraries contain only a bootstrap shim. They do not contain or own the FCB corpus.  
> Regenerate, verify, and commit affected FCB files in Git after each accepted checkpoint or amendment.  
> This corpus does not accept C4 and does not authorize C5; `.review/NEXT_STEPS.md` remains the live checkpoint authority.


These are the standing compile-acceptance obligations. A row is discharged only when its checkpoint implements the Fido rule and records both halves: the pinned-gc observation under the sanctioned probe profile and the exact Fido diagnostic. Until then, `PENDING-IMPLEMENTATION` is the only honest status.

## Gate index

| Latitude | Checkpoint | Diagnostic | Fixture(s) | Owner contracts | Status |
|---|---:|---|---|---|---|
| LAT-019 | C6 | `FIDO-E-CONSTANT-PRECISION` | lat019_shift_511_accept; lat019_shift_512_reject | SC-22 / SC-02 / SC-05 | PENDING-IMPLEMENTATION |
| LAT-049 | C13 | `FIDO-E-UNION-TERM-RESTRICTION` | lat049_union_method_reject | SC-22 / SC-04 / SC-13 | PENDING-IMPLEMENTATION |
| LAT-077 | C6 | `FIDO-E-UNUSED-LOCAL` | lat077_unused_local_reject | SC-22 / SC-03 | PENDING-IMPLEMENTATION |
| LAT-085 | C13 | `FIDO-E-EMPTY-TYPE-SET-OPERAND` | lat085_empty_type_set_operand_reject | SC-22 / SC-05 / SC-13 | PENDING-IMPLEMENTATION |
| LAT-148 | C8 | `FIDO-E-DUPLICATE-SWITCH-CASE` | lat148_duplicate_switch_case_reject | SC-22 / SC-06 | PENDING-IMPLEMENTATION |
| LAT-171 | C9 | `FIDO-E-SHADOWED-RESULT-RETURN` | lat171_shadowed_result_naked_return_reject | SC-22 / SC-06 / SC-07 | PENDING-IMPLEMENTATION |
| LAT-177 | C7 | `FIDO-E-PRINT-OPERAND-TYPE` | lat177_print_struct_reject | SC-22 / SC-15 | PENDING-IMPLEMENTATION |

## LAT-019 — FIDO-E-CONSTANT-PRECISION

**Implementing checkpoint:** `C6`  
**Owner contracts:** SC-22 / SC-02 / SC-05  
**Status:** `PENDING-IMPLEMENTATION`

**Required Fido diagnostic shape:** constant expression exceeds the countersigned accepted precision domain

**Pinned-gc fixtures:**

- `lat019_shift_511_accept` — mode `build`, status `0`, first stderr line: `(empty)`
- `lat019_shift_512_reject` — mode `build`, status `1`, first stderr line: `# example.com/fido/specclosure/lat019_shift_512_reject`

**Discharge rule:**

1. Keep the fixture source byte-exact unless the contract is re-frozen.
2. Replay pinned gc under `FIDO_FCB_TOOLCHAIN_EVIDENCE.md`.
3. Run Fido elaboration through the production path.
4. Require diagnostic ID `FIDO-E-CONSTANT-PRECISION` and the frozen text/shape.
5. Add the theorem or constructor-absence proof named by the checkpoint contract.
6. Mark the row discharged only after Rob accepts the checkpoint and the FCB is regenerated.

## LAT-049 — FIDO-E-UNION-TERM-RESTRICTION

**Implementing checkpoint:** `C13`  
**Owner contracts:** SC-22 / SC-04 / SC-13  
**Status:** `PENDING-IMPLEMENTATION`

**Required Fido diagnostic shape:** multi-term union contains comparable, methods, or an embedded interface containing them

**Pinned-gc fixtures:**

- `lat049_union_method_reject` — mode `build`, status `1`, first stderr line: `# example.com/fido/specclosure/lat049_union_method_reject`

**Discharge rule:**

1. Keep the fixture source byte-exact unless the contract is re-frozen.
2. Replay pinned gc under `FIDO_FCB_TOOLCHAIN_EVIDENCE.md`.
3. Run Fido elaboration through the production path.
4. Require diagnostic ID `FIDO-E-UNION-TERM-RESTRICTION` and the frozen text/shape.
5. Add the theorem or constructor-absence proof named by the checkpoint contract.
6. Mark the row discharged only after Rob accepts the checkpoint and the FCB is regenerated.

## LAT-077 — FIDO-E-UNUSED-LOCAL

**Implementing checkpoint:** `C6`  
**Owner contracts:** SC-22 / SC-03  
**Status:** `PENDING-IMPLEMENTATION`

**Required Fido diagnostic shape:** local variable is declared and not used

**Pinned-gc fixtures:**

- `lat077_unused_local_reject` — mode `build`, status `1`, first stderr line: `# example.com/fido/specclosure/lat077_unused_local_reject`

**Discharge rule:**

1. Keep the fixture source byte-exact unless the contract is re-frozen.
2. Replay pinned gc under `FIDO_FCB_TOOLCHAIN_EVIDENCE.md`.
3. Run Fido elaboration through the production path.
4. Require diagnostic ID `FIDO-E-UNUSED-LOCAL` and the frozen text/shape.
5. Add the theorem or constructor-absence proof named by the checkpoint contract.
6. Mark the row discharged only after Rob accepts the checkpoint and the FCB is regenerated.

## LAT-085 — FIDO-E-EMPTY-TYPE-SET-OPERAND

**Implementing checkpoint:** `C13`  
**Owner contracts:** SC-22 / SC-05 / SC-13  
**Status:** `PENDING-IMPLEMENTATION`

**Required Fido diagnostic shape:** operator has no admissible operand type because the type set is empty

**Pinned-gc fixtures:**

- `lat085_empty_type_set_operand_reject` — mode `build`, status `1`, first stderr line: `# example.com/fido/specclosure/lat085_empty_type_set_operand_reject`

**Discharge rule:**

1. Keep the fixture source byte-exact unless the contract is re-frozen.
2. Replay pinned gc under `FIDO_FCB_TOOLCHAIN_EVIDENCE.md`.
3. Run Fido elaboration through the production path.
4. Require diagnostic ID `FIDO-E-EMPTY-TYPE-SET-OPERAND` and the frozen text/shape.
5. Add the theorem or constructor-absence proof named by the checkpoint contract.
6. Mark the row discharged only after Rob accepts the checkpoint and the FCB is regenerated.

## LAT-148 — FIDO-E-DUPLICATE-SWITCH-CASE

**Implementing checkpoint:** `C8`  
**Owner contracts:** SC-22 / SC-06  
**Status:** `PENDING-IMPLEMENTATION`

**Required Fido diagnostic shape:** duplicate constant case expression in one expression switch

**Pinned-gc fixtures:**

- `lat148_duplicate_switch_case_reject` — mode `build`, status `1`, first stderr line: `# example.com/fido/specclosure/lat148_duplicate_switch_case_reject`

**Discharge rule:**

1. Keep the fixture source byte-exact unless the contract is re-frozen.
2. Replay pinned gc under `FIDO_FCB_TOOLCHAIN_EVIDENCE.md`.
3. Run Fido elaboration through the production path.
4. Require diagnostic ID `FIDO-E-DUPLICATE-SWITCH-CASE` and the frozen text/shape.
5. Add the theorem or constructor-absence proof named by the checkpoint contract.
6. Mark the row discharged only after Rob accepts the checkpoint and the FCB is regenerated.

## LAT-171 — FIDO-E-SHADOWED-RESULT-RETURN

**Implementing checkpoint:** `C9`  
**Owner contracts:** SC-22 / SC-06 / SC-07  
**Status:** `PENDING-IMPLEMENTATION`

**Required Fido diagnostic shape:** naked return is used while a named result is shadowed

**Pinned-gc fixtures:**

- `lat171_shadowed_result_naked_return_reject` — mode `build`, status `1`, first stderr line: `# example.com/fido/specclosure/lat171_shadowed_result_naked_return_reject`

**Discharge rule:**

1. Keep the fixture source byte-exact unless the contract is re-frozen.
2. Replay pinned gc under `FIDO_FCB_TOOLCHAIN_EVIDENCE.md`.
3. Run Fido elaboration through the production path.
4. Require diagnostic ID `FIDO-E-SHADOWED-RESULT-RETURN` and the frozen text/shape.
5. Add the theorem or constructor-absence proof named by the checkpoint contract.
6. Mark the row discharged only after Rob accepts the checkpoint and the FCB is regenerated.

## LAT-177 — FIDO-E-PRINT-OPERAND-TYPE

**Implementing checkpoint:** `C7`  
**Owner contracts:** SC-22 / SC-15  
**Status:** `PENDING-IMPLEMENTATION`

**Required Fido diagnostic shape:** print or println operand type is outside the pinned accepted profile

**Pinned-gc fixtures:**

- `lat177_print_struct_reject` — mode `build`, status `1`, first stderr line: `# example.com/fido/specclosure/lat177_print_struct_reject`

**Discharge rule:**

1. Keep the fixture source byte-exact unless the contract is re-frozen.
2. Replay pinned gc under `FIDO_FCB_TOOLCHAIN_EVIDENCE.md`.
3. Run Fido elaboration through the production path.
4. Require diagnostic ID `FIDO-E-PRINT-OPERAND-TYPE` and the frozen text/shape.
5. Add the theorem or constructor-absence proof named by the checkpoint contract.
6. Mark the row discharged only after Rob accepts the checkpoint and the FCB is regenerated.
