# FIDO — VOLLEY RETURN 2 BRIEF

**Date:** 2026-07-24  
**Reviewed artifact:** `FIDO_TERMINAL_CORRECTNESS_DIRECTIVE_v11_2026-07-24.md`  
**Reviewed SHA-256:** `428c609766f08025686580ab88fa25c02e06fb339629c10ec6023ed9c77d7540`  
**Amended artifact:** `FIDO_TERMINAL_CORRECTNESS_DIRECTIVE_v12_2026-07-24.md`  
**Amended SHA-256:** `89d0c88b05d833803cd9e33652edf7aa745ef74e17f7ea0a34377ab450f8779a`

## Return disposition

The sent package was amended in place and returned as one canonical ZIP. No architecture, language-semantics, latitude-policy, or toolchain-policy change was needed.

### REOPENS(D-15) — late-governance inventory disagreement

v11 generated the fixed-point manifest after the audit and freeze, but its inventory-completeness sentence still allowed only the audit JSON, freeze record, and SHA manifest after phase 1. The final-set equation allowed four late files while the inventory rule allowed three.

**Repair:** v12 defines one `late_governance_outputs` set and reuses it in the phase-1 inventory rule, final-set equation, build order, Appendix note, and terminal-verifier obligation.

**Regression gate:** directive linter `S9`; terminal check `check_late_artifact_inventory_consistent`; ratchet D-19.

### REGRESSION(D-06) — stale live directive identity

v11's read-only evidence rule said “This v10 directive enters the bundle.”

**Repair:** v12 identifies itself consistently and makes live identity one checked tuple.

**Regression gate:** directive linter `S8`; terminal check `check_live_directive_identity`; ratchet D-18.

### NEW — contradictory recurrence count

v11 described the self-reference class as its fifth occurrence and later said the count remained four.

**Repair:** v12 states both facts as five.

**Regression gate:** directive linter `S11`; ratchet D-21.

### NEW — verifier checks were not a closed inventory

v11 added `check_artifact_graph_acyclic` and `check_derived_governance_ownership`, but the directive-pinned function list did not include them and did not close the set of cited checks.

**Repair:** v12 supplies one closed audit/verifier function inventory and an exact ownership split.

**Regression gate:** directive linter `S10`; ratchet D-20.

### Rob format correction

Protocol v2's Markdown-only return rule was wrong for this game. Protocol v3 records Rob's direct rule: a return volley is an amended canonical ZIP in the same package form. `tools/validate_return.py` now validates the ZIP itself, its manifest, version increment, supersedes handshake, directive linter, and four negative controls.

**Regression gate:** package validator and ratchet D-17.

## Literal verification output

### Sent package manifest and hash handshake

```text
$ sha256sum -c MANIFEST.sha256
FIDO_TERMINAL_CORRECTNESS_DIRECTIVE_v11_2026-07-24.md: OK
FIDO_VOLLEY_PROTOCOL_SAFETIES_v2.md: OK
FIDO_VOLLEY_ADJUDICATION_BRIEF_2026-07-24.md: OK
README.md: OK
tools/lint_directive.py: OK
tools/validate_return.py: OK

$ sha256sum FIDO_TERMINAL_CORRECTNESS_DIRECTIVE_v11_2026-07-24.md
428c609766f08025686580ab88fa25c02e06fb339629c10ec6023ed9c77d7540  FIDO_TERMINAL_CORRECTNESS_DIRECTIVE_v11_2026-07-24.md
```

### Amended directive lint

```text
$ python3 tools/lint_directive.py FIDO_TERMINAL_CORRECTNESS_DIRECTIVE_v12_2026-07-24.md
LINT CLEAN — FIDO_TERMINAL_CORRECTNESS_DIRECTIVE_v12_2026-07-24.md
```

### Negative controls

```text
$ python3 tools/lint_directive.py <S8-negative-control>
LINT FINDINGS — FIDO_TERMINAL_CORRECTNESS_DIRECTIVE_v12_CONTROL_S8.md
  S8 stale live-version self-reference: line 94: v11 in v12
  S8 missing live-version self-reference for v12
CONTROL S8: PASS

$ python3 tools/lint_directive.py <S9-negative-control>
LINT FINDINGS — FIDO_TERMINAL_CORRECTNESS_DIRECTIVE_v12_CONTROL_S9.md
  S9 late-artifact-set: expected ['audit json', 'fixed-point manifest', 'freeze record', 'sha manifest'], found ['audit json', 'freeze record', 'sha manifest']
CONTROL S9: PASS

$ python3 tools/lint_directive.py <S10-negative-control>
LINT FINDINGS — FIDO_TERMINAL_CORRECTNESS_DIRECTIVE_v12_CONTROL_S10.md
  S10 check-inventory: cited but undeclared ['check_unregistered_regression']
CONTROL S10: PASS

$ python3 tools/lint_directive.py <S11-negative-control>
LINT FINDINGS — FIDO_TERMINAL_CORRECTNESS_DIRECTIVE_v12_CONTROL_S11.md
  S11 provenance-count mismatch: self-reference counts [5, 4]
CONTROL S11: PASS
```

### Package validation

The final package validator output is reproduced below after the archive is built. The validator re-runs the manifest, version/hash handshake, amended linter, and all four controls.

```text
D-14 sent handshake OK: v11 428c609766f08025686580ab88fa25c02e06fb339629c10ec6023ed9c77d7540
ARCHIVE canonical: 8 files under FIDO_VOLLEY_RETURN_2_2026-07-24/
D-18 directive identity OK: v12 89d0c88b05d833803cd9e33652edf7aa745ef74e17f7ea0a34377ab450f8779a
LINT CLEAN — FIDO_TERMINAL_CORRECTNESS_DIRECTIVE_v12_2026-07-24.md
CONTROL S8/S9/S10/S11: PASS
VALIDATE: ACCEPT
```
