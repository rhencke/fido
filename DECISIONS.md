# Decisions

Every current human decision, accepted or open. **Rob alone decides.** One row per decision; edit the row
when it changes. Git history owns the previous row and the debate that produced it.

A settled decision reopens only through Rob, and only on new information: a spec fact, a proof obstruction,
an implementation fact, or a changed project goal.

## Accepted

| id | status | decision | reopen_trigger |
|---|---|---|---|
| ADR-0001 | ACCEPTED | Pinned target: Go 1.23 on `linux/amd64` with `GOAMD64=v1`. `int` and `uint` are 64-bit and DISTINCT from `int64`/`uint64`. There is no `TargetConfig`. | C16, or any earlier request for another target or for `uintptr`. |
| ADR-0003 | ACCEPTED | Authority ordering: definite Go spec text owns meaning; the pinned `gc` owns target acceptance and adequacy where the spec permits latitude; `gc` never narrows required formal latitude. | New evidence of a definite spec/toolchain conflict. |
| LAT-X004 | ACCEPTED | Permitted rounding while computing untyped floating-point and complex constant expressions is settled as option (ii): the rounding-invariant accepted domain. | A measured proof cost or spec reading that defeats the invariant domain. |
| SR-001 | ACCEPTED | The pinned linux/amd64 64-bit validation target, as recorded in `.review/scope.tsv`. | As ADR-0001. |

## Open

| id | status | decision | reopen_trigger |
|---|---|---|---|
| ADR-0002 | OPEN | The bounded `Float.Decimal` literal domain (`\|coeff\| < 10^40`, `\|exp10\| ≤ 4096`) stands as an explicit unresolved restriction. It carries no new correctness claim. | Before C7 accepts broader floating constants, or when measured proof cost justifies a replacement. |
| ADR-0004 | DEFERRED | The multi-platform 64-bit target set. No target beyond go1.23.2 linux/amd64 is covered. | C16. |
| TOOLCHAIN-PROVENANCE | OPEN | Replace the pending local-distribution evidence with verified official tarball bytes, or expressly accept `PASS-WITH-PENDING-PROVENANCE` for a specific use. Identities in `TOOLCHAIN.md` are exact; their chain to go.dev is not. | Any claim that depends on toolchain provenance rather than toolchain identity. |
| EXTERNAL-EVIDENCE | OPEN | Commit the external Go-distribution evidence components into a Git subtree, or expressly retain them as external `PROVENANCE-PENDING` references. Their bytes are not in Git, so their recorded hashes cannot be recomputed from the repository. | A requirement to recompute external evidence from the repository alone. |
| SCOPE-APPROVAL | OPEN | Accept or amend the eight `PROPOSED`/`UNRESOLVED` rows in `.review/scope.tsv` (SR-002 … SR-009). Each states a live restriction; none has been explicitly accepted. | Any of those restrictions being challenged, or a milestone that needs one lifted. |
| ASSUMPTION-GATE-PLACEMENT | OPEN | `rocq c gate/Assumptions.v` costs ≈77 s — 59% of a cold `prove` and 29% of a cold `make check` — while the strictly stronger whole-theory `Fido Audit Assumptions` costs 1.7 s. Options: keep it as is (the default); keep it but move it off ordinary acceptance to `make audit-fresh` and pre-freeze verification; shrink it to a stated rule. Measured evidence is in Git history at `3b9c103`. | Rob deciding, or a cold-path cost that stops being tolerable. |
