# Decisions

Every current human decision, accepted or open. **Rob alone decides.** One row per decision; edit the row
when it changes. Git history owns the previous row and the debate that produced it.

A settled decision reopens only through Rob, and only on new information: a spec fact, a proof obstruction,
an implementation fact, or a changed project goal.

## Accepted

| id | status | decision | reopen_trigger |
|---|---|---|---|
| ADR-0001 | ACCEPTED | Pinned target: Go 1.23 on `linux/amd64` with `GOAMD64=v1`. `int` and `uint` are 64-bit and DISTINCT from `int64`/`uint64`. There is no `TargetConfig`. No other OS or architecture is validated. `.review/scope.tsv` row `SR-001` records the boundary this decision draws and what enforces it. | C16, or any earlier request for another target or for `uintptr`. |
| ADR-0003 | ACCEPTED | Authority ordering: definite Go spec text owns meaning; the pinned `gc` owns target acceptance and adequacy where the spec permits latitude; `gc` never narrows required formal latitude. | New evidence of a definite spec/toolchain conflict. |
| LAT-X004 | ACCEPTED | Permitted rounding while computing untyped floating-point and complex constant expressions is settled as option (ii): the rounding-invariant accepted domain. | A measured proof cost or spec reading that defeats the invariant domain. |
| ASSUMPTION-GATE-PLACEMENT | ACCEPTED | Delete `gate/Assumptions.v`. The certified-module coverage check, the whole-theory `Fido Audit Assumptions`, and adversarial controls A-E **jointly** own the build-time zero-project-axiom claim; no one of the three is sufficient alone. The handwritten list owned no public-surface guarantee: it was a hand-picked subset with no rule deriving it, weaker in coverage than the audit it sat beside, and it cost ≈77 s against the audit's 1.7 s. | Evidence that this retained chain misses a tracked certified module, Rocq declaration root, or disallowed assumption category. |

## Open

| id | status | decision | reopen_trigger |
|---|---|---|---|
| ADR-0002 | OPEN | The bounded `Float.Decimal` literal domain (`\|coeff\| < 10^40`, `\|exp10\| ≤ 4096`) stands as an explicit unresolved restriction. It carries no new correctness claim. | Before C7 accepts broader floating constants, or when measured proof cost justifies a replacement. |
| ADR-0004 | DEFERRED | The multi-platform 64-bit target set. No target beyond go1.23.2 linux/amd64 is covered. | C16. |
| TOOLCHAIN-PROVENANCE | OPEN | Replace the pending local-distribution evidence with verified official tarball bytes, or expressly accept `PASS-WITH-PENDING-PROVENANCE` for a specific use. Identities in `TOOLCHAIN.md` are exact; their chain to go.dev is not. | Any claim that depends on toolchain provenance rather than toolchain identity. |
| EXTERNAL-EVIDENCE | OPEN | Commit the external Go-distribution evidence components into a Git subtree, or expressly retain them as external `PROVENANCE-PENDING` references. Their bytes are not in Git, so their recorded hashes cannot be recomputed from the repository. | A requirement to recompute external evidence from the repository alone. |
| SCOPE-APPROVAL | OPEN | Accept or amend the eight `PROPOSED`/`UNRESOLVED` rows in `.review/scope.tsv` (SR-002 … SR-009). Each states a live restriction; none has been explicitly accepted. | Any of those restrictions being challenged, or a milestone that needs one lifted. |
| SOURCE-CHARSET | OPEN | Normalize tracked text to ASCII where a character is typographic, keeping UTF-8 only where it carries meaning. ASCII is keyboard- and grep-friendly for an English codebase; UTF-8 is not a defect. Measured at `b8fb1d7` (this row's own characters would otherwise change the count): 1,575 non-ASCII characters across 41 tracked files, 94% of them em-dash (912) and box-drawing (584), both purely typographic. Every `.v` occurrence sits inside a comment; no certified code, generated Go byte or golden contains one. Load-bearing and must stay: verbatim pinned-spec quotations in `.review/latitude.tsv` (including `日` and `ø`), and the `✓` in gate output. One stray `’` remains at `.review/latitude.tsv:188`, the tree's only curly apostrophe. | Rob deciding, or a normalization pass being folded into a milestone that already touches these files. |
