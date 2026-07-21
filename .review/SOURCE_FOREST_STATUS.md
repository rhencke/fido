# Source Forest Campaign — Status Ledger

Campaign: **Specification-Shaped Source Forest, Snapshot-Local Occurrence Identity, and Occurrence-Anchored
Compilation.** The full design is `.review/SOURCE_FOREST_MASTER_PLAN.md`; Git history is the detailed archive.

## Authority

- Active checkpoint: **C4** — source type names, compiler resolution, and unified numeric conversions.
- Functional contract: `.review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md`.
- Contract SHA-256: `9ec55b38444e3a32eaf6cb024f72285527992ba1612dabfdc99ce6f89c8517b4`.
- Accepted review basis: `.review/REVIEW_BASIS.md`.
- Baseline: `8c9212a8c814c7a99a5e3ef1970a0ae32425a918`.
- Human authorization: `C4-source-type-resolution-1`.
- Automatic Codex review: DISABLED. The directive is the accepted human Contract Review; the candidate is
  frozen and reported for Rob's human Implementation Review — no Codex review is requested or run.
- C5 and every later checkpoint remain forbidden.

## Completed checkpoints

| Checkpoint | Scope | Result |
|---|---|---|
| C0 / C0A / C0B | occurrence-index proof spike, snapshot-local identity, exact source correspondence | GREEN, human-approved |
| C1 / C1A / C1B | specification-shaped files, path-keyed source forest, standard collections | GREEN, human-approved |
| C2 | production occurrence index, references, navigation, indexed traversal | GREEN, human-approved |
| C3 | fresh-image literal-build closeout: exact `go build ./...` acceptance model, fresh-build runner, publication workflow, source type/package semantics | **ACCEPTED** by Rob at baseline `8c9212a` |

## C4 implementation state

Active under this contract.  Goal: replace the three family-specific conversion constructors
(`EIntConvert`/`EFloatConvert`/`EComplexConvert`) with one source-shaped `EConvert TypeSyntax GoExpr`; resolve
the source type name in `GoCompile` through the current predeclared context; retain occurrence-keyed type-name
facts; render from the source spelling; and delete the old path in the same checkpoint.  Sixteen live target
names (the fourteen existing numeric names plus the `byte`→`uint8` and `rune`→`int32` source aliases); no new
semantic types.  No C5 work (no `uintptr`, no rune literals/constants).

- Candidate SHA: _pending freeze after implementation + verification._
- Gate: _baseline count recorded at implementation start; final count reported at freeze._
- Verification: _pending._
- Human C4 Implementation Review: pending after the candidate is frozen.

## Standing decisions

- Platform resource limits such as NAME_MAX, PATH_MAX, disk, and memory are outside the semantic model.
- Contract Review precedes implementation for checkpoints activated after the policy was adopted. C3 was the
  explicit transition exception; C4's Contract Review is Rob's directive itself, with the automatic Codex
  review path disabled.
- Each review permits at most one bounded confirmation. A blocking confirmation returns control to Rob.
