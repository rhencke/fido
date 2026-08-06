# C6 — Declarations, scope, and the type algebra

Baseline: db73fb36b236a662910d96f5232f0f71ee32c2e9
Review: contract

Goal:
Admit declarations and named types. C6 gives the source language blocks, constant, variable and type
declarations, the blank identifier, the predeclared universe, and the type algebra those need — and keeps
static binding identity separate from runtime storage identity.

Scope — the exact rows, read from the ledger:
- 66 closure rows and 23 latitude rows whose `milestone` is `C6`;
- 27 `SPEC` rows: Variables; Types, Boolean/Numeric/String types; Properties of types and values; Underlying
  types; Core types; Type identity; Assignability; Representability; Blocks; Declarations and scope; Label
  scopes; Blank identifier; Predeclared identifiers; Exported identifiers; Uniqueness of identifiers;
  Constant declarations; Iota; Type/Alias/Type-definition declarations; Variable declarations; Short variable
  declarations; The zero value; Blank identifier occurrences;
- 17 `GRAM` rows: `Type`, `TypeName`, `TypeLit`, `Block`, `Declaration`, `TopLevelDecl`, `ConstDecl`,
  `ConstSpec`, `IdentifierList`, `ExpressionList`, `TypeDecl`, `TypeSpec`, `AliasDecl`, `TypeDef`, `VarDecl`,
  `VarSpec`, `ShortVarDecl`;
- 22 `PRE` rows: the eighteen predeclared type names plus `true`, `false`, `iota`, `nil`;
- 21 of the 23 latitude rows are `NOT-LATITUDE`; `LAT-077` is `ACCEPTANCE-ALIGNMENT` and `LAT-X004` is
  `PROVED-REFINEMENT`.

This is a full vertical, not a static addition. Every new AST constructor needs exact whole-program
`Admissible` rules matching `go build ./...`, meaning in `Property`, renderer support with its value and
syntax proofs, and a differential fixture and e2e witness where observable. The fragment today is one
`func main()` with no declarations at all.

Contract slices — C6 consumes only these, and closes no case assigned to a later milestone:
- SC-03 blocks, scope, declarations, blank uses, identifier uniqueness and export, and predeclared
  shadowing. **Not** per-iteration variables or closure capture, which need loops (C8) and closures (C9),
  and **not** the `_ = f()` fixture, which needs a user function call (C9);
- SC-04 the type algebra over predeclared, alias and defined types: underlying and core types, identity,
  assignability, representability. **No** structural type — array, slice, struct, pointer, map, channel or
  function type — and no generics;
- SC-05 the `Blank identifier occurrences` row only;
- SC-08 the `Variables` row only: static slot identity separate from dynamic place identity. No object store;
- SC-14 the zero value only. No package initialization, `init`, or program start;
- SC-21 the public surface stays exact and minimal, every proof helper local;
- SC-22 the two acceptance gates below.

Acceptance gates, both firing at C6 (`.review/acceptance.tsv`):
- `LAT-077` — `FIDO-E-UNUSED-LOCAL`, a local variable declared and not used, fixture
  `lat077_unused_local_reject`;
- `LAT-019` — `FIDO-E-CONSTANT-PRECISION`, a constant expression outside the accepted precision domain,
  fixtures `lat019_shift_511_accept` and `lat019_shift_512_reject`. Its latitude row is `C7`, but the gate
  is C6's, so C6 must land the accepted domain that `DECISIONS.md` `LAT-X004` settled as option (ii).

Open questions this contract review must settle:
1. **Type-growth order.** `ROADMAP.md` "How the language grows" states the reviewed order as `uintptr` and
   exact rune constants, then unnamed structural types, then aliases and defined types. C6's rows require
   alias and defined types (`SPEC-052`, `SPEC-053`, `SPEC-054`) while structural types stay at C10. Either
   the stated order is wrong, or these three rows do not belong to C6. **This is a conflict between an
   accepted document and an accepted ledger, and I have not resolved it.**
2. **Declaration surface.** `Syntax.File` currently admits only `Syntax.Main`. Whether C6 admits top-level
   declarations, function-local declarations, or both decides the size of the milestone and the shape of
   every `Admissible` rule in it.
3. **Split.** Whether 66 rows spanning two SC contracts and a full AST vertical is one milestone or two.

Preserve:
- `Syntax.Program` as the sole source authority, and the AST as the one IR;
- the exact retained `Compilable.Program`, `Failure` and whole-elaboration cores;
- `Machine.T` exactly as C5 froze it, with no inhabitant and no importer;
- direct rendering and the one `Emit.Mint.issue` authority;
- certified-module coverage, the whole-theory audit, and controls A-E;
- every sealed-capability, mint, transport and positive client control;
- working-tree and staged-index separation, and no-host-Python;
- every currently accepted and rejected program, and every current diagnostic;
- `life.md`.

Done:
- every C6 closure and latitude row is discharged or explicitly repriced under review;
- both acceptance gates discharge with their exact diagnostics and fixtures;
- no structural type, loop, closure, user function, object store or package initialization appears;
- `make prove`, `make check`, `make audit-fresh`, `make regenerate`, `make regen-guard` pass;
- generated bytes change only where a new admitted construct is actually rendered, with goldens updated in
  the same commit and the differential evidence to justify them;
- one whole-system implementation review passes, then Rob accepts C6.

Stop:
- open question 1 is not settled before implementation begins;
- a C6 row needs a construct assigned to a later milestone;
- a new AST constructor cannot land complete, with its `Admissible` rule, `Property` meaning, rendering
  proofs and differential evidence together;
- an acceptance gate needs a diagnostic the elaboration cannot produce from the retained object;
- implementation needs a placeholder, compatibility path, trusted shortcut, fuel, bound, or premature future
  state.
