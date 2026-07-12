# Fido — operating law for a theorem-first repository

**A proved Go generator.** Rocq builds a certified spine — `GoAst` → `GoPrint` → `GoTypes` → `GoCompile`
→ `GoEmit` — that constructs a Go program, type-checks it, proves its printed bytes, and emits them.
**Standard Rocq extraction** turns the closed certified output (`GoEmit.demo_emit`, whose exact bytes are
machine-checked by `demo_emit_bytes`) into OCaml; a **one-line writer, generated at build time and never
tracked**, prints those bytes to a `.go`; the pinned Go toolchain confirms it compiles. **There is no
handwritten OCaml backend and no extraction plugin.** The honest headline: **a verified printer / type
checker / emitter over a Rocq-constructed AST, extracted by standard Rocq extraction** — never "formally
verified Go" (Go's toolchain is trusted; there is no theorem that Go parses the bytes as the same AST).
**Current state and gates: `PROGRESS.md`. Architecture charter (binding): `ARCHITECTURE.md`.**

## The law

**There is no transition. There is only the intended architecture and things that should be deleted.**
**Ruthless correctness or ruthless deletion — no middle state.** Nothing load-bearing may rest on an
unsettled abstraction. If a foundation is wrong, incomplete, trusted-rather-than-proved, or narrower than
the intended final claim, delete the upper floors; a right idea reappears when the correct foundation
requires it. Git history is the only archaeology.

Nobody depends on this repository. There is no backwards-compatibility obligation, no migration path, no
transition artifact. A weak, half-baked, legacy, demo-only, or convenience-oriented approach is deleted
unless it is (a) part of the intended theorem-first architecture, (b) an explicitly unsupported frontier,
or (c) an isolated integration check that cannot be mistaken for proof evidence.

**The ideal is immaculate correctness at the root, so that twenty covering leaves disappear.** Cut
supported scope before weakening proof strength. **Cost is not a constraint; incorrectness is fatal** —
never trade correctness, generality, or expressive strength for a cheaper path. Given a choice between a
cheaper/less-expressive mechanism and a harder/more-general/more-correct one, take the harder one. Plans
are best-effort guidance, not gospel: when a plan conflicts with a stronger proof or a more correct
formulation, follow the stronger path and surface the divergence.

- This is a theorem-first research repo, not a product with legacy customers.
- The certified path contains only architecture we would defend long term.
- Expressiveness expands by proof principles, never by lists of examples.
- Integration checks catch regressions; they never certify semantics, safety, termination, or Go adequacy.
- Public correctness claims must be backed by zero-axiom theorem surfaces; an ungated internal theorem is
  not public evidence.
- Unsupported features are rejected, unrepresentable, or explicitly fenced — never modeled with stubs,
  dummy panics, or conservative approximations.
- No second authority: syntax, semantics, emission, and safety each have exactly one authoritative
  definition. Never add code beside a weaker path — delete the weaker path.

## Standing technical law

1. **No handwritten OCaml backend, ever.** The Go output comes ONLY from standard Rocq extraction of a
   proved closed value. The one permitted piece of OCaml is a build-GENERATED one-line writer
   (`let () = print_string …`) that prints the extracted bytes unchanged; it is never tracked, inspects
   nothing, constructs nothing, decides nothing. `tools/ocaml-origin-gate.sh` enforces **zero tracked
   `*.ml`/`*.mli`/`*.mlg`** and bans the deleted backend's hallmarks (MiniML, term inspection,
   `Go Main Extraction`, name-based lowering). Never reintroduce a backend, a validator around handwritten
   output, or an OCaml renderer.
2. **Never edit generated `*.go`.** It is produced by `make emit` from the proved bytes, gitignored, never
   committed; `make check` regenerates + re-verifies it, so it can never drift. Change the `.v`, re-emit.
3. **Model honestly — faithful or fail-loud, never plausible-but-wrong.** An unrepresentable construct is
   REJECTED mechanically (unrepresentable in the AST, or rejected by the compile relation), never preserved
   as text. ⚠ NEVER add a raw/opaque/string-rescue escape hatch to a structured AST (`LESSONS.md`).
4. **Zero project axioms — every `Print Assumptions` surface is EMPTY; preserve it.** The whole model is
   `Definition`s/`Record`s over concrete Rocq data. Never `Axiom`/`Parameter`/`Admitted`, never a kernel
   primitive (`PrimInt63`/`PrimFloat` are axioms too), never `FunctionalExtensionality` on a retained
   surface. `make check` asserts zero axioms over the spine (Rocq's own `Print Assumptions`).
5. **No fuel, ever.** No gas, step budgets, max-depths, bounded runners, cycle caps, or renamed
   equivalents in the certified path. A ranked/well-founded structural measure is acceptable ONLY as a
   termination proof from decreasing structure — never as an externally supplied execution budget. A
   bounded run is not a proof; a timeout is not nontermination.
6. **Partial/unsafe ops are safe-by-construction or proof-gated.** Prefer evidence-carrying APIs or
   check-and-branch (comma-ok / `option`). Never accidentally write a Rocq program that needs a nil deref.
7. **Naming is a correctness claim.** `GoCompile` is syntactic/static admissibility ONLY — it implies no
   semantic safety, panic-freedom, termination/divergence classification, or real-Go adequacy unless
   separately proved and exposed. Never let a syntactic gate sound like `SafeProgram`.
8. **Imports are on hold.** Emit `package main`, no `import` block; defer any builtin needing one.

## The certified spine

`GoAst` (syntax: `GExpr`/`GoTy`/operators + `classify`) · `GoPrint` (the printer, a proof-only lexer/parser,
and the round-trip / injectivity theorems; the canonical grammar `CanonExpr`/`CanonStmt`/`CanonProgram` is
the syntax authority — the parser is derived tooling, complete-not-sound) · `GoTypes` (the type-category
checker, one authority for compile + any future semantics) · `GoCompile` (static admissibility) · `GoEmit`
(the certified emitter + the byte theorem). Its foundation: `digits` (decimal authority), `GoNumeric`
(Z-based numerics), `GoRuntimeTypes`, `GoPanic`, `GoEffects`, `GoSlice`. `emitdemo/emit_demo.v` is the
standard extraction driver for the closed output.

## The foundation frontier (`ARCHITECTURE.md` governs)

The spine currently rests on a type/effect foundation that is being reset into single root authorities: one
`TargetConfig` + one certified type universe; one proof-producing compile/elaboration into a typed IR; an
independent Go grammar with one token stream and one renderer; a typed object store + value well-formedness;
accurate control/panic/blocking/model-fault; one semantics and one safe-emission boundary. Build each root
before the floor above it; delete a file that materially depends on a rejected root rather than keeping it
as "transitional."

## Workflow & commands

Verify after any change: **`make check`** — the one verify. It runs the origin/seal/toolchain gates, compiles
the spine standalone asserting zero axioms, emits the certified `.go` (zero handwritten OCaml), and confirms
the pinned Go toolchain accepts it unchanged (`gofmt -l` is a NO-OP check — the canonical printer is already
gofmt-stable; never run `gofmt -w` on certified bytes). Then commit → re-index.

```
make check          # the one verify: gates + zero-axiom spine + certified emit + Go toolchain accepts it
make emit           # produce emitdemo/spine_demo.go from GoEmit.demo_emit (zero handwritten OCaml)
make spine-verify   # compile digits..GoEmit standalone, assert zero axioms
make build          # reproducible container build; exports the certified .go
make go-verify GO=<dir>   # ground-truth Go's real semantics before modelling them
make install-hooks  # activate the pre-commit hook (once after clone)
```

Gotchas: **the certified `.go` is gitignored + never committed** — `make emit` regenerates it, `make check`
re-verifies. **`gofmt` is a no-op CHECK, never a mutating step** — the printer emits gofmt-stable bytes; a
`gofmt -l` hit is a printer bug, not something to normalize away. **Pre-commit hook** (`make install-hooks`)
runs `make check` on any proof/build change and seals the tree (no tracked `*.go`, no tracked OCaml).

## Files

- **The certified spine + foundation** (see above): `digits.v`, `GoNumeric.v`, `GoRuntimeTypes.v`, `GoPanic.v`,
  `GoEffects.v`, `GoSlice.v`, `GoAst.v`, `GoPrint.v`, `GoTypes.v`, `GoCompile.v`, `GoEmit.v`.
- `emitdemo/emit_demo.v` — the standard extraction driver (`Extraction "emit_demo.ml" GoEmit.demo_emit`).
- `tools/` — shell gates only (no OCaml, no semantic logic): `spine-gate.sh` (compile spine + zero-axiom),
  `ocaml-origin-gate.sh`, `toolchain-gate.sh`/`toolchain-selftest.sh` (single pinned Go image),
  `go-verify-selftest.sh`.
- `Makefile` / `Dockerfile` / `.githooks/pre-commit` — the certified build.

## Where the detail lives

- **`ARCHITECTURE.md`** — ★ the binding charter (the certified spine + the root frontier). Read before any
  structural change.
- **`PROGRESS.md`** — the live status ledger (what is proved, the current root frontier).
- **`LESSONS.md`** — expensive mistakes; read before lifting a printer/parser into Rocq or adding any
  "escape hatch."
- **`git log`** — the archive; commit messages carry rationale. History lives there, never in active code.
