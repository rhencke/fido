# Fido — operating law for a theorem-first repository

**A proof project aiming at a proved Go generator — currently under a FOUNDATION RESET (checkpoint 65).**
The handwritten OCaml backend and extraction plugin are gone; then the **false compile/emit authority**
(`GoCompile` fail-open-accepted an unresolved named type) and the **disconnected runtime island** were
deleted too. **There is NO emitted Go this round, by design** — a smaller root-only repository beats a green
extraction demo resting on a false compile certificate. What survives is a syntax layer (`digits`, `GoAst`,
`GoPrint`) that compiles zero-axiom but is **scheduled for the syntax-root reset and makes no Go-adequacy
claim** — it is not a certified authority. The intended end state is a proved generator built from real
roots (`TargetConfig`, a certified type universe, an independent Go grammar, typed elaboration, one token
renderer); it will never be "formally verified Go" (Go's toolchain is trusted). **Current state, defects,
and the root frontier: `PROGRESS.md`. Architecture charter (binding): `ARCHITECTURE.md`.**

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
- The repository contains only architecture we would defend long term; nothing is "transitional."
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
2. **Generated `*.go` is never committed.** There is no emission this round; when it returns it is produced
   from proved bytes, stays gitignored, and `make check` regenerates + re-verifies it so it can never drift.
   Never hand-edit generated Go — change the `.v`.
3. **Model honestly — faithful or fail-loud, never plausible-but-wrong.** An unrepresentable construct is
   REJECTED mechanically (unrepresentable in the AST, or rejected by the compile relation), never preserved
   as text. ⚠ NEVER add a raw/opaque/string-rescue escape hatch to a structured AST — a structured-or-fail
   escape hatch is the expensive mistake this project has already paid for (git history).
4. **Zero project axioms — every `Print Assumptions` surface is EMPTY; preserve it.** The whole model is
   `Definition`s/`Record`s over concrete Rocq data. Never `Axiom`/`Parameter`/`Admitted`, never a kernel
   primitive (`PrimInt63`/`PrimFloat` are axioms too), never `FunctionalExtensionality` on a retained
   surface. The live build gate (`make check`) asserts only **GoPrint's** declared `Print Assumptions`
   surfaces are axiom-free (`digits`/`GoAst` declare none; the axiom-DECLARATION scan runs only in the
   pre-commit hook, not `make check`/CI — see `PROGRESS.md`).
5. **No fuel, ever.** No gas, step budgets, max-depths, bounded runners, cycle caps, or renamed
   equivalents anywhere in retained code. A ranked/well-founded structural measure is acceptable ONLY as a
   termination proof from decreasing structure — never as an externally supplied execution budget. A
   bounded run is not a proof; a timeout is not nontermination.
6. **Partial/unsafe ops are safe-by-construction or proof-gated.** Prefer evidence-carrying APIs or
   check-and-branch (comma-ok / `option`). Never accidentally write a Rocq program that needs a nil deref.
7. **Naming is a correctness claim.** A syntactic/static gate implies NO semantic safety, panic-freedom,
   termination classification, or real-Go adequacy unless separately proved and exposed. Never let a
   syntactic gate sound like `SafeProgram`. A compile authority must be a declarative, proof-bearing typing
   relation with a soundness theorem — NEVER a boolean equality `check p = true` (that was the fail-open
   `GoCompile` this reset deleted; a green boolean is not compiler admissibility).
8. **Imports are on hold.** Emit `package main`, no `import` block; defer any builtin needing one.

## The surviving syntax layer (NOT a certified authority)

`digits` (the one decimal-rendering authority) · `GoAst` (Go syntax: `GExpr`/`GoTy`/operators) · `GoPrint`
(the printer + a proof-only lexer/parser + injectivity theorems). It compiles zero-axiom, but rests on a
**rejected syntax root** and is scheduled for the reset — see `PROGRESS.md` for the concrete defects
(`EInt : Z` signed literals, unresolved `GTNamed`, the self-mirroring `CanonExpr` that is not an independent
grammar, the complete-not-sound parser). It proves NO Go-compiler adequacy and is not consumed by any
emission path (there is none). Do not describe it as "the certified spine" or "the syntax authority."

## The root frontier (`ARCHITECTURE.md` governs — pour each root before any floor)

`TargetConfig` → one certified type universe (`CertifiedType`) → an independent Go grammar + one token stream
+ one verified renderer → a compile environment with declarative resolution/typing into a typed IR
(`TypedProgram`, static invalidity unrepresentable, executable checker proved sound) → a typed store /
accurate control/panic/blocking as consumers require → and only then a proof-bearing typed emission. Delete
a file that materially depends on a rejected root rather than keeping it as "transitional." Do not add
features; do not rebuild the old breadth from memory.

## Workflow & commands

Verify after any change: **`make check`** — zero tracked OCaml, no tracked generated Go, the surviving Rocq
type-checks, and GoPrint's declared `Print Assumptions` surfaces are axiom-free (via `tools/spine-gate.sh`;
that gates GoPrint's surfaces only, not `digits`/`GoAst` and not the axiom-declaration scan — see
`PROGRESS.md`'s trust base). No Go toolchain is involved (there is no emission this round). Then commit →
re-index.

```
make check          # the one verify: origin/seal gates + compile digits/GoAst/GoPrint, GoPrint's surfaces axiom-free
make spine-verify   # compile the surviving modules standalone, assert GoPrint's declared surfaces axiom-free
make build          # reproducible container build: the pinned Rocq toolchain compiles them, GoPrint's surfaces axiom-free
make install-hooks  # activate the pre-commit hook (once after clone)
```

**Pre-commit hook** (`make install-hooks`) runs `make check` on any proof/build change and seals the tree
(no tracked `*.go`, no tracked OCaml). When emission eventually returns it comes through a proof-bearing
typed certificate, generated Go stays gitignored, and `gofmt` is a NO-OP check (never a mutating step).

## Files

- **The surviving syntax layer** (flagged for reset, see above): `digits.v`, `GoAst.v`, `GoPrint.v`.
- `tools/` — shell gates only (no OCaml, no semantic logic): `spine-gate.sh` (compile the modules,
  zero-axiom), `ocaml-origin-gate.sh` (zero tracked OCaml + no backend hallmarks).
- `Makefile` / `Dockerfile` / `.githooks/pre-commit` / `dune` — the no-emission proof build.

## Where the detail lives

- **`ARCHITECTURE.md`** — ★ the binding charter (the intended roots + the current reset). Read before any
  structural change.
- **`PROGRESS.md`** — the live status ledger (what is proved, the concrete defects, the root frontier).
- **`git log`** — the archive; commit messages + old sources carry rationale and expensive-mistake
  postmortems. History lives there, never in active code.
