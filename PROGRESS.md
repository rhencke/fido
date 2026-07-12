# Fido — status

The live root frontier. Detail lives in `ARCHITECTURE.md` (charter) and `git log` (history).

## GREEN (proved, zero project axioms)

- **The certified spine compiles standalone and is axiom-free** — `digits · GoNumeric · GoRuntimeTypes ·
  GoPanic · GoEffects · GoSlice · GoAst · GoPrint · GoTypes · GoCompile · GoEmit`. `make check` asserts zero
  axioms via Rocq's own `Print Assumptions` (`tools/spine-gate.sh`).
- **Certified emission, end to end, with ZERO handwritten OCaml** — standard extraction of the closed
  `GoEmit.demo_emit` (bytes proved by `demo_emit_bytes`) → a build-generated one-line writer → `spine_demo.go`
  → the pinned Go toolchain accepts it unchanged (`gofmt -l` no-op + `go build` + `go vet`).
- **Printer correctness against the canonical grammar** — `gprint`/`print_ty`/`print_stmt`/`print_program`
  injectivity, resting on the parser-free canonical layer (`CanonExpr`/`CanonStmt`/`CanonProgram`,
  `canon_*_unique`, `lex_gprint_*`). The executable parser is derived tooling: complete against the grammar,
  not sound (accepts redundant parens) — nothing certified depends on it.
- **`GoCompile`** — static/syntactic admissibility (no behavioral claim).

## Trust base

Trusted: the Go toolchain (no Go-parses-the-bytes-as-the-same-AST theorem — open recognition gap), the
pinned toolchain images, Rocq, and the build-generated one-line writer (pure transport of a proved string).
Proved axiom-free: the spine above. The handwritten OCaml backend and extraction plugin are **deleted**;
`tools/ocaml-origin-gate.sh` keeps them out (zero tracked `*.ml`/`*.mli`/`*.mlg`; no backend hallmarks).

## Gates (all in `make check`, mirrored by the pre-commit hook)

`ocaml-origin-gate` (zero tracked OCaml) · uncommittable-Go seal (no tracked `*.go`) · `toolchain-gate` +
`toolchain-selftest` (one pinned Go image) · `spine-gate` (compile spine, zero axioms) · certified emit ·
pinned Go toolchain accepts the bytes. Pre-commit also runs an anti-axiom declaration tripwire over every
tracked `.v`.

## RED / NEXT — the root frontier

The spine's type/effect foundation still rests on roots being reset. Build each root, then rebuild the floor
above it; delete anything that materially depends on a rejected root (git is the archive). In order:

1. one `TargetConfig` + one certified type universe (retire the `GoRuntimeTypes` tag vs `GoAst`/`GoTypes`
   syntax split; invalid types unrepresentable or rejected).
2. one independent Go grammar + one token stream + one renderer; fix the unary/separator rules at the root
   (a `needs_separator` token law, not conservative paren tables); full statement/program lexical
   faithfulness.
3. proof-producing compile/elaboration into a typed IR (soundness + supported-subset completeness), not a
   boolean wrapper.
4. typed object store + `ValueWF`; one native representation each for slice / map / channel.
5. accurate control / panic / blocking / model-fault; structured runtime panic values; no funext.
6. one semantics + one `SafeProgram`-shaped emission boundary; official output through the certificate.

Feature breadth is allowed to collapse to what the foundation proves. Rebuild upward only after each root is
poured and set.
