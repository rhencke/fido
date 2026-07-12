# Fido — operating law for a theorem-first repository

**A proof project whose vertical slice is proved AND executed.** An untrusted proposer (an LLM) may write a
raw Go AST and arbitrary supporting lemmas; **no `.go` is emitted unless Rocq first proves the program
compile-admissible and safe.** There is **one** program representation — the AST *is* the IR; "compiled" and
"safe" are PROOFS/EVIDENCE over that one tree, never new trees:

```
GoAST → GoCompile (evidence over the SAME AST) → GoSafe (certificate) → direct GoRender
      → Rocq-computed final (path,bytes) image → standard extraction → a tiny I/O writer writes it
      → pinned Go toolchain build/run   [integration only]
```

The admitted fragment is a `MainFile` (package `main` + `func main()` are STRUCTURAL, not identifiers) whose
body is `SPrintln` statements (the builtin `println` is the statement, not a callee name) over primitive
literals: booleans and integers (`EBool`/`EInt`/`ENeg` — unsigned magnitude, negatives via `ENeg`). Anything
else (other packages, functions, callees, strings) is UNREPRESENTABLE, not rejected. Every layer is proved
axiom-free, and a witness exercising bool + int + the `-(2^63)` boundary + empty/multiple `println` is
emitted to a real `main.go` and built+run by the pinned Go toolchain against reviewed goldens. **State,
frontier: `PROGRESS.md`. Charter (binding): `ARCHITECTURE.md`. Rejected shapes: `PAINFUL_LESSONS.md`.**

## The law

**Ruthless correctness or ruthless deletion — no middle state.** Incomplete scope is acceptable; incorrect,
conservative, approximate, duplicated, self-validating, or half-built code in the certified path is not.
Every retained component must be complete and correct for the constructors it admits — a comment that a
stronger theorem is "next" does NOT make an admitted constructor safe to emit today. **Cut representable
scope before weakening a proof:** if a constructor cannot yet be modelled exactly, remove it from the AST;
never admit it with a conservative narrowing. When twenty leaf proofs/guards compensate for one missing
root, replace the root and delete the leaves.

Nobody depends on this repository. No backwards-compatibility, no migration, no transition artifact. **Cost
is not a constraint; incorrectness is fatal** — given a cheaper/less-expressive and a
harder/more-general/more-correct path, take the harder one. Plans are guidance; when a plan conflicts with a
stronger proof or a more correct formulation, follow the stronger path and surface the divergence.

- Expressiveness expands by proof principles, never by lists of examples.
- Integration checks (the pinned-Go e2e) catch regressions; they never certify semantics/safety/adequacy.
  **A Go build/run failure for an emitted program is never an expected test** — it means GoCompile,
  rendering, the target facts, or the writer is wrong. Negative candidates fail IN Rocq, before any image.
- Public correctness claims must be backed by zero-axiom theorem surfaces. Axiom-free ≠ correct — a
  kernel-checked proof can still prove a weak, self-referential, or irrelevant claim; always check that the
  theorem's STATEMENT is the right one.
- **`GoCompile` is EXACT compiler admissibility, not a subset filter.** Every representable program the
  pinned Go compiler accepts is accepted by GoCompile; every program GoCompile rejects is genuinely
  compiler-invalid (an out-of-range integer), never a supported-but-refused program. It is a declarative
  judgment with a sound+complete executable decision — never a boolean, never completeness against a mirror
  relation instead of the compiler. A non-`main` package or a `print` call is not "rejected" — it is
  unrepresentable.
- **No second authority / no second tree:** syntax, admissibility, safety, rendering, and emission each have
  exactly one authoritative definition over the ONE AST. Never copy the syntax into a parallel "compiled"
  hierarchy; never add an erasure forest to prove a copy is "the same".

## Standing technical law

1. **Handwritten OCaml is a filesystem exhaust pipe.** All semantic work — compile, safety, rendering, and
   the final `(relative-path, exact-bytes)` image — is done in proved Rocq; standard extraction generates the
   OCaml value. The ONLY handwritten OCaml is a tiny writer (`e2e/writer.ml`, ~15 lines) that receives that
   already-computed image and writes it (atomically, via staging + rename). **It does not receive, inspect,
   validate, lower, render, decode, or understand programs; it walks no Rocq terms; it chooses no paths or
   contents.** `tools/ocaml-origin-gate.sh` enforces at-most-that-one-writer, its small size, and that it
   contains no term-walking API. Never reintroduce a backend, a plugin that decodes Rocq terms, an OCaml
   renderer, or a second emission path.
2. **Generated `*.go` / `*.ml` is never committed.** The emitted program and the extraction output are
   produced at build time, gitignored, and `make check` regenerates + re-runs them so they cannot drift.
   Never hand-edit generated Go — change the `.v`.
3. **Model honestly — faithful or fail-loud, never plausible-but-wrong.** Unrepresentable ⇒ absent from the
   AST (or rejected by `go_compile`). ⚠ NEVER add a raw/opaque/string-rescue escape hatch to a structured
   AST — the expensive mistake this project has already paid for (`PAINFUL_LESSONS.md`).
4. **Zero project axioms — every `Print Assumptions` surface is EMPTY; preserve it.** `Definition`s /
   `Record`s / `Inductive`s over concrete Rocq data. Never `Axiom`/`Parameter`/`Admitted`, never a kernel
   primitive, never `FunctionalExtensionality`. `make check` asserts the public surfaces axiom-free via
   `gate/axiom_gate.v` — the sole `Print Assumptions` target, compiled fresh EVERY build and count-checked;
   the emit stage also asserts the emitted witness's assumption closure is empty.
5. **No fuel, ever.** No gas/step-budget/max-depth/bounded-runner. Totality comes from decreasing structure.
6. **Partial/unsafe ops are safe-by-construction or proof-gated.** No unused panic/control placeholder either
   — a `Panicked`/`Outcome` algebra returns WITH the first panic-capable constructor and its exact semantics,
   not predeclared. `GoSafe` states only exact current behaviour/safety facts.
7. **Naming is a correctness claim.** `GoSafe` uses REAL Go values (`VInt : Z`), not source spelling — `EInt
   0` and `ENeg 0` evaluate equal. A syntactic/static gate implies no semantic safety unless separately
   proved. Every admitted primitive has its complete rendering/value/syntax proofs NOW.
8. **Imports are on hold.** Emit `package main`, no `import` block. Adding an import needs explicit sign-off.

## The layers (one authority each, over the ONE AST)

`GoAST` — `MainFile` / `SPrintln` / `EBool`/`EInt`/`ENeg` (structural package/func/println; no identifiers,
no second tree). · `GoCompile` — the declarative `GoCompile : GoFile -> Prop` (integer representability) +
`go_compile` proved sound/complete/decidable; `CompiledProgram` = a proof-bearing wrapper over the SAME AST.
· `GoSafe` — real `GoValue` (`VBool`/`VInt Z`), exact `eval`/`run`, `GoSafe`/`SafeProgram` (no panic
algebra). · `GoRender` — direct `CompiledProgram → string`; proved all-ASCII, decimal denotes exactly the
value, no leading zero. · `GoEmit` — the fixed single-file image `emit_pairs : list (string*string)`. ·
`e2e/Extract.v` — the witness + `Extraction`. · `e2e/writer.ml` — the one tiny I/O writer. ·
`digits`/`TargetConfig` — leaf authorities.

## Workflow & commands

Verify after any change: **`make check`** — the git/shell gates (at-most-one-writer OCaml, no tracked
`*.go`) + the pinned-container **proof** (Rocq 9.2.0: `dune build` + `gate/axiom_gate.v` axiom-free,
count-checked) + the **e2e** (Dune-cached theory build; then an EXPLICIT step extracts the final image,
asserts the witness axiom-free, compiles the tiny writer, runs it; the pinned digest-pinned
`golang:1.23-alpine` — asserted to match `TargetConfig` GOVERSION/GOOS/GOARCH — gofmt-checks/`go vet`/
`go build`/runs it; stdout/stderr/exit compared byte-for-byte to reviewed goldens). **Local host Rocq is NOT
supported** — all compilation goes through the pinned toolchain via buildx.

```
make check   # gates + pinned-Rocq proof + pinned-Go e2e (all buildx)
make prove   # the proof alone (dune build + axiom gate)
make e2e     # extraction + tiny writer + pinned-Go run vs goldens
make prover-log   # stream the plain Rocq log
make install-hooks
```

⚠ A cancelled/timed-out buildx can zombie a `sharing=locked` cache lock and fake a hang on the NEXT build —
kill stale `docker buildx build` processes first; run long builds detached and poll.

## Files

- **Certified theory** (`dune`): `TargetConfig.v`, `digits.v`, `GoAST.v`, `GoCompile.v`, `GoSafe.v`,
  `GoRender.v`, `GoEmit.v`.
- `e2e/Extract.v` — witness + extraction; `e2e/writer.ml` — the ONE tiny I/O writer;
  `e2e/golden.{stdout,stderr,exit}` — reviewed goldens.
- `gate/axiom_gate.v` — the sole `Print Assumptions` target. `tools/ocaml-origin-gate.sh` — the shell gate.
- `Makefile` / `Dockerfile` / `.githooks/pre-commit` — the buildx proof + e2e (host Rocq unsupported).

## Where the detail lives

- **`ARCHITECTURE.md`** — ★ the binding charter (layers, responsibilities, the exhaust-pipe boundary, trust).
- **`PROGRESS.md`** — the live status ledger. · **`PAINFUL_LESSONS.md`** — why rejected shapes must not
  reappear. · **`git log`** — the archive.
