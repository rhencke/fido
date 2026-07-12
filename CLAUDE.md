# Fido — operating law for a theorem-first repository

**A proof project whose vertical slice is proved AND executed.** An untrusted proposer (an LLM) may write a
raw Go program and arbitrary supporting lemmas; **no `.go` is emitted unless Rocq first proves the program
compile-admissible and safe.** There is **one** program representation — a `GoProgram` (a verified finite
map from relative paths to raw file ASTs); "compiled" and "safe" are PROOFS/EVIDENCE over that one program,
never new trees:

```
GoProgram (fmap path→file AST) → GoCompile (evidence over the SAME program) → GoSafe (certificate)
      → direct GoRender (header + bytes per file) → GoEmit (finite-map DirectoryImage, path→bytes)
      → standard extraction → one dirty-directory filesystem sink installs it
      → pinned Go toolchain build/run   [integration only]
```

The admitted fragment is one main-package file: a `MainFile` (package `main` + `func main()` are STRUCTURAL,
not identifiers) whose body is `SPrintln` statements (the builtin `println` is the statement, not a callee
name) over primitive literals: booleans and integers (`EBool`/`EInt`/`ENeg` — unsigned magnitude, negatives
via `ENeg`). Anything else (other packages, functions, callees, strings, imports, a raw package hierarchy)
is UNREPRESENTABLE, not rejected. The one-file MVP is a proved SUBSET over the general program map, never a
one-file root. Every layer is proved axiom-free, and a witness exercising bool + int + the `-(2^63)`
boundary + empty/multiple `println` is emitted to a real `main.go` (first line `// fido generated.  do not
edit.`) and built+run by the pinned Go toolchain against reviewed goldens. **State, frontier: `PROGRESS.md`.
Charter (binding): `ARCHITECTURE.md`. Rejected shapes: `PAINFUL_LESSONS.md`.**

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
  rendering, the target facts, or the sink is wrong. Negative candidates fail IN Rocq, before any image.
- Public correctness claims must be backed by zero-axiom theorem surfaces. Axiom-free ≠ correct — a
  kernel-checked proof can still prove a weak, self-referential, or irrelevant claim; always check that the
  theorem's STATEMENT is the right one.
- **`GoCompile` is EXACT compiler admissibility, not a subset filter.** Every representable program the
  pinned Go compiler accepts is accepted by GoCompile; every program GoCompile rejects is genuinely
  compiler-invalid (an out-of-range integer), never a supported-but-refused program. It is a whole-program
  declarative judgment with a proof-producing sound+complete decision — never a boolean, never completeness
  against a mirror relation instead of the compiler. A non-`main` package or a `print` call is not
  "rejected" — it is unrepresentable. Keep two claims distinct: (A) the checker matches the formal judgment
  is PROVED; (B) accepted programs are accepted by real Go is the GOAL, exercised by the e2e, never a
  kernel theorem — do not overclaim "equivalent to go build".
- **No second authority / no second tree:** syntax, admissibility, safety, rendering, and emission each have
  exactly one authoritative definition over the ONE program. Never copy the syntax into a parallel
  "compiled" hierarchy or a raw `GoPackage`; never bake compiled facts into the raw file value; never add an
  erasure forest to prove a copy is "the same".

## Standing technical law

1. **Handwritten OCaml understands filesystems, not programs.** All semantic work — compile, safety,
   rendering, and the final `(relative-path, exact-bytes)` image (plus the ownership header, from Rocq) —
   is done in proved Rocq; standard extraction generates the OCaml value. The ONLY handwritten OCaml is a
   dirty-directory filesystem sink (`e2e/writer.ml`) that receives that already-computed image and
   SYNCHRONIZES it into a target directory (exclusive lock; `lstat`/no-follow preflight — real-directory
   parents, refuse any non-own-header-owned target incl. dangling symlinks; staging inside the target;
   per-file atomic rename; stale-cleanup by header ownership + desired-key-set; two reserved control names
   `.fido-staging`/`.fido-sync.lock`; foreign entries outside those never touched). **It does not receive,
   inspect, validate, lower, render, decode, or understand programs; it walks no Rocq terms; it chooses no
   paths or contents; it re-declares no header.** `tools/ocaml-origin-gate.sh` enforces at-most-that-one-sink,
   a bounded size, and no term-walking API. The sink may be more than a one-liner — a correct sync needs real
   filesystem machinery — but every part is a filesystem concern, never a semantic one. Never reintroduce a
   backend, a plugin that decodes Rocq terms, an OCaml renderer, a second emission path, or a late OCaml
   path/name validator standing in for certified path admissibility.
2. **Generated `*.go` / `*.ml` is never committed.** The emitted program and the extraction output are
   produced at build time, gitignored, and `make check` regenerates + re-runs them so they cannot drift.
   Never hand-edit generated Go — change the `.v`. The generated header is Rocq's bytes (`GoRender.header`),
   proved present on every file; the sink recognizes it as an ownership marker but adds/alters no bytes.
3. **Model honestly — faithful or fail-loud, never plausible-but-wrong.** Unrepresentable ⇒ absent from the
   AST (or rejected by `go_compile`). ⚠ NEVER add a raw/opaque/string-rescue escape hatch to a structured
   AST — the expensive mistake this project has already paid for (`PAINFUL_LESSONS.md`).
4. **Zero project axioms — every `Print Assumptions` surface is EMPTY; preserve it.** `Definition`s /
   `Record`s / `Inductive`s over concrete Rocq data. Never `Axiom`/`Parameter`/`Admitted`, never a kernel
   primitive, never `FunctionalExtensionality`. `make check` asserts the public surfaces axiom-free via
   `gate/axiom_gate.v` — the sole `Print Assumptions` target, compiled fresh EVERY build and count-checked;
   the emit stage also asserts the emitted image's assumption closure is empty. A shared
   `tools/axiom-scan.sh` (self-tested) is defense-in-depth in both `make check` and the pre-commit hook.
5. **No fuel, ever.** No gas/step-budget/max-depth/bounded-runner. Totality comes from decreasing structure.
6. **Partial/unsafe ops are safe-by-construction or proof-gated.** No unused panic/control placeholder either
   — a `Panicked`/`Outcome` algebra returns WITH the first panic-capable constructor and its exact
   semantics, not predeclared. `GoSafe` states only exact current behaviour/safety facts; today `GoSafe :=
   True` because the fragment has no unsafe operation — the honest, permanent extension point, not circular.
7. **Naming is a correctness claim.** `GoSafe` uses REAL Go values (`VInt : Z`), not source spelling — `EInt
   0` and `ENeg 0` evaluate equal. A syntactic/static gate implies no semantic safety unless separately
   proved. Every admitted primitive has its complete rendering/value/syntax proofs NOW.
8. **The root is a PROGRAM, and integer width has one authority.** The permanent root is a `GoProgram` (a
   finite map, keys unique by construction) so cross-file reasoning is native later — never collapse it to a
   single-file root. The one integer-width authority is `Ints` (64-bit); there is NO `TargetConfig` (it was
   premature); the toolchain is pinned only operationally.
9. **Imports are on hold.** Emit `package main`, no `import` block. Adding an import needs explicit sign-off.

## The layers (one authority each, over the ONE program)

`FMap` — the finite-map spine (`fmap A`): the invariant is `NoDup (fm_keys m)` (`fm_keys_nodup` +
`dup_key_unrepresentable` — duplicate keys unrepresentable), DISTINCT from the deterministic-lookup fact
`fm_MapsTo_fun`; extensional-by-lookup equality, no imposed order. · `Ints` — the one 64-bit width authority,
only the used constants (`int_min`/`int_max`; no `uint` bound without a `uint` construct). · `GoAST` —
`GoProgram := fmap GoFileAST`; raw `MainFile` / `SPrintln` / `EBool`/`EInt`/`ENeg` (structural
package/func/println; no identifiers, no second tree, no raw package, no compiled facts in raw syntax). ·
`GoCompile` — the declarative `GoCompile : GoProgram -> Prop` (the key is `main.go` + integer
representability) + proof-producing `go_compile : GoProgram -> option CompilableProgram` proved
sound/complete (`prog_ok_iff`); `CompilableProgram` = a proof-bearing wrapper over the SAME program (no facts
record); bad paths (non-`.go`/traversal/absolute/nested/control-name) rejected IN Rocq. · `GoSafe` — real
`GoValue` (`VBool`/`VInt Z`), exact `eval_file`, `GoSafe`/`SafeProgram` (no panic algebra). · `GoRender` —
direct `GoFileAST → string` with the header as the EXACT first line; proved all-ASCII, decimal denotes
exactly the value, no leading zero, first-line-is-header. · `GoEmit` — `render_program : SafeProgram ->
DirectoryImage` where `DirectoryImage := fmap string`; one entry keyed `main.go`. · `e2e/Extract.v` — the
witness + `Extraction` (header + entries). · `e2e/writer.ml` — the one dirty-directory filesystem sink. ·
`digits` — leaf authority.

## Workflow & commands

Verify after any change: **`make check`** — the git/shell gates (at-most-one-sink OCaml, no tracked `*.go`,
the axiom-declaration scan) + the pinned-container **proof** (Rocq 9.2.0: `dune build` + `gate/axiom_gate.v`
axiom-free, count-checked) + the **e2e** (Dune-cached theory build; then an EXPLICIT step extracts the final
image, asserts it axiom-free, compiles the sink, runs it against a DIRTY directory — a stale Fido file it
must clean + foreign files it must preserve + idempotence + adversarial refuse-and-preserve (foreign at the
target key, a symlinked lock, a dangling target symlink, a squatter at a reserved name); the digest-pinned
`golang:1.23-alpine` —
asserted to match the operational pin go1.23/linux/amd64 — gofmt-checks/`go vet`/`go build`/runs it;
stdout/stderr/exit compared byte-for-byte to reviewed goldens). **Local host Rocq is NOT supported** — all
compilation goes through the pinned toolchain via buildx.

```
make check   # gates + pinned-Rocq proof + pinned-Go e2e (all buildx)
make prove   # the proof alone (dune build + axiom gate)
make e2e     # extraction + dirty-directory sink + pinned-Go run vs goldens
make prover-log   # stream the plain Rocq log
make install-hooks
```

⚠ A cancelled/timed-out buildx can zombie a `sharing=locked` cache lock and fake a hang on the NEXT build —
kill stale `docker buildx build` processes first; run long builds detached and poll.

## Files

- **Certified theory** (`dune`): `digits.v`, `Ints.v`, `FMap.v`, `GoAST.v`, `GoCompile.v`, `GoSafe.v`,
  `GoRender.v`, `GoEmit.v`.
- `e2e/Extract.v` — witness + extraction; `e2e/writer.ml` — the ONE dirty-directory filesystem sink;
  `e2e/golden.{stdout,stderr,exit}` — reviewed goldens.
- `gate/axiom_gate.v` — the sole `Print Assumptions` target. `tools/ocaml-origin-gate.sh`,
  `tools/axiom-scan.sh` — the shell gates.
- `Makefile` / `Dockerfile` / `.githooks/pre-commit` — the buildx proof + e2e (host Rocq unsupported).

## Where the detail lives

- **`ARCHITECTURE.md`** — ★ the binding charter (layers, responsibilities, the exhaust-pipe boundary, trust).
- **`PROGRESS.md`** — the live status ledger. · **`PAINFUL_LESSONS.md`** — why rejected shapes must not
  reappear. · **`git log`** — the archive.
