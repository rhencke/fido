# Fido — operating law for a theorem-first repository

**A proof project whose vertical slice is now proved AND executed.** An untrusted proposer (an LLM) may
write a raw Go AST and arbitrary supporting lemmas; **no `.go` is emitted unless Rocq first proves the
program compile-admissible and safe.** The pipeline is deliberately small — the AST *is* the IR, and
"compiled"/"safe" are PROOFS about it, not new trees:

```
GoAST → GoCompile (decorated CompiledFile) → GoSafe (SafeProgram) → GoRender → GoEmit (DirectoryImage)
      → one tiny transport plugin (Fido Emit) → pinned Go toolchain build/run  [integration only]
```

Today's admitted fragment is `package main` + one `func main()` + straight-line builtin `println` over
primitive literals (bool / string / unsigned-magnitude int, negatives only as `ENeg`). It is complete and
correct on its own: every layer is proved axiom-free, and one witness (`println(true)`) is emitted to a
real `main.go` and built+run by the pinned Go toolchain against reviewed goldens. **Current state and the
next frontier: `PROGRESS.md`. Architecture charter (binding): `ARCHITECTURE.md`. Why rejected shapes must
not return: `PAINFUL_LESSONS.md`.**

## The law

**Ruthless correctness or ruthless deletion — no middle state.** Incomplete scope is acceptable; incorrect,
conservative, approximate, duplicated, half-built, or "known issue" code in the certified path is not.
Every retained component must be complete and correct in itself and may build only on foundations that are
already complete and correct. If a foundation is wrong, incomplete, trusted-rather-than-proved, or narrower
than the final claim, delete the floors above it; a right idea reappears when the correct foundation
requires it. **Cut representable scope before weakening a proof.** If a constructor cannot yet be modelled
exactly, remove it from the AST — never admit it with a conservative narrowing. When twenty leaf
proofs/guards compensate for one missing root, replace the root and delete the leaves.

Nobody depends on this repository. There is no backwards-compatibility obligation, no migration path, no
transition artifact. **Cost is not a constraint; incorrectness is fatal** — given a cheaper/less-expressive
mechanism and a harder/more-general/more-correct one, take the harder one. Plans are best-effort guidance;
when a plan conflicts with a stronger proof or a more correct formulation, follow the stronger path and
surface the divergence.

- The repository contains only architecture we would defend long term; nothing is "transitional."
- Expressiveness expands by proof principles, never by lists of examples.
- Integration checks (the pinned-Go e2e) catch regressions; they never certify semantics, safety,
  termination, or Go adequacy. **A Go build/run failure for an emitted program is never an expected test** —
  it means GoCompile, rendering, the target facts, or the transport is wrong.
- Public correctness claims must be backed by zero-axiom theorem surfaces; an ungated internal theorem is
  not public evidence. Axiom-free ≠ correct — a kernel-checked proof can still prove a weak or
  self-referential claim (the deleted `GoCompile` boolean was axiom-free and still wrong).
- **No second authority:** syntax, compile-admissibility, safety, rendering, and emission each have exactly
  one authoritative definition. Never add code beside a weaker path — delete the weaker path.

## Standing technical law

1. **No handwritten semantic OCaml, ever.** All language decisions live in proved Rocq. The ONLY permitted
   handwritten OCaml is **one tiny transparent transport glue** (`plugin/g_fido.mlg`, the `Fido Emit`
   command): it reduces a proved `DirectoryImage` in Rocq, structurally decodes path+bytes, and writes
   files verbatim/atomically — it resolves no names, inspects no program structure, chooses no files,
   provides no fallback, and fails loud on any unexpected shape. `tools/ocaml-origin-gate.sh` enforces
   **at most that one glue file** (and a textual tripwire on the deleted backend's hallmark names). Never
   reintroduce a backend, a validator around handwritten output, an OCaml renderer, name-based lowering, or
   a second emission path.
2. **Generated `*.go` is never committed.** The emitted program is produced from proved bytes at build time,
   stays gitignored, and `make check` regenerates + re-runs it so it can never drift. Never hand-edit
   generated Go — change the `.v`.
3. **Model honestly — faithful or fail-loud, never plausible-but-wrong.** An unrepresentable construct is
   ABSENT from the AST (or rejected by `go_compile`), never preserved as text or approximated. ⚠ NEVER add a
   raw/opaque/string-rescue escape hatch to a structured AST — a structured-or-fail escape hatch is the
   expensive mistake this project has already paid for (`PAINFUL_LESSONS.md`, git history).
4. **Zero project axioms — every `Print Assumptions` surface is EMPTY; preserve it.** The whole model is
   `Definition`s/`Record`s/`Inductive`s over concrete Rocq data. Never `Axiom`/`Parameter`/`Admitted`, never
   a kernel primitive (`PrimInt63`/`PrimFloat` are axioms too), never `FunctionalExtensionality` on a
   retained surface. The live build gate (`make check`) asserts the architecture's public surfaces are
   axiom-free via `gate/axiom_gate.v` — the sole `Print Assumptions` target, compiled fresh EVERY build and
   count-checked, so a warm `_build` cache can never skip it (the axiom-DECLARATION scan runs in the
   pre-commit hook, not `make check`/CI — see `PROGRESS.md`).
5. **No fuel, ever.** No gas, step budgets, max-depths, bounded runners, or renamed equivalents. A
   ranked/well-founded structural measure is acceptable ONLY as a termination proof from decreasing
   structure — never an externally supplied execution budget. A bounded run is not a proof; a timeout is not
   nontermination.
6. **Partial/unsafe ops are safe-by-construction or proof-gated.** Prefer evidence-carrying APIs or
   check-and-branch (comma-ok / `option`). Never write a Rocq program that needs a nil deref.
7. **Naming is a correctness claim.** `GoCompile` is exact static/compiler-admissibility for the
   representable domain — a declarative relation (`CompilesFile`) with an executable checker proved SOUND and
   COMPLETE against it, never a boolean `check p = true` (that was the fail-open authority this reset
   deleted). Adequacy of that model to the REAL Go compiler is a last-mile e2e integration fact, NOT a
   theorem — do not claim it as proved. `GoSafe` is a real no-panic property of an operational semantics, not
   a synonym for compiling. A syntactic/static gate implies no semantic safety unless separately proved.
8. **Imports are on hold.** Emit `package main`, no `import` block; defer any builtin needing one. Adding an
   import is the one change that still needs explicit sign-off.

## The certified layers (one authority each)

`GoAST` — the ONE raw proposed tree (may be compiler-invalid: unresolved ident, out-of-range int, wrong
package; that is intentional). No unsupported syntax (absent, not narrowed), no parenthesis node; integer
literals are unsigned magnitudes, negatives are `ENeg`. · `GoCompile` — the decorated `CompiledFile`
(resolved names, `println` builtin, intrinsic int-representability) + the `CompilesFile` relation +
`go_compile` (sound/complete/deterministic; erases back to the raw tree). · `GoSafe` — an operational
semantics (`Outcome`/print-trace/`eval_file`) + `BehaviorSafe` (no panic, proved) + `SafeProgram` (the
emission gate). · `GoRender` — the DIRECT `CompiledFile → string` printer (no tokens/lexer/parser/round-trip)
+ structural correctness (`escape_faithful`, `render_all_ascii`). · `GoEmit` — the Rocq-defined
`DirectoryImage` with proved path safety. · `plugin/g_fido.mlg` — the one transport glue. ·
`plugin/Witness.v` — the e2e witness. · `digits`/`Literals`/`GoIdent`/`TargetConfig` — leaf authorities.

## Workflow & commands

Verify after any change: **`make check`** — the git/shell gates (at-most-one-glue OCaml, no tracked `*.go`)
+ the pinned-container **proof** (Rocq 9.2.0: `dune build` + `gate/axiom_gate.v` axiom-free, count-checked)
+ the **e2e** (the `Fido Emit` plugin writes the witness's `main.go`; the pinned Go toolchain — digest-pinned
`golang:1.23-alpine` — gofmt-checks/`go vet`/`go build`/runs it; stdout/stderr/exit compared byte-for-byte to
reviewed goldens). **Local host Rocq is NOT supported** — all compilation goes through the pinned toolchain
via buildx. Then commit → re-index.

```
make check          # the one verify: gates + pinned-Rocq proof + pinned-Go e2e (all buildx)
make prove          # the proof alone (dune build + axiom gate)
make e2e            # the emit + pinned-Go run vs goldens alone
make prover-log     # stream the full plain Rocq log (diagnose a proof failure)
make install-hooks  # activate the pre-commit hook (once after clone)
```

⚠ A cancelled/timed-out buildx can zombie a `sharing=locked` cache lock and fake a hang on the NEXT build —
kill stale `docker buildx build` processes first. Run long builds detached and poll, not under a foreground
timeout.

**Pre-commit hook** (`make install-hooks`) runs `make check` on any proof/build change and seals the tree
(no tracked `*.go`, at most the one glue). Generated Go stays gitignored; goldens are human-reviewed, never
auto-regenerated; `gofmt` is a NO-OP check (never a mutating step).

## Files

- **Certified theory** (`dune` — the one module graph): `TargetConfig.v`, `Literals.v`, `GoIdent.v`,
  `digits.v`, `GoAST.v`, `GoCompile.v`, `GoSafe.v`, `GoRender.v`, `GoEmit.v`.
- `plugin/g_fido.mlg` — the ONE transport glue (`Fido Emit`). `plugin/Witness.v` — the e2e witness.
  `plugin/dune` — the plugin library + witness theory.
- `e2e/golden.{stdout,stderr,exit}` — the reviewed integration goldens.
- `gate/axiom_gate.v` — the sole `Print Assumptions` target. `tools/ocaml-origin-gate.sh` — the one shell
  gate (at-most-one-glue OCaml + backend-hallmark tripwire).
- `Makefile` / `Dockerfile` / `.githooks/pre-commit` — the buildx proof + e2e; all Rocq/Go runs in the
  pinned container (host Rocq unsupported).

## Where the detail lives

- **`ARCHITECTURE.md`** — ★ the binding charter (the layers + responsibilities + trust boundary).
- **`PROGRESS.md`** — the live status ledger (what is proved+executed, the next frontier).
- **`PAINFUL_LESSONS.md`** — why rejected architectures (backend, boolean authority, lexer/parser/round-trip,
  string-rescue) must not reappear.
- **`git log`** — the archive; commit messages carry rationale and expensive-mistake postmortems.
