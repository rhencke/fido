# Fido — operating law for a theorem-first repository

**A proof project whose vertical slice is proved AND executed.** An untrusted proposer (an LLM) may write a
raw Go program and arbitrary supporting lemmas; **no Go is emitted unless Rocq first proves the whole
program compile-admissible and safe.** There is **one** program representation — the AST *is* the IR; a
`GoProgram` is a NONEMPTY verified finite map from intrinsic `FilePath` keys to one raw `GoFileAST` per
file; "compiled" and "safe" are PROOFS/EVIDENCE + derived facts over that one program, never new trees:

```
GoProgram (nonempty fmap FilePath -> GoFileAST) -> GoCompile (whole-program admissibility + CompilationFacts
      over the SAME program) -> GoSafe (SafeProgram) -> direct GoRender -> abstract DirectoryImage
      -> the general `Fido Emit` transport command -> ownership-aware dirty-directory sink
      -> pinned Go `go build ./...` over the whole tree   [integration only]
```

The admitted fragment: files grouped by directory into `package main` packages; each `GoFileAST` is raw
top-level declarations (today only `DMain` — a `func main()` declaration; package clause / entry status are
COMPILATION RESULTS, not raw); statements are `SPrintln` over primitive literals (`EBool`/`EInt`/`ENeg` —
unsigned magnitude, negatives via `ENeg`). A `FilePath` is a narrow canonical relative path (lowercase
components + a `.go` basename); anything else — other decls, calls, params, imports, package clauses in raw
syntax, strange paths — is UNREPRESENTABLE, not rejected. Every layer is proved axiom-free; a witness
exercising bool + int + the `-(2^63)` boundary + empty/multiple `println` is emitted to a real tree (each
file's first line `// fido generated.  do not edit.`) and built by `go build ./...` + run vs reviewed
goldens, alongside a multi-package differential fixture. **State, frontier: `PROGRESS.md`. Charter (binding):
`ARCHITECTURE.md`. Rejected shapes: `PAINFUL_LESSONS.md`.**

## The law

**Ruthless correctness or ruthless deletion — no middle state.** Incomplete scope is acceptable; incorrect,
approximate, duplicated, transitional, fail-open, or half-built foundations in the certified path are not.
Every retained component must be complete and correct in itself and build only on already-complete-and-
correct foundations. **Cut representable scope before weakening a proof:** if a construct cannot be modelled
exactly, remove it from the AST (or make it unrepresentable); never admit it with a conservative narrowing.

Nobody depends on this repository. No backwards-compatibility, migration, or transition artifact. **Cost is
not a constraint; incorrectness is fatal** — take the harder/more-general/more-correct path. Plans are
guidance; when a plan conflicts with a stronger proof or a more correct formulation, follow the stronger
path and surface the divergence.

- Expressiveness expands by proof principles, never by lists of examples.
- Integration checks (the pinned-Go `go build ./...` e2e) catch regressions; they never certify
  semantics/safety/adequacy. **A Go build/run failure for an emitted program is never an expected test** —
  it means GoCompile, rendering, the derived facts, or the transport is wrong. Negative candidates fail IN
  Rocq, before any bytes.
- Public correctness claims must be backed by zero-axiom theorem surfaces. Axiom-free ≠ correct — always
  check the theorem's STATEMENT is the right one (a functional-lookup lemma is not proof of key uniqueness).
- **`GoCompile` is EXACT whole-PROGRAM compiler admissibility, not a subset filter.** It consumes the whole
  finite map; it aims to accept exactly what `go build ./...` accepts for every representable rendered
  program. Keep two claims distinct: (A) the checker matches the formal judgment is PROVED
  (`prog_ok_iff`, sound + complete); (B) accepted programs are accepted by real Go is the GOAL, attacked by
  DIFFERENTIAL experiments and the e2e, never a kernel theorem about `cmd/go`. A representable program Go
  accepts but GoCompile rejects is a MODEL BUG, never a documented limitation.
- **No second authority / no second tree:** paths, syntax, admissibility, safety, rendering, and emission
  each have exactly one authoritative definition over the ONE program. Never a copied compiled AST, a raw
  `GoPackage`, a separate/typed/target/text IR, or package/import metadata baked into raw file values.

## Standing technical law

1. **Handwritten OCaml is the transport boundary, and understands filesystems/transport — not programs.**
   All semantic work — paths, compile, safety, rendering, and the final image — is proved Rocq. The ONLY
   handwritten OCaml is the Fido Emit transport: `plugin/g_fido.mlg` (the bridge — decodes ONLY the final
   `(path, bytes)` transport via exact constructors, fail-loud; inspects no program/AST/proof) and
   `plugin/fido_sink.ml` + `e2e/sink_test.ml` (the generic dirty-directory sink + driver — filesystem
   ONLY, walk no Rocq terms). `tools/ocaml-origin-gate.sh` enforces exactly these, bounded, with those
   boundaries. NEVER reintroduce a handwritten backend/lowering/renderer/semantic decoder, or a bridge
   decoding anything but the final transport type.
2. **Generated `*.go` is never committed; emission is not a `.vo` side effect.** The `Fido Emit` command is
   an EXPLICIT always-run step (`rocq c` on the witness) after the cached theory/plugin build. `make check`
   regenerates + re-runs it so it cannot drift. The header is Rocq's bytes (`GoRender.header`), proved the
   exact first line; the sink recognizes it as an ownership marker but adds/alters no bytes.
3. **Model honestly — faithful or fail-loud, never plausible-but-wrong.** Unrepresentable ⇒ absent from the
   AST (or rejected in Rocq). ⚠ NEVER a raw/opaque/string-rescue escape hatch (`PAINFUL_LESSONS.md`).
4. **Zero project axioms — every `Print Assumptions` surface is EMPTY; preserve it.** `Definition`s /
   `Record`s / `Inductive`s over concrete data. Never `Axiom`/`Parameter`/`Admitted`, a kernel primitive,
   or `FunctionalExtensionality`. `make check` asserts the public surfaces axiom-free via `gate/axiom_gate.v`
   (the sole `Print Assumptions` target, compiled fresh + count-checked — catches EXTERNAL axioms in a
   public surface's closure) PLUS the Rocq-native `Fido Audit Assumptions` command
   (`gate/assumptions_audit.v`) that enumerates the compiled global environment and rejects ANY Fido
   constant with an axiomatic body — including UNUSED ones — which a source-text scanner cannot do
   soundly. A planted-axiom self-test proves the audit is not fail-open. NO source-text axiom scanner.
5. **No fuel, ever.** Totality comes from decreasing structure.
6. **SafeProgram is the permanent safety boundary.** `GoSafe cp := True` is honest TODAY (the fragment has
   no unsafe op); it is the extension point for guarantees beyond compiler acceptance, not circular. No
   unused panic/control placeholder.
7. **Naming is a correctness claim.** `GoSafe` uses REAL Go values (`VInt : Z`) — `EInt 0` and `ENeg 0`
   evaluate equal; `render_expr_denotes` ties the rendered spelling to the value. Every admitted primitive
   has its complete value/render/syntax proofs NOW.
8. **The program is a WHOLE-PROGRAM map with intrinsic paths, and integer width has one authority.**
   `GoProgram` is a nonempty `fmap FilePath GoFileAST`; keys are intrinsic canonical paths (raw strings are
   NOT paths — package discovery depends on them). Files group by directory into packages; package name and
   entry point are compilation results. The one width authority is `Ints` (64-bit); there is NO
   `TargetConfig`.
9. **Closed world; imports on hold.** No import syntax is representable. When imports arrive, every import
   must resolve to an owned package in the SAME program or reject the whole program — no stdlib / cache /
   network / vendor / workspace / ambient escape. Adding imports needs explicit sign-off.

## The layers (one authority each, over the ONE program)

`FilePath` — the intrinsic canonical relative-path domain (decidable eq, `fp_parent` package key; strange
paths unrepresentable). · `FMap` — key-generic finite map; `fm_keys_nodup` (THE invariant) +
`dup_key_unrepresentable`; `fm_MapsTo_fun` (distinct deterministic-lookup fact); `fm_Equal` (semantic eq ≠
record `=`); `fm_of_list` rejects duplicate keys. · `Ints` — 64-bit `int_min`/`int_max`. · `GoAST` — nonempty
`GoProgram := fmap FilePath GoFileAST`; raw `GoDecl` (`DMain`), `SPrintln`, `EBool`/`EInt`/`ENeg`; no package
clause / entry / imports in raw. · `GoCompile` — whole-program directory→package + exactly-one-main + int-
representability; `go_compile` sound/complete (`prog_ok_iff`); populated `CompilationFacts`. · `GoSafe` — real
`GoValue`, `eval_file`, `SafeProgram`. · `GoRender` — render decls + derived package clause; header exact
first line; `render_expr_denotes`. · `GoEmit` — abstract provenance-gated `DirectoryImage`; `render_program`;
`directory_entries`. · `plugin/g_fido.mlg` — the `Fido Emit` transport command. · `plugin/fido_sink.ml` — the
dirty-directory sink. · `digits` — leaf authority.

## Workflow & commands

Verify after any change: **`make check`** — the host gates (transport-only OCaml, no tracked `*.go`) + the
pinned-container **proof** (Rocq 9.2.0: `dune build` + `gate/axiom_gate.v` axiom-free, count-checked) + the
**e2e** (Dune-cached theory+plugin; then EXPLICIT `Fido Emit` synchronizes the whole tree, the Rocq-native
`Fido Audit Assumptions` gate confirms zero Fido axioms with a planted-axiom self-test, the provenance
boundary is exercised (a forged raw transport is rejected before any effect), the sink is exercised on
dirty/adversarial trees, and the digest-pinned `golang:1.23-alpine` runs `go build ./...` over the whole
tree + `go list ./...` discovery + a multi-package differential + no-main/dup-main rejection fixtures, and
runs the witness vs reviewed goldens). **Local host Rocq is NOT supported** — all compilation goes through
the pinned toolchain via buildx.

```
make check   # gates + pinned-Rocq proof + pinned-Go whole-tree e2e (all buildx)
make prove   # the proof alone (dune build + axiom gate)
make emit    # theory+plugin build + Fido Emit whole-tree sync + sink dirty/adversarial tests
make e2e     # emit + go build ./... over the tree + differential + witness vs goldens
make prover-log   # stream the plain Rocq log
make install-hooks
```

⚠ A cancelled/timed-out buildx can zombie a `sharing=locked` cache lock and fake a hang on the NEXT build —
kill stale `docker buildx build` processes first; run long builds detached and poll.

## Files

- **Certified theory** (`dune`): `digits.v`, `Ints.v`, `FilePath.v`, `FMap.v`, `GoAST.v`, `GoCompile.v`,
  `GoSafe.v`, `GoRender.v`, `GoEmit.v`.
- `plugin/g_fido.mlg` — the Fido Emit transport bridge; `plugin/fido_sink.ml` — the dirty-directory sink;
  `plugin/dune` — the plugin library. `e2e/Witness.v` — the witness (emitted explicitly); `e2e/WitnessMulti.v`
  — the multi-package differential; `e2e/sink_test.ml` — the sink driver; `e2e/golden.*` — reviewed goldens.
- `gate/axiom_gate.v` — the `Print Assumptions` target; `gate/assumptions_audit.v` — the Rocq-native
  `Fido Audit Assumptions` global-env axiom audit. `tools/ocaml-origin-gate.sh` — the host origin gate.
- `Makefile` / `Dockerfile` / `.githooks/pre-commit` — the buildx proof + whole-tree e2e (host Rocq
  unsupported).

## Where the detail lives

- **`ARCHITECTURE.md`** — ★ the binding charter (layers, responsibilities, the transport boundary, trust).
- **`PROGRESS.md`** — the live status ledger. · **`PAINFUL_LESSONS.md`** — why rejected shapes must not
  reappear. · **`git log`** — the archive.
