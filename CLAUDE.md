# Fido — operating law for a theorem-first repository

**A proof project whose vertical slice is proved AND executed.** An untrusted proposer (an LLM) may write a
raw Go program and arbitrary supporting lemmas; **no Go is emitted unless Rocq first proves the whole
program compile-admissible and safe.** There is **one** program representation — the AST *is* the IR; a
`GoProgram` is an intrinsic `ModuleSpec` (module path + Go version) paired with a (possibly EMPTY) verified
finite map from intrinsic `FilePath` keys to one raw `GoFileAST` per file; "compiled" and "safe" are
PROOFS/EVIDENCE + derived facts over that one program, never new trees:

```
GoProgram (ModuleSpec + a possibly-empty fmap FilePath -> GoFileAST) -> GoTypes (each raw literal is an
      exact UNTYPED GoConst; a use context resolves it through the ONE GoType authority {TBool,TInt,TString} to
      ProgramTyped evidence over the SAME AST) -> GoCompile (whole-program admissibility = ProgramTyped +
      exactly-one-main + CompilationFacts over the SAME program) -> GoSafe (SafeProgram) -> direct GoRender
      (incl. the go.mod) -> complete DirectoryImage (exact go.mod bytes + the .go map)
      -> the general `Fido Emit` transport command -> foreign-Go-rejecting sibling-temp dirty-directory sink
      -> one pristine `generated-module` Buildx layer (tracked go.mod + recursive .go, verified byte-exact by
         the staged-index pre-commit) -> pinned Go `GOWORK=off GOTOOLCHAIN=local go build ./...` over the
         whole tree   [integration only]
```

The admitted fragment: files grouped by directory into `package main` packages; each `GoFileAST` is raw
top-level declarations (today only `DMain` — a `func main()` declaration; package clause / entry status are
COMPILATION RESULTS, not raw); statements are `SPrintln` over primitive literals (`EBool`/`EInt`/`ENeg` —
unsigned magnitude, negatives via `ENeg` — and `EString`, whose argument is the EXACT SEMANTIC BYTE SEQUENCE,
NOT source spelling / Unicode / an escaped literal). Each raw literal denotes an EXACT UNTYPED constant
(`GoConst`); the ONE type authority `GoTypes` (universe exactly `TBool`/`TInt`/`TString`) resolves it in a use
context (int defaulting + 64-bit representability; every string constant is representable as `TString`) — a
literal is NOT a typed value, and there is no typed AST. The `ModuleSpec` is an intrinsic narrow `ModulePath` + a
singleton `GoVersion` (Go1_23), NOT a `TargetConfig`; the `go.mod` is RENDERED in Rocq. The EMPTY file map
is a valid module-only program. A `FilePath` is a narrow canonical relative path (lowercase components + a
`.go` basename); anything else — other decls, calls, params, imports, package clauses in raw syntax,
strange paths, invalid module paths — is UNREPRESENTABLE, not rejected. Every layer is proved axiom-free; a
witness exercising bool + int + the `-(2^63)` boundary + readable strings (empty/ASCII/quote/backslash/tab/
CR/NL) + empty/multiple `println` is emitted to a real tree (each file's first line `// fido generated.  do
not edit.`) and built by `go build ./...` + run vs reviewed goldens, alongside a boundary-byte string witness
(0x00/0x1f/0x7f/0x80/0xff — a byte-exact hex oracle over real Go output), a multi-package differential, and an
empty-program fixture. **State, frontier:
`PROGRESS.md`. Charter (binding): `ARCHITECTURE.md`. Rejected shapes: `PAINFUL_LESSONS.md`.**

## The law

**Ruthless correctness or ruthless deletion — no middle state.** Incomplete scope is acceptable; incorrect,
approximate, duplicated, transitional, fail-open, or half-built foundations in the certified path are not.
Every retained component must be complete and correct in itself and build only on already-complete-and-
correct foundations. **Cut representable scope before weakening a proof:** if a construct cannot be modelled
exactly, remove it from the AST (or make it unrepresentable); never admit it with a conservative narrowing.

Nobody depends on this repository. No backwards-compatibility, migration, or transition artifact. **Cost is
not a constraint; incorrectness is fatal** — take the harder/more-general/more-correct path. **The current
`.review/NEXT_STEPS.md` is binding for the active milestone. If an objective defect cannot be repaired
without changing its architecture, scope, guarantees, threat model, responsibility boundaries, or selected
algorithm, report an architectural conflict and stop. Do not implement an alternative autonomously.**

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
   All semantic work — paths, compile, safety, rendering (incl. the go.mod), and the final image — is proved
   Rocq. The ONLY handwritten OCaml is the Fido Emit transport: `plugin/g_fido.mlg` (the bridge — guards
   provenance by two kernel queries, typechecking the image type and rejecting an axiomatic assumption
   closure, then decodes ONLY the final `(go.mod bytes, (path, bytes) list)` transport via exact
   constructors, fail-loud; it understands no program/AST/semantics) and
   `plugin/fido_sink.ml` + `e2e/sink_test.ml` + `e2e/fido_apply.ml` (the generic dirty-directory sink, its
   test driver, and the `make regenerate` apply CLI — filesystem ONLY, walk no Rocq terms — the sink REJECTS
   foreign Go/module inputs and nested `.fido`, stages the complete image into RESERVED sibling temps
   `<final>.fido-tmp-v1`, installs by atomic rename, and two-phase-recovers abandoned temps fail-closed).
   `tools/ocaml-origin-gate.sh` enforces exactly these four with those boundaries — inspecting every tracked
   source at every depth (a repository-content gate, pruning only `.git`; NOT the runtime sink's opaque-dir
   skip), with NO source-line size cap (a numeric cap is not a correctness invariant). NEVER reintroduce a
   handwritten backend/lowering/renderer/semantic decoder, a bridge decoding anything but the final transport
   type, a central `.fido/staging/` design, or the deleted stage-record/nonce subsystem.
2. **The canonical generated module is a TRACKED, reviewed artifact; emission is not a `.vo` side effect.**
   Root `go.mod` + recursive `.go` are committed (Fido-headed) and verified byte-exact against the pristine
   `generated-module` Buildx layer by `make check` on the WORKING TREE (vs a pristine built from the same
   working-tree inputs) AND the pre-commit hook on the STAGED snapshot (vs a pristine built from the staged
   inputs — the SAME shared compare); `make regenerate` rewrites them
   through the SAME `Fido_sink`. The `Fido Emit` command is an EXPLICIT always-run step (`rocq c` on the
   witness) after the cached theory/plugin build, never a `.vo` side effect. The header is Rocq's bytes
   (`GoRender.header`), proved the exact first line; the sink recognizes it as an ownership marker but
   adds/alters no bytes. (There is NO no-tracked-Go seal; nested `go.mod`, tracked `.fido`/temp, and
   non-Fido-headed tracked Go are forbidden by `tools/generated-output-gate.sh`.)
3. **Model honestly — faithful or fail-loud, never plausible-but-wrong.** Unrepresentable ⇒ absent from the
   AST (or rejected in Rocq). ⚠ NEVER a raw/opaque/string-rescue escape hatch (`PAINFUL_LESSONS.md`).
4. **Zero project axioms — every `Print Assumptions` surface is EMPTY; preserve it.** `Definition`s /
   `Record`s / `Inductive`s over concrete data. Never `Axiom`/`Parameter`/`Admitted`, a kernel primitive,
   or `FunctionalExtensionality`. `make prove` (the complete proof gate) asserts the public surfaces
   axiom-free via `gate/axiom_gate.v` (the sole `Print Assumptions` target, compiled fresh + count-checked)
   PLUS the Rocq-native `Fido Audit Assumptions` command — a WHOLE-CERTIFIED-THEORY assumption-closure audit
   seeded from every Fido CONSTANT **and every Fido mutual INDUCTIVE (via `IndRef`) and every surviving
   named assumption**, computing the union of their closures (descending opaque Qed bodies) and rejecting
   every `Printer.Axiom` category (incl. assumed positivity / disabled guardedness / type-in-type / UIP) AND
   every `Printer.Variable` — catching an external axiom reached transitively through any internal/opaque
   lemma, an unused Fido axiom, AND an unreferenced assumption-bearing inductive, which a source-text scanner
   cannot do soundly. A coverage gate requires every tracked root `.v` to equal dune's `(modules …)`, and
   adversarial self-tests A-E (unused axiom / opaque-transitive external axiom / unused assumed-positive
   inductive / surviving section Variable rejected, closed Section theorem accepted) prove it is not
   fail-open. The emit command reuses the SAME closure mechanism to reject any image whose assumption closure
   is non-empty. Tracked axiom-bearing fixtures are FORBIDDEN — forged-image and audit negatives are
   generated transiently. NO source-text axiom scanner.
5. **No fuel, ever.** Totality comes from decreasing structure.
6. **SafeProgram is the permanent safety boundary.** `GoSafe cp := True` is honest TODAY (the fragment has
   no unsafe op); it is the extension point for guarantees beyond compiler acceptance, not circular. No
   unused panic/control placeholder.
7. **Naming is a correctness claim.** `GoSafe` uses REAL Go values (`VInt : Z`, `VString` exact bytes) — `EInt 0` and `ENeg 0`
   evaluate equal; runtime values carry the SAME `GoType` (`value_type`), evaluation IS the one constant
   interpretation mapped to a value (`eval_expr := const_to_value ∘ const_value`), and a resolved expression
   evaluates to a value of its resolved type (`eval_expr_resolved_type`); `render_expr_denotes` /
   `render_resolved_expr_denotes` tie the rendered spelling to that value and its type. Every admitted
   primitive has its complete type/value/render/syntax proofs NOW.
8. **The program is a `ModuleSpec` + a WHOLE-PROGRAM map with intrinsic paths, and integer width AND the
   type universe each have one authority.** `GoProgram` is `{ prog_module : ModuleSpec ; prog_files : fmap
   FilePath GoFileAST }`; the file map MAY be EMPTY (a module-only program); keys are intrinsic canonical
   paths (raw strings are NOT paths — package discovery depends on them). Files group by directory into
   packages; package name and entry point are compilation results. `ModuleSpec` (intrinsic `ModulePath` +
   singleton `GoVersion`) describes the GENERATED module, NOT the environment — it is NOT a `TargetConfig`;
   `go.mod` is not a `FilePath`. The one width authority is `Ints` (64-bit) and the one type authority is
   `GoTypes` (`TBool`/`TInt`/`TString` — `TString` is a LIVE type, landed together with its `EString` syntax +
   value + canonical rendering + decoder proofs, never ahead of it); there is NO `TargetConfig`, no second
   width/type authority, no `unknown`/`opaque`/`raw` type ahead of its syntax, and no typed AST beside the
   one raw `GoAST`.
9. **Closed world; imports on hold.** No import syntax is representable. When imports arrive, every import
   must resolve to an owned package in the SAME program or reject the whole program — no stdlib / cache /
   network / vendor / workspace / ambient escape. Adding imports needs explicit sign-off.

## The layers (one authority each, over the ONE program)

`FilePath` — the intrinsic canonical relative-path domain (decidable eq, `fp_parent` package key; strange
paths unrepresentable). · `FMap` — key-generic finite map; `fm_keys_nodup` (THE invariant) +
`dup_key_unrepresentable`; `fm_MapsTo_fun` (distinct deterministic-lookup fact); `fm_Equal` (semantic eq ≠
record `=`); `fm_of_list` rejects duplicate keys. · `Ints` — 64-bit `int_min`/`int_max`. · `ModulePath` —
the intrinsic narrow canonical module-path domain (decidable eq; invalid paths unrepresentable). ·
`GoVersion` — singleton `Go1_23`, renders "1.23". · `GoAST` — `ModuleSpec` + `GoProgram := { prog_module ;
prog_files : fmap FilePath GoFileAST }` (the map MAY be empty); raw `GoDecl` (`DMain`), `SPrintln`,
`EBool`/`EInt`/`ENeg`/`EString` (string = exact bytes); no package clause / entry / imports / TYPES in raw. ·
`GoTypes` — the ONE type authority (EVIDENCE over the raw AST): `GoType` {`TBool`,`TInt`,`TString`}, exact
untyped `GoConst` (`CBool`/`CInt`/`CString`), one `const_value` + `const_default_type` + `ConstRepresentable`
(the single 64-bit int range decision; every string representable as `TString`), reflected `ResolveExpr`,
`Stmt/Decl/File/ProgramTyped` (empty map typed vacuously). · `GoCompile` — whole-program directory→package +
exactly-one-main + whole-program typing (`ProgramTyped` via GoTypes; empty program accepted); `go_compile`
sound/complete (`prog_ok_iff`); `CompilationFacts` exposing typing by canonical projection. · `GoSafe` —
real `GoValue` (`VBool`/`VInt`/`VString`), `value_type` over the same `GoType`, `eval_expr := const_to_value ∘
const_value`, resolved-type preservation, `eval_file`, `SafeProgram`. · `GoRender` — render decls + derived
package clause + the go.mod from the `ModuleSpec`; strings via ONE canonical interpreted literal
(`render_string_literal`) with an INDEPENDENT decoder (`decode_string_literal` / `render_string_roundtrip`);
header exact first line; all-ASCII (bytes ≥ 128 only via `\xhh`); `render_expr_denotes` /
`render_resolved_expr_denotes`. · `GoEmit` — provenance-gated `DirectoryImage` (go.mod +
.go map); `render_program`; `di_transport`. · `plugin/g_fido.mlg` — the `Fido Emit` transport command +
whole-theory audit. · `plugin/fido_sink.ml` — the foreign-Go-rejecting sibling-temp sink. · `digits` —
leaf authority.

## Workflow & commands

Verify after any change: **`make check`** — verifies the WORKING TREE: the host policy gates (transport-only
OCaml, no whole-repo historical-name scanner; the generated-output policy gate: tracked Go/go.mod Fido-headed,
no nested go.mod, no tracked `.fido`/temp — both inspecting EVERY file at EVERY depth, pruning only `.git`) +
the pinned-container
**proof** (`make prove`, the COMPLETE gate: `dune build` + `gate/axiom_gate.v` axiom-free count-checked +
certified-module coverage + the whole-certified-theory `Fido Audit Assumptions` over constants + inductives +
named assumptions + adversarial self-tests A-E) + the **e2e** (Dune-cached theory+plugin; then EXPLICIT
`Fido Emit` synchronizes each tree — witness, multi-package, and the EMPTY module (rendered go.mod + zero
.go); the provenance boundary is exercised (a forged raw transport AND transiently-generated
axiom/variable-backed images are all rejected before any effect); the sink is exercised on dirty/adversarial
trees (foreign-Go/module + nested-.fido rejection, sibling-temp two-phase recovery, complete-image staging,
crash points writing/staged/installing, cleanup-failure aggregation, EXDEV no-copy, overwrite/delete-time
ownership rechecks); the pristine `generated-module` layer feeds the digest-pinned `golang:1.23-alpine`,
which runs `GOWORK=off GOTOOLCHAIN=local GOPROXY=off go build ./...` over the whole tree using the RENDERED
go.mod + the empty module + `go list ./...` discovery + a multi-package differential + no-main/dup-main
rejection fixtures, runs the witness vs reviewed goldens, with `go vet` DIAGNOSTIC-only) + a WORKING-TREE
generated-byte compare (the "no generated-byte delta" check: materialize the tracked files' working-tree
content — tracked PLUS untracked-non-gitignored via `git ls-files --cached --others --exclude-standard` — and
the pristine `generated-artifact` from the SAME working-tree proof inputs, then byte-compare the working-tree
go.mod + recursive .go against it — since `.dockerignore` hides the committed bytes from Buildx, this is the
ONLY thing that catches a header-preserving edit to a tracked `.go`). The pre-commit hook verifies the STAGED
tree instead (exports the Git index once, rebuilds `generated-module` from the staged inputs, and runs the
SAME shared byte compare over that snapshot). **Local host
Rocq is NOT supported** — all compilation goes through the pinned toolchain via buildx.

```
make check       # gates + pinned-Rocq proof + pinned-Go whole-tree e2e + verify-generated byte-compare (all buildx)
make prove       # the COMPLETE proof gate (dune build + readable gate + coverage + whole-theory audit + self-tests A-E)
make emit        # theory+plugin build + Fido Emit witness/multi/empty sync + provenance + sink tests
make e2e         # emit + pristine generated-module + go build ./... + empty + differential + witness vs goldens
make regenerate  # rebuild + apply the pristine canonical module into the repo via Fido_sink (then git add + commit)
make prover-log  # stream the plain Rocq log
make install-hooks
```

⚠ A cancelled/timed-out buildx can zombie a `sharing=locked` cache lock and fake a hang on the NEXT build —
kill stale `docker buildx build` processes first; run long builds detached and poll.

## Files

- **Certified theory** (`dune`): `digits.v`, `Ints.v`, `FilePath.v`, `FMap.v`, `ModulePath.v`,
  `GoVersion.v`, `GoAST.v`, `GoTypes.v`, `GoCompile.v`, `GoSafe.v`, `GoRender.v`, `GoEmit.v`.
- `plugin/g_fido.mlg` — the Fido Emit transport bridge + the whole-theory audit; `plugin/fido_sink.ml` —
  the foreign-Go-rejecting sibling-temp sink; `plugin/dune` — the plugin library. `e2e/Witness.v` — the
  witness (emitted explicitly, and the canonical tracked module); `e2e/WitnessMulti.v` — the multi-package
  differential; `e2e/WitnessEmpty.v` — the empty-program witness; `e2e/WitnessNeg.v` — the raw-transport
  rejection fixture (the forged-image provenance fixtures are GENERATED TRANSIENTLY in the emit stage — no
  tracked axioms); `e2e/sink_test.ml` — the sink driver; `e2e/fido_apply.ml` — the filesystem-only
  `make regenerate` apply CLI; `e2e/golden.*` — reviewed goldens.
- **Tracked canonical generated module**: `go.mod` + `main.go` at the repo root (Fido-headed; the reviewed
  derived artifact, verified byte-exact against the pristine `generated-module` Buildx layer by `make check`
  on the working tree AND the pre-commit hook on the staged snapshot).
- `gate/axiom_gate.v` — the `Print Assumptions` target. The Rocq-native `Fido Audit Assumptions`
  whole-certified-theory closure audit (constants + inductives + named assumptions) runs in the **prove**
  stage over a module list GENERATED from dune's `(modules …)` (no static file), with a coverage check
  (tracked root `.v` == that list) and adversarial self-tests A-E. `tools/ocaml-origin-gate.sh` — the host
  origin gate (transport-only OCaml allowlist + responsibility checks; NO whole-repo historical-name scanner);
  `tools/generated-output-gate.sh` — the tracked-generated-output policy gate; `tools/generated-mode-gate.sh`
  — the index-authoritative exact-mode-100644 gate (hook only); `tools/staged-generated-compare.sh` — the
  SHARED byte/path compare (working tree for `make check`, exported index for the hook) (the policy gates
  inspect every file at every depth, pruning only `.git`).
- `Makefile` / `Dockerfile` / `.githooks/pre-commit` — the buildx proof + whole-tree e2e + the pristine
  `generated-module`/`sync`/`generated-artifact` stages (host Rocq unsupported). `make check` verifies the
  WORKING TREE (byte-compare working-tree generated files vs the pristine); the pre-commit hook verifies the
  proposed STAGED snapshot (exports the Git INDEX once, runs the same shared compare over it, and never
  mutates the index or working tree). The hook is bypassable with `--no-verify` (a documented prototype-stage
  escape); it provides reasonable assurance against accidental stale generated output for a cooperating
  developer, NOT resistance to deliberate modification of its own verifier.

## Where the detail lives

- **`ARCHITECTURE.md`** — ★ the binding charter (layers, responsibilities, the transport boundary, trust).
- **`PROGRESS.md`** — the live status ledger. · **`PAINFUL_LESSONS.md`** — why rejected shapes must not
  reappear. · **`git log`** — the archive.
