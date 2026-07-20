# Fido — operating law for a theorem-first repository

**A proof project whose vertical slice is proved AND executed.** An untrusted proposer (an LLM) may write a
raw Go program and arbitrary supporting lemmas; **no Go is emitted unless Rocq first proves the whole program
compile-admissible and safe.** There is **one** program representation — the AST *is* the IR; a `GoProgram` is
a `ModuleSpec` (module path + Go version) paired with a possibly-EMPTY `GoFileMap` (a pinned-stdlib
`FilePath`-keyed `FMapAVL` of source-file roots; the PATH is the map KEY). "Compiled" and "safe" are
PROOFS/EVIDENCE over that one program, never new trees. The certified pipeline:

```
GoProgram -> GoTypes (evidence, ONE type authority) -> GoCompile (whole-program admissibility = the pinned
  one-shot `go build ./...` acceptance) -> GoSafe -> GoRender -> DirectoryImage -> `Fido Materialize` writes
  the authoritative pristine image -> pinned Go `go build ./...` VALIDATES it -> ONLY THEN the internal
  `make regenerate` sink publishes the SAME validated bytes   [integration only]
```

**The admitted fragment is small and grows only by proof.** Files group by directory into `package main`
packages; each source file is a source-owned `package main` clause + empty imports + `DMain` (a `func main()`);
statements are `SPrintln` over primitive literals: bool, the ten integer types, float32/64, complex64/128, exact
strings, and the explicit integer/float/complex conversions. Each literal is an exact UNTYPED constant; a
conversion is a TYPED constant. Anything else — other decls, calls, params, non-empty imports, non-`main`
packages, strange paths — is UNREPRESENTABLE, not rejected. Every layer is proved axiom-free and exercised by a
real emitted-and-built witness tree (see `ARCHITECTURE.md` for the layer-by-layer charter and the full witness
inventory).

**State, frontier: `PROGRESS.md`. Charter (binding): `ARCHITECTURE.md`. Rejected shapes: `PAINFUL_LESSONS.md`.
Active checkpoint: `.review/NEXT_STEPS.md`.**

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
  (`go_compile_ok_valid` + `go_compile_complete`, sound + complete; `elaborate_ok_iff_GoCompile`); (B)
  accepted programs are accepted by real Go is the GOAL, attacked by DIFFERENTIAL experiments and the e2e,
  never a kernel theorem about `cmd/go`. A representable program Go accepts but GoCompile rejects is a MODEL
  BUG, never a documented limitation.
- **No second authority / no second tree:** paths, syntax, admissibility, safety, rendering, and emission
  each have exactly one authoritative definition over the ONE program. Never a copied compiled AST, a raw
  `GoPackage`, a separate/typed/target/text IR, or package/import metadata baked into raw file values.

## Standing technical law

1. **Handwritten OCaml is the transport boundary — it understands filesystems/transport, not programs.**
   All semantic work — paths, compile, safety, rendering (incl. the go.mod), and the final image — is proved
   Rocq. The ONLY handwritten OCaml is the Fido transport: `plugin/g_fido.mlg` (the bridge — guards provenance
   ONCE by two kernel queries, typechecking the image type and rejecting a non-empty assumption closure, then
   decodes ONLY the final `(go.mod bytes, (path, bytes) list)` transport via exact constructors, fail-loud, and
   hands it to `Fido Materialize`, the SOLE Rocq transport command; there is NO public `Fido Emit`, and the
   sink publication `Fido_sink.sync` is INTERNAL, reached only from `fido_apply`/`sink_test`) and
   `plugin/fido_sink.ml` + `e2e/sink_test.ml` + `e2e/fido_apply.ml` (the pristine materializer + the generic
   dirty-directory sink, its test driver, and the tiny `make regenerate` apply adapter — filesystem ONLY, walk
   no Rocq terms; `materialize` writes the decoded image into a FRESH disposable build-validation root, never a
   user dir; the sink REJECTS foreign Go/module inputs and nested `.fido`, stages into RESERVED sibling temps
   `<final>.fido-tmp-v1`, installs by atomic rename, and two-phase-recovers abandoned temps fail-closed).
   **VALIDATE-BEFORE-PUBLISH** (the `make regenerate` workflow) is the Docker DAG: building the `sync` image
   COPYs go-e2e's `/fresh-build-ok` edge, so a failed pinned `go build ./...` makes `sync` unbuildable and
   prevents publication; the sink then publishes the ORIGINAL generated-module bytes. **No checksum/manifest
   stands in for validation provenance** — provenance is the supported Docker workflow graph. ⚠ This is
   accidental-publication protection for a COOPERATING developer (the pre-commit hook's level); the project does
   NOT attempt to resist a deliberate local bypass (`.review/C3_WEEDWHACKER_DIRECTIVE.md` §0.3).
   The OCaml uses mature runtime collections for identity/membership: the sink keys desired outputs by path in
   a `Map.Make(String)` (rejecting a duplicate path before any effect; canonical path-sorted iteration) and
   holds stale-target / abandoned-temp membership in a `Set.Make(String)`; the bridge's assumption-audit roots
   use `Names.GlobRef.Set`; the transport `list` stays a certified enumeration validated INTO the map, never
   itself the identity authority (lists remain ONLY for the order-meaningful rollback stacks). NEVER a raw
   `List.mem`/`::` identity authority or a custom hash/tree. `tools/ocaml-origin-gate.sh` enforces exactly these
   four with those boundaries, inspecting every tracked source at every depth (pruning only `.git`), with NO
   source-line size cap. NEVER reintroduce a handwritten backend/lowering/renderer/semantic decoder, a bridge
   decoding anything but the final transport type, a central `.fido/staging/` design, or the deleted
   stage-record/nonce subsystem.
2. **The canonical generated module is a TRACKED, reviewed artifact; emission is not a `.vo` side effect.**
   Root `go.mod` + recursive `.go` are committed (Fido-headed) and verified byte-exact against the pristine
   `generated-module` Buildx layer by `make check` on the WORKING TREE AND the pre-commit hook on the STAGED
   snapshot (the SAME shared compare, each vs a pristine built from those same inputs); `make regenerate`
   rewrites them through the SAME `Fido_sink`. The emit step (`Fido Materialize` on the witnesses) is an
   EXPLICIT always-run step after the cached theory/plugin build, never a `.vo` side effect. The header is
   Rocq's bytes (`GoRender.header`), proved the exact first line; the sink recognizes it as an ownership marker
   but adds/alters no bytes. Nested `go.mod`, tracked `.fido`/temp, and non-Fido-headed tracked Go are forbidden
   by `tools/generated-output-gate.sh`.
3. **Model honestly — faithful or fail-loud, never plausible-but-wrong.** Unrepresentable ⇒ absent from the
   AST (or rejected in Rocq). ⚠ NEVER a raw/opaque/string-rescue escape hatch (`PAINFUL_LESSONS.md`).
4. **Zero project axioms — every `Print Assumptions` surface is EMPTY; preserve it.** `Definition`s /
   `Record`s / `Inductive`s over concrete data. Never `Axiom`/`Parameter`/`Admitted`, a kernel primitive, or
   `FunctionalExtensionality`. `make prove` asserts the public surfaces axiom-free via `gate/axiom_gate.v` (the
   sole `Print Assumptions` target, compiled fresh + count-checked) PLUS the Rocq-native `Fido Audit
   Assumptions` command — a WHOLE-CERTIFIED-THEORY assumption-closure audit seeded from every Fido CONSTANT
   **and every Fido mutual INDUCTIVE (via `IndRef`) and every surviving named assumption**, computing the union
   of their closures (descending opaque Qed bodies) and rejecting every `Printer.Axiom` category (incl. assumed
   positivity / disabled guardedness / type-in-type / UIP) AND every `Printer.Variable` — catching an external
   axiom reached transitively through any opaque lemma, an unused Fido axiom, AND an unreferenced
   assumption-bearing inductive, which a source-text scanner cannot do soundly. A coverage gate requires every
   tracked root `.v` to equal dune's `(modules …)`, and adversarial self-tests A-E prove it is not fail-open.
   The transport command reuses the SAME closure mechanism to reject any image whose assumption closure is
   non-empty. Tracked axiom-bearing fixtures are FORBIDDEN — negatives are generated transiently. NO
   source-text axiom scanner.
5. **No fuel, ever.** Totality comes from decreasing structure.
6. **SafeProgram is the permanent safety boundary.** `GoSafe cp := True` is honest TODAY (the fragment has
   no unsafe op); it is the extension point for guarantees beyond compiler acceptance, not circular. No
   unused panic/control placeholder.
7. **Naming is a correctness claim.** `GoSafe` uses REAL Go values (`VInteger` carrying the exact value at its
   exact type; `VFloat` a proof-carrying canonical `spec_float` at its format; `VComplex` a PAIR of general
   `FloatValue` components — so a RUNTIME complex MAY carry -0/inf/NaN though a typed complex CONSTANT cannot;
   `VString` exact bytes). `EInt 0` and `ENeg 0` evaluate equal; every runtime integer value is
   range-well-formed (`ValueWF`; a float's/complex's canonicality lives in `FloatValue`); values carry the SAME
   `GoType` (`value_type`). Evaluation is DERIVED from the one constant-status analysis (`const_info` →
   `resolve_const_info` → `typed_const_to_value`) and is PARTIAL (a compiler-invalid conversion has no value —
   never a wrap; a typed float PROJECTS its stored canonical `tfc_runtime`, rounded ONCE at conversion and never
   re-rounded). `render_const_info_denotes` / `render_resolved_expr_denotes` tie the rendered spelling to the
   analyzed `ConstInfo`, value, and type. Every admitted primitive has its complete type/value/render/syntax
   proofs NOW.
8. **The program is a `ModuleSpec` + a WHOLE-PROGRAM STANDARD FilePath MAP of source files; integer width,
   float format, complex format, AND the type universe each have one authority.** The map KEY is the path (raw
   strings are NOT paths), so a duplicate path is unrepresentable by construction and `filemap_of_nodes` is
   sound + complete + exact (no silent overwrite). `GoFileNode` is a construction/view, NOT the stored value;
   semantic file-map equality is standard map `Equal`; enumerations are CANONICAL derived lists. Files group by
   directory into packages via a one-pass `PackageMap` aggregation (no O(files²) scan); the package clause is
   SOURCE-owned, entry point is a compilation result. `ModuleSpec` describes the GENERATED module, NOT the
   environment — it is NOT a `TargetConfig`. The one integer authority is `Ints` (the ten-member `IntegerType`;
   `int`/`uint` pinned 64-bit, distinct from `int64`/`uint64`), the one float authority is `Floats` (F32/F64),
   the one complex authority is `Complexes` (C64/C128, all format via the ONE `complex_component_type` mapping),
   and the one type authority is `GoTypes` (each type landed together with its syntax + value + rendering +
   proofs, never ahead of it). There is NO `TargetConfig`, no second width/type authority, no per-width runtime
   record family, no `GoTypeTag`, no `unknown`/`opaque`/`raw` type ahead of its syntax, and no typed AST beside
   the one raw `GoAST`.
9. **Closed world; imports on hold.** No import syntax is representable. When imports arrive, every import
   must resolve to an owned package in the SAME program or reject the whole program — no stdlib / cache /
   network / vendor / workspace / ambient escape. Adding imports needs explicit sign-off.
10. **Standard collections only — never roll your own (the binding COLLECTION LAW).** When a suitable mature
   collection exists in the pinned Rocq standard library, the OCaml standard library, or the Rocq runtime,
   Fido MUST use it. Fido may provide a THIN DOMAIN WRAPPER (instantiate a standard functor with a domain key,
   alias/delegate operations, enforce stronger domain construction like duplicate-rejection, define domain
   folds, prove project-specific facts, seal an interface over a standard map/set) but MUST NOT implement
   collection STORAGE or generic collection ALGORITHMS itself — no project-authored map / set / dictionary /
   keyed table / multimap / hash table / balanced tree / trie / membership-bag / adjacency collection, no
   `list + NoDup` as public identity-keyed storage, no parallel association-list backing/cache, no reimplemented
   find/mem/add/remove/balance/union. Choose by SEMANTIC ROLE: identity-keyed → a mature finite map
   (`FMapAVL`/`FMapPositive`; future sets → `MSet*`); membership-only → a mature finite set; ordered
   sequence / repetition / positional structure / rollback stack / transport enumeration → a `list`;
   duplicate-invalid source → the AST sequence or a duplicate-REJECTING builder (`mem` before `add`), NEVER a
   silent overwrite; graph → a map from vertex to a set. A map/set `elements`/`bindings` list is a DERIVED
   enumeration, NEVER a second identity authority. A failed collection builder STAYS FAILED — no
   `match build … with Some c => c | None => empty` (unless the semantics explicitly define failure as empty,
   which no Fido builder does). If NO standard collection fits: document the exact mismatch + the alternatives
   considered, report an ARCHITECTURAL CONFLICT, notify Rob, and STOP — never autonomously implement a
   collection. (`NodeTable` is acceptable ONLY because it delegates its type + operations to `FMapPositive` with
   no Fido-authored storage.) OCaml identity/membership collections likewise use `Map.Make`/`Set.Make` /
   `Names.GlobRef.Set`, never a raw `List.mem`/`::` authority.

## The layers

One authority per layer, over the ONE program:
`FilePath` · `Collections` (the ONE standard-collection foundation) · `Ints` · `Floats` · `Complexes` ·
`ModulePath` · `GoVersion` · `GoAST` · `GoIndex` (structural occurrence identity + navigation) · `GoTypes`
(the ONE type authority, evidence over the raw AST) · `GoCompile` (whole-program admissibility) · `GoSafe` ·
`GoRender` · `GoEmit` · the OCaml transport (`g_fido.mlg` / `fido_sink.ml`). The full responsibility of each
layer — its definitions, invariants, and theorem surfaces — is the binding charter in **`ARCHITECTURE.md`**;
do not restate it here.

## Workflow & commands

Verify after any change with **`make check`** (all through buildx — **local host Rocq is NOT supported**). It
verifies the WORKING TREE: the host policy gates (transport-only OCaml; the generated-output policy gate —
tracked Go/go.mod Fido-headed, no nested go.mod, no tracked `.fido`/temp — both inspecting EVERY file at EVERY
depth, pruning only `.git`) + the pinned-container **proof** (`make prove`) + the **e2e** (`make e2e`) + a
WORKING-TREE generated-byte compare (materialize the tracked files' working-tree content and byte-compare vs a
pristine built from the SAME inputs — since `.dockerignore` hides the committed bytes from Buildx, this is the
ONLY check that catches a header-preserving edit to a tracked `.go`). The pre-commit hook runs the SAME shared
compare over the STAGED snapshot instead.

- **`make prove`** — the COMPLETE proof gate: `dune build` + `gate/axiom_gate.v` axiom-free count-checked +
  certified-module coverage + the whole-certified-theory `Fido Audit Assumptions` + adversarial self-tests A-E.
- **`make e2e`** — Dune-cached theory+plugin; EXPLICIT `Fido Materialize` writes each pristine tree (witness,
  multi-package, EMPTY module); the provenance boundary is exercised (a forged raw transport and
  transiently-generated axiom/variable-backed images all rejected before any effect); the sink is exercised on
  dirty/adversarial trees; the pristine `generated-module` layer feeds the digest-pinned `golang:1.23-alpine`,
  which runs `GOWORK=off GOTOOLCHAIN=local GOPROXY=off go build ./...` over the whole tree + `go list ./...`
  discovery + a multi-package differential + no-main/dup-main + out-of-range/non-integer/wrong-type rejection
  fixtures + the witness vs reviewed goldens (with `go vet` diagnostic-only).

```
make check       # gates + pinned-Rocq proof + pinned-Go whole-tree e2e + working-tree generated byte-compare
make prove       # the COMPLETE proof gate
make emit        # theory+plugin build + Fido Materialize witness/multi/empty pristine + provenance + sink tests
make e2e         # emit + pristine generated-module + go build ./... + empty + differential + witness vs goldens
make regenerate  # rebuild + apply the pristine canonical module into the repo via Fido_sink (then git add + commit)
make prover-log  # stream the plain Rocq log
make install-hooks
```

⚠ A cancelled/timed-out buildx can zombie a `sharing=locked` cache lock and fake a hang on the NEXT build —
kill stale `docker buildx build` processes first; run long builds detached and poll.

## Review process

Two review types (`.review/CODEX_REVIEW_POLICY.md`): a **Contract Review** before implementation and an
**Implementation Review** after. Each has ONE initial review and AT MOST ONE bounded confirmation after ONE
complete repair batch. A BLOCKING confirmation (or ARCHITECTURAL CONFLICT) ENDS autonomous work — close
`REVIEW_REQUEST`, record, notify Rob, and STOP; do NOT repair or re-request without an explicit later
`human_override` token. The stop hook runs a substantive review only when `.review/REVIEW_REQUEST.md` has
`state: requested`; otherwise it returns `ALLOW` immediately.

## Files

- **Certified theory** (`dune`): `digits.v`, `Ints.v`, `Floats.v`, `Complexes.v`, `FilePath.v`,
  `Collections.v` (the ONE standard-collection foundation — pinned `FMapAVL`/`FMapPositive` wrappers; there is
  NO project-authored `FMap.v`), `ModulePath.v`, `GoVersion.v`, `GoAST.v`, `GoIndex.v`, `GoTypes.v`,
  `GoCompile.v`, `GoSafe.v`, `GoRender.v`, `GoEmit.v`. `GoIndex.v` (Source Forest C2) is the production
  occurrence-index / structural authority, landed between `GoAST` and `GoTypes`; it imports ONLY
  `GoAST`/`Collections`/`FilePath` (it knows no semantic type, compiler acceptance, rendering, or diagnostics)
  and is CONSUMED by `GoCompile`'s `elaborate` as the ONE indexed whole-program pass. Every generated byte is
  UNCHANGED by `GoIndex`. Full responsibilities: `ARCHITECTURE.md`.
- `plugin/g_fido.mlg` — the Fido transport bridge (`Fido Materialize`) + the whole-theory audit;
  `plugin/fido_sink.ml` — the foreign-Go-rejecting sibling-temp sink; `plugin/dune` — the plugin library.
  `e2e/Witness.v` — the witness (emitted explicitly, and the canonical tracked module); `e2e/WitnessMulti.v` —
  the multi-package differential; `e2e/WitnessEmpty.v` — the empty-program witness; `e2e/WitnessNeg.v` — the
  raw-transport rejection fixture (forged-image provenance fixtures are GENERATED TRANSIENTLY — no tracked
  axioms); `e2e/sink_test.ml` — the sink driver; `e2e/fido_apply.ml` — the filesystem-only `make regenerate`
  apply adapter; `e2e/golden.*` — reviewed goldens.
- **Tracked canonical generated module**: `go.mod` + `main.go` at the repo root (Fido-headed; verified
  byte-exact against the pristine `generated-module` Buildx layer by `make check` and the pre-commit hook).
- `gate/axiom_gate.v` — the `Print Assumptions` target. `tools/ocaml-origin-gate.sh` — the transport-only OCaml
  origin gate; `tools/generated-output-gate.sh` — the tracked-generated-output policy gate;
  `tools/generated-mode-gate.sh` — the index-authoritative exact-mode gate (hook only);
  `tools/staged-generated-compare.sh` — the SHARED byte/path compare (working tree for `make check`, exported
  index for the hook).
- `Makefile` / `Dockerfile` / `.githooks/pre-commit` — the buildx proof + whole-tree e2e + the pristine
  `generated-module`/`sync`/`generated-artifact` stages. The hook is bypassable with `--no-verify` (a
  documented prototype-stage escape); it gives reasonable assurance against accidental stale generated output
  for a cooperating developer, NOT resistance to deliberate modification of its own verifier.

## Where the detail lives

- **`ARCHITECTURE.md`** — ★ the binding charter (layers, responsibilities, the transport boundary, trust).
- **`PROGRESS.md`** — the live status ledger. · **`PAINFUL_LESSONS.md`** — why rejected shapes must not
  reappear. · **`.review/`** — the active checkpoint, review policy, and campaign status. · **`git log`** —
  the archive.
