# Fido — operating law for a theorem-first repository

**A proof project whose vertical slice is proved AND executed.** An untrusted proposer (an LLM) may write a
raw Go program and arbitrary supporting lemmas; **no Go is emitted unless Rocq first proves the whole
program compile-admissible and safe.** There is **one** program representation — the AST *is* the IR; a
`GoProgram` is an intrinsic `ModuleSpec` (module path + Go version) paired with a (possibly EMPTY)
`GoFileMap` — a STANDARD pinned-stdlib `FilePath`-keyed finite map (`FMapAVL`) of specification-shaped source
file roots, the PATH is the map KEY (never stored in the mapped value); a construction/view `GoFileNode` = a
`FilePath` + a `GoSourceFile` (= a source-owned package clause + empty imports + top-level declarations);
"compiled" and "safe" are PROOFS/EVIDENCE + derived facts over that one program, never new trees:

```
GoProgram (ModuleSpec + a possibly-empty GoFileMap standard source-file map) -> GoTypes (each raw literal is an
      exact UNTYPED GoConst; an explicit EIntConvert/EFloatConvert/EComplexConvert is a TYPED constant; a use
      context resolves it through the ONE GoType authority {TBool, the integer family TInteger over the
      ten-member IntegerType, the float family TFloat over FloatType, the complex family TComplex over
      ComplexType, TString} to
      ProgramTyped evidence over the SAME AST) -> GoCompile (whole-program admissibility = the pinned one-shot
      `go build ./...` acceptance = fresh-build output preflight + SourceProgramValid (ProgramTyped + the
      factored package rules) over the SAME program) -> GoSafe (SafeProgram) -> direct GoRender
      (source-owned package clause + the go.mod) -> complete DirectoryImage (exact go.mod bytes + the .go map)
      -> `Fido Materialize` writes the AUTHORITATIVE pristine image DIRECTLY (never from a sink dir) into one
         `generated-module` Buildx layer (tracked go.mod + recursive .go) -> pinned Go `GOWORK=off
         GOTOOLCHAIN=local go build ./...` VALIDATES that pristine (fresh materialization, whole tree)
      -> ONLY THEN the INTERNAL sink STEP of the ONE validated `make regenerate` workflow (there is NO public
         `Fido Emit` command — the sink `Fido_sink.sync` is reached only from `fido_apply`/`sink_test`) sinks
         the SAME validated pristine bytes (never a post-build byte) through the foreign-Go-rejecting
         sibling-temp dirty-directory sink (validation-before-publication — a failed fresh build prevents
         publication; byte-exact vs the pristine, verified by the
         staged-index pre-commit)   [integration only]
```

The admitted fragment: files grouped by directory into `package main` packages; each `GoSourceFile` is a
source-owned package clause (`PkgMain` → `package main`), intrinsically-empty imports, and top-level
declarations (today only `DMain` — a `func main()` declaration; entry status is a COMPILATION RESULT, the
package clause is SOURCE syntax rendered by GoRender); statements are `SPrintln` over primitive literals (`EBool`/`EInt`/`ENeg` —
unsigned magnitude, negatives via `ENeg` — `EString`, whose argument is the EXACT SEMANTIC BYTE SEQUENCE,
NOT source spelling / Unicode / an escaped literal, `EFloat` — a bounded-canonical finite DECIMAL value (NOT
source spelling), `EComplex` — a semantic complex literal (a PAIR of `DecimalFloat` components, canonical
spelling `complex(re, im)`, NOT imaginary-literal syntax / `real`/`imag` / a general call), and
`EIntConvert it e` / `EFloatConvert ft e` / `EComplexConvert ct e` — explicit integer / float / complex
conversions).
Each raw literal denotes an EXACT UNTYPED constant (`GoConst`); an explicit conversion of a constant is a
TYPED constant of the destination type (integer conversions value-preserving + range-checked, float
conversions ROUND once, complex conversions ROUND each component once — representability rechecked at every
nesting layer). The ONE type authority `GoTypes`
(universe = `TBool`, the integer family `TInteger` over the ten-member `IntegerType`, the float family
`TFloat` over `FloatType`, the complex family `TComplex` over `ComplexType` (complex64/complex128, components
float32/float64), and `TString`) resolves it in a use
context (an untyped int defaults to `TInteger IInt`, a bare float to `TFloat F64`, a bare complex to
`TComplex C128`; a typed constant keeps its
type + value and is not re-defaulted; representability is CHECKED for an untyped constant — the per-type
inclusive-range / float decision over `Ints`/`Floats`/`Complexes`, following Go's zero-imaginary rule for
scalar↔complex — and INTRINSIC for a typed one (validity carried by
its own dependently-typed constant, not re-checked); every string constant is representable as `TString`) — a literal is NOT a typed value, and
there is no typed AST. The `ModuleSpec` is an intrinsic narrow `ModulePath` + a
singleton `GoVersion` (Go1_23), NOT a `TargetConfig`; the `go.mod` is RENDERED in Rocq. The EMPTY file map
is a valid module-only program. A `FilePath` is a narrow canonical relative path (lowercase components + a
`.go` basename); the package clause is SOURCE-owned (`PkgMain` → `package main`) and the import section is
intrinsically empty — anything else — other decls, calls, params, non-empty imports, arbitrary (non-`main`)
package clauses, strange paths, invalid module paths — is UNREPRESENTABLE, not rejected. Every layer is proved axiom-free; a
witness exercising bool + int + the `-(2^63)` boundary + explicit conversions across ALL TEN integer types
(signed/unsigned narrow + 64-bit boundaries, platform int/uint, `uint64(2^63)`, nested `int8(int16(127))`) +
float64/float32 (an exact float->int, int->float, the direct-vs-nested double-round scar as EXACT uint64
observations, underflow to +0) + complex64/complex128 (a bare complex128 literal `complex(1.5, -2.5)`, its
complex64/complex128 conversions, zero-imaginary complex->int/float32, the component double-round scar as an
EXACT uint64 observation) + readable strings (empty/ASCII/quote/backslash/tab/CR/NL) + empty/multiple
`println` is emitted to a real tree
(each file's first line `// fido generated.  do not edit.`) and built by `go build ./...` + run vs reviewed
goldens (with hand-written differential fixtures asserting real Go REJECTS the out-of-range / non-integer
conversions the model rejects), alongside a boundary-byte string witness
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
  (`go_compile_ok_valid` + `go_compile_complete`, sound + complete; `elaborate_ok_iff_GoCompile`); (B) accepted programs are accepted by real Go is the GOAL, attacked by
  DIFFERENTIAL experiments and the e2e, never a kernel theorem about `cmd/go`. A representable program Go
  accepts but GoCompile rejects is a MODEL BUG, never a documented limitation.
- **No second authority / no second tree:** paths, syntax, admissibility, safety, rendering, and emission
  each have exactly one authoritative definition over the ONE program. Never a copied compiled AST, a raw
  `GoPackage`, a separate/typed/target/text IR, or package/import metadata baked into raw file values.

## Standing technical law

1. **Handwritten OCaml is the transport boundary, and understands filesystems/transport — not programs.**
   All semantic work — paths, compile, safety, rendering (incl. the go.mod), and the final image — is proved
   Rocq. The ONLY handwritten OCaml is the Fido transport: `plugin/g_fido.mlg` (the bridge — guards
   provenance ONCE by two kernel queries, typechecking the image type and rejecting an axiomatic assumption
   closure, then decodes ONLY the final `(go.mod bytes, (path, bytes) list)` transport via exact
   constructors, fail-loud, and hands it to `Fido Materialize` — the AUTHORITATIVE pristine write for build
   validation, the SOLE Rocq transport command (there is NO public `Fido Emit`; the sink publication
   `Fido_sink.sync` is INTERNAL — reached only from `fido_apply`/`sink_test`); it understands no program/AST/semantics) and
   `plugin/fido_sink.ml` + `e2e/sink_test.ml` + `e2e/fido_apply.ml` (the pristine materializer + the generic
   dirty-directory sink, its test driver, and the `make regenerate` apply CLI — filesystem ONLY, walk no Rocq
   terms — `materialize` writes the exact decoded image into a FRESH empty disposable build-validation root
   with NO control state (never a user dir); the sink REJECTS
   foreign Go/module inputs and nested `.fido`, stages the complete image into RESERVED sibling temps
   `<final>.fido-tmp-v1`, installs by atomic rename, and two-phase-recovers abandoned temps fail-closed.
   VALIDATION-BEFORE-PUBLICATION (canonical `make regenerate` workflow): the pinned `go build ./...` validates
   the materialized pristine and only then does the sink publish the SAME bytes — a failed build prevents
   publication (the Docker-DAG ordering; the apply CLI additionally requires a byte-INTEGRITY manifest bijection).
   ⚠ This is accidental-publication protection for a cooperating developer (the pre-commit hook's level), NOT
   resistance to a DELIBERATE local bypass — a validation-embedded inaccessible sink is a pending threat-model
   decision (`.review/C3_ARCH_CONFLICT.md`)).
   The OCaml uses mature runtime collections for identity/membership (C1A §11): the sink keys desired outputs
   by path in a `Map.Make(String)` (rejecting a duplicate path before any effect; canonical path-sorted
   iteration independent of transport order) and holds stale-target / abandoned-temp membership in a
   `Set.Make(String)`; the bridge's assumption-audit roots use `Names.GlobRef.Set`; the transport `list` stays
   a certified enumeration validated into the map, never itself the identity authority. Lists remain ONLY for
   the rollback stacks (order-meaningful). NEVER a raw `List.mem`/`::` identity authority or a custom hash/tree.
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
   through the SAME `Fido_sink`. The emit step (`Fido Materialize` on the witnesses) is an EXPLICIT always-run step (`rocq c` on the
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
7. **Naming is a correctness claim.** `GoSafe` uses REAL Go values (`VInteger : IntegerType -> Z` carrying the
   exact value at its exact type, `VFloat : forall ft, FloatValue ft -> GoValue` a proof-carrying canonical
   `spec_float` at its format, `VComplex : forall ct, ComplexValue ct -> GoValue` a PAIR of general
   `FloatValue` components — so a RUNTIME complex MAY carry -0/inf/NaN though a typed complex CONSTANT cannot,
   `VString` exact bytes) — `EInt 0` and `ENeg 0` evaluate equal, and every
   runtime integer value is range-well-formed (`ValueWF`; a `VFloat`'s / `VComplex`'s canonicality lives in the
   `FloatValue` type, so `ValueWF` there is `True`); runtime values carry the SAME `GoType` (`value_type`). Evaluation is
   DERIVED from the one constant-status analysis (`const_info` → `resolve_const_info` → `typed_const_to_value`)
   and is PARTIAL (a compiler-invalid conversion has no value — never a wrap; a typed float PROJECTS its stored
   canonical `FloatValue` `tfc_runtime`, rounded ONCE at conversion and never re-rounded — only
   finite/+0), so a RESOLVED expression evaluates to a
   well-formed value of its resolved type (`eval_expr_resolved`); `render_const_info_denotes` /
   `render_resolved_expr_denotes` (via the ONE `RenderedConstInfoDenotes`) tie the rendered spelling to the
   analyzed `ConstInfo` — a bare integer UNTYPED, a conversion typed — and to that value and its type. Every admitted primitive has its complete type/value/render/syntax proofs NOW.
8. **The program is a `ModuleSpec` + a WHOLE-PROGRAM STANDARD FilePath MAP of source files, and
   integer width, float format, AND the type universe each have one authority.** `GoProgram` is `{ prog_module
   : ModuleSpec ; prog_files : GoFileMap }` where `GoFileMap = FileMapBase.t GoSourceFile` (the pinned-stdlib
   `FMapAVL` over a `FilePath` ordered key); the map MAY be EMPTY (a module-only program); the PATH is the map
   KEY (ONE path authority — raw strings are NOT paths; package discovery depends on them), so a duplicate path
   is unrepresentable by construction and the duplicate-rejecting builder `filemap_of_nodes` is sound + complete
   + exact (each node maps to its own source, no silent overwrite). `GoFileNode` is a construction/view value,
   NOT the stored map value; a `GoFileMap` binding IS the file-root program occurrence; semantic file-map
   equality is standard map `Equal` (≠ record `=`); enumerations (`file_bindings`/`prog_keys`) are CANONICAL
   derived lists. Files group by directory into packages via a one-pass `PackageMap` aggregation (§8, no
   O(files²) scan); the package clause is SOURCE-owned (`source_package`), entry point is a compilation result.
   `ModuleSpec` (intrinsic `ModulePath` +
   singleton `GoVersion`) describes the GENERATED module, NOT the environment — it is NOT a `TargetConfig`;
   `go.mod` is not a `FilePath`. The one integer-family + range authority is `Ints` (the ten-member
   `IntegerType`; `int`/`uint` pinned 64-bit and DISTINCT from `int64`/`uint64` though they share a range on
   this target), the one float-format authority is `Floats` (the two-member `FloatType` F32/F64; precision
   24/53, exponent bound 128/1024), the one complex authority is `Complexes` (the two-member `ComplexType`
   C64/C128, all precision/keyword/rounding sourced from the ONE `complex_component_type` mapping C64->F32,
   C128->F64 — no complex-specific format), and the one type authority is `GoTypes` (`TBool`, the integer
   family `TInteger`, the float family `TFloat`, the complex family `TComplex`, and `TString` — each a LIVE
   type landed together with its syntax +
   value + rendering + proofs, never ahead of it); there
   is NO `TargetConfig`, no second width/type authority, no per-width runtime record family, no `GoTypeTag`,
   no `unknown`/`opaque`/`raw` type ahead of its syntax, and no typed AST beside the one raw `GoAST`.
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
   enumeration (canonical order / structural recursion / API / proof), NEVER a second identity authority.
   A failed collection builder STAYS FAILED — no `match build … with Some c => c | None => empty` (unless the
   semantics explicitly define failure as empty, which no Fido source/program builder does). If NO standard
   collection fits: document the exact mismatch + the alternatives considered, report an ARCHITECTURAL CONFLICT,
   notify Rob, and STOP — never autonomously implement a collection. (`NodeTable` is acceptable ONLY because it
   delegates its type + operations to `FMapPositive` with no Fido-authored storage.) OCaml identity/membership
   collections likewise use `Map.Make`/`Set.Make` / `Names.GlobRef.Set`, never a raw `List.mem`/`::` authority.

## The layers (one authority each, over the ONE program)

`FilePath` — the intrinsic canonical relative-path domain (decidable eq, `fp_parent` package key; strange
paths unrepresentable). · `Collections` — the ONE standard-collection foundation: thin wrappers over pinned
rocq-stdlib `FMapAVL` (the `FileMapBase` file map over a `FilePath` ordered key, the `PackageMapBase` map over
the `String` key) and `FMapPositive` (`NodeMapBase`) — Fido authors NO map/set; the wrapper facts
(`fp_str_inj`, `filemap_elements_Equal`: extensionally-equal maps have the SAME canonical `elements`) are
axiom-free. · `Ints` — the ten-member `IntegerType` family + the ONE
representability / range / keyword authority (`int`/`uint` pinned 64-bit, distinct from `int64`/`uint64`;
`int_min`/`int_max`/`uint_max` derived). · `Floats` — the ONE float-format authority: the two-member
`FloatType` (F32/F64; precision 24/53, exponent bound 128/1024), the exact canonical-rational `FloatConst`
(coprime lowest terms, canonical zero, decidable rational eq) + the single-round normalizer `round_float_sf`
(F32 DIRECTLY at binary32, never via F64) + `FloatConstRepresentable` + the proof-carrying canonical
`FloatValue` + the bounded finite-decimal raw-literal domain `DecimalFloat`. · `Complexes` — the ONE complex
authority (over `Floats`, below `GoAST`/`GoTypes`): the two-member `ComplexType` (C64/C128) with the ONE
`complex_component_type` mapping (C64->F32, C128->F64) sourcing all precision/keyword/rounding; the exact
untyped `ComplexConst` (a PAIR of canonical-rational `FloatConst` components); `round_typed_complex` (rounds
EACH component ONCE via `round_typed_float`); the intrinsic `TypedComplexConst ct` (a PAIR of coherent
`TypedFloatConst` components — no duplicated float coherence); the general runtime `ComplexValue ct` (a PAIR
of general `FloatValue` components — may be -0/inf/NaN); the bounded raw-literal domain `DecimalComplex`. ·
`ModulePath` —
the intrinsic narrow canonical module-path domain (decidable eq; invalid paths unrepresentable). ·
`GoVersion` — singleton `Go1_23`, renders "1.23". · `GoAST` — `ModuleSpec` + `GoProgram := { prog_module ;
prog_files : GoFileMap }` (`GoFileMap = FileMapBase.t GoSourceFile`, MAY be empty); the map key is the path;
a construction/view `GoFileNode` = `FilePath` + `GoSourceFile` (source-owned `PkgMain` package clause +
intrinsically-empty imports + `source_decls`); the file-map API (`find_file`/`file_bindings`/`file_paths`/
`FilesEqual`) + the sound/complete/exact/order-independent duplicate-rejecting builder (`filemap_of_nodes`
success-iff-unique / none-iff-duplicate / maps_to / mapsto_source / permutation) + `build_program`; raw `GoDecl`
(`DMain`), `SPrintln`,
`EBool`/`EInt`/`ENeg`/`EString` (string = exact bytes)/`EIntConvert` (integer conversion)/`EFloat` (a bounded
finite-decimal literal)/`EFloatConvert` (float conversion)/`EComplex` (a semantic complex literal, `complex(re,
im)`)/`EComplexConvert` (complex conversion); no entry / non-empty imports / non-`main` package / TYPES in
raw. · `GoIndex` — the ONE structural occurrence-identity + navigation authority DERIVED from one immutable
`GoProgram` (imports only `GoAST`/`Collections`/`FilePath`): canonical file-local `positive` preorder ids
(file root = 1); per-file `NodeMeta` {kind, option parent, role, subtree_end} in a SEALED `NodeTable` over
pinned `FMapPositive`, aggregated by the outer `SyntaxIndex p` (`FileMapBase.map index_file (prog_files p)`);
an INDEPENDENT table-free `source_occurrence_at` + the universal `index_file_source_exact` (presence +
absence); snapshot-indexed SEALED `FileRef p`/`NodeRef p`/`NodeKey`/kind-refined `NodeRefOf p k` (identity =
NodeKey identity, minted only via `file_of_path`/`ref_of_key`, cross-snapshot non-interchangeable); a TOTAL
query API (only `parent_of` optional); exact parent / interval-jump children / interval ancestry / canonical
enumeration; the §19 `visit_file` indexed traversal (original syntax + validated ref together, one pass);
consumed by `GoCompile`'s production elaboration (`elaborate`, the ONE indexed whole-program traversal — GoTypes no
longer runs a peer indexed checker; the C2 `indexed_program_typedb` demonstration is removed). · `GoTypes` — the ONE type
authority (EVIDENCE over the raw AST): `GoType` = `TBool` | `TInteger IntegerType` | `TFloat FloatType` |
`TComplex ComplexType` | `TString`, exact untyped `GoConst` (`CBool`/`CInt Z`/`CFloat FloatConst`/`CComplex
ComplexConst`/`CString`), the intrinsic
dependently-typed `TypedConst : GoType -> Type` (`TCBool`/`TCInteger it z <fits>`/`TCFloat ft (TypedFloatConst
ft)`/`TCComplex ct (TypedComplexConst ct)`/`TCString` — a mismatched/out-of-range typed constant UNREPRESENTABLE), the ONE target-directed
conversion authority `convert_const : forall target, ConstInfo -> option (TypedConst target)` (integer←integer
value-preserving + range-checked, integer←float exact integral in-range, float←int/float ROUND once — a
same-format float unchanged; complex←complex/scalar ROUND each component once, scalar↔complex by Go's
zero-imaginary rule; bool/string source-or-target reject) + the `ConstInfo` analyzer
(`CIUntyped`/`CITyped`) with `const_info_exact` the exact value (no separate `const_value`) +
`resolve_const_info` (an untyped constant DEFAULTS via `default_const` — int → `TInteger IInt`, bare float →
`TFloat F64`, bare complex → `TComplex C128`; a typed constant PACKS unchanged into a `ResolvedConst`, validity INTRINSIC) + `ConstRepresentable`
DERIVED from successful typing (`type_untyped_const_at`, no second range/overflow checker; every string
representable as `TString`), reflected `ResolveExpr` with its `ResolvedConst` witness (`resolve_expr_const`),
`Stmt/Decl/File/ProgramTyped` map-based (`ProgramTyped` over `maps_to_file`, respects `FilesEqual`; empty map
typed vacuously). · `GoCompile` —
whole-program typing + one-pass `PackageMap` grouping via a single `FM.fold` into `PackageSummary` (each file
contributes its `main` count once to its `fp_parent` package; the fold is characterized EXACTLY —
count = sum, no empty package — and is order-independent).  `GoCompile` is the EXACT acceptance model for the
pinned one-shot `go build ./...`: `GoCompile p := fresh_build_preflight_ok p ∧ SourceProgramValid p`, where
`SourceProgramValid` = `ProgramTyped` ∧ `PackageRulesValid` (the FACTORED `PackageDeclsUnique` +
`MainPackagesHaveEntry`, proved = the old one-main rule by `current_package_rules_exactly_one`) and
`fresh_build_preflight_ok` is the cmd/go default-OUTPUT part (a SOLE main package's default executable name —
import-path basename, a trailing `/vN` stripped — must not be an existing root DIRECTORY; 0 or ≥2 packages
write no default output; empty program accepted).  The ONE elaboration root `elaborate`
builds one retained `IndexedProgram` and returns a `ProgramElaboration`; `go_compile` PROJECTS it (no second
checker — `go_compile_projects_elaborate`) into a
`CompileOutcome` (`CompiledOk` carrying a `CompilableProgram` that RETAINS program + exact elaborated index +
`ElaborationFacts` = the sealed occurrence-keyed `ExprFactTable` + package main-ref buckets + the fresh-build
preflight witness, or `CompileFailed`
carrying the EXACT structured diagnostics), sound/complete (`go_compile_ok_valid`/`go_compile_complete`,
`elaborate_ok_iff_GoCompile`), the class invariant under file insertion order.  Diagnostics are structured `DiagnosticReason`
(invalid conversion — innermost primary + enclosing `outer_context`; default-not-representable; n-1
duplicate-main; missing-main; build-output-directory) anchored in the exact snapshot; the three diagnostic
LAYERS (`semantic_diagnostics` / `fresh_build_diagnostics` / the command-ordered `elaboration_diagnostics`)
each have an emptiness characterization and a FAILED preflight takes PRECEDENCE (exactly one build-output
diagnostic, hiding the semantic ones); a snapshot-free `erased_report`/`erase_diagnostic`
compares diagnostics across snapshots without a dependent transport; the coarse `legacy_compile_class` is ONLY
a projection of the diagnostics.  Typing exposed by canonical projection (`compile_program_typed`) — NO
`cf_pkg_name` (the package clause is source-owned). · `GoSafe` — real `GoValue` (`VBool`/`VInteger IntegerType Z`/
`VFloat ft (FloatValue ft)`/`VComplex ct (ComplexValue ct)`/`VString`), `value_type` over the same `GoType`,
`ValueWF` range invariant (a float's / complex component's canonicality lives in `FloatValue`), PARTIAL
`eval_expr` (`const_info` → `resolve_const_info` →
`typed_const_to_value`, which PROJECTS the stored `tfc_runtime` — rounded ONCE at conversion, never
re-rounded — only finite/+0), resolved-eval well-formedness + type
preservation, `eval_file`, `SafeProgram`. · `GoRender` —
render decls + the SOURCE-owned
package clause (`render_package_clause`, `PkgMain` → `main`) + the go.mod from the `ModuleSpec`; strings via ONE canonical interpreted literal
(`render_string_literal`) with an INDEPENDENT decoder (`decode_string_literal` / `render_string_roundtrip`);
floats via ONE canonical decimal spelling (`render_decimal`) with an INDEPENDENT decoder (`decode_decimal` /
`decode_render_decimal`); complexes via ONE canonical `complex(<real>, <imag>)` spelling (both components via
`render_decimal`) with an INDEPENDENT decoder + semantic round trip; header exact first line; all-ASCII (bytes ≥ 128 only via `\xhh`); the ONE
constant-status render root `render_const_info_denotes` (FUNCTIONAL — `render_const_info_denotes_functional`:
one spelling, at most one ConstInfo) / `render_resolved_expr_denotes`; `render_file` STRUCTURALLY consumes the
(intrinsically-empty) `source_imports` so a future import forces a renderer update. · `GoEmit` —
provenance-gated `DirectoryImage` (go.mod + `di_go_files : FileMapBase.t string`, the standard `FM.map
render_file` of the source map; `di_go_file_entries` a CANONICAL `FileMap.elements` transport list); rendered
map has the same key domain + exact bytes as the source, respects `FilesEqual`, and `di_transport` is
independent of input-node order; `render_program`; `di_transport`. · `plugin/g_fido.mlg` — the `Fido Materialize` transport command +
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
`Fido Materialize` writes each pristine tree — witness, multi-package, and the EMPTY module (rendered go.mod + zero
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
make check       # gates + pinned-Rocq proof + pinned-Go whole-tree e2e + working-tree generated byte-compare (all buildx)
make prove       # the COMPLETE proof gate (dune build + readable gate + coverage + whole-theory audit + self-tests A-E)
make emit        # theory+plugin build + Fido Materialize witness/multi/empty pristine + provenance + sink tests
make e2e         # emit + pristine generated-module + go build ./... + empty + differential + witness vs goldens
make regenerate  # rebuild + apply the pristine canonical module into the repo via Fido_sink (then git add + commit)
make prover-log  # stream the plain Rocq log
make install-hooks
```

⚠ A cancelled/timed-out buildx can zombie a `sharing=locked` cache lock and fake a hang on the NEXT build —
kill stale `docker buildx build` processes first; run long builds detached and poll.

## Files

- **Certified theory** (`dune`): `digits.v`, `Ints.v`, `Floats.v`, `Complexes.v`, `FilePath.v`,
  `Collections.v` (the ONE standard-collection foundation — pinned `FMapAVL`/`FMapPositive` wrappers; there is
  NO project-authored `FMap.v`, deleted at C1A), `ModulePath.v`, `GoVersion.v`, `GoAST.v`, `GoIndex.v`,
  `GoTypes.v`, `GoCompile.v`, `GoSafe.v`, `GoRender.v`, `GoEmit.v`.
  `GoIndex.v` is the production occurrence-index / structural authority (Source Forest C2), landed between
  `GoAST` and `GoTypes` — it imports ONLY `GoAST` / `Collections` / `FilePath` + axiom-free stdlib (NOT
  `GoTypes`/`GoCompile`/`GoSafe`/`GoRender`/`GoEmit`; it knows no semantic type, compiler acceptance,
  rendering, or diagnostics).  It derives, from one immutable `GoProgram`, a canonical file-local occurrence
  identity, a certified structural index (outer standard `FMapAVL FilePath FileIndex`, inner sealed
  `FMapPositive positive NodeMeta`), an INDEPENDENT table-free source-occurrence specification with a
  UNIVERSAL per-file source/index exactness theorem, total navigation (root-canonical / unique-parent /
  interval-jump children / preorder-interval ancestry / canonical enumeration + reachability), and a SEALED
  reference layer indexed by the exact `GoProgram` (`SyntaxIndex`/`FileRef`/`NodeRef`/`NodeKey` + kind-refined
  `NodeRefOf`, validated minting, a total query API, and the exact source-occurrence correspondence lifted
  through the sealed API), plus the §19 indexed traversal (`visit_file` runs the SINGLE-PASS `walk_file` —
  a next-free-id cursor, no per-node boundary rescan; `occs_file` is its readable spec, `walk_file = occs_file`
  — pairing each ORIGINAL syntax fragment with its validated `NodeRef`, proved exact / source-ordered / NoDup).  `GoCompile`'s production elaboration
  (`elaborate`) CONSUMES this traversal as the ONE indexed whole-program pass: it let-binds ONE `index_program p`
  and folds `visit_file`'s `(NodeRef, syntax)` pairs, taking each occurrence's ROLE from the index THROUGH the
  reference (`node_role idx (fst rocc)` — an outer-FileMap + inner-PositiveMap lookup in the PRECOMPUTED
  `si_outer`, no rebuild) and its SYNTAX from the DELIVERED fragment (`view_expr (snd rocc)` — no
  `node_at`/`source_occurrence_of_ref` recovery), delegating to the SAME `expr_typedb`/`const_info` resolver.
  `GoTypes` owns only the type/constant relation and imports NO `GoIndex`; the per-occurrence predicate
  `occ_arg_typedb` (`occs_file_typedb_eq`) lives in `GoCompile` (the sole `GoIndex`+`GoTypes` meeting point).
  `GoTypes` runs NO peer indexed whole-program checker (the C2 `indexed_program_typedb` demonstration is
  removed, §19/§26).
  The isolated C0 spike `OccurrenceSpike.v` it generalized is DELETED (no parallel spike authority remains).
  Current Go behavior and every generated byte are UNCHANGED by `GoIndex`.
- `plugin/g_fido.mlg` — the Fido transport bridge (`Fido Materialize`) + the whole-theory audit; `plugin/fido_sink.ml` —
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
