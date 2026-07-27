# Fido — status

A concise inventory of what is DONE and the immediate frontier. Architecture lives in `ARCHITECTURE.md`;
contributor law in `CLAUDE.md`; the current checkpoint and candidate in `.review/NEXT_STEPS.md`; commit-level history
in the git log.

## GREEN — proved axiom-free (every gated `Print Assumptions` surface + the whole-theory audit)

One authority per layer, over the ONE `Syntax.Program`; every layer axiom-free in the pinned container.

- **`FilePath.T`** — intrinsic canonical relative paths (lowercase components + `.go` basename); decidable eq;
  `FilePath.parent` package key; strange paths UNREPRESENTABLE. Public component authority: `dir_components`
  (+ `dir_components_concat`), over the internal `split_slash` helper.
- **`Collections`** — the ONE standard-collection foundation: thin wrappers over pinned-stdlib `FMapAVL`
  (`FileMap` over the `FilePath.T` key, `PackageMap` over `String`) and `FMapPositive` (`NodeMap`);
  Fido authors no map/set. `Collections.file_path_text_inj`, `Collections.file_elements_equal` axiom-free.
- **`Integer`** — the ten-member `Integer.Kind` family + the ONE representability/range/keyword authority
  (`int`/`uint` pinned 64-bit, distinct from `int64`/`uint64`).
- **`Float`** — the ONE float-format authority (axiom-free over `SpecFloat`): F32/F64; exact canonical-rational
  `Float.Constant`; single-round `Float.round_ieee` (F32 directly at binary32); proof-carrying `Float.Value`; the
  bounded finite-decimal `Float.Decimal`; the double-round scar.
- **`Complex`** — the ONE complex authority over `Float`: C64/C128 via the `Complex.component_kind` mapping;
  exact `Complex.Constant`; intrinsic `Complex.TypedConstant`; general runtime `Complex.Value` (pairs of `Float.Value`,
  may be -0/inf/NaN); `Complex.Decimal`; `Complex.round_typed` (each component once).
- **`ModulePath.T`** — intrinsic narrow canonical module path; decidable eq; public component authority
  `ModulePath.segments` (+ `ModulePath.text_concat`); invalid paths UNREPRESENTABLE. **`Version`** — singleton `Go1_23`, renders "1.23".
- **`Syntax`** — `ModuleSpec` + `Syntax.Program := { Syntax.module_spec ; Syntax.files : Syntax.Files }` (may be empty); the map
  KEY is the path; a construction/view `Syntax.FileNode` = `FilePath.T` + source-owned `Syntax.MainPackage` clause + empty imports
  + `Syntax.declarations`; the sound/complete/exact duplicate-rejecting `Syntax.files_of_nodes`; `Syntax.Main`, `Syntax.Println`,
  `Syntax.BoolLiteral`/`Syntax.IntegerLiteral`/`Syntax.NegatedIntegerLiteral`/`Syntax.StringLiteral` (exact bytes)/`Syntax.FloatLiteral`/`Syntax.ComplexLiteral` + ONE source-shaped `Syntax.Convert Syntax.TypeExpr`
  conversion over the closed sixteen source names (the fourteen numeric + `byte`→uint8 / `rune`→int32 aliases).
- **`Index`** — the ONE structural occurrence-identity + navigation authority derived from one immutable
  `Syntax.Program` (imports only `Syntax`/`Collections`/`FilePath.T`): canonical file-local `positive` ids; sealed
  `Table`; the universal `index_file_source_exact`; sealed snapshot-indexed refs; the `visit_file`
  single-pass indexed traversal.
- **`Typing`** — the ONE type authority, EVIDENCE over the raw AST (no typed AST): `Typing.SemanticType` = {`Typing.BoolType`,
  `Typing.IntegerType`, `Typing.FloatType`, `Typing.ComplexType`, `Typing.StringType`}; exact untyped `Typing.Constant`; intrinsic dependently-typed
  `Typing.TypedConstant`; the ONE `Typing.convert_constant` authority; `Typing.ConstantInfo`/`Typing.resolve_constant_info`/`Typing.ConstantRepresentable`;
  `Typing.Program` map-based (respects `FilesEqual`).
- **`Admissible`** — EXACT whole-program admissibility for the pinned one-shot `go build ./...`:
  `Admissible p := fresh_build_preflight_ok p /\ SourceProgramValid p`; `SourceProgramValid := Typing.Program /\
  PackageRulesValid` (the FACTORED `PackageDeclsUnique` + `MainPackagesHaveEntry`). The readable index-free
  SPECIFICATION decision (`source_spec_valid_b`/`source_spec_package_rules_b`, for fixtures) reflects the
  factored roots directly; the PRODUCTION decision is the retained-bucket diagnostic pass, whose redeclaration /
  missing-entry / all-package diagnostics are empty IFF `PackageDeclsUnique` / `MainPackagesHaveEntry` /
  `PackageRulesValid`. The ONE `elaborate` builds one `Index.Program` + `Compilable.Elaboration`; `Compilable.compile`
  projects it (sound/complete, class-invariant under file order). Default executable name is component-based:
  cmd/go's rule (`default_exec_name_c`) applied DIRECTLY to `package_import_components`
  (`ModulePath.segments` ++ `FilePath.dir_components`, no string reparse); the import-path string is their
  `/`-join, injective in the package directory (`package_import_path_inj`). Structured `DiagnosticReason` in the exact snapshot;
  the three diagnostic layers each have an emptiness characterization; a failed preflight takes precedence.
- **`Property`** — real `Safe.Value`; `value_type`; `Safe.ValueWellFormed`; PARTIAL `eval_expr` (projects the stored canonical
  runtime value, rounded once at conversion); resolved-eval well-formedness + type preservation; `Safe.Program`.
- **`Render`** — direct renderer + source-owned package clause + go.mod; strings/floats/complexes each via ONE
  canonical spelling with an INDEPENDENT decoder + round trip; header exact first line; all-ASCII.
- **`Emit`** — provenance-gated `Emit.Image` (go.mod + `.go` map, carrying a proof both came from rendering
  one `Safe.Program`); rendered map has the same key domain + exact bytes as the source; `Emit.of_safe`.

## GREEN — executed (integration evidence, never proof)

- **Transport + validate-before-publish.** `Fido Materialize` (the SOLE Rocq transport vernac) guards provenance
  in one four-step decode (typecheck the image, reject a non-empty assumption closure, decode only the final
  `(go.mod, entries)` transport, hand to the writer) and writes the authoritative pristine into a fresh
  disposable root. There is NO public `Fido Emit`; the publication sink (`Sink.sync`) is a PRIVATE plugin
  module, reached only from `sink_test` + the tiny internal `make regenerate` apply adapter (fixed source
  `/generated`, no arbitrary root, no Go, no hashing). Validate-before-publish is the Docker DAG: building the
  `sync` image COPYs go-e2e's `/fresh-build-ok`, so a failed pinned `go build ./...` makes `sync` unbuildable;
  it publishes the ORIGINAL generated-module bytes. No checksum system exists (a checksum cannot prove a build
  succeeded); cooperating-developer threat model (the pre-commit hook's level), no deliberate-bypass resistance.
- **The sink** (`plugin/sink.ml`) — the foreign-Go-rejecting sibling-temp dirty-directory synchronizer:
  rejects foreign Go/module + nested `.fido`, stages into reserved `<final>.fido-tmp-v1` temps, installs by
  atomic rename, two-phase-recovers abandoned temps fail-closed. Exercised on dirty/adversarial trees.
- **Tracked artifact + pinned Go.** One content-addressed `generated-module` Buildx layer holds the pristine
  canonical module; the tracked root `go.mod` + recursive `.go` are verified byte-exact against it by `make
  check` (working tree) and the pre-commit hook (staged). The digest-pinned `golang:1.23-alpine` runs
  `GOWORK=off GOTOOLCHAIN=local GOPROXY=off go build ./...` over the whole tree, the witness vs reviewed
  goldens, the multi-package differential, no-main/dup-main + out-of-range/non-integer/wrong-type conversion
  rejection fixtures, and the directory-collision matrix — each through the tiny `fresh_go_build` helper: a
  fail-closed state machine that runs `go build ./...` once in a fresh disposable copy and returns the reserved
  status 125 (with no run flag, no log, no output root) for every setup / `cd` / launch failure, so an
  infrastructure failure can never be read as a Go rejection (four fault self-tests).
- **Zero project axioms**, enforced two ways in `make prove`: the count-checked `gate/Assumptions.v` (Print
  Assumptions on public surfaces) AND the Rocq-native `Fido Audit Assumptions` whole-certified-theory closure
  audit (constants + inductives + named assumptions), with a module-coverage gate and adversarial self-tests A-E.

## Source Forest campaign (ACTIVE)

Multi-checkpoint C0..C6. C4 covers source type names, compiler resolution, the unified `Syntax.Convert`, and
the `byte`/`rune` source aliases.

> Checkpoint, candidate, and authorization state live only in `.review/NEXT_STEPS.md` and the FCB human-act data.
> This file records proved surfaces and the technical frontier.

The static-capability boundary retains the exact causal elaboration object (A001 / D-22): one
`Compilable.Core` holds the input, the phase, the package buckets, the root layout, the fresh-build plan and
both diagnostic lists, each stored with the proof that it IS the canonical value; the decision is indexed by
that core; success and failure both retain it; and `Compilable.Program` / `Compilable.Failure` /
`Compilable.Facts` are SEALED, so `Compilable.compile` is the only mint.

The production expression path is ONE `Compilable.Phase` over ONE retained `Compilable.Input`, driven by ONE
proof-carrying `Compilable.WorkForest`. Its ordered item list carries SOURCE ORDER and nothing else: identity
is a separate carried standard-map index, total and overwrite-free because it demands the key-NoDup as a proof
argument, so no keyed list scan remains in the member lookup path. The phase is a DEPENDENT CHAIN — each
component is typed by the exact prior object it consumes — so a foreign component is UNREPRESENTABLE by type
mismatch rather than rejected by a check. Each member's cause is a PROJECTION of the retained trace, never an
equality to a rerun.

The exact surfaces are the charter's (`ARCHITECTURE.md`) and the gate's (`gate/Assumptions.v`); restating them
here would be a second inventory that drifts.

Scope lives in `.review/UNSUPPORTED_AND_RESTRICTED_SCOPE.md`; `ADR-0001` is ADOPTED FOR CURRENT BASIS and
`ADR-0002` remains OPEN / DEFERRED (FCB Governance ADR register).
Each checkpoint is activated ONLY by explicit Rob authorization.

## NEXT — the frontier (pour roots before floors; do NOT add breadth for its own sake)

- `byte`→uint8 / `rune`→int32 SOURCE ALIASES are LANDED in C4 (source-name resolution; distinct source, equal
  semantic type). `uintptr` and exact rune constants/literals are priced scope changes, NOT C5 (needs explicit
  sign-off). Bool, the ten integer types, F32/F64, C64/C128, and exact strings are LANDED as static constant roots.
- The first construct that can panic or not terminate — `Property` grows a real `Panicked`/`Outcome` distinction,
  introduced together with the constructor (`Property` stops being `True`).
- Imports — a complete closed-world resolution model (every import resolves to an owned package in the same
  `Syntax.Program`, or reject the whole program). Needs explicit sign-off.
- Integer/float/complex ARITHMETIC — operators, wrapping, division/bitwise/shifts, no-overflow exactness, IEEE
  operations — come AFTER the type roots (an operational-foundation milestone; NOT started).

## Build-trust tasks

Done: base + Go images digest-pinned; the opam retry loop fails closed; one shared Dune cache builds theory +
plugin; zero project axioms enforced two ways (above). Still open: pin/snapshot the opam repo + verify installed
package versions.
