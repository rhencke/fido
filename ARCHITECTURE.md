# Fido — Architecture Charter (binding)

Read before any structural change. This governs. The AST is the IR: there is **one** program
representation — an intrinsic `ModuleSpec` (module path + Go version) paired with a (possibly EMPTY)
`Syntax.Files`: a STANDARD pinned-stdlib `FilePath.T`-keyed finite map (`FMapAVL`) of specification-shaped
`Syntax.File` roots (the PATH is the map KEY; a construction/view `Syntax.FileNode` = a `FilePath.T` +
a `Syntax.File`: a source-owned package clause + empty imports + top-level declarations). `Admissible`/`Property`
are EVIDENCE and facts over that same program (never copies), the generated module file (`go.mod`) is
RENDERED in Rocq, and the only handwritten OCaml is the Fido transport boundary (a term-decoding
bridge + a filesystem sink), which understands filesystems, not programs.

## The law of this repository

Ruthless correctness or ruthless deletion — no middle state. Incomplete scope is acceptable; incorrect,
approximate, duplicated, transitional, fail-open, or half-built foundations are not. Every retained
component must be complete and correct in itself and may build only on foundations that are already complete
and correct. Cut representable scope before weakening a proof. A green boolean checker is not a compile
authority; a printer's own inverse is not a Go-semantics theorem; a functional-lookup theorem is not proof
of key uniqueness; regex source scanning is not a sound zero-axiom gate; axiom-free is not correct.

**Binding contract, not advisory plan.** The current `.review/NEXT_STEPS.md` is binding for the active
milestone. If an objective defect cannot be repaired without changing its architecture, scope, guarantees,
threat model, responsibility boundaries, or selected algorithm, report an architectural conflict and stop.
Do not implement an alternative autonomously.

**The binding COLLECTION LAW (no roll-your-own).** When a suitable mature collection exists in the pinned Rocq
standard library (`FMapAVL`/`FMapPositive`, and `MSet*` for future sets), the OCaml standard library
(`Map.Make`/`Set.Make`), or the Rocq runtime (`Names.GlobRef.Set`), Fido MUST use it. A thin DOMAIN WRAPPER is
allowed and encouraged — instantiate a standard functor with a domain key, alias/delegate operations, enforce
stronger domain construction (e.g. duplicate-rejection), define domain folds, prove project-specific facts,
seal an interface over a standard map/set. Fido MUST NOT implement collection storage or generic algorithms
itself: no project-authored map/set/dictionary/table/multimap/hash/balanced-tree/trie/membership-bag/
adjacency collection, no `list + NoDup` as public identity-keyed storage, no parallel association-list
backing/cache, no reimplemented find/mem/add/remove/balance/union, no raw standard-tree constructor as public
API. Choose by SEMANTIC ROLE — identity-keyed → mature map; membership-only → mature set; ordered
sequence/repetition/stack/transport enumeration → `list`; duplicate-invalid source → the AST sequence or a
duplicate-REJECTING builder (never a silent `add` overwrite); graph → map-to-set. A map/set `elements` list is
a DERIVED enumeration, never a second identity authority. A failed collection builder STAYS FAILED (no
`Some c | None => empty` default). If none fits: document the mismatch + alternatives, report an architectural
conflict, notify Rob, and stop — never autonomously implement a collection. This is an architectural review
law backed by explicit audit and code inspection, NOT a brittle source-scanning "collection gate."

## The pipeline

```
  Syntax.Program      the ONE program representation: { Syntax.module_spec : ModuleSpec ; Syntax.files : Syntax.Files }.  The
                 source map MAY be EMPTY (a module-only program — a go.mod and no packages).  Syntax.Files =
                 Collections.FileMap.t Syntax.File (the pinned-stdlib FMapAVL over a FilePath.T ordered key):
                 the PATH is the map KEY, so paths are unique BY CONSTRUCTION and a duplicate is unrepresentable;
                 lookup by path is deterministic; enumeration (file_bindings = elements) is a CANONICAL derived
                 list; SEMANTIC equality is standard map Equal (FilesEqual), distinct from Rocq record =.  The
                 duplicate-rejecting builder Syntax.files_of_nodes (list Syntax.FileNode -> option Syntax.Files) is sound +
                 complete + EXACT (each node maps to its own source, no silent overwrite) + order-independent.
                 A construction/view Syntax.FileNode = { Syntax.path : FilePath.T ; Syntax.source : Syntax.File }: the
                 path is the map key, not stored in the mapped value — ONE path authority.  A Syntax.Files binding
                 IS the file-root program occurrence.  A Syntax.File = { Syntax.package (Syntax.MainPackage, the source-owned package
                 clause) ; Syntax.imports (INTRINSICALLY empty — Syntax.ImportSpec has no constructors) ;
                 Syntax.declarations (a list of Syntax.Decl; today only Syntax.Main = a `func main()` decl) }.  Entry-point
                 status, symbols, and types are COMPILATION RESULTS; the package clause is SOURCE syntax.

  ModuleSpec     an intrinsic fact about the GENERATED module (NOT environment config, NOT a TargetConfig):
                 { module_path : ModulePath.T ; Syntax.module_version : Version }.  ModulePath.T is an INTRINSIC
                 narrow canonical module path (slash-separated lowercase segments [a-z][a-z0-9.]* ending
                 a-z0-9, no `..`/leading-trailing/repeated slash, arbitrary length (no cap); FIRST element dotted (no
                 stdlib-colliding dotless prefix), NO `/vN` version-suffix tail, NO `gopkg.in/` — the two
                 Go-1.23 semantic-import-versioning reject classes; accepted by go 1.23 as a `module`
                 directive, exact one-way (valid `/v2`/gopkg modules are out of scope, excluded not narrowed);
                 invalid paths UNREPRESENTABLE).  Version is a SINGLETON today
                 (Go1_23, renders exactly "1.23"); adding a later constructor is a reviewed semantic
                 milestone.  The exact compiler binary/toolchain pin is operational, off the theorems.

  FilePath.T       an INTRINSIC canonical relative source path (not a raw string): slash-separated
                 lowercase-ASCII directory components + an ordinary lowercase-ASCII `.go` basename, with
                 no empty/`.`/`..` component, no absolute/leading/trailing/repeated slash, no leading dot
                 or underscore (so no hidden/`_test`/`_GOOS` file, no control-name collision).  Path length
                 is UNBOUNDED in the model/grammar/sink (platform host limits like `NAME_MAX`/`PATH_MAX` are
                 NOT a Fido domain concern — see PAINFUL_LESSONS): every representable path is well-formed for
                 `go build ./...` package DISCOVERY, and materialization is the ONE place an over-long path
                 fails LOUD at the OS (`ENAMETOOLONG`), never silently.  `Admissible == go build` is exact for
                 the SEMANTIC + cmd/go package/output logic, EXCLUDING such platform filesystem limits.
                 Validity is a carried proof; equality is decidable.  (`go.mod` is NOT a FilePath.T — a distinct
                 root field carries it.)

  Index        the ONE structural occurrence-identity + navigation authority, DERIVED from one immutable
                 Syntax.Program snapshot (imports only Syntax/Collections/FilePath.T; it knows no semantic types,
                 admissibility, rendering, or diagnostics).  Each represented source occurrence gets ONE
                 canonical file-local `positive` id by a deterministic preorder (file root = 1); its Index.Meta
                 lives in a per-file SEALED Table (a thin API over pinned-stdlib FMapPositive — no
                 Fido-authored storage), aggregated by the program index Index.Syntax p.  An INDEPENDENT,
                 table-free source_occurrence_at re-derives each occurrence's metadata directly from the syntax;
                 the universal `index_file_source_exact` pins stored metadata = source-occurrence metadata at
                 every id in PRESENCE and ABSENCE (a mislabeled table is unprovable).  References
                 (FileRef/NodeRef/Index.Key + kind-refined NodeRefOf) are SEALED, indexed by the EXACT Syntax.Program
                 and minted only through validated `file_of_path`/`ref_of_key`; identity is Index.Key identity,
                 and a different-payload OR different-ModuleSpec snapshot yields non-interchangeable reference
                 types even when the erased index data is equal.  A conversion `Syntax.Convert ts x` occupies TWO
                 children — the source type-name occurrence (kind `Index.TypeNameKind`, role `Index.ConversionTarget`, a LEAF
                 carrying `Index.TypeNameView ts`) at `Pos.succ me`, then the operand subtree (`Index.ConversionOperand`) at
                 `Pos.succ (Pos.succ me)`; `TypeNameRef` (= `NodeRefOf Index.TypeNameKind`) recovers the retained source
                 `Syntax.TypeExpr` THROUGH the reference (`type_name_ref_syntax`, always Some for a real ref).  A TOTAL query API (only parent_of optional) is
                 total by carried validity, never a semantic fallback; navigation is exact (parent via metadata,
                 direct children by preorder interval-jumps, ancestry by intervals, a canonical enumeration, and
                 the SINGLE-PASS `visit_file` traversal supplying each ORIGINAL syntax fragment with its
                 validated NodeRef in one structural pass — no per-node search, no copied/located AST, no second
                 tree).  Admissible's `elaborate` consumes it as the ONE indexed whole-program pass (see the
                 Admissible entry); Typing imports NO Index and runs NO peer indexed whole-program checker.

  Typing        the ONE Go type-system authority — EVIDENCE over the raw Syntax, never a typed AST.  The
                 permanent type universe is EXACTLY { Typing.BoolType, the integer family Typing.IntegerType over the ten-member Integer.Kind, Typing.FloatType Float.Kind, the complex family Typing.ComplexType over Complex.Kind, Typing.StringType }.  A raw literal denotes an EXACT
                 UNTYPED constant (Typing.Constant := Typing.BoolConstant bool | Typing.IntegerConstant Z | Typing.FloatConstant Float.Constant | Typing.ComplexConstant Complex.Constant |
                 Typing.StringConstant string — ints
                 arbitrary-precision, a bare float literal (Syntax.FloatLiteral) an EXACT canonical rational, a complex
                 literal (Syntax.ComplexLiteral) an EXACT pair of rational components, strings exact
                 byte sequences).  Typing.constant_info analyzes an expression's constant STATUS (Typing.ConstantInfo := Typing.UntypedInfo
                 Typing.Constant | Typing.TypedInfo t (Typing.TypedConstant t)), where Typing.TypedConstant : Typing.SemanticType -> Type is an INTRINSIC
                 dependently-typed family (Typing.TypedBool / Typing.TypedInteger it z <proof z fits it> / Typing.TypedFloat ft
                 (Float.TypedConstant ft) / Typing.TypedComplex ct (Complex.TypedConstant ct) / Typing.TypedString) — a mismatched or out-of-range typed constant is
                 UNREPRESENTABLE, never merely rejected.  The exact value of an expression is Typing.constant_info_exact of
                 Typing.constant_info (there is NO separate const_value path).  Typing.convert_constant : forall target, Typing.ConstantInfo ->
                 option (Typing.TypedConstant target) is the ONE conversion authority (int←int value-preserving +
                 range-checked; int←float exact-integral + in-range; float←int/float rounds ONCE at the
                 destination — a same-format float returns the existing Float.TypedConstant unchanged; complex←
                 complex/scalar rounds EACH component ONCE, scalar↔complex by Go's zero-imaginary rule (a
                 complex→scalar requires exact-zero imaginary); bool/string
                 reject).  ONE source-shaped explicit conversion (Syntax.Convert ts e) names a SOURCE type ts
                 (Syntax.TypeExpr); its semantic target is the compiler-owned resolution rt ts (a total resolver
                 Syntax.TypeExpr -> Typing.SemanticType that Admissible supplies — the index-free typing spec Typing.constant_info … Typing.Program
                 is wrapped in a Coq Section parameterized by rt, so Typing never owns a source-name→Typing.SemanticType table).
                 The conversion routes through Typing.convert_constant at rt ts: an integer target yields a value-preserving
                 TYPED constant repr-checked at EVERY nesting layer; a float target ROUNDS ONCE (F32 DIRECTLY at
                 binary32, never via F64 — the double-round scar); a complex target rounds EACH component ONCE.
                 Typing.resolve_constant_info : Typing.ConstantInfo -> option Typing.ResolvedConstant is the USE
                 CONTEXT (today Typing.PrintlnArgument) resolution: an UNTYPED constant DEFAULTS via Typing.default_constant (an int
                 to Typing.IntegerType Integer.Int, a float to Typing.FloatType F64, a complex to Typing.ComplexType C128), a TYPED constant PACKS unchanged (its validity is
                 INTRINSIC — not re-defaulted, not re-checked).  Typing.ConstantRepresentable is DERIVED from successful
                 typing (exists tc, Typing.type_untyped_constant_at t c = Some tc — the ONE typing/defaulting construction,
                 routing numeric targets through Typing.convert_constant so representability and conversion never disagree,
                 no second integer-range or float-overflow checker).  Typing.Resolve
                 u e t (reflected by Typing.resolve, sound + complete + deterministic) is the resolved typing of
                 one expression; Typing.resolve_constant exposes its Typing.ResolvedConstant witness;
                 Typing.Stmt/Typing.Decl/Typing.File/Typing.Program lift it to the whole program (the
                 EMPTY file map is typed vacuously).  There is NO placeholder/unknown/raw type, NO second
                 numeric-width authority, and NO typed AST.

  Admissible      EXACT WHOLE-PROGRAM admissibility = the pinned one-shot `go build ./...` acceptance:
                 Admissible p := fresh_build_preflight_ok p /\ SourceProgramValid p.  SourceProgramValid =
                 Typing.Program /\ PackageRulesValid, where PackageRulesValid FACTORS the two independent Go rules
                 PackageDeclsUnique (package-block name uniqueness) and MainPackagesHaveEntry (a main package has
                 a `main`), proved EXACTLY the old "every package has one main" ([current_package_rules_exactly_one],
                 universal).  Files are grouped by parent directory ([FilePath.parent]); the whole program is TYPED
                 through Typing (a typing failure is a constant fitting no integer type, a non-integer conversion
                 operand, or an invalid nested conversion); one invalid package rejects all (all-or-nothing).
                 [fresh_build_preflight_ok] is the cmd/go default-OUTPUT part: a SOLE main package's default
                 executable name (import-path basename, a trailing `/vN` major-version element stripped) must not
                 be an existing root DIRECTORY (0 or ≥2 packages write no default output; empty program accepted).
                 The ONE elaboration root [elaborate] builds ONE retained [Index.Program] and returns a
                 [Compilable.Elaboration]; [Compilable.compile] PROJECTS it (no second checker — [Compilable.compile_projects_elaborate])
                 into a [Compilable.Outcome] — [Compilable.Compiled] carrying a
                 [Compilable.Program] (which RETAINS the program, its exact elaborated index, and its
                 [Compilable.Facts]: the sealed occurrence-keyed [Compilable.ExpressionFactTable] + the sealed occurrence-keyed
                 [Compilable.TypeNameFacts] (each conversion's SOURCE type name resolved by the ONE compiler-owned
                 [predeclared_type] context (§7) to a semantic [Typing.SemanticType] — the fact stores that resolved type
                 ONLY, keyed by [Index.Key]; the total [type_name_fact_at] query PROJECTS the sealed table without
                 recomputing resolution; `byte`/`uint8` and `rune`/`int32` are DISTINCT source syntax with EQUAL
                 facts) + the package main-ref buckets +
                 the fresh-build preflight witness),
                 or [Compilable.Rejected] carrying the EXACT structured diagnostics.  A rejected program yields NO
                 [Compilable.Program] (hence no Safe.Program/image).  Diagnostics are structured [DiagnosticReason]
                 values (invalid conversion — primary = the innermost failing conversion, with an [outer_context]
                 field for the enclosing conversions; default-not-representable; n-1 duplicate-main — one per
                 redundant main relative to the first; missing-main; and build-output-directory) anchored in the
                 EXACT snapshot ([DiagnosticAnchor]: NodeRef/FileRef/PackageRef/program).  The three diagnostic
                 LAYERS ([semantic_diagnostics] / [fresh_build_diagnostics] / the command-ordered
                 [elaboration_diagnostics]) each have an emptiness characterization, and a FAILED preflight takes
                 PRECEDENCE (exactly one build-output diagnostic, hiding the sole package's semantic errors); a
                 snapshot-independent [erased_report]/[erased_elaboration_report] enables cross-snapshot comparison
                 without a dependent transport.  The coarse
                 [legacy_compile_class] (with Compilable.LegacyBuildOutput) remains ONLY as a projection of the structured
                 diagnostics.  Determinism is split (FilesEqual source facts vs the full ProgramInputEqual for
                 the plan/report/class), and the Emit.Image bridge proves the rendered image REALIZES the
                 fresh root layout ([Emit.realizes_fresh_layout]).  The package
                 clause is SOURCE-owned (Syntax.package), NOT a compiler-derived fact — there is NO [cf_pkg_name];
                 the compiled evidence EXPOSES that the same p is typed via a canonical projection
                 (compilable_program_typed), not a stored typed copy.

  Property         the safety capability Safe.Program over Compilable.Program, plus a PER-FILE abstract
                 println-trace with REAL values (Safe.BoolValue/Safe.IntegerValue Integer.Kind Z/Safe.FloatValue ft (Float.Value ft)/
                 Safe.ComplexValue ct (Complex.Value ct)/Safe.StringValue exact bytes).  Runtime values use the SAME Typing.SemanticType
                 authority (value_type) and are range-well-formed (Safe.ValueWellFormed; a Float.Value is a PROOF-CARRYING
                 canonical Stdlib SpecFloat.spec_float — the image of the format normalizer, Flocq NOT used — so
                 Safe.ValueWellFormed(Safe.FloatValue) := Safe.ValueWellFormed(Safe.ComplexValue) := True with canonicality in the type; a general runtime
                 Complex.Value is a PAIR of Float.Value components that MAY be -0/inf/NaN, while constant eval
                 produces only finite/+0).  Evaluation is DERIVED from Typing.constant_info and is PARTIAL (a
                 compiler-invalid conversion has no value — never a wrap), so a resolved expression evaluates to
                 a well-formed value of its resolved Typing.SemanticType (eval_expr_resolved).  Property := True TODAY (the
                 fragment has no unsafe op), documented honestly — the PERMANENT extension point for guarantees
                 beyond compiler acceptance.  There is no whole-PROGRAM execution semantics yet (only the witness
                 package is executed vs goldens); a per-package program semantics arrives when a construct needs
                 it.

  Render       the direct renderer.  It renders each Syntax.File to bytes (the package clause from the
                 file's OWN Syntax.package via Render.package_clause — Syntax.MainPackage -> `main`, each Syntax.Main as a
                 `func main()`) AND renders the go.mod from the ModuleSpec (`module <path>` + `go <version>`).
                 Every rendered file — go.mod and every
                 .go — begins with the exact header `// fido was here.  woof woof.  do not edit.` as its FIRST LINE.
                 A conversion renders as `<Render.type_expr ts>(<inner>)`, reading the RETAINED SOURCE
                 identifier (Names.render_supported — NOT the resolved Typing.SemanticType), so all sixteen source names render their own
                 spelling: the fourteen numeric names, and `byte(<inner>)`/`rune(<inner>)` distinct from
                 `uint8`/`int32` even though they resolve to the same semantic type;
                 a float constant renders by ONE canonical decimal spelling (zero → `0.0`; nonzero →
                 `<signed-coeff>.0e<±exp>`) paired with an INDEPENDENT decoder proving `decode(render d) = Some d`
                 (the exact rational round trip), and a complex constant by ONE canonical `complex(<real>, <imag>)`
                 spelling (both components via that decimal spelling) with an INDEPENDENT complex decoder + a
                 semantic round trip.  Proved: all-ASCII (keywords + conversions included);
                 Render.const_info_denotes (rendering an expression denotes exactly the Typing.ConstantInfo Typing computes — a bare
                 integer/float is UNTYPED, an explicit conversion is a typed constant routed through Typing.convert_constant —
                 via the ONE Render.ConstantInfoDenotes relation, now with float cases), and that relation is FUNCTIONAL
                 (Render.const_info_denotes_functional: a spelling denotes AT MOST ONE Typing.ConstantInfo — the six recognisers
                 are pairwise disjoint, so no spelling carries two conflicting constant statuses);
                 Render.resolved_expr_denotes (a resolved argument EVALUATES to a well-formed value of its
                 resolved Typing.SemanticType whose spelling denotes it — tying the three authorities); decimal-faithful, no
                 leading zero, header-first-line; go.mod exact bytes / header first line / ASCII.

  Emit.Image the COMPLETE module: exact root go.mod bytes (Emit.module_bytes) + a finite map from FilePath.T to
                 exact final .go bytes (Emit.files), PROVENANCE-GATED: a value carries a proof BOTH came
                 from rendering ONE Safe.Program (Emit.provenance).  A CLOSED proof witnesses that; but a proof can be
                 POSTULATED (axiom/variable), so the type alone is not sufficient — the live transport
                 boundary (`Fido Materialize`) is the real gate (it rejects an assumption-dependent proof).  The .go map MAY be
                 empty; there is NO nonemptiness claim.  Emit.MakeImage is public but demands the proof;
                 Emit.of_safe is the canonical closed construction.  Emit.transport projects it to the
                 (exact go.mod bytes, (on-disk path, bytes) list) transport.

  Fido            the ONE Rocq transport command (a vernac), `Fido Materialize`, guards provenance via ONE
  Materialize     shared decode (`decode_guarded`): before ANY effect it typechecks its argument's Emit.transport
                 as a Emit.Image projection (rejecting a raw transport) AND rejects any argument whose
                 assumption closure contains an axiom (rejecting a same-typed image built from a forged
                 proof); only then does it decode ONLY the final (go.mod bytes, (path, bytes) list) transport
                 (exact constructors of prod/list/string/ascii/bool, fail-loud otherwise).  `Fido Materialize
                 <image> To "<root>"` writes those authoritative bytes DIRECTLY into a fresh disposable
                 build-VALIDATION root (no sink control state, never a user dir).  There is NO public `Fido
                 Emit`: the publication SINK (`Sink.sync`) is INTERNAL — reached only from the sink's
                 own test driver and the `make regenerate` apply CLI, which the validated workflow invokes ONLY
                 after the pinned `go build ./...` validates the materialized image.  VALIDATION-BEFORE-
                 PUBLICATION: the committed canonical artifact is copied from THAT materialization; the sink
                 publishes only the SAME validated bytes — a failed build prevents publication.  Not
                 witness-specific; no recompile for a different Safe.Program.

  materialize    the authoritative pristine writer (in the sink file): exact decoded image bytes into a fresh
                 EMPTY disposable root, O_EXCL/fail-closed, NO `.fido`/staging/foreign-rejection.  Filesystem ONLY.

  sink           the generic ownership-aware dirty-directory synchronizer (PUBLICATION): it REJECTS foreign
                 Go/module inputs + nested .fido, then stages the complete image into reserved sibling temps
                 `<final>.fido-tmp-v1` and installs by atomic rename (two-phase recovery).  Filesystem ONLY.

  pinned Go      `go build ./...` over the WHOLE canonical `generated-module` tree + witness run.
                 Integration only.
```

**There is no second tree, no separate/typed/target/text IR, no tokenizer/lexer/parser, no
AST->output->AST round-trip authority, no copied compiled AST, no handwritten OCaml language semantics.**
`Admissible` produces facts + a proof over the one `Syntax.Program`; the renderer traverses it directly.

## Two honest claims (never conflate)

- **(A) KERNEL-internal exactness — PROVED.** The executable `Compilable.compile` succeeds exactly for the
  declarative `Admissible` judgment (`Compilable.compile_ok_valid` + `Compilable.compile_complete`, sound + complete; the one
  elaboration root satisfies `Compilable.elaboration_accepted_iff_admissible`), and the renderer/semantics facts hold — asserted
  axiom-free every build.
- **(B) EXTERNAL adequacy target — the GOAL, not a kernel theorem.** The declarative judgment matches `go
  build ./...` acceptance for every representable rendered program. We model the acceptance semantics
  independently; `cmd/go` is used only for DIFFERENTIAL experiments and the e2e. A representable program `go
  build ./...` accepts but Admissible rejects is a MODEL BUG (fix the model or narrow the representation), never
  a "permanent limitation"; a program Admissible accepts but `go build ./...` rejects is a correctness failure.

## Responsibility table (does / does NOT)

| Layer | Does | Does NOT |
|---|---|---|
| **FilePath.T** | the intrinsic canonical relative-path domain; decidable eq; `FilePath.parent` (package key); safe + `go build ./...`-discoverable by construction | admit raw strings, absolute/`..`/hidden/`_test`/GOOS-suffixed/non-`.go` paths |
| **Collections** | the ONE standard-collection foundation: thin wrappers over pinned-stdlib `FMapAVL` (`FileMap` over a `FilePath.T` ordered key, `PackageMap` over `String`) + `FMapPositive` (`NodeMap`); axiom-free wrapper facts (`Collections.file_path_text_inj`; `Collections.file_elements_equal` — extensionally-equal maps have the SAME canonical `elements`) | author a map/set implementation (no tree/list-backed collection); expose the backing tree; use a list + `NoDup` as a map |
| **ModuleSpec** | intrinsic module facts: narrow `ModulePath.T` (decidable eq, canonical render) + singleton `Version` (Go1_23 → "1.23") | be a `TargetConfig`; carry GOOS/GOARCH/ABI/scheduler/point-release; admit an invalid module path (unrepresentable) |
| **Syntax** | `ModuleSpec` + a possibly-EMPTY program map + raw `Syntax.Decl` (a `func main` form) over `Syntax.BoolLiteral`/`Syntax.IntegerLiteral`/`Syntax.NegatedIntegerLiteral`/`Syntax.StringLiteral`/`Syntax.FloatLiteral` (a bare float literal carrying an INTRINSIC bounded-canonical finite decimal `coeff·10^exp`, `\|coeff\|<10^40`, `\|exp\|≤4096`)/`Syntax.ComplexLiteral` (a semantic complex literal, a PAIR of `Float.Decimal` components spelled `complex(re, im)`)/ONE `Syntax.Convert Syntax.TypeExpr Syntax.Expr` (a source-shaped explicit conversion naming a SOURCE type — the closed sixteen-name lexical class carried as a `Syntax.TypeExpr`: the fourteen numeric names plus the `byte`/`rune` SOURCE ALIASES — over any `Syntax.Expr` operand; the SOURCE name never decides its semantic type); a SOURCE-owned package clause (`Syntax.package`, `Syntax.MainPackage`) + an intrinsically-empty import section (`Syntax.imports`); key-uniqueness intrinsic (the map key) | carry an entry-point flag / a compiler-derived package name / package GROUPING / a raw path stored in the mapped value; an ARBITRARY (non-`main`) package clause or non-empty imports; a nonemptiness restriction; a second tree; a type on a raw literal; a resolved SEMANTIC target (`Typing.SemanticType`, or a `byte`/`rune` collapsed to `uint8`/`int32`) baked into raw conversion syntax; a source-name→`Typing.SemanticType` table in the AST; arithmetic / imaginary-literal / `real`/`imag` / NaN / Inf syntax |
| **Index** | the ONE structural occurrence-identity + navigation authority DERIVED from one immutable `Syntax.Program` (imports only Syntax/Collections/FilePath.T): canonical file-local `positive` preorder ids (file root = 1); `Index.Meta` {kind, option parent, role, subtree_end} in a SEALED per-file `Table` (thin API over pinned `FMapPositive`) aggregated by `Index.Syntax p` (`FileMap.map index_file (Syntax.files p)`); an INDEPENDENT table-free `source_occurrence_at` + the universal `index_file_source_exact` (stored metadata = source-occurrence metadata at every id, PRESENCE + ABSENCE); snapshot-indexed SEALED `FileRef p`/`NodeRef p`/`Index.Key`/kind-refined `NodeRefOf p k`, identity = Index.Key identity, minted only via validated `file_of_path`/`ref_of_key`; a TOTAL query API (`ref_meta`/`node_kind`/`node_role`/`node_subtree_end`/`containing_file`/`children_of`/`source_occurrence_of_ref`; only `parent_of` optional); exact parent / interval-jump direct children / interval ancestry / canonical preorder enumeration; the `visit_file` indexed traversal (original syntax + validated ref together, one pass) | import Typing/Admissible/Property/Render/Emit; know semantic types / admissibility / rendering / diagnostics; author collection storage or a node trie; add a hidden file slot / a parallel path map / an author id / root id 0; copy the source tree or build a second/located/typed AST; deduplicate structurally-equal occurrences; index Syntax.ComplexLiteral components or Syntax.NegatedIntegerLiteral as child nodes; rebuild the index per query; a fail-soft query fallback |
| **Typing** | the ONE type authority — EVIDENCE over the raw AST: `Typing.SemanticType` = `Typing.BoolType` \| `Typing.IntegerType Integer.Kind` \| `Typing.FloatType Float.Kind` \| `Typing.ComplexType Complex.Kind` \| `Typing.StringType`; exact untyped `Typing.Constant` (bool / int / float / complex / byte-string; a `Typing.FloatConstant` is an exact CANONICAL rational — numerator `Z` / positive coprime denominator, canonical zero, decidable eq, NOT a float/spec_float/decimal-string/rounded value; a `Typing.ComplexConstant` a PAIR of such rationals); the intrinsic dependently-typed `Typing.TypedConstant : Typing.SemanticType -> Type` (a mismatched/out-of-range typed constant UNREPRESENTABLE; `Typing.TypedComplex ct` a PAIR of coherent `Float.TypedConstant` components — no duplicated float coherence); the ONE conversion authority `Typing.convert_constant : forall target, Typing.ConstantInfo -> option (Typing.TypedConstant target)` (int conversions value-preserving, float conversions ROUND ONCE at the destination — F32 direct at binary32, a same-format float unchanged; complex conversions ROUND each component once, scalar↔complex by Go's zero-imaginary rule); the `Typing.ConstantInfo` analyzer (`Typing.UntypedInfo`/`Typing.TypedInfo`, repr-checked at every nesting layer) with `Typing.constant_info_exact` the exact value (no separate `const_value`); `Typing.resolve_constant_info` (untyped DEFAULTS via `Typing.default_constant` int → `Typing.IntegerType Integer.Int`, float → `Typing.FloatType F64`, complex → `Typing.ComplexType C128`; typed PACKS unchanged, validity INTRINSIC); `Typing.ConstantRepresentable` DERIVED from successful typing (`Typing.type_untyped_constant_at`, no second range/overflow checker); reflected `Typing.Resolve` with its `Typing.ResolvedConstant` witness (`Typing.resolve_constant`); `Stmt/Decl/File/Typing.Program` | a typed AST / `TypedIR` / copied "resolved expression"; a placeholder/unknown/raw/opaque type ahead of its syntax; a second numeric-width or conversion authority; a `GoTypeTag`; a float stored as a rounded/spec_float/decimal-string constant; a complex-specific float format or duplicated component coherence; typing a literal outside a use context |
| **Admissible** | the SOLE meeting point of Index identity + Typing semantics (owns the per-occurrence `Compilable.occurrence_arg_typedb` + its `occs_*_typedb_eq` traversal bridge, moved off Typing); whole-program map-based typing + one-pass `PackageMap` grouping (a single `FileMap.fold` into `PackageSummary`, characterized EXACTLY: count = sum over the package's files, no empty package) + the fresh-build output preflight over the factored source rules (`Admissible p := fresh_build_preflight_ok p /\ SourceProgramValid p`, via Typing); `Compilable.compile` sound/complete, its accept/error class invariant under file insertion order; the retained `elaborate` produces ONE `Compilable.Facts` (indexed BY the exact accepted `Compilable.Core` AND its acceptance evidence, so it cannot be paired with a different elaboration) carrying the occurrence-keyed expression facts + the occurrence-keyed type-name facts (each conversion's source name resolved via the ONE compiler-owned `predeclared_type` context to a semantic `Typing.SemanticType`; `byte`→`uint8`, `rune`→`int32`) + package `main`-ref buckets + the fresh-build preflight witness, exposed by canonical projection; the production expression path is ONE `Compilable.Phase` built from ONE retained `Compilable.Input`, driven by ONE proof-carrying retained work forest OBJECT — the `Compilable.WorkForest` record (`build_expr_work_forest`; its stored `Compilable.forest_blocks`/`Compilable.forest_items` with `Compilable.forest_items = concat Compilable.forest_blocks`, forward domain `Compilable.forest_forward` + reverse domain `Compilable.forest_reverse` + key-NoDup `Compilable.forest_keys_nodup` + per-file/flat order + operand-in-suffix `Compilable.forest_operand_in_tail`, all carried as FIELDS; `build_forest_blocks` stays PRIVATE inside, returning its proof INTO the record — no `proj1_sig` discard) whose IDENTITY role is a SEPARATE carried field, the exact standard work-member index `Compilable.forest_index : Compilable.WorkIndex Compilable.forest_items` — the ONE identity authority over the work items: a pinned-stdlib `Index.KeyMap` (`FMapAVL`) map built ONCE by `build_work_index` from the ALREADY-BUILT item list (so it can neither re-traverse `Compilable.input_visit` nor re-run `build_forest_blocks`), TOTAL with no option/fallback/empty-default precisely because it DEMANDS `Compilable.forest_keys_nodup` as a PROOF ARGUMENT, and OVERWRITE-FREE (`work_index_fresh`/`work_index_add_fresh` prove every `add` writes an absent key); the record is INDEXED BY `Compilable.forest_items` and `Compilable.index_exact` pins map to list in BOTH directions, so a foreign map is not pairable with a forest and a duplicate-keyed list has no index at all; `Compilable.index_domain` and `Compilable.index_key_inj` are DERIVED (never stored — no second domain or uniqueness authority, and `Compilable.forest_key_inj` is now that map-derived theorem). The ordered `Compilable.forest_items` therefore keeps its ORDER role ONLY: the TOTAL member queries `index_member_at`/`forest_index_member_at` are ONE `KeyMap.find` with the impossible `None` discharged by a Prop existence hypothesis, `build_conversion_work` queries the index at the key of the operand `ExprRef` the item ALREADY CARRIES (`Compilable.work_conv`) rather than a separately computed value, and NO `List.find`/`existsb`/recursive key scan exists anywhere in the work-member lookup path (`index_no_foreign`/`index_nonexpr_absent` exclude foreign and wrong-kind keys), each item an `Compilable.Work` carrying its own `ExprRef` plus a total `Compilable.Conversion` view of its conversion target/operand refs (with the exact operand `WorkMember` + the target-before-operand SOURCE order `Compilable.conversion_target_before_op`, NOT a suffix-membership proof — processed-suffix membership is the SEPARATE `Compilable.forest_operand_in_tail`), which the outcome fold, the facts, the annotation, and the diagnostics ALL consume by RECEIVING the exact object as a parameter (no second work discovery, no reminted conversion ref): the PROOF-CARRYING `Compilable.Outcomes forest tnft` (`build_forest_outcome_table`, folding the object's `Compilable.forest_items` into the proof-carrying `Compilable.Accumulator` `Compilable.outcomes_acc` PAIRED WITH the `Compilable.Trace` `Compilable.outcomes_trace` that BUILT it (INDEXED by `Compilable.outcomes_acc`, so the accumulator and its causal predecessor chain are NOT freely pairable — a foreign rest accumulator that merely reproduces a head outcome cannot be attached); the per-member RETAINED direct cause is a PROJECTION of the trace (`total_forest_outcome_cause` returning each member's `RetainedMemberCause` — its exact suffix split `Compilable.forest_items = prefix ++ current :: rest`, the AUTHENTICATED prior `Compilable.Accumulator` for `rest`, the member/suffix-indexed `StepCause` reading the operand outcome THROUGH the exact operand `SuffixMember` via the total `Compilable.accumulator_total acc_rest`, AND the tail-to-final QUERY PRESERVATION — NEVER `local_conv_failure`/a resolver/a recursive `Typing.constant_info`) together with its EXACT domain `Compilable.outcomes_dom` (`Compilable.accumulator_domain`: every key is a visited EXPRESSION occurrence — the domain is EXACTLY membership in `Compilable.forest_items`, `Compilable.outcomes_domain_iff_forest`, so an extra/foreign key is uninhabitable and a non-expression key is absent `Compilable.outcomes_nonexpr_absent`); the index-free source specification is REACHED per member by the SEPARATE match `total_forest_outcome_at_matches` (`trace_match`, projected from the trace), never carried a second time) that CONSUMES the once-built `Compilable.TypeNameFacts` object (`build_type_name_fact_table`): each conversion step queries the table at its retained target `TypeNameRef` (the TOTAL `type_name_fact_at_table` query, no fallback), reads its operand's ALREADY-COMPUTED outcome THROUGH the exact operand `SuffixMember` of the processed tail (`Compilable.step_operand_suffix`, whose tail-membership is `Compilable.forest_operand_in_tail`; the TOTAL `Compilable.accumulator_total acc_rest` query on the prior accumulator — missing-operand impossible by `Compilable.accumulator_covers`, never a raw `find`/`operand_key`/fallback), and calls `Typing.convert_constant` ONCE per conversion (no raw Index.Key arithmetic, no second visit, no `Typing.constant_info` on the live path, no per-ancestor re-evaluation, no `index_program` reconstruction in the phase closure); the invalid-conversion outcome (`Compilable.ConversionFailure`) CARRIES the exact conversion / target / operand refs, so the diagnostic PROJECTS them — the operand ref is a field of `Compilable.InvalidConversion`, nothing re-minted; the TOTAL fact projection (`forest_facts`, folding `Compilable.forest_items` via `total_forest_outcome_at`) and the TOTAL diagnostic projection (the retained `Compilable.Diagnostics` object's stored list, via `forest_awork_diags` over the retained `Compilable.AnnotatedWork` OBJECT `build_annotated_work_forest` — a proof-carrying record whose members ARE `Compilable.forest_items` in order (`Compilable.annotated_members`), whose `Compilable.annotated_diag_fold` ties them to the one-pass `annotate_program` (so diagnostics CONSUME the object — no `proj1_sig` discard, no re-annotation), and which carries context soundness/same-file/nearest-first/nodup; keyed by each work item's OWN carried `Compilable.work_expr_ref`, so NO `as_expr` call and NO fail-open `None` branch) both read that SAME `Compilable.Outcomes` inside the one phase, which RETAINS the whole flow as a DEPENDENT CHAIN of objects — `Compilable.phase_ot : Compilable.Outcomes Compilable.phase_work Compilable.phase_type_name_facts`, `Compilable.phase_awork : Compilable.AnnotatedWork Compilable.phase_work`, `Compilable.phase_fact_table : Compilable.ExpressionFacts Compilable.phase_work Compilable.phase_ot`, `Compilable.phase_diag : Compilable.Diagnostics Compilable.phase_awork Compilable.phase_ot` — each TYPED by the exact prior object it consumes (NO provenance-equality field; the causal chain is the dependent types, shown definitionally by `phase_ot_consumes_work`/`phase_awork_consumes_work`/`Compilable.phase_fact_table_consumes_work_outcomes`/`phase_diag_consumes_awork_ot`), so a foreign component is UNREPRESENTABLE by type mismatch (`Compilable.phase_facts = Compilable.fact_table_map (Compilable.expression_facts_table Compilable.phase_fact_table)`; `facts_and_diags_share_phase`, object identity — no fail-open `find`); the phase's `Compilable.TypeNameFacts` (`Compilable.phase_type_name_facts`) is reached through `Compilable.Facts` by OBJECT IDENTITY (`compilable_retains_tnfacts`) and its `Compilable.ExpressionFactTable` likewise (`compilable_retains_expr_facts`, the retained OBJECT `Compilable.expression_facts (Compilable.facts cp) = Compilable.expression_facts_table (Compilable.phase_fact_table (Compilable.program_phase cp))`, not a map equality — a projection of the retained core, no rebuild after the decision), a stored outcome's cause is PROJECTED from the retained `Compilable.Trace` keyed by the WORK member (`total_forest_outcome_cause` returning each member's exact `RetainedMemberCause` — its suffix split + the AUTHENTICATED tail `Compilable.Accumulator` + the `StepCause` producing the FINAL outcome + the tail-to-final query preservation, so a foreign tail accumulator cannot satisfy it; `final_operand_outcome` closes a conversion's operand into the final table); the direct cause is projected axiom-free by `Compilable.conversion_failure_cause_yields_step`/`Compilable.child_failure_cause_yields_member`/`Compilable.conversion_success_cause_yields_step`, each reading the operand outcome THROUGH the exact operand `SuffixMember` via `Compilable.accumulator_total acc_rest`), and the erased report retains the target source spelling; `Compilable.Program` RETAINS the exact accepted `Compilable.Core` (index, phase, buckets, layout, plan and both diagnostic lists are PROJECTIONS of it, never a stored equality to a rerun; the buckets are folded from the elaboration's OWN retained `input_visit` and the package diagnostics CONSUME that stored map, so the production chain never reruns `program_visit`), and `Compilable.Core`/`Compilable.Program`/`Compilable.Failure`/`Compilable.Facts` are ALL SEALED — the raw records, their constructors and `build_elaboration_core` stay inside the sealed implementation, so a client cannot assemble a peer core, and the only mint is `Compilable.compile`; NO `cf_pkg_name` (package clause is source-owned) | be a boolean; accept per-file partially; re-scan the file list per package (O(files²)); hide package grouping / entry status in a raw node; store a typed copy of the program; reconstruct the index rather than retain it; recover a keyed work member by SCANNING the ordered item list (a `list + NoDup` standing in for an identity map) |
| **Property** | real `Safe.Value` (`Safe.BoolValue`/`Safe.IntegerValue Integer.Kind Z`/`Safe.FloatValue ft (Float.Value ft)`/`Safe.ComplexValue ct (Complex.Value ct)`/`Safe.StringValue`; a `Float.Value` is a PROOF-CARRYING canonical Stdlib `SpecFloat.spec_float`, Flocq unused; a `Complex.Value` a PAIR of them that MAY be -0/inf/NaN, unlike a constant); `value_type` over the SAME `Typing.SemanticType`; `Safe.ValueWellFormed` range invariant (`Safe.ValueWellFormed (Safe.FloatValue …) := Safe.ValueWellFormed (Safe.ComplexValue …) := True` — canonicality in the type; constant eval only finite/+0); PARTIAL `eval_expr` derived from `Typing.constant_info`; resolved-eval well-formedness + type preservation; abstract `eval_file`; `Safe.Program` (0 = -0); honest `Property := True` | observe spelling as value; a separate runtime type universe; a per-width runtime record family / `GoTypeTag`; keep an unused panic placeholder; circularly reference compilation |
| **Render** | render decls + the SOURCE-owned package clause (from the file's OWN `Syntax.package` via `Render.package_clause`, `Syntax.MainPackage` → `main` — NOT a derived/deduced name); render go.mod from the ModuleSpec; a conversion as `<source-name>(<inner>)` rendering the exact SOURCE spelling from the `Syntax.TypeExpr` (`Render.type_expr` = `Names.render_supported`; `byte`/`rune` render their OWN spelling, NEVER the resolved `uint8`/`int32`); ONE canonical float decimal spelling (`0.0`; else `<signed-coeff>.0e<±exp>`) with an INDEPENDENT decoder proving `decode(render d) = Some d`, and ONE canonical complex spelling `complex(<real>, <imag>)` (both components via that decimal spelling) with an INDEPENDENT complex decoder + semantic round trip; header exact first line (go.mod and .go); `Render.const_info_denotes` / `Render.resolved_expr_denotes` (spelling ↔ Typing.ConstantInfo ↔ value/resolved type; the conversion case via `Typing.convert_constant` over the rendered SOURCE spelling — one determinism theorem `Render.const_info_denotes_functional` over the sixteen source names; all via the ONE `Render.ConstantInfoDenotes`) | tokenize/lex/parse/round-trip; deduce packages/entry; invoke a formatter; add require/replace/toolchain to go.mod |
| **Emit.Image** | the complete module (exact go.mod bytes + a possibly-empty .go map), provenance-gated (`Emit.provenance` proves BOTH came from `Emit.of_safe`; `Emit.MakeImage` demands that proof); `Fido Materialize` typechecks its argument's `Emit.transport` AND rejects any argument with an axiomatic assumption closure | be an arbitrary-map escape that bypasses Safe.Program; invent go.mod in the sink; make a nonemptiness claim; accept a raw transport, or a same-typed image built from a forged (axiomatic) proof, at the transport boundary |
| **Fido Materialize + internal sink** | ONE provenance-guarded decode (typecheck the image, reject a non-empty assumption closure, decode ONLY the final (go.mod, entries) transport with exact constructors) feeding the SOLE Rocq writer, `Fido Materialize`, which writes the authoritative bytes DIRECTLY into a fresh disposable build-validation root (no sink state).  There is NO public `Fido Emit`: the publication SINK (`Sink.sync`, the foreign-Go-rejecting sibling-temp sync) is INTERNAL OCaml (sink_test + the `make regenerate` apply CLI), which the validated workflow invokes only AFTER a fresh `go build ./...` succeeds — a failed build prevents publication | inspect the program/AST/behaviour/semantics; materialize without both provenance guards; expose a standalone public sink command; build after sinking into a user dir; copy the committed artifact from a post-sink dir; merge/preserve a foreign `.go`/`go.mod`; delete/overwrite/follow foreign state; keep a stage-record/nonce/central-staging design |

## The handwritten-OCaml boundary (hard)

**All semantic work is proved Rocq.** The ONLY handwritten OCaml is the Fido TRANSPORT boundary:
- `plugin/materialize.mlg` — the transport bridge, a four-step boundary: (1) typecheck the argument's
  `Emit.transport` projection as the certified image type; (2) reject a non-empty assumption closure (a kernel
  provenance query that descends Qed proof bodies — the SAME `closure_assums`/`assums_disallowed` mechanism
  the whole-theory audit uses); (3) reduce and STRUCTURALLY decode ONLY the final `string * list
  (string*string)` transport — the exact go.mod bytes and the (path, bytes) list (exact constructors,
  fail-loud); (4) hand to `Fido Materialize` (the SOLE Rocq transport vernac — the authoritative pristine
  write for build validation).  There is no public `Fido Emit`: the publication SINK (`Sink.sync`) is a
  PRIVATE plugin module (NOT exported from `fido.emit`, so not independently usable as publication by any OCaml
  consumer), reached only from INTERNAL OCaml (`e2e/sink_test.ml` + the `make regenerate` apply CLI), over the
  SAME decoded bytes. It does no semantic program/AST/
  behaviour inspection. That both provenance guards stay live is a mutation-sensitive REGRESSION gate, not a
  proof: the emit stage's negative fixtures (a raw transport + TRANSIENTLY-generated axiom/variable-backed
  images) execute forged inputs and, if either guard were removed, the corresponding command would succeed
  and create a target — failing the e2e (a spoofable source grep would not).
- `plugin/sink.ml` + `e2e/sink_test.ml` + `e2e/apply.ml` — the pristine `materialize` (exact image
  bytes into a fresh EMPTY disposable validation root, no control state; a low-level EXPORT primitive, never
  publication) + the generic dirty-directory PUBLICATION synchronizer (`Sink.sync`, a private plugin
  module), its test driver, and the tiny INTERNAL `make regenerate` apply adapter.  The adapter has a FIXED
  source (`/generated`) and destination; it enumerates the pristine layer and hands `(go.mod, .go)` to the
  sink; it runs no Go, hashes nothing, and accepts no arbitrary source root.  Filesystem ONLY: they walk no
  Rocq terms and run no programs.  VALIDATE-BEFORE-PUBLISH ordering (supported / cooperating-developer threat
  model): building the `sync` image COPYs go-e2e's `/fresh-build-ok` Docker-DAG edge, so `make regenerate`
  cannot publish unless the pinned `go build ./...` succeeded first, and it publishes the ORIGINAL
  generated-module bytes, never a post-build byte.  No checksum/manifest system exists (a checksum cannot prove
  a build succeeded); the project does not attempt to resist a deliberate local bypass (extracting a binary,
  hand-editing the Dockerfile/hooks) — the pre-commit hook's assurance level.

`tools/ocaml-origin-gate.sh` enforces exactly these four files (inspecting every source at every depth — a
repository-content gate, not the runtime sink, so it prunes only `.git`), filesystem-only for the
sink/driver/apply, transport-only for the bridge — there is NO source-line size cap (a numeric cap is not a
correctness invariant) and NO whole-repository historical-name scanner (the real boundary is this allowlist
plus the responsibility checks; repository prose may freely discuss deleted history). **Never reintroduce a
handwritten OCaml backend / lowering / renderer / semantic decoder, or a bridge that decodes anything but
the final transport type.** If the transport boundary cannot be met correctly, delete the e2e — a false
transport foundation is worse than no integration.

### Dirty-directory synchronization (honest guarantee)

`Admissible`, `Property`, and Emit.Image production are whole-program ALL-OR-NOTHING. Installation into an
existing dirty tree is locked (a persistent `<root>/.fido/` control dir with an exact marker + a git-style
`index.lock`). Before any effect the sink (generic over raw strings, so it trusts no caller) VALIDATES the
`root` (every proper ancestor must be an existing real directory — a symlink in ANY prefix component is
rejected, else ordinary resolution would follow it and redirect all effects) and REJECTS a desired path
inside the RESERVED `<root>/.fido/` namespace.

**Foreign Go/module inputs REJECT the whole emission** (fail-closed scan, before any generated-file
mutation): any foreign `.go` anywhere in the Go-DISCOVERED namespace (a regular file whose first line is not
the header, or a `.go` symlink/nonregular entry), a foreign root `go.mod`, a `go.mod` symlink, or any nested
`go.mod`. The traversal SKIPS the opaque dot/underscore/`testdata`/`vendor` trees `go build ./...` itself
ignores (so `.git` stays untouched); everything under them is preserved, as are foreign NON-Go files/dirs.
Installed `.go` files and the root `go.mod` are Fido-owned iff their first line is the exact header AND they
are regular non-symlink files (rechecked by lstat immediately before every overwrite/delete, so a symlink is
never followed); a foreign `.go`/`go.mod` forging the header is the accepted limit (a header is public).

**Sibling-temp staging (no records, no nonce, no stage directory, no parser).** `<root>/.fido/` holds
EXACTLY the marker and, during an active run or after a crash, the git-style `index.lock` — any other
root-control entry rejects without modification. Each final output stages into its RESERVED sibling temporary
`<final>.fido-tmp-v1` (the lock serializes cooperating emitters, so the name needs no nonce and recovery no
record). The sink stages the COMPLETE image (go.mod + every .go) before any install, then installs each file
by rename from its sibling temp — same filesystem, so nested mount points inside root are supported; EXDEV
fails loud with no copy fallback. Only then are stale Fido-owned `.go` files removed (the empty program
removes them all, keeping/updating the owned go.mod). A **regular non-symlink** `.fido-tmp-v1` file is, by
PUBLIC (forgeable) CONVENTION, an abandoned Fido temp ONLY IF its suffix-stripped path maps to a Fido FINAL
path (the root `go.mod` or an intrinsic FilePath.T `.go`); a non-mappable suffixed entry, or a
symlink/directory/special with that suffix, is NOT owned (refuse + preserve). A nested `.fido` (any type) in
the traversed namespace is an emission error and aborts.

**Fail-closed, two-phase.** Only a confirmed `ENOENT` means "missing"; every other filesystem error aborts.
After the lock: PHASE 1 inspects the whole namespace once (validating the foreign-Go/module/control rules and
COLLECTING every VALID abandoned temp), deleting nothing; if any path is invalid or uninspectable the run
rejects before any mutation, preserving every collected temp. PHASE 2 (only after the scan succeeds)
re-`lstat`s each collected temp, requires it is still a regular reserved-suffix file mapping to a final path,
and deletes it (fail-loud on any mismatch). A handled failure removes this run's created temps + newly-empty
parents, aggregates body + cleanup + lock-release errors, and releases the lock. Install is a sequential
rename loop — a mid-install failure may leave earlier files installed (nontransactional, stated honestly);
residue remains only after an uncatchable CRASH or a cleanup/lock-release failure, and a rerun (after the
stale lock clears) removes the temps and converges. It is **NOT** hardened against a concurrent
non-cooperating process (this OCaml `Unix` exposes no `openat`/`O_NOFOLLOW`); the honest model is COOPERATING
emitters serialized by the lock, in the Linux/amd64 scope. Ownership is by header + regular-file +
desired-key-set (or the reserved suffix mapping to a final path, for temps), never timestamps, a manifest,
records, or device/inode identity.

**The exact guarantee.** *Syntax.Program acceptance, Safe.Program certification, and Emit.Image creation are
semantically all-or-nothing. Dirty-directory installation is locked for cooperating emitters, rejects
foreign Go/module inputs and nested `.fido` in the Go-discovered namespace (skipping the opaque
dot/underscore/testdata/vendor trees `go build ./...` ignores), inspects that namespace fail-closed, stages
the complete image into reserved sibling temporary files before installation, uses per-file rename in the
ordinary same-filesystem case, cleans handled-failure temps immediately, removes validated abandoned
suffix-owned temps (whose suffix-stripped path maps to a Fido final path) on a later run, and converges when
the directory namespace remains stable. It is not a portable
transactional multi-file filesystem commit, not hardened against malicious concurrent mutation, and does not
model arbitrary unmount/remount/backing-store replacement between runs.*

### Pristine generated-module layer + tracked artifact (prototype pre-commit)

One ordinary content-addressed Buildx stage, `generated-module`, holds EXACTLY the canonical generated
module (`/generated/go.mod` + recursive `.go` — the primary witness), assembled from the authoritative
generation inputs (certified `.v`, dune, plugin, pinned toolchain, canonical witness) and never from the
committed generated bytes, never a mutable cache mount. Every canonical-output workflow — the Go e2e,
`make regenerate`, and the pre-commit staged-index verification — consumes THAT one layer. The canonical
generated module (root `go.mod` + recursive `.go`) is a **tracked, reviewed derived artifact** (Fido-headed;
`.v`/proof sources remain authoritative; no `dist/`, no handwritten Go in the module, no nested `go.mod`).
`make regenerate` rewrites it into the repo through the SAME `Sink`. Verification is split coherently:
`make check` verifies the **working tree** (it materializes the working-tree content of every relevant file —
`git ls-files --cached --others --exclude-standard` through tar: tracked files with their uncommitted edits
PLUS untracked non-gitignored files, so a rogue untracked `foreign.go`/`.ml` is caught, while the gitignored
local residue `.fido/`/`*.fido-tmp-v1`/`*.vo` is excluded — rebuilds the
pristine `generated-module`/`generated-artifact` from the same working-tree inputs, and byte-compares the
working-tree `go.mod` + recursive `.go` against it, path set + bytes both directions); the **pre-commit hook**
verifies the proposed **staged** commit (it exports the Git INDEX once, runs the SAME shared compare over that
staged snapshot, and never reads the unstaged working tree or auto-stages). This byte-compare is essential
because `.dockerignore` hides the committed `go.mod`/`.go` from the Buildx context, so the proof/e2e cannot
incidentally validate their bytes. The pre-commit hook is a PROTOTYPE boundary providing **reasonable
assurance** against accidental stale generated output for a cooperating developer using ordinary Git commands;
it is bypassable with `git commit --no-verify` and does NOT defend against deliberate modification of its own
verifier — local verifier tamper-resistance is explicitly OUT OF SCOPE (a future PR CI runs the same
comparison server-side as a stronger boundary).

## Closed world

Imports are absent and UNREPRESENTABLE. **Permanent contract:** when import declarations are added,
`Admissible` must resolve every import to an owned package derived from the SAME `Syntax.Program`; any unresolved or
external import (stdlib, module cache, network, vendor, workspace, or ambient filesystem) rejects the whole
program unless a later reviewed foundation explicitly and completely models that source.

## Growing the language

Every new AST constructor enters only when COMPLETE: exact whole-program `Admissible` rules matching `go build
./...` (constructor absent otherwise), operational meaning in `Property`, renderer support with its value/syntax
proofs, and — where observable — a differential fixture + e2e witness. Shrink the representable language before
weakening `Admissible`. The package clause and future import declarations are SOURCE syntax owned by the file
(`Syntax.package` / `Syntax.imports`); package GROUPING, entry status, and import RESOLUTION are compilation
results, never raw metadata. Integer width, float
precision + single-round conversion, complex format, and the type universe each have ONE authority (`Integer`
64-bit / `Float` F32/F64 / `Complex` C64/C128 over `Float` via the ONE `Complex.component_kind` mapping,
no complex-specific format / `Typing` = {`Typing.BoolType`, `Typing.IntegerType`, `Typing.FloatType`, `Typing.ComplexType`, `Typing.StringType`}); `int`/`uint`
are pinned 64-bit and DISTINCT from `int64`/`uint64`; there is no `TargetConfig`. **A COMPOUND typed constant is
COMPOSED from already-coherent typed COMPONENT constants** (a `Complex.TypedConstant` is a pair of
`Float.TypedConstant` components; a runtime `Complex.Value` a pair of `Float.Value`s) — the component authority's
coherence + runtime-denotation proofs are REUSED, never duplicated at the aggregate layer; and the UNTYPED /
TYPED / RUNTIME distinction holds at every level (a runtime complex MAY carry -0/inf/NaN; a typed complex
constant CANNOT). A new type constructor arrives ONLY with the syntax and complete semantic obligations that
need it (as `Typing.StringType` did — value + canonical rendering + an independent decoder proving the byte round trip,
claiming no source-spelling inverse), never a speculative `unknown`/`opaque`/`raw` type, and never a typed
AST. Raw literals stay UNTYPED syntax: they denote exact untyped constants, and defaulting/representability
happen in a use context.

## Static Type Universe Arc

The type universe grows in ONE reviewed order, each root landing COMPLETE with its static facts before the
next begins: (1) integers; (2) floats; (3) complex; (4) the predeclared source aliases (`byte` = `uint8`,
`rune` = `int32`) as conversion SOURCE NAMES, then `uintptr` + exact rune constants/literals; (5) unnamed
structural types (arrays, slices, structs, pointers, function signatures, maps, channels); (6) type aliases,
defined named types, and valid recursion; (7) method signatures and method sets as type-level facts; (8)
non-generic value interfaces; (9) only THEN the operations that consume those roots. **Integers, floats, and
complex are DONE; the `byte`/`rune` source-alias RESOLUTION landed in C4 (distinct source syntax, equal
resolved `Typing.SemanticType`); `uintptr` + exact rune constants/literals are the C5 phase (which reopens ADR-0001),
pending review sign-off.**

**Types before operations.** Each root adds only STATIC facts (identity, underlying type, canonical rendering,
zero-value/nilability/comparability/map-key classification, recursive validity, assignability, constant
representability, function/method signatures + method sets). It builds NO runtime models yet
(slice/map/channel/pointer/closure/interface-dynamic), and must NEVER resurrect a fake operational value to
assert a static type exists (faithful-or-absent — a static-only type carries no runtime placeholder).

**Non-generic boundary.** This arc admits NO type parameters, generic types/aliases, constraint-only interface
semantics, instantiation/inference, or imports; the eventual `any`/`error`/ordinary-interface story belongs to
the non-generic value-interface phase, never earlier.

## Trust base (say it exactly)

Trusted: Rocq and its kernel; the digest-pinned Docker/Go images plus the opam-repo state and apt packages;
the Fido **transport boundary** (the bridge typechecks the image type and rejects an axiomatic
assumption closure — both via Rocq's own kernel/assumptions machinery — then decodes only the final
transport constructors; the sink is filesystem-only — all trusted-not-proved); and the Go toolchain
(claim (B), the `go build ./...` adequacy, is exercised differentially by the e2e, not proved). Proved (axiom-free, asserted every build in the **prove** stage by
`gate/Assumptions.v` PLUS the Rocq-native `Fido Audit Assumptions` command — a whole-certified-theory
assumption-closure audit seeded from every Fido CONSTANT, every Fido mutual INDUCTIVE (via `IndRef`), and
every surviving named assumption, that rejects every `Printer.Axiom` category (incl. assumed positivity /
guardedness / type-in-type / UIP) and `Printer.Variable` — catching an external axiom reached transitively
through any internal/opaque lemma, an unused Fido axiom, and an unreferenced assumption-bearing inductive,
with a module-coverage gate and adversarial self-tests A-E): the Integer boundary values; the Float single-round `Typing.convert_constant` boundary (F32 direct at binary32); the Complex component mapping + scalar↔complex zero-imaginary rule + the component double-round scar; ModulePath.T decidable eq + representable/
unrepresentable module-path fixtures; Version's exact "1.23" rendering; FilePath.T decidable eq +
representable/unrepresentable path fixtures; the Collections standard-map foundation (FilePath.T ordered-key law + extensionally-equal maps enumerate identically) and the Syntax duplicate-rejecting `Syntax.files_of_nodes` (sound + complete + exact + permutation-stable) + `build_program`; Index — the universal source/index exactness (`index_file_source_exact`, presence + absence), canonical root id + no metadata at a nonexistent id, sealed `FileRef`/`NodeRef` soundness + completeness + decidable key/ref identity + cross-snapshot non-interchangeability + the repeated-`println(1,1)` distinct-ref regression, total-query source-exactness, interval-jump child soundness/completeness/order + parent/child inverse + reachability + ancestry, and the indexed traversal (source-view exactness / order / NoDup), consumed by Admissible's `elaborate` as the ONE indexed whole-program pass (no peer indexed checker in Typing); Typing — the one type authority: zero-sign constant equality, `Typing.default_constant`
resolution exactness, representability reflection, expression resolution sound + complete + deterministic, statement +
program typing reflection, int max/min accepted, overflow/underflow rejected; Admissible claim (A) —
`Compilable.compile_ok_valid` + `Compilable.compile_complete` (sound + complete), the direct source reflection
`source_spec_valid_b_iff`/`Compilable.semantic_ok_b_source_program_valid`, rejection ⇒ no Compilable.Program, the compiled
evidence exposes `Typing.Program`, the empty program accepted; Property's zero-sign-agnostic fact + resolved-type
preservation (`eval_expr_resolved_type`); Render's `Render.const_info_denotes` + `Render.resolved_expr_denotes`
+ all-ASCII + decimal-faithful + no-leading-zero + the canonical float decimal round trip + header-first-line + boundaries + the exact go.mod render
(bytes / header first line / ASCII); Emit.Image's go.mod-and-.go header-first-line / ASCII / unique-paths over
EVERY image (NO nonemptiness claim — the empty program is valid). "No assumptions" is never evidence a
theorem's STATEMENT is right — the gated invariant must be the one advertised.

## What must never come back

A handwritten OCaml backend / lowering / renderer / semantic decoder, or a bridge decoding anything but the
final transport type; a SECOND program-AST hierarchy, a raw `GoPackage` tree, a copied compiled AST, or a
typed AST / `TypedIR` / copied "resolved-expression" tree beside the one raw `Syntax`; a type attached to a
raw literal, or a placeholder/unknown/opaque/raw/`Typing.StringType` type constructor added ahead of the syntax that
needs it; a second numeric-width, float-precision, complex, conversion, or type authority beside
`Integer`/`Float`/`Complex`/`Typing.convert_constant`/`Typing`; F32 rounded through F64; a complex-specific float
format or float coherence/runtime-denotation duplicated at the aggregate complex layer; a float stored as a
rounded/spec_float/decimal-string constant; package/import metadata in raw file values; `MainFile`
(package/main/entry collapsed into one raw node); raw `string` map keys; a nonemptiness restriction on the
program/image; a handwritten `go.mod` or a `go.mod` smuggled into the FilePath.T map; central
`<root>/.fido/staging/`, a central cross-device rejection, or the deleted stage-record / nonce /
local-stage-directory / record-driven-recovery subsystem; device/inode/mount-identity ownership records; a
foreign `.go`/`go.mod` preserved-and-merged into the built tree, or a nested `.fido` skipped instead of
rejected; handled-failure residue left deliberately for the next run; a checksum/manifest posing as proof that
the build succeeded; a constant-only audit that skips certified inductives or surviving named assumptions;
a `Undef`-body-only axiom check posing as a whole-theory audit; tracked axiom-bearing fixtures; `go vet` as a
blocking acceptance gate; single-file compiler semantics or a subset filter posing as compiler admissibility;
a witness-specific extracted emit executable or a hard-coded `main.go` Docker copy; a fail-open regex axiom
scanner; a no-tracked-Go seal; a `dist/` directory; handwritten Go in the canonical module; a pre-commit that
reads the unstaged working tree or auto-stages; timestamps/manifests as ownership authority; a claimed
transactional whole-directory guarantee; a `TargetConfig`; a lexer/parser/tokenizer/round-trip/text-IR/
target-IR in the certified path; fuel. Git carries the history; re-admit a feature only when the roots make
its proof obligations natural.
