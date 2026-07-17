# Fido — status

The vertical slice is **proved AND executed**, over ONE program representation: an intrinsic `ModuleSpec`
paired with a (possibly-empty) `GoFileMap` — a STANDARD pinned-stdlib `FilePath`-keyed finite map (`FMapAVL`)
of specification-shaped source-file roots (the path is the map key).
`ARCHITECTURE.md` is the charter, `PAINFUL_LESSONS.md` the postmortems, `git log` the archive.

## The admitted fragment

A `GoProgram` is a `ModuleSpec` (a narrow intrinsic `ModulePath` + a singleton `GoVersion` = Go1_23 — the
generated module's facts, rendered as `go.mod`; NOT a target config) plus a possibly-EMPTY `GoFileMap`
(`Collections.FileMapBase.t GoSourceFile` — the pinned-stdlib `FMapAVL` over a `FilePath` ordered key).
Files group by directory into `package main` packages; each `GoSourceFile` is a source-owned package clause
(`PkgMain`), intrinsically-empty imports, and top-level declarations (today only `DMain` — a `func main()`
declaration); statements are `SPrintln` over bool (`EBool`), untyped
integers (`EInt` magnitude / `ENeg` negation), byte-sequence strings (`EString` — exact bytes, not
spelling), explicit integer conversions (`EIntConvert it e`) to any of the ten-member `IntegerType`, bare
floating literals (`EFloat d`, an intrinsic bounded-canonical finite-decimal value), explicit float
conversions (`EFloatConvert ft e`, `float32`/`float64`), semantic complex literals (`EComplex dc`, a PAIR of
`DecimalFloat` components rendered `complex(re, im)`), and explicit complex conversions (`EComplexConvert ct
e`, `complex64`/`complex128`). Each raw literal denotes an EXACT UNTYPED constant;
the ONE type authority `GoTypes` (universe `TBool` / the integer family `TInteger` / the float family
`TFloat` (F32/F64) / the complex family `TComplex` (C64/C128, components F32/F64) / `TString`) resolves it in a use context (untyped-int defaulting to `TInteger IInt`,
bare float to `TFloat F64`, bare complex to `TComplex C128` + representability, scalar↔complex by Go's
zero-imaginary rule; every string constant is representable as `TString`) — a
literal is NOT a typed value and there is no typed AST. `FilePath` is a narrow
canonical relative path (lowercase dir components + a `.go` basename); `go.mod` is a distinct root field, not
a FilePath. The EMPTY source forest is a valid module-only program. The package clause is SOURCE syntax
(`PkgMain`); package grouping, entry-point status, and TYPES are compilation/typing RESULTS, not raw.
Anything else — other decls, calls, params, non-empty imports, non-`main` packages, strange paths, invalid
module paths — is UNREPRESENTABLE. A
compiler-invalid candidate (a constant fitting no integer type, an invalid integer/float/complex conversion —
float/complex-component overflow, a fractional or out-of-range float→int, a nonzero-imaginary complex→scalar,
a wrong-type conversion — zero/duplicate main in a package)
is rejected IN Rocq before any bytes — **zero expected Go build failures, ever.**

## GREEN — proved axiom-free in the pinned container (every gated `Print Assumptions` surface)

- **`FilePath`** — intrinsic canonical relative paths; decidable eq (`fp_eqb_eq`); representable/
  unrepresentable fixtures (`ok_main`/`no_dotdot`/`no_test`); `fp_parent` groups files into packages.
- **`Collections`** — the ONE standard-collection foundation (C1A): thin wrappers over pinned-stdlib
  `FMapAVL` (`FileMapBase` over a `FilePath` ordered key, `PackageMapBase` over `String`) + `FMapPositive`
  (`NodeMapBase`) — Fido authors NO map/set. Axiom-free wrapper facts: `fp_str_inj` (the FilePath ordered-key
  law), `filemap_elements_Equal` (extensionally-equal maps enumerate to the SAME canonical `elements`). The
  project-authored `FMap.v` (an association list + `NoDup`) is DELETED.
- **`Ints`** — the ONE integer-family authority: the ten-member `IntegerType` + `integer_signed`/`_bits`/
  `_min`/`_max`/`_keyword` + `IntRepresentable`/`integer_representableb` (the per-type inclusive-range
  decision); `int`/`uint` pinned 64-bit and DISTINCT from `int64`/`uint64` (equal ranges only on this target);
  `int_min`/`int_max`/`uint_max` derived; no `TargetConfig`, no `PrimInt63`/`Sint63`.
- **`Floats`** — the ONE float-family authority (axiom-free over Stdlib `SpecFloat.spec_float` + computable
  `Z`; NO `PrimFloat`/`Prim2SF`/`SF2Prim`, NO Flocq): `FloatType` = {`F32`,`F64`} with single-sourced keyword/
  precision (24/53)/exponent bound (128/1024); exact canonical rational `FloatConst` INTRINSICALLY canonical
  (coprime `num`/`den` is a record well-formedness FIELD — `fc_canonical_intrinsic`, so a `FloatConst` is fixed
  by its num/den `fc_num_den_eq` and reflected `fc_eqb` IS Leibniz equality `fc_eqb_eq`), canonical zero,
  decidable eq; `round_float_sf` = `SFdiv prec emax` — F32 rounds DIRECTLY at binary32,
  NEVER through F64 (the double-rounding scar: `float32(2^61+2^37+1)` = 2^61+2^38 ≠ `float32(float64(…))` =
  2^61, both pinned); `round_typed_float` is the ONE float-constant construction authority (rounds once via
  `round_float_sf`; rejects overflow/NaN; underflow and signed zero normalize to +0), packaging a
  `TypedFloatConst ft` (`tfc_exact` exact rounded rational + `tfc_runtime` canonical `FloatValue` + a coherence
  proof they denote the same value + a +0-or-finite shape proof); `round_float_const`/`FloatConstRepresentable`
  are its exact-rational projections (`option_map tfc_exact`, single `round_float_sf` construction site); the
  intrinsic bounded-canonical `DecimalFloat` raw literal (`coeff`·10^`exp`, |coeff|<10^40, |exp|≤4096 from
  pinned-Go-1.23 experiments) + `decimal_value`; the proof-carrying canonical runtime `FloatValue ft` (a
  `spec_float` in the image of the format normalizer — future-compatible with finite/±0/inf/NaN) is built ONLY
  inside `round_typed_float` and reached only as `tfc_runtime`, so a constant NEVER evaluates to negative zero
  (`tfc_runtime_not_neg_zero`, incl. the bare-negative-underflow path).
- **`Complexes`** — the ONE complex authority (over `Floats`, below `GoAST`/`GoTypes`; axiom-free): `ComplexType`
  = {`C64`,`C128`} with the ONE `complex_component_type` mapping (C64→F32, C128→F64) single-sourcing all
  precision/keyword/rounding — no complex-specific format; the exact untyped `ComplexConst` (a PAIR of
  canonical-rational `FloatConst` components — no signed zero/inf/NaN/spec_float/spelling, each component's
  canonicality already living in its `FloatConst`, so no aggregate proof field); `round_typed_complex` (the ONE
  construction authority — rounds EACH component ONCE via `round_typed_float`); the intrinsic `TypedComplexConst
  ct` (a PAIR of coherent `TypedFloatConst` components `tcc_real`/`tcc_imag` — NO duplicated float coherence,
  projections `typed_complex_exact`/`typed_complex_runtime`); the general runtime `ComplexValue ct` (a PAIR of
  general `FloatValue` components — so it MAY carry -0/inf/NaN, unlike a `TypedComplexConst`); the bounded
  raw-literal `DecimalComplex`.
- **`ModulePath`** — intrinsic narrow canonical module path; decidable eq (`mp_eqb_eq`); the FIRST element
  is dotted (no stdlib-colliding dotless prefix), there is no `/vN` version-suffix tail and no `gopkg.in/`
  path (Go 1.23's two semantic-import-versioning reject classes — excluded, not admitted-then-narrowed);
  representable/unrepresentable fixtures (`ok_generated`/`no_dotless_go`/`no_ver_v1`/`no_gopkg_bare`/`no_at`).
  Invalid paths unrepresentable; `representable ⇒ Go-accepts` is exact one-way.
- **`GoVersion`** — singleton `Go1_23`; `render_goversion_go1_23` pins the exact "1.23"; decidable eq.
- **`GoAST`** — `ModuleSpec` (`ModulePath` + `GoVersion`) + `GoProgram := { prog_module ; prog_files :
  GoFileMap }` (`GoFileMap = FileMapBase.t GoSourceFile`, the standard `FMapAVL` map keyed by path, MAY be
  empty); a construction/view `GoFileNode` = `FilePath` + `GoSourceFile` (source-owned
  `PkgMain` package clause + empty imports + `source_decls`); the map API
  (`find_file`/`file_bindings`/`file_paths`/`FilesEqual`) + the duplicate-rejecting builder `filemap_of_nodes`
  (success-iff-unique / none-iff-duplicate / maps_to / mapsto_source / permutation) + `build_program`; raw `GoDecl` (`DMain`)/`SPrintln`/`EBool`/`EInt`/`ENeg`/
  `EString` (exact bytes)/`EIntConvert` (explicit integer conversion to an intrinsic `IntegerType`)/`EFloat`
  (bare `DecimalFloat` literal)/`EFloatConvert` (explicit `FloatType` conversion)/`EComplex` (a semantic
  complex literal — a `DecimalComplex`, canonical `complex(re, im)`, NOT imaginary syntax/`real`/`imag`/a
  call)/`EComplexConvert` (explicit `ComplexType` conversion); no package/entry/import/
  TYPE metadata in raw. `prog_nonempty`/`MainFile` deleted.
- **`GoTypes`** — the ONE type authority, EVIDENCE over the raw AST (no typed AST): `GoType` = {`TBool`,
  `TInteger IntegerType` (ten-member family), `TFloat FloatType` (F32/F64), `TComplex ComplexType` (C64/C128,
  components F32/F64), `TString`}; exact untyped
  `GoConst` (`CBool`/`CInt Z`/`CFloat FloatConst`/`CComplex ComplexConst`/`CString` bytes); the intrinsic dependently-typed
  `TypedConst : GoType -> Type` (`TCBool`/`TCInteger it z <proof z fits it>`/`TCFloat ft (TypedFloatConst ft)`/
  `TCComplex ct (TypedComplexConst ct)`/`TCString` — a mismatched/out-of-range typed constant UNREPRESENTABLE). The ONE target-directed conversion
  authority `convert_const : forall target, ConstInfo -> option (TypedConst target)` (int←int
  value-preserving+range-checked; int←float exact-integral+in-range; float←int/float rounds ONCE at the
  destination — a same-format float returns its `TypedFloatConst` unchanged; complex←complex/scalar rounds each
  component ONCE, scalar↔complex by Go's zero-imaginary rule; bool/string reject) drives
  `EIntConvert`, `EFloatConvert`, and `EComplexConvert`. The `ConstInfo` analyzer (`CIUntyped GoConst` | `CITyped t (TypedConst t)`;
  `EInt 0` = `ENeg 0`); the exact value of an expression is `const_info_exact` of `const_info` (no separate
  `const_value`); `resolve_const_info : ConstInfo -> option ResolvedConst` resolves a use context — an untyped
  constant DEFAULTS via `default_const` (int→`TInteger IInt`, float→`TFloat F64`, complex→`TComplex C128`), a typed constant PACKS
  unchanged (validity INTRINSIC, no `ci_ok`, no re-round); the representability decision
  `ConstRepresentable`/`const_representableb` (`const_representableb_iff`) DERIVED from successful typing
  (`type_untyped_const_at`, the ONE typing/defaulting construction over `Ints`/`Floats`, no second checker);
  reflected `ResolveExpr`/`resolve_expr` (sound + complete + deterministic) with its `ResolvedConst` witness
  (`resolve_expr_const`); `StmtTyped`/`DeclTyped`/`FileTyped`/`ProgramTyped` + `program_typedb` (exact reflection; the
  empty file/program typed vacuously). Fixtures: int + float default/convert resolve; every int type's convert
  min/max accept + ±1 reject; transitive nested conversions; ★the direct-vs-nested double-round scar analyzes
  to DIFFERENT typed constants (float AND complex-component); float→int (int(3.0) accept / int(3.5) reject);
  scalar↔complex by the zero-imaginary rule (0i as int, 42+0i as float32, 42i NOT as float32, nonzero-imaginary
  complex→scalar rejected); type identity (int≠int64,
  F32≠F64, C64≠C128); mixed + empty println typed; overflow/underflow/cross-type/non-integer/wrong-type rejected.
  Replaced the old `ExprOk`/`StmtOk`/`DeclOk`/`FileOk` family.
- **`GoCompile`** — EXACT WHOLE-PROGRAM: files group by parent directory; each package has exactly one `main`
  (0 or ≥2 reject the whole program); the whole program is TYPED through `GoTypes` (`ProgramTyped`; a typing
  failure is a constant fitting no integer type, an invalid integer/float/complex conversion — a float or
  complex-component overflow, a fractional or out-of-range float→integer, a nonzero-imaginary complex→scalar,
  a wrong-type or invalid nested conversion — reported by the honest
  `ErrTyping`); one invalid package rejects all. `go_compile :
  GoProgram -> result CompileError CompilableProgram` sound + complete (`prog_ok_iff`); rejection ⇒ no
  `CompilableProgram` (`reject_no_compile`); the empty program accepted (`prog_ok_empty`).  `GoCompile p :=
  ProgValid p` — NO `CompilationFacts`/`cf_pkg_name` (the package clause is source-owned); the compiled
  evidence EXPOSES that the same program is typed via a canonical projection (`compilable_program_typed`),
  not a stored typed copy.
- **`GoSafe`** — real values (`GoValue` = `VBool`/`VInteger IntegerType Z`/`VFloat (forall ft, FloatValue ft)`
  /`VComplex (forall ct, ComplexValue ct)`/`VString`) carrying the SAME `GoType` (`value_type`) + the `ValueWF` range invariant (`ValueWF (VFloat …)`
  = `ValueWF (VComplex …)` = True — a float/complex value is canonical BY CONSTRUCTION, the invariant living in `FloatValue`; a general runtime
  `ComplexValue` MAY carry -0/inf/NaN components, unlike a constant); PARTIAL
  `eval_expr` (`const_info` → `resolve_const_info` → `typed_const_to_value`, which PROJECTS the stored runtime —
  the float branch returns `tfc_runtime`, rounded ONCE at conversion and never re-rounded; no second evaluator
  and no total runtime→constant fallback — the honest `ValueDenotesConst` relation gives a value's exact
  constant, and a NaN/inf/−0 value has none), `eval_zero_sign_agnostic`, an integer
  conversion carries exactly its `convert_const` value, and resolved-eval well-formedness + type preservation
  (`eval_expr_resolved`); constant evaluation produces only finite/+0 (never -0/inf/NaN); `eval_file`;
  `GoSafe := True` (honest permanent `SafeProgram` boundary).
- **`GoRender`** — direct renderer; an integer conversion renders `<integer_keyword it>(<inner>)`, a float
  conversion `float32`/`float64(<inner>)`, a complex conversion `complex64`/`complex128(<inner>)`, a bare float
  through ONE canonical decimal spelling (zero →
  `0.0`; nonzero → `<signed-coeff>.0e<explicit-signed-exp>`) with an INDEPENDENT decoder proving the §27
  semantic round trip `decode_decimal (render_decimal d) = Some (decimal_value d)`, and a complex literal
  through the ONE canonical `complex(<real>, <imag>)` spelling (both components via `render_decimal`) with an
  INDEPENDENT complex decoder + semantic round trip; `render_const_info_denotes`
  (rendering denotes exactly the ConstInfo GoTypes computes — a bare integer/float/complex stays UNTYPED, a conversion
  is typed through `convert_const` — the ONE `RenderedConstInfoDenotes` root, with float and complex cases; FUNCTIONAL by
  `render_const_info_denotes_functional`, so a spelling denotes AT MOST ONE ConstInfo — the recognisers are
  pairwise disjoint (`complex(` is disjoint from `complex64(`/`complex128(` at index 7), no spelling carries two conflicting statuses) and
  `render_resolved_expr_denotes` (a resolved argument EVALUATES to a well-formed value of its resolved
  `GoType` whose spelling denotes it — tying GoTypes ↔ GoSafe ↔ GoRender); `render_file_ascii`/`print_Z_dec_faithful`/
  `print_Z_pos_no_leading_zero`/`render_file_first_line`/boundaries. The package clause is rendered from the
  file's SOURCE-owned `source_package` (`render_package_clause`, `PkgMain` → `main`). `render_go_mod` renders
  the `go.mod` from the `ModuleSpec` — `render_go_mod_exact`
  (exact bytes: module path + go version in place), `render_go_mod_first_line` (header), `render_go_mod_ascii`.
- **`GoEmit`** — `DirectoryImage` = exact `go.mod` bytes + a `.go` map, carrying a provenance proof BOTH came
  from rendering ONE `SafeProgram` (a closed proof witnesses that; a postulated axiom/variable proof does
  not — the live emit boundary is the gate, not the type); `render_program`/`di_transport`; the go.mod and
  every `.go` file begin with the header first line and are ASCII (`render_program_go_mod_header/_ascii`,
  `render_program_header/_ascii`), on-disk `.go` paths unique (`render_image_keys_nodup`). NO nonemptiness
  claim — the empty program is valid.

## GREEN — executed (integration evidence, never proof)

- **General `Fido Emit` transport** (`plugin/g_fido.mlg`): `Fido Emit <image> To "<root>"` is a four-step
  boundary — (1) typecheck the image's `di_transport`, (2) reject a non-empty assumption closure (a kernel
  provenance query descending Qed bodies — the SAME `closure_assums` the audit uses), (3) decode only the
  final `(go.mod bytes, (path, bytes) list)` transport (exact constructors, fail-loud), (4) call the sink.
  Run EXPLICITLY (`rocq c` on the witnesses) after the cached theory+plugin build — not a `.vo` side effect;
  no per-witness recompile. `e2e/Witness.v` (witness), `e2e/WitnessMulti.v` (two-package + empty-file tree),
  and `e2e/WitnessEmpty.v` (empty module — go.mod + zero `.go`) each emit their tree; `e2e/WitnessNeg.v`
  rejects a raw transport; the direct-axiom / opaque-Qed / direct- and transitive-section-variable forged
  images are GENERATED TRANSIENTLY in the emit stage (no tracked axioms) and each rejected (reason-checked)
  before any effect.
- **The foreign-Go-rejecting sibling-temp sink** (`plugin/fido_sink.ml`) — FROZEN after the ignored-directory
  classification-order correction (in the per-entry `inspect`, an opaque Go-ignored DIRECTORY tree is skipped
  BEFORE reserved-suffix/`go.mod`/`.go` classification; see `PAINFUL_LESSONS.md`), reviewed only against its
  declared practical threat model (single owner, cooperating emitters serialized by one lock, ordinary
  filesystems + crashes; NOT a malicious-concurrent-filesystem-adversary guard): persistent
  `<root>/.fido/` control dir = marker + git-style `index.lock` ONLY (no records, no nonce, no stage dir, no
  parser — the deleted subsystem). Before any generated-file mutation it validates the `root` (a symlink in
  ANY prefix component is rejected), reserves `.fido/`, and REJECTS foreign Go/module inputs + nested `.fido`
  fail-closed — over the Go-DISCOVERED namespace, SKIPPING the opaque dot/underscore/`testdata`/`vendor` trees
  `go build ./...` ignores (so it never touches `.git` or rejects because of anything beneath them). Installed
  `.go`/`go.mod` are owned by their header first line + regular-non-symlink (rechecked before overwrite/
  delete). Each output stages into its RESERVED sibling temp `<final>.fido-tmp-v1` (the lock serializes
  cooperating emitters, so no nonce/record is needed); the COMPLETE image stages before any install; per-file
  atomic rename (sibling → nested mounts OK; EXDEV fails loud, no copy). Recovery is TWO-PHASE: phase 1
  inspects that namespace once (foreign rules + collect regular reserved-suffix temps, delete nothing), phase
  2 deletes the validated temps; a symlink/dir/special reserved-suffix entry, OR one whose suffix-stripped
  path does NOT map to a Fido final path (root `go.mod` or an intrinsic `.go`), aborts + is preserved, while a
  regular MAPPED one (forgeable public convention) is removed. Handled-failure cleanup is immediate
  + error-aggregating. Fault seams are `checkpoint`/`unlink`/`rename`/`before_*` PARAMETERS (real
  `Unix._exit` crashes at writing/staged/installing, unlink failures, EXDEV) through the real algorithm — no
  ambient env. Honest: normal completion releases the lock; a crash (or a lock-UNLINK failure) leaves the
  lock + temps and the next run refuses until the stale lock is cleared, then removes the temps and
  converges; install is nontransactional across the tree. See `ARCHITECTURE.md` for the full contract. NOT
  transactional, NOT a concurrent-adversary guard; Linux/amd64 operational scope.
- **Pristine generated-module + tracked artifact**: one ordinary content-addressed Buildx `generated-module`
  layer holds exactly the canonical witness `go.mod` + recursive `.go` (no `.fido`/temp/proof/fixture),
  built from the authoritative generation inputs (never the committed bytes, never a cache mount). Root
  `go.mod` + `main.go` are TRACKED, Fido-headed derived artifacts; `make regenerate` rewrites them via the
  same `Fido_sink`. Verification is SPLIT coherently: `make check` verifies the WORKING TREE (it materializes
  the working-tree content of tracked-plus-untracked-non-gitignored files — `git ls-files --cached --others
  --exclude-standard`, so a rogue untracked `.go`/`.ml` is caught and only the gitignored `.fido`/`.vo`
  residue is excluded — and byte-compares its `go.mod` + recursive `.go` against a pristine built from the
  same working-tree inputs); the pre-commit hook verifies the proposed STAGED commit (exports
  the Git index once, runs the SAME shared compare over it, never reads the unstaged working tree or
  auto-stages) — the ONLY check that catches generated-byte drift, since `.dockerignore` hides the committed
  `go.mod`/`.go` from Buildx (pre-commit bypassable with `--no-verify`; it provides reasonable assurance for a
  cooperating developer, NOT tamper resistance — prototype policy). `tools/generated-output-gate.sh`
  (Fido-header + no-nested-go.mod policy, run over the working tree by `check` and the exported index by the
  hook) is separate; the index-authoritative exact-mode-100644 check `tools/generated-mode-gate.sh` (read from
  `git ls-files -s`, so a `core.symlinks=false` export cannot hide a symlink-mode entry) is a committed-policy
  check run ONLY in the hook. Together they replace the old no-tracked-Go seal.
- **Pinned Go** (`golang:1.23-alpine`, `GOWORK=off GOTOOLCHAIN=local GOPROXY=off`): `go build ./...` over
  the WHOLE tree using the RENDERED `go.mod` (no handwritten shell) + gofmt-clean, with `go vet`
  DIAGNOSTIC-only (nonblocking); the witness runs vs reviewed goldens (`e2e/golden.*`); the EMPTY module
  builds (zero packages accepted); representative differential fixtures — a multi-package tree ACCEPTED,
  no-main/duplicate-main trees REJECTED, and `go list ./...` matching the emitted package set — exercise the
  whole-program rules against real `go build ./...` (discovering discrepancies, not proving universal
  agreement).
- `make check` verifies the WORKING TREE = host policy gates (transport-only OCaml, no whole-repo
  historical-name scanner; the generated-output Fido-header policy gate) + prove + e2e + the working-tree
  generated-byte compare (the "no generated-byte delta" check), green. The pre-commit hook runs the same
  verification over the STAGED snapshot (plus the index-mode gate). There is NO pre-commit self-test fortress:
  the sink and hook are reviewed against their DECLARED practical threat models (single owner, cooperating
  emitters, ordinary Git commands), not a deliberate-verifier-attack model. The COMPLETE assumption audit
  (constants + inductives + named) + self-tests A-E run in **prove** (not emit). One shared Dune cache builds
  theory + plugin.

## The Static Type Universe Arc (the reviewed campaign order — types before the operations that consume them)

Complete, accurate STATIC representation of Fido's non-generic, no-import Go 1.23 type universe BEFORE the
operational foundations that consume those types, in reviewed phases: (1) integers — DONE; (2) float32/
float64 — DONE; (3) complex64/complex128 — DONE; (4) `uintptr` and predeclared aliases (`byte` = `uint8`, `rune` =
`int32`) — NEXT (pending review sign-off); (5) unnamed structural types (arrays, slices, structs, pointers, function signatures, maps,
channels); (6) type aliases and defined named types + valid recursion; (7) method signatures and method sets
as type-level facts; (8) non-generic value interfaces; (9) only THEN the operations consuming those roots.
"Types before operations" adds only STATIC facts (identity, underlying type, canonical rendering, zero-value
classification, nilability, comparability, map-key admissibility, recursive validity, assignability, constant
representability, signatures, method sets) — NOT runtime models (slice backing arrays, map heaps, channel
queues, pointer heaps, closures, interface dynamic values); never a fake operational value merely to say a
static type exists. NON-GENERIC boundary: no type parameters, generic types/aliases, constraint-only
interface semantics, instantiation/inference, or imports (the `any`/`error`/ordinary-interface story is the
non-generic interface phase).

## Source Forest campaign (ACTIVE) — spec-shaped source forest + occurrence identity + occurrence-anchored compilation

The binding multi-checkpoint plan is `.review/SOURCE_FOREST_MASTER_PLAN.md` (ledger
`.review/SOURCE_FOREST_STATUS.md`); only the ONE active checkpoint lives in `.review/NEXT_STEPS.md`, and each
checkpoint is activated only by explicit sign-off.

- **C0 / C0A / C0B — occurrence architecture (ACCEPTED by Rob; foundation frozen):** `OccurrenceSpike.v` is
  an ISOLATED, TEMPORARY, axiom-free spike (NOT wired into the certified pipeline; nothing in it is imported by
  `GoAST`/`GoTypes`/…; deleted when the production `GoIndex` lands at C2) that validates snapshot-local
  occurrence identity on a toy `file → decls → stmts → nested-exprs` grammar.  **C0** built the spike (file-local
  `positive` preorder ids, `NodeKey`, validated `NodeRef`, a SELECTED certified positive-key radix-trie
  `NodeTable` over rejected primitive-array/list candidates, a one-pass builder, and the C0.4 structural theorem
  set) + the preflight residue (three stale complex-era comments + the complex-underflow scalar-conversion
  scar).  **C0A** made references belong to the EXACT source snapshot — `SyntaxIndex fs`/`FileRef fs`/`NodeRef
  fs` indexed by `fs`, `si_outer = outer_of fs` exact index/source correspondence, TOTAL navigation (only
  `parent_of` optional), no file-list scan, sealed constructors, non-circular minting, NodeRef-level ancestry.
  **C0B** proved the EXACT per-occurrence source/metadata correspondence: an INDEPENDENT table-free
  builder-independent `source_occurrence_at` + the universal `build_file_source_exact` (the stored metadata at
  each local id is exactly the metadata of the exact source occurrence there — kind/role/parent/subtree,
  presence + absence), lifted through the sealed API as `ref_meta_matches_source` (a valid `NodeRef`'s metadata
  IS its exact source occurrence's), with the public raw-slot `index_at` removed.  Frozen decisions: immutable
  spec-shaped source forest; snapshot-indexed SyntaxIndex/FileRef/NodeRef; file-local positive preorder ids;
  abstract radix-trie `NodeTable`; parent/role/subtree-end metadata; hidden FileRef slot; public identity =
  `(FilePath, LocalNodeId)`; total navigation except `parent_of` at the root; interval-jump child enumeration;
  strict source/semantic separation.  Generated bytes UNCHANGED throughout.
- **C1 — specification-shaped file roots and path-keyed source forest (ACTIVE):** replace `map[path,
  declaration-list]` with path-bearing file roots (`GoSourceFile`/`GoFileNode`/`GoFileSet`/`GoProgram`), move
  the package clause into source syntax, one path authority, migrate the pipeline — NO occurrence index (C2),
  NO new Go feature, generated bytes byte-identical.  Later checkpoints (C2 production `GoIndex`; C3
  occurrence-anchored diagnostics; C4 source type-name syntax; C5 remaining predeclared numerics) each need
  explicit sign-off before starting.  (Proof-only source recovery is NOT a hot-path guarantee — ordinary
  compilation receives the syntax fragment and its `NodeRef` together.)

## NEXT — the frontier (pour roots before floors; do NOT add breadth for its own sake)

- Per the arc, `uintptr` + the predeclared aliases (`byte`=`uint8`, `rune`=`int32`) are the next type phase
  (needs explicit sign-off before starting, per the checkpoint protocol). (Complex LANDED: `Complexes.v` —
  `ComplexType` C64/C128 over the ONE `complex_component_type` mapping (components F32/F64); exact
  `ComplexConst` / intrinsic `TypedComplexConst` / general runtime `ComplexValue` (all PAIRS of the
  corresponding `Floats` components — a runtime value MAY carry -0/inf/NaN, a constant CANNOT);
  `TComplex`/`CComplex`/`TCComplex`/`VComplex`; `EComplex`/`EComplexConvert`; `round_typed_complex`; canonical
  `complex(re, im)` rendering + decoder; scalar↔complex by the zero-imaginary rule; the component double-round
  scar + real-Go differential; NO complex arithmetic/comparison/`real`/`imag`/general calls. Floats LANDED
  earlier — exact-rational `FloatConst`, direct single-round conversions, `TFloat`/`CFloat`, canonical
  `FloatValue`; NO float arithmetic/comparison.)
- The first construct that can panic or not terminate — `GoSafe` grows a real `Panicked`/`Outcome`
  distinction, introduced together with the constructor (`GoSafe` stops being `True`).
- Imports — needs a complete closed-world resolution model (every import resolves to an owned package in the
  same `GoProgram`, or reject the whole program). The one change needing explicit sign-off.
  (Strings LANDED: `EString`/`CString`/`VString`/`TString` — exact byte values, a canonical interpreted
  literal, and an INDEPENDENT decoder round-trip; string operations remain out of scope.)
- Integer/float/complex ARITHMETIC — operators, wrapping, division/remainder/bitwise/shifts, no-overflow
  exactness, and IEEE float operations — come AFTER the type roots (an operational-foundation milestone); NOT started.
  (Integer, float, and complex FAMILIES LANDED as static constant roots; the historical wrap/exactness/`SFadd`/`SFmul`
  proofs are the quarry for the arithmetic milestone.)

## Build-trust tasks

Done: base + Go images digest-pinned; the opam retry loop fails closed; one shared Dune cache builds theory +
plugin; zero project axioms enforced two ways, both in **prove** — the count-checked `gate/axiom_gate.v`
(Print Assumptions on public surfaces, for external axioms) AND the Rocq-native `Fido Audit Assumptions`
WHOLE-CERTIFIED-THEORY assumption-closure audit seeded from every Fido CONSTANT + every Fido mutual INDUCTIVE
(via `IndRef`) + every surviving named assumption, computing the union of their closures (descending opaque
Qed bodies) and rejecting every `Printer.Axiom` category (incl. assumed positivity/guardedness/type-in-type/
UIP) AND `Printer.Variable` — catching an external axiom reached transitively through any internal/opaque
lemma, an unused Fido axiom, AND an unreferenced assumption-bearing inductive, with a coverage gate (tracked
root `.v` == dune's `(modules …)`) and adversarial self-tests A-E — replacing the fail-open source-text
scanner, the weaker Undef-body-only audit, and the constant-only seeding. Still open: pin/snapshot the opam
repo + verify installed package versions.
