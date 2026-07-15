# Fido — status

The vertical slice is **proved AND executed**, over ONE program representation: an intrinsic `ModuleSpec`
paired with a (possibly-empty) verified finite map from intrinsic `FilePath` keys to raw file ASTs.
`ARCHITECTURE.md` is the charter, `PAINFUL_LESSONS.md` the postmortems, `git log` the archive.

## The admitted fragment

A `GoProgram` is a `ModuleSpec` (a narrow intrinsic `ModulePath` + a singleton `GoVersion` = Go1_23 — the
generated module's facts, rendered as `go.mod`; NOT a target config) plus a possibly-EMPTY map of files.
Files group by directory into `package main` packages; each raw `GoFileAST` is top-level declarations (today
only `DMain` — a `func main()` declaration); statements are `SPrintln` over bool (`EBool`), untyped
integers (`EInt` magnitude / `ENeg` negation), byte-sequence strings (`EString` — exact bytes, not
spelling), explicit integer conversions (`EIntConvert it e`) to any of the ten-member `IntegerType`, bare
floating literals (`EFloat d`, an intrinsic bounded-canonical finite-decimal value), and explicit float
conversions (`EFloatConvert ft e`, `float32`/`float64`). Each raw literal denotes an EXACT UNTYPED constant;
the ONE type authority `GoTypes` (universe `TBool` / the integer family `TInteger` / the float family
`TFloat` (F32/F64) / `TString`) resolves it in a use context (untyped-int defaulting to `TInteger IInt`,
bare float to `TFloat F64` + representability; every string constant is representable as `TString`) — a
literal is NOT a typed value and there is no typed AST. `FilePath` is a narrow
canonical relative path (lowercase dir components + a `.go` basename); `go.mod` is a distinct root field, not
a FilePath. The EMPTY file map is a valid module-only program. Package clauses, package names, entry-point
status, and TYPES are compilation/typing RESULTS, not raw. Anything else — other decls, calls, params,
imports, package clauses in raw syntax, strange paths, invalid module paths — is UNREPRESENTABLE. A
compiler-invalid candidate (a constant fitting no integer type, an invalid integer/float conversion — float
overflow, a fractional or out-of-range float→int, a wrong-type conversion — zero/duplicate main in a package)
is rejected IN Rocq before any bytes — **zero expected Go build failures, ever.**

## GREEN — proved axiom-free in the pinned container (every gated `Print Assumptions` surface)

- **`FilePath`** — intrinsic canonical relative paths; decidable eq (`fp_eqb_eq`); representable/
  unrepresentable fixtures (`ok_main`/`no_dotdot`/`no_test`); `fp_parent` groups files into packages.
- **`FMap`** — key-generic finite map; THE invariant `fm_keys_nodup` (duplicate keys unrepresentable) +
  `dup_key_unrepresentable`; the DISTINCT `fm_MapsTo_fun` (deterministic first-match lookup, weaker);
  `fm_Equal` (semantic eq, distinct from record `=`); `fm_of_list` rejects duplicate keys.
- **`Ints`** — the ONE integer-family authority: the ten-member `IntegerType` + `integer_signed`/`_bits`/
  `_min`/`_max`/`_keyword` + `IntRepresentable`/`integer_representableb` (the per-type inclusive-range
  decision); `int`/`uint` pinned 64-bit and DISTINCT from `int64`/`uint64` (equal ranges only on this target);
  `int_min`/`int_max`/`uint_max` derived; no `TargetConfig`, no `PrimInt63`/`Sint63`.
- **`Floats`** — the ONE float-family authority (axiom-free over Stdlib `SpecFloat.spec_float` + computable
  `Z`; NO `PrimFloat`/`Prim2SF`/`SF2Prim`, NO Flocq): `FloatType` = {`F32`,`F64`} with single-sourced keyword/
  precision (24/53)/exponent bound (128/1024); exact canonical rational `FloatConst` (coprime `num`/`den`,
  canonical zero, decidable eq); `round_float_sf` = `SFdiv prec emax` — F32 rounds DIRECTLY at binary32,
  NEVER through F64 (the double-rounding scar: `float32(2^61+2^37+1)` = 2^61+2^38 ≠ `float32(float64(…))` =
  2^61, both pinned); `round_float_const`/`FloatConstRepresentable` (round once at destination — reject
  overflow, underflow → +0, never NaN); the intrinsic bounded-canonical `DecimalFloat` raw literal
  (`coeff`·10^`exp`, |coeff|<10^40, |exp|≤4096 from pinned-Go-1.23 experiments) + `decimal_value`; the
  proof-carrying canonical runtime `FloatValue ft` (a `spec_float` in the image of the format normalizer —
  future-compatible with finite/±0/inf/NaN).
- **`ModulePath`** — intrinsic narrow canonical module path; decidable eq (`mp_eqb_eq`); the FIRST element
  is dotted (no stdlib-colliding dotless prefix), there is no `/vN` version-suffix tail and no `gopkg.in/`
  path (Go 1.23's two semantic-import-versioning reject classes — excluded, not admitted-then-narrowed);
  representable/unrepresentable fixtures (`ok_generated`/`no_dotless_go`/`no_ver_v1`/`no_gopkg_bare`/`no_at`).
  Invalid paths unrepresentable; `representable ⇒ Go-accepts` is exact one-way.
- **`GoVersion`** — singleton `Go1_23`; `render_goversion_go1_23` pins the exact "1.23"; decidable eq.
- **`GoAST`** — `ModuleSpec` (`ModulePath` + `GoVersion`) + `GoProgram := { prog_module ; prog_files : fmap
  FilePath GoFileAST }` (the file map MAY be empty); raw `GoDecl` (`DMain`)/`SPrintln`/`EBool`/`EInt`/`ENeg`/
  `EString` (exact bytes)/`EIntConvert` (explicit integer conversion to an intrinsic `IntegerType`)/`EFloat`
  (bare `DecimalFloat` literal)/`EFloatConvert` (explicit `FloatType` conversion); no package/entry/import/
  TYPE metadata in raw. `prog_nonempty`/`MainFile` deleted.
- **`GoTypes`** — the ONE type authority, EVIDENCE over the raw AST (no typed AST): `GoType` = {`TBool`,
  `TInteger IntegerType` (ten-member family), `TFloat FloatType` (F32/F64), `TString`}; exact untyped
  `GoConst` (`CBool`/`CInt Z`/`CFloat FloatConst`/`CString` bytes). The ONE target-directed conversion
  authority `convert_const : GoType -> GoConst -> option GoConst` (int←int value-preserving+range-checked;
  int←float exact-integral+in-range; float←int/float rounds ONCE at the destination; bool/string reject)
  drives both `EIntConvert` and `EFloatConvert`. `const_value` is now PARTIAL (`option GoConst`): a bare
  literal is exact (`EInt 0` = `ENeg 0`; a bare float is its exact rational, unrounded), a conversion routes
  through `convert_const` (integer conversions preserve the value, FLOAT conversions round once). The
  `ConstInfo` analyzer (untyped vs typed constants); one `const_default_type` (int→`TInteger IInt`,
  float→`TFloat F64`); the representability decision `ConstRepresentable`/`const_representableb`
  (`const_representableb_iff`, over the `Ints`/`Floats` authorities); reflected `ResolveExpr`/`resolve_expr`
  (sound + complete + deterministic) — representability is checked for an UNTYPED (defaulted) constant and
  TRUSTED for a TYPED constant (already validated by `convert_const`; a `ci_ok` premise, not a redundant
  re-round); `StmtTyped`/`DeclTyped`/`FileTyped`/`ProgramTyped` + `program_typedb` (exact reflection; the
  empty file/program typed vacuously). Fixtures: int + float default/convert resolve; every int type's convert
  min/max accept + ±1 reject; transitive nested conversions; ★the direct-vs-nested double-round scar analyzes
  to DIFFERENT typed constants; float→int (int(3.0) accept / int(3.5) reject); type identity (int≠int64,
  F32≠F64); mixed + empty println typed; overflow/underflow/cross-type/non-integer/wrong-type rejected.
  Replaced the old `ExprOk`/`StmtOk`/`DeclOk`/`FileOk` family.
- **`GoCompile`** — EXACT WHOLE-PROGRAM: files group by parent directory; each package has exactly one `main`
  (0 or ≥2 reject the whole program); the whole program is TYPED through `GoTypes` (`ProgramTyped`; a typing
  failure is a constant fitting no integer type, an invalid integer/float conversion — a float overflow, a
  fractional or out-of-range float→integer, a wrong-type or invalid nested conversion — reported by the honest
  `ErrTyping`); one invalid package rejects all. `go_compile :
  GoProgram -> result CompileError CompilableProgram` sound + complete (`prog_ok_iff`); rejection ⇒ no
  `CompilableProgram` (`reject_no_compile`); the empty program accepted (`prog_ok_empty`). `CompilationFacts`
  carries the derived package name and EXPOSES that the same program is typed via a canonical projection
  (`compilable_program_typed`), not a stored typed copy.
- **`GoSafe`** — real values (`GoValue` = `VBool`/`VInteger IntegerType Z`/`VFloat (forall ft, FloatValue ft)`
  /`VString`) carrying the SAME `GoType` (`value_type`) + the `ValueWF` range invariant (`ValueWF (VFloat …)`
  = True — a float value is canonical BY CONSTRUCTION, the invariant living in `FloatValue`); PARTIAL
  `eval_expr` DERIVED from `const_info` (no second evaluator; `const_to_value` rounds a float constant ONCE
  into a canonical `FloatValue`, and trusts a typed constant), `eval_zero_sign_agnostic`, an integer
  conversion carries exactly its `convert_const` value, and resolved-eval well-formedness + type preservation
  (`eval_expr_resolved`); constant evaluation produces only finite/+0 (never -0/inf/NaN); `eval_file`;
  `GoSafe := True` (honest permanent `SafeProgram` boundary).
- **`GoRender`** — direct renderer; an integer conversion renders `<integer_keyword it>(<inner>)`, a float
  conversion `float32`/`float64(<inner>)`, and a bare float through ONE canonical decimal spelling (zero →
  `0.0`; nonzero → `<signed-coeff>.0e<explicit-signed-exp>`) with an INDEPENDENT decoder proving the §27
  semantic round trip `decode_decimal (render_decimal d) = Some (decimal_value d)`; `render_const_info_denotes`
  (rendering denotes exactly the ConstInfo GoTypes computes — a bare integer/float stays UNTYPED, a conversion
  is typed through `convert_const` — the ONE `RenderedConstInfoDenotes` root, with float cases) and
  `render_resolved_expr_denotes` (a resolved argument EVALUATES to a well-formed value of its resolved
  `GoType` whose spelling denotes it — tying GoTypes ↔ GoSafe ↔ GoRender); `render_file_ascii`/`print_Z_dec_faithful`/
  `print_Z_pos_no_leading_zero`/`render_file_first_line`/boundaries. The package clause comes from
  `CompilationFacts`. `render_go_mod` renders the `go.mod` from the `ModuleSpec` — `render_go_mod_exact`
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
float64 — DONE; (3) complex64/complex128; (4) `uintptr` and predeclared aliases (`byte` = `uint8`, `rune` =
`int32`); (5) unnamed structural types (arrays, slices, structs, pointers, function signatures, maps,
channels); (6) type aliases and defined named types + valid recursion; (7) method signatures and method sets
as type-level facts; (8) non-generic value interfaces; (9) only THEN the operations consuming those roots.
"Types before operations" adds only STATIC facts (identity, underlying type, canonical rendering, zero-value
classification, nilability, comparability, map-key admissibility, recursive validity, assignability, constant
representability, signatures, method sets) — NOT runtime models (slice backing arrays, map heaps, channel
queues, pointer heaps, closures, interface dynamic values); never a fake operational value merely to say a
static type exists. NON-GENERIC boundary: no type parameters, generic types/aliases, constraint-only
interface semantics, instantiation/inference, or imports (the `any`/`error`/ordinary-interface story is the
non-generic interface phase).

## NEXT — the frontier (pour roots before floors; do NOT add breadth for its own sake)

- Per the arc, `complex64`/`complex128` constants are the next type phase (needs explicit sign-off before
  starting, per the checkpoint protocol). (Floats LANDED: `Floats.v` — `FloatType`, exact-rational
  `FloatConst`, direct single-round `SpecFloat` conversions, `DecimalFloat`, the one `convert_const`, `TFloat`/
  `CFloat`, canonical `FloatValue`, canonical decimal rendering + decoder, the double-round scar + real-Go
  differential; NO float arithmetic/comparison/complex.)
- The first construct that can panic or not terminate — `GoSafe` grows a real `Panicked`/`Outcome`
  distinction, introduced together with the constructor (`GoSafe` stops being `True`).
- Imports — needs a complete closed-world resolution model (every import resolves to an owned package in the
  same `GoProgram`, or reject the whole program). The one change needing explicit sign-off.
  (Strings LANDED: `EString`/`CString`/`VString`/`TString` — exact byte values, a canonical interpreted
  literal, and an INDEPENDENT decoder round-trip; string operations remain out of scope.)
- Integer/float ARITHMETIC — operators, wrapping, division/remainder/bitwise/shifts, no-overflow exactness,
  and IEEE float operations — come AFTER the type roots (an operational-foundation milestone); NOT started.
  (Integer + float FAMILIES LANDED as static constant roots; the historical wrap/exactness/`SFadd`/`SFmul`
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
