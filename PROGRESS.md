# Fido — status

The vertical slice is **proved AND executed**, over ONE program representation: an intrinsic `ModuleSpec`
paired with a (possibly-empty) verified finite map from intrinsic `FilePath` keys to raw file ASTs.
`ARCHITECTURE.md` is the charter, `PAINFUL_LESSONS.md` the postmortems, `git log` the archive.

## The admitted fragment

A `GoProgram` is a `ModuleSpec` (a narrow intrinsic `ModulePath` + a singleton `GoVersion` = Go1_23 — the
generated module's facts, rendered as `go.mod`; NOT a target config) plus a possibly-EMPTY map of files.
Files group by directory into `package main` packages; each raw `GoFileAST` is top-level declarations (today
only `DMain` — a `func main()` declaration); statements are `SPrintln` over bool (`EBool`) and 64-bit
integers (`EInt` magnitude / `ENeg` negation). Each raw literal denotes an EXACT UNTYPED constant; the ONE
type authority `GoTypes` (universe `TBool`/`TInt`) resolves it in a use context (defaulting + 64-bit
representability) — a literal is NOT a typed value and there is no typed AST. `FilePath` is a narrow
canonical relative path (lowercase dir components + a `.go` basename); `go.mod` is a distinct root field, not
a FilePath. The EMPTY file map is a valid module-only program. Package clauses, package names, entry-point
status, and TYPES are compilation/typing RESULTS, not raw. Anything else — other decls, calls, params,
imports, package clauses in raw syntax, strange paths, invalid module paths — is UNREPRESENTABLE. A
compiler-invalid candidate (a literal outside the 64-bit range, zero/duplicate main in a package) is rejected
IN Rocq before any bytes — **zero expected Go build failures, ever.**

## GREEN — proved axiom-free in the pinned container (every gated `Print Assumptions` surface)

- **`FilePath`** — intrinsic canonical relative paths; decidable eq (`fp_eqb_eq`); representable/
  unrepresentable fixtures (`ok_main`/`no_dotdot`/`no_test`); `fp_parent` groups files into packages.
- **`FMap`** — key-generic finite map; THE invariant `fm_keys_nodup` (duplicate keys unrepresentable) +
  `dup_key_unrepresentable`; the DISTINCT `fm_MapsTo_fun` (deterministic first-match lookup, weaker);
  `fm_Equal` (semantic eq, distinct from record `=`); `fm_of_list` rejects duplicate keys.
- **`Ints`** — the ONE 64-bit width authority (`int_min`/`int_max`); no `uint`, no `TargetConfig`.
- **`ModulePath`** — intrinsic narrow canonical module path; decidable eq (`mp_eqb_eq`); the FIRST element
  is dotted (no stdlib-colliding dotless prefix), there is no `/vN` version-suffix tail and no `gopkg.in/`
  path (Go 1.23's two semantic-import-versioning reject classes — excluded, not admitted-then-narrowed);
  representable/unrepresentable fixtures (`ok_generated`/`no_dotless_go`/`no_ver_v1`/`no_gopkg_bare`/`no_at`).
  Invalid paths unrepresentable; `representable ⇒ Go-accepts` is exact one-way.
- **`GoVersion`** — singleton `Go1_23`; `render_goversion_go1_23` pins the exact "1.23"; decidable eq.
- **`GoAST`** — `ModuleSpec` (`ModulePath` + `GoVersion`) + `GoProgram := { prog_module ; prog_files : fmap
  FilePath GoFileAST }` (the file map MAY be empty); raw `GoDecl` (`DMain`)/`SPrintln`/`EBool`/`EInt`/`ENeg`;
  no package/entry/import/TYPE metadata in raw. `prog_nonempty`/`MainFile` deleted.
- **`GoTypes`** — the ONE type authority, EVIDENCE over the raw AST (no typed AST): `GoType` = {`TBool`,
  `TInt`}; exact untyped `GoConst` (`CBool`/`CInt Z`) via one `const_value` (`EInt 0` = `ENeg 0`); one
  `const_default_type`; one representability decision `ConstRepresentable`/`const_representableb` over the
  `Ints` authority (`const_representableb_iff`); reflected `ResolveExpr`/`resolve_expr` (sound + complete +
  deterministic + resolved-type-is-default); `StmtTyped`/`DeclTyped`/`FileTyped`/`ProgramTyped` +
  `program_typedb` (exact reflection; the empty file/program typed vacuously). Boundary/range fixtures: bool/
  int/max/min resolve, mixed + empty println typed, overflow/underflow/cross-type rejected. Replaced the old
  `ExprOk`/`StmtOk`/`DeclOk`/`FileOk` family.
- **`GoCompile`** — EXACT WHOLE-PROGRAM: files group by parent directory; each package has exactly one `main`
  (0 or ≥2 reject the whole program); the whole program is TYPED through `GoTypes` (`ProgramTyped`; the only
  typing failure today is a literal outside the 64-bit range); one invalid package rejects all. `go_compile :
  GoProgram -> result CompileError CompilableProgram` sound + complete (`prog_ok_iff`); rejection ⇒ no
  `CompilableProgram` (`reject_no_compile`); the empty program accepted (`prog_ok_empty`). `CompilationFacts`
  carries the derived package name and EXPOSES that the same program is typed via a canonical projection
  (`compilable_program_typed`), not a stored typed copy.
- **`GoSafe`** — real values (`GoValue`) carrying the SAME `GoType` (`value_type`); `eval_expr :=
  const_to_value ∘ const_value` (no second evaluator), `eval_zero_sign_agnostic`, and resolved-type
  preservation (`eval_expr_resolved_type`: a resolved expression evaluates to a value of its resolved type);
  `eval_file`; `GoSafe := True` (honest permanent `SafeProgram` boundary).
- **`GoRender`** — direct renderer; `render_expr_denotes` (rendered spelling denotes exactly the value) and
  `render_resolved_expr_denotes` (a resolved argument's spelling denotes the exact value AND that value has
  the resolved `GoType` — tying GoTypes ↔ GoSafe ↔ GoRender); `render_file_ascii`/`print_Z_dec_faithful`/
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
- **The foreign-Go-rejecting sibling-temp sink** (`plugin/fido_sink.ml`): persistent
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
  same `Fido_sink`; the pre-commit hook exports the Git index and verifies the STAGED tree byte-exact against
  `/generated` (bypassable with `--no-verify` — prototype policy). `tools/generated-output-gate.sh` replaces
  the old no-tracked-Go seal.
- **Pinned Go** (`golang:1.23-alpine`, `GOWORK=off GOTOOLCHAIN=local GOPROXY=off`): `go build ./...` over
  the WHOLE tree using the RENDERED `go.mod` (no handwritten shell) + gofmt-clean, with `go vet`
  DIAGNOSTIC-only (nonblocking); the witness runs vs reviewed goldens (`e2e/golden.*`); the EMPTY module
  builds (zero packages accepted); representative differential fixtures — a multi-package tree ACCEPTED,
  no-main/duplicate-main trees REJECTED, and `go list ./...` matching the emitted package set — exercise the
  whole-program rules against real `go build ./...` (discovering discrepancies, not proving universal
  agreement).
- `make check` = host gates (transport-only OCaml; the generated-output policy gate) + prove + e2e, green.
  The COMPLETE assumption audit (constants + inductives + named) + self-tests A-E run in **prove** (not
  emit). One shared Dune cache builds theory + plugin.

## NEXT — the frontier (pour roots before floors; do NOT add breadth for its own sake)

- The first construct that can panic or not terminate — `GoSafe` grows a real `Panicked`/`Outcome`
  distinction, introduced together with the constructor (`GoSafe` stops being `True`).
- Imports — needs a complete closed-world resolution model (every import resolves to an owned package in the
  same `GoProgram`, or reject the whole program). The one change needing explicit sign-off.
- Strings — `EStr` only WITH an independent Go string-literal denotation.

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
