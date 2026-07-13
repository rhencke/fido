# Fido — status

The vertical slice is **proved AND executed**, over ONE program representation: an intrinsic `ModuleSpec`
paired with a (possibly-empty) verified finite map from intrinsic `FilePath` keys to raw file ASTs.
`ARCHITECTURE.md` is the charter, `PAINFUL_LESSONS.md` the postmortems, `git log` the archive.

## The admitted fragment

A `GoProgram` is a `ModuleSpec` (a narrow intrinsic `ModulePath` + a singleton `GoVersion` = Go1_23 — the
generated module's facts, rendered as `go.mod`; NOT a target config) plus a possibly-EMPTY map of files.
Files group by directory into `package main` packages; each raw `GoFileAST` is top-level declarations (today
only `DMain` — a `func main()` declaration); statements are `SPrintln` over bool (`EBool`) and 64-bit
integers (`EInt` magnitude / `ENeg` negation). `FilePath` is a narrow canonical relative path (lowercase
dir components + a `.go` basename); `go.mod` is a distinct root field, not a FilePath. The EMPTY file map is
a valid module-only program. Package clauses, package names, and entry-point status are compilation RESULTS,
not raw. Anything else — other decls, calls, params, imports, package clauses in raw syntax, strange paths,
invalid module paths — is UNREPRESENTABLE. A compiler-invalid candidate (out-of-range int, zero/duplicate
main in a package) is rejected IN Rocq before any bytes — **zero expected Go build failures, ever.**

## GREEN — proved axiom-free in the pinned container (every gated `Print Assumptions` surface)

- **`FilePath`** — intrinsic canonical relative paths; decidable eq (`fp_eqb_eq`); representable/
  unrepresentable fixtures (`ok_main`/`no_dotdot`/`no_test`); `fp_parent` groups files into packages.
- **`FMap`** — key-generic finite map; THE invariant `fm_keys_nodup` (duplicate keys unrepresentable) +
  `dup_key_unrepresentable`; the DISTINCT `fm_MapsTo_fun` (deterministic first-match lookup, weaker);
  `fm_Equal` (semantic eq, distinct from record `=`); `fm_of_list` rejects duplicate keys.
- **`Ints`** — the ONE 64-bit width authority (`int_min`/`int_max`); no `uint`, no `TargetConfig`.
- **`ModulePath`** — intrinsic narrow canonical module path; decidable eq (`mp_eqb_eq`); representable/
  unrepresentable fixtures (`ok_generated`/`no_dotdot`/`no_leading_slash`/`no_at`). Invalid paths
  unrepresentable.
- **`GoVersion`** — singleton `Go1_23`; `render_goversion_go1_23` pins the exact "1.23"; decidable eq.
- **`GoAST`** — `ModuleSpec` (`ModulePath` + `GoVersion`) + `GoProgram := { prog_module ; prog_files : fmap
  FilePath GoFileAST }` (the file map MAY be empty); raw `GoDecl` (`DMain`)/`SPrintln`/`EBool`/`EInt`/`ENeg`;
  no package/entry/import metadata in raw. `prog_nonempty`/`MainFile` deleted.
- **`GoCompile`** — EXACT WHOLE-PROGRAM: files group by parent directory; each package has exactly one `main`
  (0 or ≥2 reject the whole program); every decl int-representable; one invalid package rejects all. `go_
  compile : GoProgram -> result CompileError CompilableProgram` sound + complete (`prog_ok_iff`); rejection
  ⇒ no `CompilableProgram` (`reject_no_compile`). Populated `CompilationFacts` (the derived package name).
- **`GoSafe`** — real values (`GoValue`), `eval_file`, `eval_zero_sign_agnostic`; `GoSafe := True` (honest
  permanent `SafeProgram` boundary).
- **`GoRender`** — direct renderer; the ROOT theorem `render_expr_denotes` (rendered spelling denotes exactly
  the value); `render_file_ascii`/`print_Z_dec_faithful`/`print_Z_pos_no_leading_zero`/`render_file_first_
  line`/boundaries. The package clause comes from `CompilationFacts`. `render_go_mod` renders the `go.mod`
  from the `ModuleSpec` — `render_go_mod_exact` (exact bytes: module path + go version in place),
  `render_go_mod_first_line` (header), `render_go_mod_ascii`.
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
- **The foreign-Go-rejecting local-staging sink** (`plugin/fido_sink.ml`): persistent `<root>/.fido/`
  control dir + marker + git-style `index.lock` + a `stage-records/` namespace (records only, no payloads).
  Before any generated-file mutation it validates the `root` (a symlink in ANY prefix component is
  rejected), reserves `.fido/`, and REJECTS foreign Go/module inputs fail-closed (any foreign `.go`, a `.go`
  symlink/nonregular, a foreign root `go.mod`, a `go.mod` symlink, any nested `go.mod`). Installed
  `.go`/`go.mod` are owned by their header first line + regular-non-symlink (rechecked before
  overwrite/delete). Staging is LOCAL: one `<parent>/.fido-stage-<nonce>` per final parent (OS
  `/dev/urandom` nonce), each owned by a root-owned record created atomically (`O_CREAT|O_EXCL`) and
  written BEFORE its stage dir; the COMPLETE image stages before any install; per-file atomic rename
  (sibling → nested mounts OK; EXDEV fails loud, no copy). Record-driven recovery (never a name scan) is
  fail-closed: a valid record's stage is removed, a malformed/escaping/mismatched/symlinked record aborts,
  a recordless lookalike is preserved. Handled-failure cleanup is immediate + error-aggregating. Fault seams
  are `rand_hex`/`checkpoint`/`unlink` PARAMETERS (nonce collisions, real `Unix._exit` crashes at each
  staging point, unlink failures) through the real algorithm — no ambient env. Honest: normal completion
  releases the lock; a crash (or a lock-UNLINK failure) leaves the lock and the next run refuses until it is
  removed, then recovers the record-owned residue (a lock-close failure is reported but still unlinks the
  lock). See `ARCHITECTURE.md` for the full contract. NOT
  transactional, NOT a concurrent-adversary guard; Linux/amd64 operational scope.
- **Pinned Go** (`golang:1.23-alpine`, `GOWORK=off GOTOOLCHAIN=local GOPROXY=off`): `go build ./...` over
  the WHOLE tree using the RENDERED `go.mod` (no handwritten shell) + gofmt-clean, with `go vet`
  DIAGNOSTIC-only (nonblocking); the witness runs vs reviewed goldens (`e2e/golden.*`); the EMPTY module
  builds (zero packages accepted); representative differential fixtures — a multi-package tree ACCEPTED,
  no-main/duplicate-main trees REJECTED, and `go list ./...` matching the emitted package set — exercise the
  whole-program rules against real `go build ./...` (discovering discrepancies, not proving universal
  agreement).
- `make check` = host gates (transport-only OCaml, no tracked `*.go`) + prove + e2e, green. Axioms are
  checked INSIDE the pinned build (not by any host text scan). One shared Dune cache builds theory + plugin.

## NEXT — the frontier (pour roots before floors; do NOT add breadth for its own sake)

- The first construct that can panic or not terminate — `GoSafe` grows a real `Panicked`/`Outcome`
  distinction, introduced together with the constructor (`GoSafe` stops being `True`).
- Imports — needs a complete closed-world resolution model (every import resolves to an owned package in the
  same `GoProgram`, or reject the whole program). The one change needing explicit sign-off.
- Strings — `EStr` only WITH an independent Go string-literal denotation.

## Build-trust tasks

Done: base + Go images digest-pinned; the opam retry loop fails closed; one shared Dune cache builds theory +
plugin; zero project axioms enforced two ways — the count-checked `gate/axiom_gate.v` (Print Assumptions on
public surfaces, for external axioms) AND the Rocq-native `Fido Audit Assumptions` WHOLE-CERTIFIED-THEORY
assumption-closure audit (the union of every Fido constant's closure, descending opaque Qed bodies —
catching an external axiom reached transitively through any internal/opaque lemma AND unused Fido axioms),
with a coverage gate (tracked root `.v` == dune's `(modules …)`) and a planted-axiom self-test — replacing
both the fail-open source-text scanner and the weaker Undef-body-only audit. Still open: pin/snapshot the
opam repo + verify installed package versions.
