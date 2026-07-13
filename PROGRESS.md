# Fido — status

The vertical slice is **proved AND executed**, over ONE program representation: a nonempty verified finite
map from intrinsic `FilePath` keys to raw file ASTs. `ARCHITECTURE.md` is the charter, `PAINFUL_LESSONS.md`
the postmortems, `git log` the archive.

## The admitted fragment

Files group by directory into `package main` packages; each raw `GoFileAST` is top-level declarations (today
only `DMain` — a `func main()` declaration); statements are `SPrintln` over bool (`EBool`) and 64-bit
integers (`EInt` magnitude / `ENeg` negation). `FilePath` is a narrow canonical relative path (lowercase
dir components + a `.go` basename). Package clauses, package names, and entry-point status are compilation
RESULTS, not raw. Anything else — other decls, calls, params, imports, package clauses in raw syntax, strange
paths — is UNREPRESENTABLE. A compiler-invalid candidate (out-of-range int, zero/duplicate main in a package)
is rejected IN Rocq before any bytes — **zero expected Go build failures, ever.**

## GREEN — proved axiom-free in the pinned container (every gated `Print Assumptions` surface)

- **`FilePath`** — intrinsic canonical relative paths; decidable eq (`fp_eqb_eq`); representable/
  unrepresentable fixtures (`ok_main`/`no_dotdot`/`no_test`); `fp_parent` groups files into packages.
- **`FMap`** — key-generic finite map; THE invariant `fm_keys_nodup` (duplicate keys unrepresentable) +
  `dup_key_unrepresentable`; the DISTINCT `fm_MapsTo_fun` (deterministic first-match lookup, weaker);
  `fm_Equal` (semantic eq, distinct from record `=`); `fm_of_list` rejects duplicate keys.
- **`Ints`** — the ONE 64-bit width authority (`int_min`/`int_max`); no `uint`, no `TargetConfig`.
- **`GoAST`** — nonempty `GoProgram := fmap FilePath GoFileAST`; raw `GoDecl` (`DMain`)/`SPrintln`/`EBool`/
  `EInt`/`ENeg`; no package/entry/import metadata in raw. `MainFile` deleted.
- **`GoCompile`** — EXACT WHOLE-PROGRAM: files group by parent directory; each package has exactly one `main`
  (0 or ≥2 reject the whole program); every decl int-representable; one invalid package rejects all. `go_
  compile : GoProgram -> result CompileError CompilableProgram` sound + complete (`prog_ok_iff`); rejection
  ⇒ no `CompilableProgram` (`reject_no_compile`). Populated `CompilationFacts` (the derived package name).
- **`GoSafe`** — real values (`GoValue`), `eval_file`, `eval_zero_sign_agnostic`; `GoSafe := True` (honest
  permanent `SafeProgram` boundary).
- **`GoRender`** — direct renderer; the ROOT theorem `render_expr_denotes` (rendered spelling denotes exactly
  the value); `render_file_ascii`/`print_Z_dec_faithful`/`print_Z_pos_no_leading_zero`/`render_file_first_
  line`/boundaries. The package clause comes from `CompilationFacts`.
- **`GoEmit`** — abstract `DirectoryImage` carrying a provenance proof it came from rendering a `SafeProgram`
  (a closed proof witnesses that; a postulated axiom/variable proof does not — the live emit boundary is the
  gate, not the type); `render_program`/`directory_entries`; every image begins with the header first line,
  is ASCII, nonempty, unique paths (`render_image_keys_nodup`).

## GREEN — executed (integration evidence, never proof)

- **General `Fido Emit` transport** (`plugin/g_fido.mlg`): `Fido Emit <image> To "<root>"` is a four-step
  boundary — (1) typecheck the image type, (2) reject a non-empty assumption closure (a kernel provenance
  query descending Qed bodies), (3) decode only the final (path, bytes) transport (exact constructors,
  fail-loud), (4) call the sink. Run EXPLICITLY (`rocq c` on `e2e/Witness.v`) after the cached theory+plugin
  build — not a `.vo` side effect; no per-witness recompile. `e2e/WitnessMulti.v` emits a two-package +
  empty-file tree; `WitnessForge{,Opaque,Var,VarIndirect}.v` are the direct-axiom / opaque-Qed-axiom /
  direct- and transitive-section-variable forged images each rejected (reason-checked) before any effect.
- **The dirty-directory sink** (`plugin/fido_sink.ml`): persistent `<root>/.fido/` control dir + marker +
  git-style `index.lock`. Before any effect it validates the `root` (every ancestor must be a real dir — a
  symlink in ANY prefix component is rejected) and reserves `.fido/` (a desired path inside it is refused;
  foreign preservation is scoped OUTSIDE it). Installed `.go` is owned by its header first line (rechecked
  before overwrite/delete, lstat S_REG so symlinks are never followed). Transient staging goes
  into `.fido/staging/`, a reserved location: each target → an `O_CREAT|O_EXCL` `.fido/staging/<seq>` then
  atomic rename (the preflight rejects a cross-filesystem target). Recovery runs FIRST, recover-all-or-
  REJECT and fail-CLOSED: `staging/` must hold ONLY flat canonical regular temps — a dir/symlink/special/
  non-canonical entry is REFUSED (never traversed or deleted, so a nested tree or mount is not recursively
  removed); any readdir/lstat/removal error but a confirmed ENOENT aborts; it never scans the tree. The
  finalizer's sole obligation is releasing the lock (fail-loud once, combining body+lock errors). Fault
  seams are `unlink`/`after_stage` PARAMETERS (a real `Unix._exit` crash, a recovery-unlink failure) through
  the real algorithm — no ambient env. Honest: normal completion releases the lock (immediate rerun
  proceeds); a crash (or lock-release failure) leaves the lock and the next run refuses until it is removed.
  See `ARCHITECTURE.md` for the full contract. NOT transactional, NOT a concurrent-adversary guard.
- **Pinned Go** (`golang:1.23-alpine`): `go build ./...` over the WHOLE tree + `go vet` + gofmt-clean; the
  witness runs vs reviewed goldens (`e2e/golden.*`); representative differential fixtures — a multi-package
  tree ACCEPTED, no-main/duplicate-main trees REJECTED, and `go list ./...` matching the emitted package
  set — exercise the whole-program rules against real `go build ./...` (discovering discrepancies, not
  proving universal agreement).
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
public surfaces, for external axioms) AND the Rocq-native `Fido Audit Assumptions` global-environment audit
(over a module list derived from dune's `(modules …)`, catching unused Fido axioms, with a planted-axiom
self-test) — replacing the fail-open source-text scanner. Still open: pin/snapshot the opam repo + verify
installed package versions.
