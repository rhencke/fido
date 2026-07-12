# Fido — status

The vertical slice is **proved AND executed**, over ONE program representation: a `GoProgram` (a finite map
from relative paths to raw file ASTs). `ARCHITECTURE.md` is the charter, `PAINFUL_LESSONS.md` the postmortems,
`git log` the history.

## The admitted fragment

A `GoProgram` is `fmap RelativePath GoFileAST` — a verified finite map (unique keys by construction). Today
it holds exactly one main-package file: a `MainFile` (package `main` + one `func main()` — STRUCTURAL, not
identifiers) whose body is `SPrintln` statements (the builtin `println` is the statement) over primitive
literals: bool (`EBool`) and integers (`EInt` unsigned magnitude / `ENeg` its negation). Other packages,
functions, callees, strings, imports, and any raw `GoPackage` hierarchy are UNREPRESENTABLE — not "rejected as
invalid Go". A compiler-invalid candidate (an out-of-range integer) is rejected IN Rocq by `go_compile`,
before any bytes exist — **zero expected Go compile failures, ever.**

## GREEN — proved axiom-free in the pinned container (27 gated `Print Assumptions` surfaces)

- **`FMap`** — the one finite-map spine (`fmap A`): keys UNIQUE BY CONSTRUCTION (a `NoDup`-keys proof;
  duplicate keys unrepresentable), deterministic `fm_find`, extensional-by-lookup `fm_Equal`, no imposed
  order. `fm_MapsTo_fun`: a key never maps to two values. Shared by the program (path→file) and the image
  (path→bytes).
- **`Ints`** — the ONE 64-bit integer authority: `int_min = -2^63`, `int_max = 2^63-1`, `uint_max = 2^64-1`.
  No `TargetConfig`, no parameterization by Go release / GOOS / GOARCH / word size; the toolchain is pinned
  only operationally.
- **`GoAST`** — the ONE representation: `GoProgram := fmap GoFileAST` + raw `GoFileAST` (`MainFile`/`SPrintln`/
  `EBool`/`EInt`/`ENeg`). No second "compiled" tree, no raw `GoPackage`, no compiled facts in raw syntax.
- **`GoCompile`** — EXACT whole-PROGRAM static admissibility as evidence over that program: the only
  obligation is integer representability (`ExprOk`/`StmtOk`; `GoCompile p (facts)`). `CompilationFacts p` is
  the (empty today) home for derived static facts, never a second tree. `go_compile : GoProgram -> option
  CompilableProgram` is proof-producing and **sound + complete** (`go_compile_sound`/`_complete`), reflected
  by `prog_ok_iff`; a rejected program yields no `CompilableProgram` (`reject_no_compile`). Kernel-checked
  boundary facts: `accept_max_int`/`accept_min_int` (`-(2^63)` admitted), `reject_pos_overflow`/
  `reject_neg_overflow` (bare `2^63` not); `path_unique` (duplicate paths unrepresentable).
- **`GoSafe`** — the exact ABSTRACT println-trace semantics with REAL values (`GoValue = VBool | VInt Z`):
  `eval_expr`/`eval_file`, and `eval_zero_sign_agnostic` (`EInt 0` and `ENeg 0` agree). `GoSafe cp := True`
  TODAY (the fragment has no unsafe operation) — the honest, PERMANENT extension point for guarantees beyond
  compiler acceptance, not circular. `SafeProgram` is the capability over `CompilableProgram`.
- **`GoRender`** — the direct renderer. Every file begins with the exact header `// fido generated.  do not
  edit.` (`render_file_header`). `render_file_ascii` (every byte < 128); `print_Z_dec_faithful` (the emitted
  decimal denotes exactly the value, under a numeral denotation, not a parser); `print_Z_pos_no_leading_zero`
  (no octal reinterpretation); `render_bool/int/neg_faithful` + `render_boundary_max/min`. Digits from the one
  authority `digits`.
- **`GoEmit`** — the public capability `render_program : SafeProgram -> DirectoryImage`, where
  `DirectoryImage := fmap string` is a TRUE finite map (path→bytes). One entry per file
  (`render_program_one_file`); keys are the program's paths (`render_program_keys`); every entry has the
  header (`render_program_header`) and is ASCII (`render_program_ascii`).

## GREEN — executed (integration evidence, never proof)

- **Extraction boundary** (`e2e/Extract.v`): the witness `demo_program = fm_singleton "main.go" (MainFile
  […])`; `demo_ok : GoCompile …` by `prog_ok_iff`; `demo_safe = certify (mkCompilable …)`; `demo_image =
  render_program demo_safe`; `image_entries = fm_list demo_image`. Standard extraction (`ExtrOcamlBasic` +
  `ExtrOcamlNativeString`) hands the sink an ordinary OCaml `(string*string) list` with unique keys.
  `Print Assumptions image_entries` is asserted axiom-free by the emit stage.
- **The one filesystem sink** (`e2e/writer.ml`): a dirty-directory synchronizer — exclusive lock, staging
  INSIDE the target, per-file atomic rename, Fido-ownership by header first-line, stale-cleanup by
  header + desired-key-set, foreign files/dirs never touched. File I/O only; walks/decodes no Rocq terms.
  The emit stage exercises it against a DIRTY directory (a stale Fido file it must clean + foreign files it
  must preserve) and asserts idempotence.
- **Pinned Go** (digest-pinned `golang:1.23-alpine`, asserted to match the operational pin go1.23/linux/amd64,
  a 64-bit target): gofmt-clean, `go vet` + `go build`, runs the witness (bool + int + `-(2^63)` boundary +
  empty/multiple `println`); stdout/stderr/exit match reviewed goldens (`e2e/golden.*`). `make check` = gates
  (ocaml-origin, uncommittable-Go, axiom-scan) + prove + e2e, green. The theory is Dune-cached (one shared
  cache id); the extraction+sync+run is an explicit always-run step (not a Dune side-effect).

## NEXT — the frontier (pour roots before floors; do NOT add breadth for its own sake)

- Strings — return `EStr` only WITH its complete obligations at that time: an independent Go
  interpreted-string-literal denotation (every escape legal, the literal denotes exactly the payload), not
  just the printer's own inverse.
- The first construct that can actually panic or not terminate — at which point `GoSafe` grows a real
  `Panicked`/`Outcome` distinction and premises (and `GoSafe` stops being `True`), introduced together with
  that constructor.
- Multi-file / cross-file programs (file A imports file B, both owned) — the reason the root is a program map;
  needs a complete package/import model. Imports remain on hold (the one change needing explicit sign-off).

## Build-trust tasks (do while the source graph is small)

Done: base + Go images digest-pinned; the opam retry loop fails closed; `dune` is the one module graph; the
always-run count-checked `gate/axiom_gate.v`; the axiom-DECLARATION scan is now in `make check` AND the
pre-commit hook (one shared `tools/axiom-scan.sh` with self-tests); the e2e asserts the toolchain matches the
operational pin and the image is axiom-free; cached build separated from the always-run emission; one shared
Dune cache id. Still open: pin/snapshot the opam repo + verify installed package *versions*.
