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

## GREEN — proved axiom-free in the pinned container (33 gated `Print Assumptions` surfaces)

- **`FMap`** — the one finite-map spine (`fmap A`): THE invariant is `fm_keys_nodup` (`NoDup (fm_keys m)`) +
  `dup_key_unrepresentable` (a key-colliding list cannot satisfy the constructor obligation) — duplicate keys
  are unrepresentable; DISTINCT from `fm_MapsTo_fun` (deterministic first-match lookup). Extensional-by-lookup
  `fm_Equal`, no imposed order. Shared by the program (path→file) and the image (path→bytes).
- **`Ints`** — the ONE 64-bit width authority, only the used constants: `int_min = -2^63`, `int_max = 2^63-1`.
  No `uint` bound (no `uint` construct exists), no `TargetConfig`, no parameterization by Go release / GOOS /
  GOARCH / word size; the toolchain is pinned only operationally.
- **`GoAST`** — the ONE representation: `GoProgram := fmap GoFileAST` + raw `GoFileAST` (`MainFile`/`SPrintln`/
  `EBool`/`EInt`/`ENeg`). No second "compiled" tree, no raw `GoPackage`, no compiled facts in raw syntax.
- **`GoCompile`** — EXACT whole-PROGRAM static admissibility as evidence over that program: `GoCompile :
  GoProgram -> Prop` — the single key is the canonical build path `main.go` and every integer is
  representable (`ExprOk`/`StmtOk`). `CompilableProgram` wraps the SAME program + the proof (no facts
  record — an empty one would be scaffolding). `go_compile : GoProgram -> option CompilableProgram` is
  proof-producing and **sound + complete** (`go_compile_sound`/`_complete`), reflected by `prog_ok_iff`; a
  rejected program yields no `CompilableProgram` (`reject_no_compile`); the one compiled key is `main.go`
  (`compiled_main_go`). Kernel-checked facts: `accept_max_int`/`accept_min_int` (`-(2^63)` admitted),
  `reject_pos_overflow`/`reject_neg_overflow` (bare `2^63` not), and bad-path rejection —
  `reject_non_go_ext`/`reject_traversal_path`/`reject_absolute_path`/`reject_nested_path`/
  `reject_control_name`.
- **`GoSafe`** — the exact ABSTRACT println-trace semantics with REAL values (`GoValue = VBool | VInt Z`):
  `eval_expr`/`eval_file`, and `eval_zero_sign_agnostic` (`EInt 0` and `ENeg 0` agree). `GoSafe cp := True`
  TODAY (the fragment has no unsafe operation) — the honest, PERMANENT extension point for guarantees beyond
  compiler acceptance, not circular. `SafeProgram` is the capability over `CompilableProgram`.
- **`GoRender`** — the direct renderer. Every file begins with the exact header `// fido generated.  do not
  edit.` AS THE FIRST LINE (`render_file_first_line`: `render_file f = header ++ nl_c :: rest`).
  `render_file_ascii` (every byte < 128); `print_Z_dec_faithful` (the emitted decimal denotes exactly the
  value, numeral denotation not a parser); `print_Z_pos_no_leading_zero` (no octal reinterpretation);
  `render_bool/int/neg_faithful` + `render_boundary_max/min`. Digits from the one authority `digits`.
- **`GoEmit`** — the public capability `render_program : SafeProgram -> DirectoryImage`, where
  `DirectoryImage := fmap string` is a TRUE finite map (path→bytes). One entry keyed `main.go`
  (`render_program_main_go`); keys are the program's paths (`render_program_keys`); every entry begins with
  the header first line (`render_program_header`) and is ASCII (`render_program_ascii`).

## GREEN — executed (integration evidence, never proof)

- **Extraction boundary** (`e2e/Extract.v`): the witness `demo_program = fm_singleton "main.go" (MainFile
  […])`; `demo_ok : GoCompile demo_program` by `prog_ok_iff`; `demo_safe = certify (mkCompilable …)`;
  `demo_image = render_program demo_safe`; `emit_image = (header, fm_list demo_image)`. Standard extraction
  (`ExtrOcamlBasic` + `ExtrOcamlNativeString`) hands the sink the ownership header (the sole authority) plus
  an ordinary OCaml `(string*string) list` with unique keys. `Print Assumptions emit_image` is asserted
  axiom-free by the emit stage.
- **The one filesystem sink** (`e2e/writer.ml`): a dirty-directory synchronizer — exclusive lock, `lstat`/
  no-follow preflight (real-directory parents; refuse any non-own-header-owned target incl. dangling
  symlinks), staging INSIDE the target, per-file atomic rename, Fido-ownership by the extracted header's
  first line, stale-cleanup by header + desired-key-set. Two reserved control names
  (`.fido-staging`/`.fido-sync.lock`); foreign entries outside those never touched. File I/O only; consumes
  the Rocq header, re-declares none; walks/decodes no Rocq terms. The emit stage exercises it against a DIRTY
  directory (stale Fido file cleaned + foreign preserved, header DERIVED from output, idempotent) AND four
  adversarial foreign entries it must refuse-and-preserve (foreign at the target key, a symlinked lock, a
  dangling target symlink, a squatter at a reserved name).
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
