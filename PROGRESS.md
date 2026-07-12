# Fido — status

The vertical slice is **proved AND executed**, over ONE program AST. `ARCHITECTURE.md` is the charter,
`PAINFUL_LESSONS.md` the postmortems, `git log` the history.

## The admitted fragment

`MainFile` (package `main` + one `func main()` — STRUCTURAL, not identifiers) whose body is `SPrintln`
statements (the builtin `println` is the statement) over primitive literals: bool (`EBool`) and integers
(`EInt` unsigned magnitude / `ENeg` its negation). Other packages, functions, callees, and strings are
UNREPRESENTABLE (no constructors) — not "rejected as invalid Go". A compiler-invalid candidate (an
out-of-range integer) is rejected IN Rocq by `go_compile`, before any bytes exist — **zero expected Go
compile failures, ever.**

## GREEN — proved axiom-free in the pinned container (13 gated `Print Assumptions` surfaces)

- **`TargetConfig`** — the one authority for pinned facts. `tc_int_bits` (64) derives exact
  `int_min`/`int_max`, consumed by `GoCompile`. `tc_go_version`/`tc_goos`/`tc_goarch` name the target the e2e
  asserts the running toolchain against.
- **`GoAST`** — the ONE tree (`MainFile`/`SPrintln`/`EBool`/`EInt`/`ENeg`). No second "compiled" tree.
- **`GoCompile`** — EXACT static admissibility as evidence over that AST: the only obligation is integer
  representability (`ExprOk`/`StmtOk`/`GoCompile`); `go_compile` proved **sound + complete + decidable**
  (`go_compile_sound`/`_complete`/`_iff`, `GoCompile_dec`). Every representable program Go accepts is
  accepted; every one rejected is a genuine constant-overflow (`-(2^63)` admitted, bare `2^63` not).
  `CompiledProgram` is a proof-bearing wrapper over the SAME `GoFile`.
- **`GoSafe`** — the exact semantics with REAL values (`GoValue = VBool | VInt Z`): `eval_expr`/`run`, and
  `eval_zero_sign_agnostic` (`EInt 0` and `ENeg 0` agree). No `Panicked`/`Outcome` placeholder — the fragment
  has no unsafe operation. `SafeProgram` is the safety certificate over `CompiledProgram`.
- **`GoRender`** — the direct renderer. `render_all_ascii` (every byte < 128); `print_Z_dec_faithful` (the
  emitted decimal denotes exactly the value, under a numeral denotation, not a parser); and
  `print_Z_pos_no_leading_zero` (no octal reinterpretation). Digits come from the one authority `digits`.
- **`GoEmit`** — the final image `emit_pairs : SafeProgram -> list (string * string)`: exactly one fixed
  file, `main.go` (`emit_is_single_main_go`); no generic path predicate.

## GREEN — executed (integration evidence, never proof)

- **Extraction boundary** (`e2e/Extract.v`): the witness `demo = certify (mkCompiled demo_ast demo_ok)`;
  `demo_pairs = emit_pairs demo`; standard extraction (`ExtrOcamlBasic` + `ExtrOcamlNativeString`) hands the
  writer an ordinary OCaml `(string*string) list`. `Print Assumptions demo_pairs` is asserted axiom-free by
  the emit stage.
- **The one tiny writer** (`e2e/writer.ml`, ~15 lines): file I/O only (staging dir + rename); walks/decodes
  no Rocq terms.
- **Pinned Go** (digest-pinned `golang:1.23-alpine`, asserted to match `TargetConfig` GOVERSION/GOOS/GOARCH):
  gofmt-clean, `go vet` + `go build`, runs the witness (bool + int + `-(2^63)` boundary + empty/multiple
  `println`); stdout/stderr/exit match reviewed goldens (`e2e/golden.*`). `make check` = gates + prove + e2e,
  green. The theory is Dune-cached; the extraction+writer+run is an explicit always-run step (not a Dune
  side-effect).

## NEXT — the frontier (pour roots before floors; do NOT add breadth for its own sake)

- Strings — return `EStr` only WITH its complete obligations at that time: an independent Go
  interpreted-string-literal denotation (every escape legal, the literal denotes exactly the payload), not
  just the printer's own inverse.
- The first construct that can actually panic or not terminate — at which point `GoSafe` grows a real
  `Panicked`/`Outcome` distinction and premises, introduced together with that constructor.
- Multi-file emission — only with a complete `GoSourceFileName` model.
- Imports remain on hold (the one change needing explicit sign-off).

## Build-trust tasks (do while the source graph is small)

Done: base + Go images digest-pinned; the opam retry loop fails closed; `dune` is the one module graph; the
always-run count-checked `gate/axiom_gate.v`; the e2e asserts the toolchain matches `TargetConfig` and the
witness is axiom-free; cached build separated from the always-run emission. Still open: pin/snapshot the opam
repo + verify installed package *versions*; move the axiom-DECLARATION scan (pre-commit-hook-only) into
`make check`; a single machine-consumed target manifest shared by Rocq + the build (today three literals —
Rocq `TargetConfig`, Makefile `PLATFORM`, Dockerfile Go image — with the e2e asserting the toolchain side).
