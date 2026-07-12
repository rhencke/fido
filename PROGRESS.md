# Fido — status

The first vertical slice is **proved AND executed**. `ARCHITECTURE.md` is the charter, `PAINFUL_LESSONS.md`
the postmortems, `git log` the history. This is the live frontier only.

## The admitted fragment

`package main` + one `func main()` + straight-line builtin `println` over primitive literals: bool /
string (printable-ASCII + tab/newline charset) / int (unsigned magnitude; negatives ONLY as `ENeg`, unary
minus over a magnitude). Imports, user functions, variables, and control flow are UNREPRESENTABLE (no
constructors). A compiler-invalid candidate is rejected IN Rocq by `go_compile` before any `.go` exists —
**zero expected Go compile failures, ever.**

## GREEN — proved axiom-free in the pinned container (17 gated `Print Assumptions` surfaces)

- **`TargetConfig`** — the one authority for pinned target facts. `tc_int_bits` (64) derives exact
  `int_min`/`int_max`; `tc_println_builtin` is a required premise of GoCompile's `println` rule. `tc_goos`/
  `tc_goarch`/`tc_go_version` name the target the e2e goldens are facts about (checked by the e2e, not a
  proof).
- **`Literals`** — the admitted string-payload charset (`str_ok`); integer representability lives
  intrinsically on the compiled constructors, not here.
- **`GoIdent`** — validated Go identifiers (`sig` type; keyword/empty/ill-formed unrepresentable);
  `goident_payload_eq` (equality reduces to the payload) is what erasure uses.
- **`GoAST`** — the one raw proposed tree (`EIdent`/`EInt N`/`ENeg N`/`EStr`; `SCall`; func; file). May be
  compiler-invalid; carries no unsupported syntax and no parenthesis node.
- **`GoCompile`** — the authority. A decorated `CompiledFile` (`EIdent`→`CBool`, callee→the `CPrintln`
  builtin, `CInt`/`CNeg` carry intrinsic representability, pkg/fn are the pinned `main` constants); the
  declarative `CompilesFile` relation; the executable `go_compile` proved **sound + complete + deterministic**
  (`go_compile_sound`/`_complete`/`_iff`, `CompilesFile_det`) and **erasing back to the raw tree**
  (`compiled_erases_to_raw`); `GoCompile` decidable. Never a boolean. Adequacy to the REAL Go compiler is the
  e2e's job, not a theorem.
- **`GoSafe`** — an operational semantics (`Outcome = Returned | Panicked`, a `println`-event trace,
  `eval_file`) and the universal floor `BehaviorSafe` (the run does not panic), proved for the whole
  fragment (`fragment_never_panics`; no panic source exists — it gains real premises when one arrives).
  `SafeProgram` ties raw ↔ compiled ↔ safe (`sp_erases` proves faithfulness).
- **`GoRender`** — the direct `CompiledFile → string` printer. `escape_faithful` (Go string escaping is
  invertible — the emitted literal denotes exactly the value) and `render_all_ascii` (every emitted byte
  < 128), both structural over the intrinsically-grammatical tree — no parser.
- **`GoEmit`** — the Rocq-defined `DirectoryImage`; `emit_directory` accepts `SafeProgram`; every path proved
  relative / separator-&-NUL-free / not `.`/`..` / `.go` / unique.

## GREEN — executed (integration evidence, never proof)

- **`Fido Emit` transport plugin** (`plugin/g_fido.mlg`, the one tiny handwritten glue): reduces
  `emit_directory demo` in Rocq, structurally decodes the `DirectoryImage`, writes files atomically.
- **e2e witness** (`plugin/Witness.v`): `demo = certify` of a `CompilesFile` proof for `println(true)`;
  emits exactly the proved `main.go`. The pinned `golang:1.23-alpine` (digest-pinned) confirms it is
  gofmt-clean, passes `go vet` + `go build`, runs, and produces `stderr "true\n"` / empty stdout / exit 0 —
  byte-for-byte against reviewed goldens (`e2e/golden.*`). `make check` = gates + prove + e2e, green.

## NEXT — the frontier (pour roots before floors; do NOT add breadth for its own sake)

- More primitive witnesses (multiple/mixed `println` args: strings with each escape, ints incl.
  `0`/`1`/`-1`/`-(2^63)`, bools) with their compile+safety proofs and goldens.
- Stronger renderer obligations where they buy correctness: an independent forward Go-subset
  grammar-membership (structural, never a parser) and a decimal-value faithfulness theorem.
- The first construct that can actually panic or not terminate — at which point `GoSafe.BehaviorSafe` stops
  being free and must be proved with real premises, and the semantics gains a `Panicked` branch.
- Imports remain on hold (the one change needing explicit sign-off).

## Build-trust tasks (do while the source graph is small)

Done: base + Go images digest-pinned; the opam retry loop fails closed; `dune` is the one module graph; the
always-run count-checked `gate/axiom_gate.v` is the sole axiom-gate target; the e2e emits + runs through the
pinned Go toolchain. Still open: pin/snapshot the opam repo + verify installed package *versions*; move the
axiom-DECLARATION scan (currently pre-commit-hook-only, so `--no-verify`-bypassable and absent in CI) into
`make check`.
