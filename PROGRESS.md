# Fido — status

Short live ledger. Binding design is in `ARCHITECTURE.md`; rules/commands in `CLAUDE.md`; expensive
mistakes in `LESSONS.md`; the Go-spec conformance table in `SPEC_CONFORMANCE.md`. History is in git — this
file shows the **current** state only.

## The goal

Be **safer than Go's compiler can prove** — type, memory, and concurrency safety lifted to compile time —
while still lowering into ordinary Go for the primitives we like (channels, goroutines, maps, slices). Go
*contains* memory errors (nil deref / OOB trap into a panic; under a race it isn't memory-safe at all); Fido
proves they cannot happen — nil deref, use-after-close, out-of-bounds, send-on-closed, failed assertion,
data race, silent overflow — ruled out before any Go is emitted. Rocq supplies the guarantees; Go supplies
the runtime. The long-term target is concurrent programs with session-typed protocol compliance, race
freedom (ownership through channel ops), and deadlock freedom (liveness), grounded in the Go memory model's
happens-before relation. Built incrementally.

**Honest claim:** this is *verified model components with a TRUSTED extraction backend* — NOT "formally
verified Go". Theorems are proved in Rocq; the `*.go` is extracted from `*.v` by the trusted plugin. No
theorem yet relates emitted Go to its source term (gap #10), and there is no behavioral-safety layer yet, so
do not headline it as "formally verified Go".

## Architecture (AST-first certified emission — `ARCHITECTURE.md` governs)

Spine: **GoAst** (structured Go syntax) → **GoPrint** (printing + expression parse round-trip / program
print-injectivity; SYNTAX only) →
**GoSafe** (`SupportedProgram` syntactic gate now; `BehaviorSafe` later, over GoSem) → **GoEmit** (the only
blessed emit; requires a certificate — `EmittableProgram` now; no raw `emit : Program -> string`).
`GoTypes` is the shared lower module (`ptype`/`svalue`, conservative supported-subset classifier) that
GoSafe consults. **GoSem** — the AST's behavioral semantics, which will BRIDGE the existing authoritative
semantics (`unified.v`/`concurrency.v`/`cmd.v`) — is **planned, not built**; it holds no authority yet and no
behavioral-safety claim is active.

The legacy **trusted plugin** (`plugin/go.ml`) still emits `main.go`; GoPrint is wired live for only the
var-OP-var binop class so far. `plugin/printer.ml` is the verified printer extracted from GoPrint.

## GREEN (proved / working)

- **Spine compiles ZERO-AXIOM** (`make emit-verify`): GoAst, GoPrint, GoTypes, GoSafe, GoEmit.
- **GoPrint round-trip** `parse_str (gprint 0 e) = Some (e, [])` + `gprint_inj`, proven at zero axioms over
  the binop/unary/atom core + every postfix form (selector / index / two-bound slice / variadic call /
  type-assertion) + the prefix type-form conversion `EConv` + slice/map composite literals + string literals
  (`EStr`, with a fail-closed, PROVEN-exact lexer: `unescape_opt_image` — accepted == emitted).
- **Program/statement layer**: `GoStmt` (expr-statement / `return` / `return e` / `_ = e`); `print_stmt_inj`
  and `print_program_inj` (distinct programs emit distinct Go); zero axioms.
- **GoSafe `SupportedProgram`** — a DECIDABLE supported-subset gate (not a package-name proxy): rejects
  bare-value statements, non-callable calls, value-returns from void `main`, free/undefined identifiers
  (only the predeclared `nil`, only inside a slice/chan conversion), and closed type-errors (`GoTypes.ptype`
  is a conservative constant-aware category checker). `classify` lives in GoAst, so GoSafe does not import
  the printer.
- **GoEmit** emits ONLY via a certificate (`EmittableProgram = Program + SupportedProgram`;
  `emit_supported = print_program`; `emit_supported_program_inj`). `make emit-demo` extracts one certified
  program and the real Go toolchain BUILDS it (gofmt-clean + go build + go vet); it is a dependency of
  `make check`.
- **Model layer** (proof-only, emits no Go): `builtins.v` (the modelled Go layer — IO/heap/channels/maps/
  slices/sessions over concrete Rocq data, zero axioms), `cmd.v` (effect evaluator), `unified.v` (the ONE
  authoritative closed-world operational semantics `ustep` — race-freedom and liveness/deadlock proved on
  it), `concurrency.v` (calculus-agnostic trace / happens-before / race / bounded-deadlock theory).
- **Whole model is axiom-free**: `Print Assumptions main_effect` = "Closed under the global context";
  `EXPECTED_ASSUMPTIONS.txt` is empty and the build fails on any drift.
- **Golden end-to-end**: `make check` extracts and diffs observable output against `expected_output.txt`.

## RED (not done — do not overclaim)

- **No GoSem / no behavioral safety.** The blessed certificate is `SupportedProgram` (SYNTACTIC
  supportedness), NOT `BehaviorSafe`. The safety properties in the goal are modelled in the proof-only
  theories but are not yet a gate on emitted programs.
- **gap #10**: the MiniML→Go plugin (`plugin/go.ml`) is trusted and unverified — no theorem relates the
  emitted Go to the source term. The golden tests are the only end-to-end check.
- **Main output is the legacy path.** `main.go` is produced by the trusted plugin, not the certificate-gated
  emitter (`emit-demo` is a separate certified demo). GoPrint drives only the var-OP-var binop class live.
- **Map literals / map conversions are QUARANTINED** from `SupportedProgram` (key-type comparability +
  assignability are not soundly structural without types); re-admit when GoSem seals a comparable-key builder.
- Latent typed-lowering residuals (e.g. an untyped higher-order `func(x any) any` lambda) remain dead today
  but unproven.

## NEXT

Build **GoSem** — the AST's behavioral semantics — by BRIDGING the existing authoritative `cmd`/`unified`/
`concurrency` models (no second semantics universe), then `BehaviorSafe` → `SafeProgram` (= EmittableProgram
+ BehaviorSafe) → `emit_safe`, and wire the certified path to the main output. In parallel, widen the live
GoPrint plugin bridge (unary / atoms / calls) and grow the `GoStmt` forms — gate-honestly, only as needed.

## Known trust base (TCB)

Rocq kernel · the string→`.go` extraction step · the Go toolchain · trusted foreign imports · the whole
trusted plugin `plugin/go.ml` (gap #10) · and (once GoSem exists) the `GoSem`≈real-Go adequacy assumption,
heir to gap #10. The MODEL's logical trust base is empty (zero axioms); the extraction plugin is the
separate, still-trusted TCB.

## Current gates

- `make check` — Docker prover stage: re-extract, run, diff vs `expected_output.txt`; plus the axiom-manifest
  gate (`Print Assumptions` vs empty `EXPECTED_ASSUMPTIONS.txt`), the fail-closed `negtests/` harness, the
  smart-ctor / dead-name / emission-discipline gate, `emit-demo` (certified bytes go-build), gofmt, and
  `go vet`.
- `make emit-verify` — local: spine compiles zero-axiom (GoAst/GoPrint/GoTypes/GoSafe/GoEmit).
- `make printer-verify` — local: GoPrint zero-axiom + `plugin/printer.ml` in sync.
- `make negtest` — local: each `negtests/*.v` ABORTS extraction at a fail-closed backend site.
- Pre-commit hook (`make install-hooks`): re-extracts + auto-stages Go, and an anti-axiom scan over every
  tracked `.v`.
