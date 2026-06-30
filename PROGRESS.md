# Fido — status

Short live ledger. Binding design is in `ARCHITECTURE.md`; rules/commands in `CLAUDE.md`; expensive
mistakes in `LESSONS.md`; the Go-spec conformance table in `SPEC_CONFORMANCE.md`. History is in git — this
file shows the **current** state only.

## The goal

The long-term aim is to be **safer than Go's compiler can prove** — lifting type, memory, and concurrency
safety to compile time — while still lowering into ordinary Go for the primitives we like (channels,
goroutines, maps, slices). Go *contains* memory errors (nil deref / OOB trap into a panic; under a race it
isn't memory-safe at all). The behavioral-safety TARGET is to PROVE these cannot happen — nil deref,
use-after-close, out-of-bounds, send-on-closed, failed assertion, data race, silent overflow — before
behaviorally safe Go is emitted, with Rocq supplying the compile-time guarantees and Go the runtime. ⚠️ TODAY
the certified-emission spine proves SUPPORTED SYNTACTIC emission ONLY; behavioral safety is NOT active yet. The long-term target is concurrent programs with
session-typed protocol compliance, race freedom (ownership through channel ops), and deadlock freedom
(liveness), grounded in the Go memory model's happens-before relation. Built incrementally.

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
GoSafe consults. **GoSem** — the AST's behavioral semantics, which BRIDGES (or retires) the existing
proof-only semantics (`unified.v`/`concurrency.v`/`cmd.v`) — is **slice-1 landed** (the `cmd.v` bridge +
real println/print/panic effect denotation + `gosem_sound`: denotation⊆`SupportedProgram`); it holds NO
behavioral-safety authority yet (slice 1 is denotation⊆gate, NOT `BehaviorSafe`).

The legacy **trusted plugin** (`plugin/go.ml`) still emits `main.go`. The extracted printer `plugin/printer.ml`
(machine-checked from GoPrint) is wired into that live path for only a SMALL expression class — a binop tree
over runtime locals, int/int64/uint64 literals, the bare int64/uint64 complement `^x`, and the runtime
conversions — narrow→int64 widening `is_i64_of_narrow_ref`, float64→float32 narrowing
`is_f64_to_f32_ref`+`operand_is_runtime`, float64→int64/uint64 truncation
`is_f64_to_i64_ref`/`is_f64_to_u64_ref`, narrow→int widening `is_int_of_fw`, numeric→float64
`is_num_to_f64_ref` over int/int64/float32/uint64, and int/int64/uint64→float32 `is_int_to_f32_ref` — and the
fixed-width ARITHMETIC `(u|i)N_add`/`sub`/`mul` (unsigned: the masked `(int(a) op int(b)) & 0xMASK`; signed:
that masked form additionally SIGN-EXTENDED; masks/sign-bits = the verified `EHex` leaf) when a bridging-binop
operand (NOT every producer of those surface bytes — e.g. the fixed-width CONVERSIONS `uint8(x)`, fw
shifts/div/mod, and standalone fw ops stay on `pp_expr`: their mask constant is the verified `print_hex`, but
the surrounding expression is trusted-assembled by `fw_wrap`); every other shape is
printed by the trusted OCaml `pp_expr`. The printer proofs cover only AST→string
serialization (`gprint`'s expression round-trip / program injectivity over the Rocq grammar) — they do NOT
cover the trusted MiniML→`GExpr` CONSTRUCTION that feeds it, and are not a Go-parser-acceptance proof; so the
live emission is not "verified Go."

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
  the printer. Composite literals admitted structurally: slice literals (elements assignable to the element
  type) and integer-key MAP literals (`map[K]V{..}` — comparable integer key, constant keys distinct +
  assignable to `K`, values assignable to `V`; Go's duplicate-constant-key error is enforced via `nodup_z`).
- **GoEmit** emits ONLY via a certificate (`EmittableProgram = Program + SupportedProgram`;
  `emit_supported = print_program`; `emit_supported_program_inj`). `make emit-demo` extracts one certified
  program and the real Go toolchain BUILDS it (gofmt-clean + go build + go vet); it is a dependency of
  `make check`.
- **GoSem slice 1 (Phase 5)** — `denote_program : Program -> option (Cmd unit)` BRIDGES the AST into `cmd.v`'s
  proven command tree (reuses `cbind`/`denote`/`run_cmd`, no second universe) with REAL effects: `println`/`print`
  → `COut` (faithful — the model's own `w_log`), `panic` → `CPan`, over a PARTIAL `eval_value` (string literals +
  supported integer/exact-float/bool CONSTANTS, the full list in NEXT; fails CLOSED elsewhere — `GTUint`/runtime/
  fractional). `gosem_sound`: denotation ⊆ `SupportedProgram`.
  `denote_program_dec`: denotability is DECIDABLE (`denote_program p <> None ↔ denotable_program p`) — scaffold
  toward an eventual `supported ⟺ denotes` (NOT proved in general; `eval` is partial). `denotable_supported`:
  denotable ⊆ supported (STRICT). The COMPLETENESS converse holds OUTRIGHT on the println-of-evaluable-args
  fragment — `println_main_denotes`/`println_main_runs`: an UNBOUNDED class (N `println(args)` + `return`, each
  arg `denotable_arg` = evaluates+printable, i.e. any string/int/float/bool constant) ALWAYS denotes AND runs.
  `denote_program_runs`: a DENOTED program runs to an Outcome (executable totality; concrete run-witnesses are
  in the trust surface). Zero axioms.
  ★ Certified public surface = `gosem_trust_surface` (the bundled tuple, gated by `Print Assumptions`); a GoSem
  theorem not in it is compiled but NOT advertised zero-axiom. ⚠ denotation⊆gate, NOT `BehaviorSafe`. Next:
  runtime/`len`/`int(x)` + fractional-float `eval` (extends the converse's reach), then `BehaviorSafe`.
- **Model layer** (proof-only, emits no Go): `builtins.v` (the modelled Go layer — IO/heap/channels/maps/
  slices/sessions over concrete Rocq data, zero axioms), `cmd.v` (effect evaluator), `unified.v` (an existing
  proof-only closed-world operational semantics `ustep` with race-freedom + liveness/deadlock proved on it —
  NOT the semantics of the certified-emission path), `concurrency.v` (calculus-agnostic trace / happens-before /
  race / bounded-deadlock theory).
- **cmd↔unified bridge (FIRST slice)** — `cmd_unified.v` + `GoSemUnified.v` (proof-only): `cmd_to_ucmd` totally
  translates cmd.v's command tree into `unified.v`'s output/panic/return/defer fragment, `COut`'s println flag
  PRESERVED (`UOut`/`uc_out` carry the bool). PUBLIC `cmd_to_ucmd_run_agrees` / `denote_program_run_agrees`: a
  DENOTED program (`no_defer` discharged) runs under `ustep` to completion AND AGREES with cmd.v's authoritative
  `run_cmd 1 c w` — unified output events EQUAL `run_cmd`'s appended `w_output`, `uc_panic 0` EQUALS the Outcome
  panic. So GoSem's denotation runs on the SAME `ustep` race-freedom/liveness hold on. Zero axioms.
  ⚠ Defer + channel/heap/spawn not yet bridged — later slices.
- **Whole model is axiom-free**: `Print Assumptions main_effect` = "Closed under the global context"; the
  manifest gate, the printer gate, and the emit gate (see **Current gates** for the exact split) each assert
  their surfaces zero-axiom via Rocq's own assumption output, `EXPECTED_ASSUMPTIONS.txt` is empty, and the
  build fails on any drift.
- **Golden end-to-end**: `make check` extracts and diffs observable output against `expected_output.txt`.

## RED (not done — do not overclaim)

- **GoSem is slice 1 only / no behavioral safety.** The blessed certificate is `SupportedProgram` (SYNTACTIC
  supportedness), NOT `BehaviorSafe`. GoSem's slice 1 (see GREEN) denotes a SUBSET of the supported programs
  and only proves denotation⊆gate — `eval_value` reaches only string literals + integer constants (excluding
  `GTUint`) + exact-integer-valued float constants + constant bools (numeric/string-literal comparisons,
  `&&`/`||`/`!`, `bool(x)`), NOT a non-literal-string comparison / runtime (`len(..)`/`int(x)`) / fractional-float
  values; there is NO `BehaviorSafe`, and no GoSem-backed gate on emission. The safety properties in the goal are modelled in
  the proof-only theories but are not yet a gate on emitted programs.
- **gap #10**: the MiniML→Go plugin (`plugin/go.ml`) is trusted and unverified — no theorem relates the
  emitted Go to the source term. The golden tests are the only end-to-end check.
- **Main output is the legacy path.** `main.go` is produced by the trusted plugin, not the certificate-gated
  emitter (`emit-demo` is a separate certified demo). GoPrint drives only the small live-bridged expression
  class enumerated once in the **Architecture** section above (the trusted plugin CONSTRUCTS those nodes; only
  the verified `gprint` PRINTS them); everything else is trusted `pp_expr`.
- **Map CONVERSIONS (`map[K]V(x)`) are QUARANTINED** from `SupportedProgram` (key-type comparability not
  soundly structural for a conversion); re-admit when GoSem/types seal a comparable-key builder. (Map
  LITERALS graduated — see GREEN: an integer-key `map[K]V{..}` with distinct, representable constant keys/values
  is now structurally supported.)
- Latent typed-lowering residuals (e.g. an untyped higher-order `func(x any) any` lambda) remain dead today
  but unproven.

## NEXT

GROW **GoSem** — slice 1 landed (the `cmd.v` bridge `denote_program` + real println/print/panic effect
denotation + `gosem_sound`: denotation⊆`SupportedProgram`, faithful to the model; `eval_value` now folds string
literals + integer constants/conversions/arithmetic + exact-integer-valued float constants + constant bools
(numeric/string-literal comparisons, `&&`/`||`/`!`, `bool(x)`)). Continue: `eval_value` for runtime values
(`len`/`int(x)`, incl. a non-literal-string comparison) and fractional floats — each WIDENS the completeness
converse (`println_main_denotes`, OUTRIGHT on evaluable-printable args) toward a GENERAL `supported ⟺ denotes`.
BRIDGE `unified.v`/`concurrency.v` (no second universe) — FIRST slice landed
(`cmd_unified.v` + `GoSemUnified.v`: `denote_program_run_agrees` already runs DENOTED programs under `ustep`
agreeing with `run_cmd`, for the defer-free fragment); next bridge slices are DEFER (cmd.v `run_defers` ↔ unified
`UDfr` LIFO) and the channel/heap/spawn effects, then LIFT SUPPORTED programs once the completeness converse +
remaining effects land. Then `BehaviorSafe` → `SafeProgram`
(= EmittableProgram + BehaviorSafe) → `emit_safe`, and wire the certified path to the main output. In parallel,
widen the live GoPrint plugin bridge (unary / atoms / calls) and grow the `GoStmt` forms — gate-honestly, only as needed.

## Known trust base (TCB)

Rocq kernel · the string→`.go` extraction step · the Go toolchain · trusted foreign imports · the whole
trusted plugin `plugin/go.ml` (gap #10) · and (once GoSem BACKS EMISSION) the `GoSem`≈real-Go adequacy assumption,
heir to gap #10. The MODEL's logical trust base is empty (zero axioms); the extraction plugin is the
separate, still-trusted TCB.

## Current gates

Zero-axiom is gated by `Print Assumptions` in THREE flows (trust-boundary ledger — single-sourced here):
**manifest** (`manifest-axioms.sh` diffs the `dune build` log's `Axioms:` vs empty `EXPECTED_ASSUMPTIONS.txt`)
covers `main_effect` / `gosem_trust_surface` / the bridge surfaces (`cmd_to_ucmd_run_agrees` /
`denote_program_run_agrees`); **printer** + **emit** (GoAst/GoPrint and GoTypes/GoSafe/GoEmit compiled STANDALONE →
grep `^Axioms:`) cover the spine. A `Print Assumptions` under none of the three is not a gated public surface.

- `make check` — Docker prover stage: re-extract, run, diff vs `expected_output.txt`; plus the three zero-axiom
  flows above, the axiom-authority self-test, the fail-closed `negtests/` harness, the smart-ctor / dead-name /
  emission-discipline / bridge-recognizer gate, `emit-demo` (certified bytes go-build), gofmt, and `go vet`.
- `make emit-verify` / `make printer-verify` — local mirrors of the emit / printer gates (spine zero-axiom +
  `plugin/printer.ml` in sync).
- `make negtest` — local: each `negtests/*.v` ABORTS extraction at a fail-closed backend site.
- Pre-commit hook (`make install-hooks`): re-extracts + auto-stages Go, and an anti-axiom DECLARATION scan over
  every tracked `.v`.
