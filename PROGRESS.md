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
  → `COut` (faithful — the model's own `w_log`), `panic` → `CPan`, over a PARTIAL `eval_value` (string literals;
  supported integer constants — literals/conversions/arith/`^x`, EXCLUDING `GTUint`; exact-integer float consts;
  constant bools via numeric/string-literal comparisons + `&&`/`||`/`!`/`bool(x)`, string order DELEGATED to the
  model's qualified `str_*`), failing CLOSED outside that slice. `gosem_sound`: denotation ⊆ `SupportedProgram`.
  `denote_program_dec`: denotability is DECIDABLE (`denote_program p <> None ↔ denotable_program p`) — scaffold
  toward an eventual `supported ⟺ denotes` (NOT proved; `eval` is partial). `denotable_supported`: denotable ⊆
  supported (STRICT). A concrete UNBOUNDED class denotes OUTRIGHT (`strlit_main_denotes`: N `println(str-lits)` +
  `return`). `denote_program_runs`: a DENOTED program runs to an Outcome (executable totality; assumes it denotes,
  NOT supported ⟹ denotes). Demos RUN `println("hi"/int64(3)/float64(3)/3<5)` through `run_cmd`. Zero axioms.
  ★ Certified public surface = `gosem_trust_surface` (the bundled tuple, gated by `Print Assumptions`); a GoSem
  theorem not in it is compiled but NOT advertised zero-axiom. ⚠ denotation⊆gate, NOT `BehaviorSafe`. Next:
  runtime/`len`/`int(x)` + fractional-float `eval`, the completeness converse, then `BehaviorSafe`.
- **Model layer** (proof-only, emits no Go): `builtins.v` (the modelled Go layer — IO/heap/channels/maps/
  slices/sessions over concrete Rocq data, zero axioms), `cmd.v` (effect evaluator), `unified.v` (an existing
  proof-only closed-world operational semantics `ustep` with race-freedom + liveness/deadlock proved on it —
  NOT the semantics of the certified-emission path), `concurrency.v` (calculus-agnostic trace / happens-before /
  race / bounded-deadlock theory).
- **cmd↔unified bridge (FIRST slice)** — `cmd_unified.v` + `GoSemUnified.v` (proof-only): `cmd_to_ucmd` totally
  translates cmd.v's command tree into `unified.v`'s output/panic/return/defer fragment — `COut`'s println flag
  PRESERVED (`unified.v`'s `UOut`/`uc_out` now carry the bool, matching the model's `w_output`, so print≠println
  is not collapsed). `cmd_to_ucmd_runs` proves EXACT OUTPUT EVENTS + EXACT PANIC + RUN-TO-DONE for the DEFER-FREE
  fragment (`cmd.no_defer`, which GoSem slice 1 denotes): running `cmd_to_ucmd c` `usteps` to completion
  (`uc_live 0 := false`), emitting EXACTLY `c`'s output events (flag+payload) into `uc_out`, ending
  `uc_panic 0 = cmd_panic c`. `GoSemUnified.denote_program_usteps` COMPOSES it with GoSem: a DENOTED program
  (`denote_program p = Some c`) runs under `ustep` (`no_defer` discharged via `denote_body_no_defer`) — GoSem's
  denotation now runs on the SAME `ustep` race-freedom/liveness are proved on. Zero axioms. ⚠ Defer
  (`run_defers` ↔ `UDfr` LIFO) + channel/heap/spawn are NOT yet bridged — later slices.
- **Whole model is axiom-free**: `Print Assumptions main_effect` = "Closed under the global context". The
  manifest gate also covers GoSem's `gosem_trust_surface` (the bundled certified GoSem results — Rocq's own
  assumption output over their whole cone, not a source-text scan); `EXPECTED_ASSUMPTIONS.txt` is empty and the
  build fails on any drift in either cone.
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
(`len`/`int(x)`, incl. a non-literal-string comparison) and fractional floats; the COMPLETENESS converse
(supported ⇒ denotes). BRIDGE `unified.v`/`concurrency.v` (no second universe) — FIRST slice landed
(`cmd_unified.v`: output-preservation for the defer-free fragment); next bridge slices are DEFER (cmd.v
`run_defers` ↔ unified `UDfr` LIFO) and the channel/heap/spawn effects, then compose with GoSem's
`denote_program` so a supported program's denotation runs under `ustep`. Then `BehaviorSafe` → `SafeProgram`
(= EmittableProgram + BehaviorSafe) → `emit_safe`, and wire the certified path to the main output. In parallel,
widen the live GoPrint plugin bridge (unary / atoms / calls) and grow the `GoStmt` forms — gate-honestly, only as needed.

## Known trust base (TCB)

Rocq kernel · the string→`.go` extraction step · the Go toolchain · trusted foreign imports · the whole
trusted plugin `plugin/go.ml` (gap #10) · and (once GoSem BACKS EMISSION) the `GoSem`≈real-Go adequacy assumption,
heir to gap #10. The MODEL's logical trust base is empty (zero axioms); the extraction plugin is the
separate, still-trusted TCB.

## Current gates

- `make check` — Docker prover stage: re-extract, run, diff vs `expected_output.txt`; plus the axiom-manifest
  gate (`Print Assumptions` vs empty `EXPECTED_ASSUMPTIONS.txt` — now captures EVERY module's `Axioms:` report,
  so it also gates GoSem's trusted-theorem surface zero-axiom via Rocq's own output), the axiom-authority
  self-test (pins that gate catches every axiom declaration form), the fail-closed `negtests/` harness, the
  smart-ctor / dead-name / emission-discipline / bridge-recognizer gate, `emit-demo` (certified bytes go-build),
  gofmt, and `go vet`.
- `make emit-verify` — local: spine compiles zero-axiom (GoAst/GoPrint/GoTypes/GoSafe/GoEmit).
- `make printer-verify` — local: GoPrint zero-axiom + `plugin/printer.ml` in sync.
- `make negtest` — local: each `negtests/*.v` ABORTS extraction at a fail-closed backend site.
- Pre-commit hook (`make install-hooks`): re-extracts + auto-stages Go, and an anti-axiom scan over every
  tracked `.v`.
