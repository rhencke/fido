# Fido — status

Short live ledger. Design: `ARCHITECTURE.md`; rules: `CLAUDE.md`; mistakes: `LESSONS.md`; Go-spec table:
`SPEC_CONFORMANCE.md`. History is in git — this file is the **current** state only.

## The goal

Be **safer than Go's compiler can prove** — lift type/memory/concurrency safety to compile time — while still
lowering into ordinary Go (channels, goroutines, maps, slices). The behavioral-safety TARGET: PROVE, before
emitting, that nil deref / use-after-close / out-of-bounds / send-on-closed / failed assertion / data race /
silent overflow cannot happen. Long-term: concurrent programs with session-typed protocol compliance, race
freedom, and deadlock freedom over the Go memory model's happens-before. Built incrementally. ⚠️ TODAY the
spine gates SUPPORTED SYNTACTIC emission ONLY; behavioral safety is NOT active.

**Honest claim:** *verified model components with a TRUSTED extraction backend* — NOT "formally verified Go."
Theorems are proved in Rocq; `*.go` is extracted from `*.v` by the trusted plugin. No theorem relates emitted
Go to its source term (gap #10), and there is no behavioral-safety emission gate (only proof-only properties).

## Architecture (AST-first certified emission — `ARCHITECTURE.md` governs)

Spine: **GoAst** (structured syntax) → **GoPrint** (printing + expression round-trip / program injectivity;
SYNTAX only) → **GoSafe** (`SupportedProgram` syntactic gate now; `BehaviorSafe` later) → **GoEmit** (the only
blessed emit; needs a certificate — `EmittableProgram`; no raw `emit`). `GoTypes` is the shared classifier
(`ptype`/`svalue`) GoSafe consults. **GoSem** bridges the AST's behavior into the existing proof-only
semantics (`cmd.v`/`unified.v`/`concurrency.v`); slice 1 only (below).

**Live plugin bridge:** the legacy trusted plugin (`plugin/go.ml`) still emits `main.go`; the extracted
`plugin/printer.ml` (from GoPrint) prints a SMALL expression class on that live path — a binop tree over
runtime locals, int/int64/uint64 literals, the bare `^x` complement, a runtime local's plain field selector
`local.Field` (`is_record_proj`, NOT an embedded field nor a defined-type value projection, and only a local
receiver — the one shape where `gprint` matches the trusted `pp_expr`'s peel/atom rendering, pinned by the
selector-bridge gate), the runtime numeric
conversions, and fixed-width `(u|i)N_add`/`sub`/`mul` as a bridging-binop operand. Every other shape stays on
trusted `pp_expr`. The trusted plugin CONSTRUCTS the `GExpr` (choice of AST); only the verified `gprint`
PRINTS it — the proofs cover AST→string serialization, NOT the MiniML→`GExpr` construction, and are not a
Go-parser acceptance. So the live emission is NOT "verified Go."

## GREEN (proved / working)

- **Spine ZERO-AXIOM** (`make emit-verify`): GoAst / GoPrint / GoTypes / GoSafe / GoEmit.
- **GoPrint round-trip** `parse_str (gprint 0 e) = Some (e, [])` + `gprint_inj`, zero axioms, over the
  binop/unary/atom core + every postfix form (selector / index / two-bound slice / variadic call /
  type-assertion) + the prefix conversion `EConv` + slice/map composite literals + string literals
  (`EStr`, fail-closed exact lexer `unescape_opt_image` — accepted == emitted).
- **Program/statement layer:** `GoStmt` (expr-stmt / `return` / `return e` / `_ = e` / `defer <call>`);
  `print_stmt_inj` (5-ctor/25-case) + `print_program_inj` (distinct programs emit distinct Go); zero axioms.
  `GsDefer` is syntactically supported + emittable (gated to a call via `expr_stmt_ok`), but GoSem does NOT
  denote it yet (its `CDfr` denotation needs `run_cmd` fuel > 1 — see GoSem slice-1 below).
- **GoSafe `SupportedProgram`** — a DECIDABLE supported-subset gate (not a package-name proxy): rejects
  bare-value statements, non-callable calls, value-returns from void `main`, free/undefined identifiers, and
  closed type-errors (`ptype`, a conservative constant-aware classifier). Admits slice literals + integer-key
  map literals structurally (`nodup_z` enforces distinct constant keys). `classify` lives in GoAst, so GoSafe
  does not import the printer.
- **GoEmit** emits ONLY via a certificate (`EmittableProgram = Program + SupportedProgram`;
  `emit_supported = print_program`; `emit_supported_program_inj`). `make emit-demo` builds one certified
  program with the real Go toolchain (gofmt-clean + go build + go vet); a dependency of `make check`.
- **GoSem slice 1** — `denote_program : Program -> option (Cmd unit)` bridges the AST into `cmd.v`'s command
  tree (reuses `cbind`/`run_cmd`, no second universe): print/println → `COut` (the model's own `w_log`),
  panic → `CPan`, `return`, and blank constant-assignment, over a PARTIAL `eval_value` (string / integer /
  exact-float / bool CONSTANTS incl. in-range `uint`; fails CLOSED on runtime / fractional / out-of-range —
  exact coverage in `GoSem.v`). Proves denotation ⊆ `SupportedProgram` and that denoted programs run through
  `cmd.v`. Certified public surface = `gosem_trust_surface` + `gosem_string_authority_surface` (the string
  comparators ARE the model's `str_*`); a GoSem fact in neither tuple is an internal helper / example, not
  certified. NO `BehaviorSafe`. Zero axioms.
- **Model layer** (proof-only): `builtins.v` (the Go layer over concrete Rocq data), `cmd.v` (effect
  evaluator), `unified.v` (`ustep` operational semantics with race-freedom + liveness/deadlock proved on it —
  NOT the emission path), `concurrency.v` (trace / happens-before / race / bounded-deadlock theory).
- **cmd↔unified bridge** — `cmd_unified.v` + `GoSemUnified.v` (proof-only): `cmd_to_ucmd` translates cmd.v's
  tree into `unified.v`'s output/panic/return/defer fragment (println flag preserved). `cmd_to_ucmd_run_agrees`
  / `denote_program_run_agrees`: a denoted program runs under `ustep` and AGREES with `run_cmd`. Defer bridged by
  the single general `bridge_agrees`: for ANY `c` (arbitrary defer nesting, ANY panics) the `ustep` run agrees
  with `run_cmd` — finishes, panic EQUALS the Outcome's, output EQUALS `run_cmd`'s appended `w_output` (unwinds
  the LIFO defer forest under the `(prog, pa)` 2-mode, threading the last-raised panic). Supporting cmd.v-side
  properties for ANY `c`: `run_cmd_terminates` (returns `Some` for enough fuel, via a `defers_sz` measure) +
  `run_cmd_out_monotone` (a completing run's output only APPENDS) + `run_cmd_no_panic_ret` (a completing
  panic-free run returns `ORet`). ⚠ chan/heap/spawn later. Zero axioms.
- **First behavioral-safety PROPERTIES** — `GoSemSafe.v`: `panic_free_runs_ret` (a panic-free denoted program
  runs to `ORet`, never panics) + `panic_free_runs_ret_ustep` (same, lifted to `ustep`, where race-freedom /
  liveness live). `panic_free_denotable` folds "denotes + panic-free" into ONE DECIDABLE predicate on the raw
  `Program` (the gate SHAPE, computable without a denotation handed in); `panic_free_denotable_runs_ret`[`_ustep`]
  prove it entails the safe run. SEED of `BehaviorSafe`; ⚠ NOT a gate (name stays specific, not `safe`). Zero axioms.
- **Whole model axiom-free**: `Print Assumptions main_effect` = "Closed under the global context"; the three
  gates (below) assert their surfaces zero-axiom and fail the build on drift (`EXPECTED_ASSUMPTIONS.txt` empty).
- **Golden end-to-end**: `make check` diffs observable output against `expected_output.txt`.

## RED (not done — do not overclaim)

- **GoSem slice 1 only / no behavioral safety.** The blessed certificate is `SupportedProgram` (SYNTACTIC),
  NOT `BehaviorSafe`; slice 1 denotes a SUBSET of supported programs and proves denotation⊆gate. No
  `BehaviorSafe` gate, no GoSem-backed emission gate (`panic_free_runs_ret*` are proved but are NOT gates).
- **gap #10:** the MiniML→Go plugin is trusted/unverified — no theorem relates emitted Go to the source term;
  golden tests are the only end-to-end check.
- **Main output is the legacy path:** `main.go` comes from the trusted plugin, not the certificate-gated
  emitter (`emit-demo` is a separate certified demo). GoPrint drives only the small live-bridged class above
  (construct trusted, print verified).
- **Map CONVERSIONS `map[K]V(x)` QUARANTINED** from `SupportedProgram` (key comparability not soundly
  structural for a conversion); re-admit when types seal a comparable-key builder. Map LITERALS graduated (GREEN).
- Latent typed-lowering residuals (e.g. an untyped `func(x any) any` lambda) remain dead but unproven.

## NEXT

- GROW `eval_value` (runtime `len`/`int(x)`; fractional floats) — each widens the completeness converse
  (`out_main_denotes`, the print/println-of-DENOTABLE-args fragment) toward a general `supported ⟺ denotes`.
- Extend the cmd↔unified bridge past the output/panic/return/defer fragment to chan/heap/spawn.
- Grow behavioral safety toward `BehaviorSafe` → `SafeProgram` (= EmittableProgram + BehaviorSafe) →
  `emit_safe`; wire the certified path to the main output.
- Widen the live GoPrint plugin bridge (postfix / atoms / calls) + grow `GoStmt` forms — gate-honestly.

## Known trust base (TCB)

Rocq kernel · the string→`.go` extraction step · the Go toolchain · trusted foreign imports · the whole
trusted plugin `plugin/go.ml` (gap #10) · and (once GoSem backs emission) the `GoSem`≈real-Go adequacy
assumption, heir to gap #10. The MODEL's logical trust base is empty (zero axioms); the plugin is the
separate, still-trusted TCB.

## Current gates

Zero-axiom is gated by `Print Assumptions` in THREE flows (single-sourced here): **manifest**
(`manifest-axioms.sh` diffs the `dune build` `Axioms:` vs empty `EXPECTED_ASSUMPTIONS.txt`) covers
`main_effect` / `gosem_trust_surface` / `gosem_string_authority_surface` / the bridge surfaces (`cmd_to_ucmd_run_agrees` /
`bridge_agrees` / `run_cmd_out_monotone` / `run_cmd_no_panic_ret` /
`run_cmd_terminates` / `denote_program_run_agrees`) / `panic_free_runs_ret` /
`panic_free_runs_ret_ustep` / `panic_free_denotable_runs_ret`[`_ustep`]; **printer** + **emit** (GoAst/GoPrint and GoTypes/GoSafe/GoEmit compiled
STANDALONE, grep `^Axioms:`) cover the spine. A `Print Assumptions` under none of the three is not gated.

- `make check` — Docker prover stage: re-extract, run, diff vs `expected_output.txt`; plus the three zero-axiom
  flows, the axiom-authority self-test, the fail-closed `negtests/` harness, the code-discipline gate (the
  structural checks enumerated in `plugin/smart-ctor-gate.sh`), `emit-demo`, gofmt, and `go vet`.
- `make emit-verify` / `make printer-verify` — local mirrors of the emit / printer gates.
- `make negtest` — local: each `negtests/*.v` ABORTS extraction at a fail-closed backend site.
- Pre-commit hook: re-extracts + auto-stages Go, and an anti-axiom DECLARATION scan over every tracked `.v`.
