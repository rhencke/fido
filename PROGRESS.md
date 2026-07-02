# Fido — status

Short live ledger — the size discipline is BYTES, not lines (keep this file under ~8 KB; long lines
are not a loophole; details live in the `.v` files, theorem names, and plans). Design: `ARCHITECTURE.md`; rules: `CLAUDE.md`; mistakes: `LESSONS.md`; Go-spec:
`SPEC_CONFORMANCE.md`. History is in git — **current** state only.

## The goal

Be **safer than Go's compiler can prove** — lift type/memory/concurrency safety to compile time — while
still lowering into ordinary Go. TARGET: prove, before emitting, that nil deref / OOB / send-on-closed /
failed assertion / data race / silent overflow cannot happen; long-term, session-typed protocols +
race/deadlock freedom. ⚠️ TODAY the spine gates SUPPORTED SYNTACTIC emission on the main path;
behavioral safety is only the narrow off-main `emit_panic_free` seed.

**Honest claim:** *verified model components with a TRUSTED extraction backend* — NOT "formally verified
Go." No theorem relates emitted Go to its source term (gap #10). `emit_panic_free` accepts iff the
program denotes to `c` with `cmd_no_panic c` (any denotable panic rejected there; an ABSENT program by
non-denotation) — no full BehaviorSafe gate.

## Architecture (AST-first certified emission — `ARCHITECTURE.md` governs)

Spine: **GoAst** → **GoPrint** (round-trip/injectivity; SYNTAX only) → **GoSafe** (`SupportedProgram`
now; `BehaviorSafe` later) → **GoEmit** (certificate-only emit). `GoTypes` = the shared conservative
classifier (`ptype`/`svalue`). **GoSem** bridges AST behavior into `cmd.v`/`unified.v` (slice 1).

**Live plugin bridge:** `plugin/go.ml` (trusted) still emits `main.go`; the extracted verified printer
prints a SMALL expression class on that path (binop trees over runtime locals, literals, `^x`, plain
field selectors, runtime numeric conversions, fixed-width bridging binops — the rest stays on trusted
`pp_expr`). The plugin CONSTRUCTS the `GExpr`; only `gprint` is verified. NOT "verified Go."

## GREEN (proved / working)

- **Spine ZERO-AXIOM** (`make emit-verify`): GoAst / GoPrint / GoTypes / GoSafe / GoEmit.
- **GoPrint round-trip + injectivity** over the binop/unary/atom core, all postfix forms, `EConv`,
  slice/map composite literals, exact-lexer string literals.
- **Statement layer:** `GoStmt` (expr-stmt / return / return e / `_ = e` / defer-call);
  `print_stmt_inj` + `print_program_inj`. `GsDefer` supported, emittable, and denoted.
- **GoSafe `SupportedProgram`** — decidable supported-subset gate (closed type-errors rejected via
  `ptype`; slice + integer-key map literals admitted structurally; invalid nested map keys rejected
  even in empty literals; quarantines ledger-pinned).
- **GoEmit** — certificate-only (`EmittableProgram`); `make emit-demo` builds a certified program with
  the real Go toolchain.
- **GoSem slice 1** (detail lives in `GoSem.v`; the SURFACES are the authority — this ledger
  deliberately lists no theorem inventory):
  - partial AST → `Cmd` denotation for print/println / panic / return / blank-assign / defer /
    call args, over the exact-or-absent constant fold — faithful-or-absent, all fail-closed.
  - the runtime GTInt tier R1–R8 and the typed-runtime tier T1–T5 LANDED + SEALED: the model's
    own ops through ONE shared evaluator, dispatch authorities pinned, outcome trichotomies
    proved, boundary/hole rows pinned absent (frontier surface).
  - float constants exact-or-reject behind `floats_checked`; fold verification is the
    CONSTANT-op layer (`sf_const_binop`/`sf_const_neg` — no signed zero); the dyadic↔SF
    agreement arc is live (`plans/dyadic-sf-agreement.md`).
  - denotation ⊆ `SupportedProgram` (`gosem_sound`) + compositional converses.
  - public surfaces (topic-split, manifest-gated): `gosem_trust_surface`
    (core/float/slice-index/runtime-int/map/frontier) + `gosem_string_authority_surface`.
  - NO BehaviorSafe; main output still legacy. Zero axioms.
- **Model layer** (proof-only): `builtins.v`, `cmd.v`, `unified.v` (race-freedom/liveness proved on
  `ustep`), `concurrency.v`.
- **cmd↔unified bridge** (`cmd_unified.v`): the general `bridge_agrees` — for ANY command the `ustep`
  run agrees with `run_cmd` (panic, output, completion); termination via `cmd.run_cmd_terminates`.
  ⚠ chan/heap/spawn later. Zero axioms.
- **GoSemSafe** — panic-freedom properties + the narrow gate: `panic_free_runs_ret`(+`_ustep`),
  decidable `panic_free_denotable`, `PanicFreeEmittable` refining `EmittableProgram`,
  `panic_free_gate` (sound+complete) + `emit_panic_free_gated`. Both rejection mechanisms pinned
  (`panic_free_gate_{slice,div,defer,arg_panic}` the denoted-panic side; `_absent` the non-denotation
  side, panic shapes included). Off the main path; NOT BehaviorSafe. Zero axioms.
- **Whole model axiom-free**: `Print Assumptions main_effect` empty; gates fail the build on drift.
- **Golden end-to-end**: `make check` diffs runtime output vs `expected_output.txt`.

## RED (not done — do not overclaim)

- Behavioral cert narrow + off-main (see GoSemSafe above); nil deref / send-on-closed / race unmodeled.
- **gap #10:** the MiniML→Go plugin is trusted/unverified; golden tests are the only end-to-end check.
- **Main output is the legacy path** (`main.go` from the plugin; `emit-demo` is the certified demo).
- **Map CONVERSIONS quarantined** (`ctmap_conv_unsupported_target_rejected` seals the class).
- Latent typed-lowering residuals remain dead but unproven.

## NEXT

- The dyadic↔`SF*` agreement arc (`plans/dyadic-sf-agreement.md`): rungs 1–4 + 5a/5b landed —
  NEG-f64 + the signed-zero constant layer; the `shl_align` spec; `binary_round_exact` with
  the LIVE-boundary bridge (`ptype_float_const_repr`, `ptype_float_payload_{f64,f32}`,
  `box_float_gate`) and `renorm_binary_round_idem`; the WIDE bridge
  `binary_round_of_norm_wide` (raw-digits-unbounded odd-core determinism, gated; the carry
  class pinned `add_carry_raw_wide_accepted`); the determinism endpoint
  `binary_normalize_wide_determined` + `dy_norm_value_unique` + the live render endpoint
  `sf_render_signed_value_f64`. Next: the `SFadd` finite-arm assembly closing ADD/SUB. (The typed-runtime tier T1–T5 + R8 is COMPLETE — `LESSONS.md`.)
- CONSOLIDATION directive (2026-07-02, boss): no new features next; shrink bytes — GoSem.v
  physical split per the plan in `ARCHITECTURE.md`, surfaces stay endpoint-only.
- Extend the cmd↔unified bridge to chan/heap/spawn.
- Grow behavioral safety toward `BehaviorSafe` → `SafeProgram` → `emit_safe`; wire the certified path
  to the main output. Widen the live GoPrint bridge + `GoStmt` forms — gate-honestly.

## Known trust base (TCB)

Rocq kernel · the string→`.go` extraction step · the Go toolchain · trusted foreign imports · the whole
trusted plugin `plugin/go.ml` (gap #10) · and (once GoSem backs emission) the `GoSem`≈real-Go adequacy
assumption. The MODEL's logical trust base is empty (zero axioms); the plugin is separate.

## Current gates

Zero-axiom is gated by `Print Assumptions` in THREE flows (single-sourced here): **manifest**
(`manifest-axioms.sh` vs empty `EXPECTED_ASSUMPTIONS.txt`) covers `main_effect` /
`gosem_trust_surface` / `gosem_string_authority_surface` / `cmd.run_cmd_terminates` / the bridge
surfaces (`cmd_to_ucmd_run_agrees` / `bridge_agrees` / `run_cmd_out_monotone` /
`run_cmd_no_panic_ret`) / `gosem_panic_free_surface` / `builtins.slice_get_bounds_surface`;
**printer** + **emit** (compiled STANDALONE, grep `^Axioms:`) cover the spine. A `Print Assumptions`
under none of the three is not gated.

- `make check` — Docker: re-extract, run, golden diff; the three zero-axiom flows, the axiom-authority
  self-test, `negtests/`, the code-discipline gates (`plugin/smart-ctor-gate.sh`), `emit-demo`, gofmt,
  `go vet`.
- `make emit-verify` / `make printer-verify` — local mirrors. `make negtest` — fail-closed harness.
- Pre-commit hook: re-extracts + auto-stages Go; anti-axiom declaration scan.
