# Fido — status

Live ledger, bytes under ~8 KB. Design: `ARCHITECTURE.md`; rules: `CLAUDE.md`; mistakes:
`LESSONS.md`; Go-spec: `SPEC_CONFORMANCE.md`. History is in git — **current** state only.

## The goal

Be **safer than Go's compiler can prove** — lift type/memory/concurrency safety to compile time —
while still lowering into ordinary Go. TARGET: prove, before emitting, that nil deref / OOB /
send-on-closed / failed assertion / data race / silent overflow cannot happen. ⚠️ TODAY the spine
gates SUPPORTED SYNTACTIC emission on the main path; behavioral safety is only the narrow off-main
`emit_panic_free` seed.

**Honest claim:** *verified model components with a TRUSTED extraction backend* — NOT "formally
verified Go." No theorem relates emitted Go to its source term (gap #10). `emit_panic_free`
accepts iff the program denotes to `c` with `cmd_no_panic c` (any denotable panic rejected there;
an ABSENT program by non-denotation) — no full BehaviorSafe gate.

## Architecture (AST-first certified emission — `ARCHITECTURE.md` governs)

Spine: **GoAst** → **GoPrint** (round-trip/injectivity; SYNTAX only) → **GoSafe**
(`SupportedProgram` now; `BehaviorSafe` later) → **GoEmit** (certificate-only emit). `GoTypes` =
the shared conservative classifier. **GoSem** bridges AST behavior into `cmd.v`/`unified.v`.

**Live plugin bridge:** `plugin/go.ml` (trusted) still emits `main.go`; the extracted verified
printer prints a SMALL expression class on that path (binop trees over runtime locals, literals,
`^x`, plain field selectors, runtime numeric conversions, fixed-width bridging binops). The
plugin CONSTRUCTS the `GExpr`; only `gprint` is verified. NOT "verified Go."

## GREEN (proved / working)

- **Spine ZERO-AXIOM** (`make emit-verify`): digits / GoAst / GoPrint / GoTypes / GoSafe / GoEmit
  (digits.v = the shared decimal authority, compiled in both gated flows).
- **GoPrint round-trip + injectivity** over the expression core (all postfix forms, `EConv`,
  slice/map composite literals, exact-lexer strings) + the statement layer
  (`print_stmt_inj`/`print_program_inj`). `GsDefer` supported+emittable+denoted; `GsShortDecl`
  gate-admitted; the expression-level env evaluator exists; statement-level env denotation is
  NEXT — short-decl programs are currently supported-but-undenoted.
- **GoSafe `SupportedProgram`** — decidable supported-subset gate (closed type errors rejected
  via `ptype`; slice + integer-key map literals admitted structurally; quarantines
  ledger-pinned); locals `x := e` via the sealed `ScopeS` fold (declare-only binding, marked
  uses, unused rejected; decl-free agreement `body_okS_nil_declfree`).
- **GoEmit** — certificate-only (`EmittableProgram`); `make emit-demo` go-builds a certified
  program.
- **GoSem slice 1** (SURFACES are the authority — no theorem inventory): partial AST → `Cmd`
  denotation (print/println / panic / return / blank-assign / defer / call args) over the
  exact-or-absent constant fold; the runtime int + typed-runtime tiers SEALED through ONE shared
  evaluator with dispatch authorities pinned and boundary rows pinned absent; float constants
  exact-or-reject behind `floats_checked` with checker completeness `fsf_checked_complete` +
  guard-unreachability `floats_checked_total` (guard KEPT, fail-closed); denotation ⊆
  `SupportedProgram` (`gosem_sound`) + compositional converses; surfaces topic-split +
  manifest-gated. NO BehaviorSafe; main output still legacy. Zero axioms.
- **Model layer** (proof-only): the split model modules (GoNumeric → GoRuntimeTypes →
  GoEffects/GoPanic → GoSlice/GoMap/GoChan/GoHeap → GoSession/GoString/GoSwitch/GoComplex;
  plans/builtins-split.md — `builtins.v` is DELETED), `cmd.v`, `unified.v`
  (race-freedom/liveness proved on `ustep`), `concurrency.v`.
- **cmd↔unified bridge** (`cmd_unified.v`): ONE bridge, `bridge_heap_agrees` — any completing
  command (typed heap cells, ALLOCATION, the CHANNEL trio send/recv/close with per-site TYPED
  closed-recv zeros, arbitrary defer nesting, any panics) agrees with `run_cmd` end to end
  incl. final heaps/buffers/closedness, capacities pinned to the world's; the typed-zero
  obligations (TI64+TString instances, panic agreements, would-block absences, tag-mismatch
  rejection, the translation pin) are gated theorems. ⚠ spawn/select later. Zero axioms.
- **GoSemSafe** — panic-freedom properties + the narrow gate (`panic_free_gate` sound+complete,
  `emit_panic_free_gated`; both rejection mechanisms pinned). Off the main path; NOT
  BehaviorSafe. Zero axioms.
- **No project axioms; gated surfaces empty**: every manifest surface's `Print
  Assumptions` (incl. `main_effect`) is empty; gates fail the build on drift. Stdlib
  funext survives only at two named NON-gated families (`run_io_inj`; `unified.v`'s
  rstep-embedding lemmas).
- **Golden end-to-end**: `make check` diffs runtime output vs `expected_output.txt`.

## RED (not done — do not overclaim)

- Behavioral cert narrow + off-main; nil deref / send-on-closed / race unmodeled.
- **gap #10:** the MiniML→Go plugin is trusted/unverified; golden tests are the only end-to-end
  check.
- **Main output is the legacy path** (`main.go` from the plugin; `emit-demo` is the certified
  demo).
- **Map CONVERSIONS quarantined** (`ctmap_conv_unsupported_target_rejected` seals the class).
- Latent typed-lowering residuals remain dead but unproven.

## NEXT

- Continue the cmd↔unified bridge (`plans/bridge-effects.md`): `CAlloc` AND the channel
  slice LANDED (typed zeros through the channel's own tag, gated obligations); next spawn
  (design deferred until reached) — or return to the canonical relational syntax authority
  per the checkpoint-49 review's recommended order.
- Grow behavioral safety toward `BehaviorSafe` → `SafeProgram` → `emit_safe` — locals arc OPEN
  (`plans/gosem-locals.md`; next: the env statement layer); wire the certified path to the main
  output; widen the live GoPrint bridge — gate-honestly.

## Known trust base (TCB)

Rocq kernel · the string→`.go` extraction step · the Go toolchain · trusted foreign imports ·
the whole trusted plugin `plugin/go.ml` (gap #10) · and (once GoSem backs emission) the
`GoSem`≈real-Go adequacy assumption. No project-declared axioms; every GATED surface's
`Print Assumptions` is empty (stdlib funext survives at the two named non-gated families
— see SPEC_CONFORMANCE's trust ledger); the plugin is separate.

## Current gates

Zero-axiom is gated by `Print Assumptions` in THREE flows (single-sourced here): **manifest**
(`manifest-axioms.sh` vs empty `EXPECTED_ASSUMPTIONS.txt`) covers `main_effect` /
`gosem_trust_surface` / `gosem_string_authority_surface` / `cmd.cmd_semantics_surface` /
`cmd_unified_surface` / `gosem_panic_free_surface` / `GoSlice.slice_get_bounds_surface` /
`GoCFG.blocks_cfg_surface`;
**printer** + **emit** (compiled STANDALONE incl. `digits.v`, grep `^Axioms:`) cover the spine. A
`Print Assumptions` under none of the three is not gated.

- `make check` — Docker: re-extract, run, golden diff; the three zero-axiom flows, the
  axiom-authority self-test, `negtests/`, the code-discipline gates
  (`plugin/smart-ctor-gate.sh`), `emit-demo`, gofmt, `go vet`.
- `make emit-verify` / `make printer-verify` — local mirrors. `make negtest` — fail-closed
  harness.
- Pre-commit hook: re-extracts + auto-stages Go; anti-axiom declaration scan.
