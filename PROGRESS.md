# Fido — status

Short live ledger. Design: `ARCHITECTURE.md`; rules: `CLAUDE.md`; mistakes: `LESSONS.md`; Go-spec:
`SPEC_CONFORMANCE.md`. History is in git — **current** state only.

## The goal

Be **safer than Go's compiler can prove** — lift type/memory/concurrency safety to compile time — while still
lowering into ordinary Go (channels, goroutines, maps, slices). TARGET: PROVE, before emitting, that nil deref
/ use-after-close / out-of-bounds / send-on-closed / failed assertion / data race / silent overflow cannot
happen; long-term, session-typed protocol compliance + race/deadlock freedom over Go's happens-before. Built
incrementally. ⚠️ TODAY the spine gates SUPPORTED SYNTACTIC emission on the main path; behavioral safety is
only a narrow off-main `emit_panic_free` seed.

**Honest claim:** *verified model components with a TRUSTED extraction backend* — NOT "formally verified Go."
Theorems are proved in Rocq; `*.go` is extracted from `*.v` by the trusted plugin. No theorem relates emitted
Go to its source term (gap #10); `emit_panic_free` is a narrow emission cert OFF the main path (accepted iff the program denotes to `c` with `cmd_no_panic c` — any denotable panic rejected there; an ABSENT (undenoted) program by non-denotation) — no full BehaviorSafe gate.

## Architecture (AST-first certified emission — `ARCHITECTURE.md` governs)

Spine: **GoAst** (structured syntax) → **GoPrint** (printing + expression round-trip / program injectivity;
SYNTAX only) → **GoSafe** (`SupportedProgram` syntactic gate now; `BehaviorSafe` later) → **GoEmit** (the only
blessed emit; needs a certificate — `EmittableProgram`; no raw `emit`). `GoTypes` is the shared classifier
(`ptype`/`svalue`) GoSafe consults. **GoSem** bridges the AST's behavior into the existing proof-only
semantics (`cmd.v`/`unified.v`/`concurrency.v`); slice 1 only (below).

**Live plugin bridge:** the legacy trusted plugin (`plugin/go.ml`) still emits `main.go`; the extracted
`plugin/printer.ml` (from GoPrint) prints a SMALL expression class on that live path — a binop tree over
runtime locals, int/int64/uint64 literals, the bare `^x` complement, a runtime local's plain field selector
(`is_record_proj`: local receiver, not embedded/defined-type projection — pinned by the selector-bridge gate),
the runtime numeric conversions, and fixed-width `(u|i)N_add`/`sub`/`mul` as a bridging-binop operand. Every
other shape stays on trusted `pp_expr`. The trusted plugin CONSTRUCTS the `GExpr`; only the verified `gprint`
PRINTS it — serialization proofs only, NOT MiniML→`GExpr` construction. The live emission is NOT "verified Go."

## GREEN (proved / working)

- **Spine ZERO-AXIOM** (`make emit-verify`): GoAst / GoPrint / GoTypes / GoSafe / GoEmit.
- **GoPrint round-trip** `parse_str (gprint 0 e) = Some (e, [])` + `gprint_inj`, zero axioms, over the
  binop/unary/atom core + every postfix form (selector / index / two-bound slice / variadic call /
  type-assertion) + the prefix conversion `EConv` + slice/map composite literals + string literals
  (`EStr`, fail-closed exact lexer `unescape_opt_image` — accepted == emitted).
- **Program/statement layer:** `GoStmt` (expr-stmt / `return` / `return e` / `_ = e` / `defer <call>`);
  `print_stmt_inj` (5-ctor/25-case) + `print_program_inj` (distinct programs emit distinct Go); zero axioms.
  `GsDefer` is syntactically supported + emittable (gated to a call via `expr_stmt_ok`) AND denoted by GoSem
  (`CDfr` — see the GoSem bullet below).
- **GoSafe `SupportedProgram`** — a DECIDABLE supported-subset gate (not a package-name proxy): rejects
  bare-value statements, non-callable calls, value-returns from void `main`, free/undefined identifiers, and
  closed type-errors (`ptype`, a conservative constant-aware classifier). Admits slice literals + integer-key
  map literals structurally (`nodup_z` distinct constant keys; `goty_supported` rejects invalid nested map keys
  even in EMPTY literals; valid ptr/chan keys ledger-pinned per rejecting surface). `classify` is in GoAst, so GoSafe does not import the printer.
- **GoEmit** emits ONLY via a certificate (`EmittableProgram = Program + SupportedProgram`;
  `emit_supported = print_program`; `emit_supported_program_inj`). `make emit-demo` builds one certified
  program with the real Go toolchain (gofmt-clean + go build + go vet); a dependency of `make check`.
- **GoSem slice 1** — `denote_program : Program -> option (Cmd unit)` bridges the AST into `cmd.v`'s command
  tree (reuses `cbind`/`run_cmd`, no second universe): print/println → `COut` (the model's own `w_log`),
  panic → `CPan`, `return`, blank assignment + call ARGS via the EFFECTFUL `denote_expr`/`denote_args` (a
  constant falls through; a determined integer divide-by-zero panics with the model's `rt_div_zero` — typed
  fields `rc_div_zero`/`rc_arg_panic`), and `defer <call>` → `CDfr` (runs at return, LIFO — typed fields
  `rc_defer_lifo`/`rc_defer_panic`; its ARGS evaluate at DEFER time, `rc_defer_arg_panic`), over a PARTIAL
  `eval_value` (string / integer /
  exact-DYADIC-float (SEALED normalized payload; fractional incl., exact-or-reject; `eval_value`'s `floats_checked` BOUNDARY re-verifies every `PtFloatConst` subexpression — any depth/position, laundered-through-`int(..)` included — via `fsf_checked` against the model op; gated: the per-constructor recursion equations `floats_checked_children_eqs` + `eval_value_floats_checked` + `fsf_checked_*_agrees`) / bool CONSTANTS incl. in-range `uint`, an IN-BOUNDS index into an ALL-CONSTANT int-slice literal `[]int{..}[k]`→element, `len` of such a literal→its length (`eval_len_{reduces,supported}`; whole literal evaluated — a runtime element rejects either; in-bounds DENOTES, OOB DECLINED), `len` of an ALL-CONSTANT integer-keyed `goty_supported`-typed MAP literal→its entry count (`eval_map_len_{reduces,supported}`, same whole-literal discipline — a runtime VALUE rejects, `map_len_eval_absent`; both empty-literal `len` forms feed the div-zero shape)) — the FOLD ITSELF fails CLOSED (EVAL-level ABSENCE only, NOT behavioral rejection)
  on runtime / rounding / out-of-range / OOB forms (exact coverage in `GoSem.v`; class-level in-bounds/OOB over the fully-evaluable ALL-CONSTANT subfragment: `eval_slice_index_{reduces,inbounds_class,oob_class}`, a STRICT subset of `ptype`-support via the `eval_slice_index_supported` INCLUSION bridge — runtime index/elements EVAL-absent, `slice_index_supported_but_undenoted`; evaluator sealed to `ptype`'s own `assignable_to_ty`+`int_const_repr`) — PLUS the RUNTIME tier `reval_int` (R1–R7 — the `reval_int` CARRIER is GTInt: typed-width conversion EXITS from GTInt operands DENOTE (`denote_expr_conv_*`); OPERATIONS on non-GTInt runtime carriers stay absent — pinned by `typed_runtime_{not,convchain,shift}_absent`), `denote_expr`'s SECOND stage behind the same float boundary, which DENOTES the determined GTInt-fragment runtime forms the fold declines, via the MODEL'S OWN ops: runtime `len` with abort-on-panicking-element, `+ - * / %` + unary `- ^` (R6/R7 — the evidence-carrying `int_mod`, `int_neg`, the new modelled `int_not`; class lemmas `denote_expr_{div,rem,neg,not}_runs`+panics), checked `rval_len`, the runtime slice INDEX (in-bounds→element, OOB→the model's `rt_index_oob` panic; all four outcomes CLASS-quantified, `denote_expr_index_{in_bounds,oob,elem_panic,idx_panic}`; the emission-gate consequence on the valid-Go OOB pair is `GoSemSafe.panic_free_gate_slice`), (R3) width CONVERSIONS of runtime ints — `int(x)` in-fragment, every other integer width via `wrap_runint` (the model's own per-width wraps incl. the total `uintwrap`; Go's runtime truncation — `uint8(300runtime)`→44 pinned), class theorems `denote_expr_conv_{runs,panic}` sealed by `ptype_call_runint_conv`+`wrap_runint_total` — (R4) runtime bool COMPARISONS via the model's `int_eqb`/`int_ltb`/`int_leb` (`cmp_verdict`, its whole dispatch table SEALED qualified+total; class theorems `denote_expr_cmp_{runs,left_panic,right_panic}`) — and (R5) map-`len` over RUNTIME map values, walked by THE shared value evaluator (`reval_val_with`: fold → GTInt fragment → R3/R4 exits — the SAME pipeline `denote_expr` is a wrapper over, so R3/R4-form values construct exactly as they denote standalone; a panic denotes ONLY order-INDEPENDENTLY — Go leaves map-literal order unspecified; SEALED by the quantified `rconstr_vals_{ok_iff,panic_sound,two_panics_absent}`; `denote_expr_maplen_{runs,panic}`). Proves denotation ⊆ `SupportedProgram` (`gosem_sound`) and — the CONVERSE
  direction — that whole classes of supported programs DENOTE: `out_main_denotes` (the output-call fragment)
  and the GENERAL statement-compositional `denotable_stmts_main_denotes` (any body whose every statement
  individually denotes — return/panic terminators, blank-assign, print·println interleaved, incl. a
  terminator + supported dead tail; SUFFICIENT not necessary, still conditional on `stmt_denotable`, not full
  `supported_program`). Its tightness is PROVED, not asserted: `denotable_body_terminator_free_iff` — on a
  terminator-free body the compositional converse is EXACT (iff), the terminator dead-tail escape being the
  SOLE slack. Every denotation RUNS for enough fuel (`cmd.run_cmd_terminates`, universal). Certified public surface =
  `gosem_trust_surface` + `gosem_string_authority_surface` (the string comparators ARE the model's `str_*`); a
  GoSem fact in neither tuple is an internal helper / example, not certified. NO `BehaviorSafe`. Zero axioms.
- **Model layer** (proof-only): `builtins.v` (the Go layer over concrete Rocq data), `cmd.v` (effect
  evaluator), `unified.v` (`ustep` operational semantics with race-freedom + liveness/deadlock proved on it —
  NOT the emission path), `concurrency.v` (trace / happens-before / race / bounded-deadlock theory).
- **cmd↔unified bridge** — `cmd_unified.v` (proof-only): `cmd_to_ucmd` translates cmd.v's
  tree into `unified.v`'s output/panic/return/defer fragment (println flag preserved). The single general
  `bridge_agrees`: for ANY `c` (arbitrary defer nesting, ANY panics — so every GoSem denotation) the `ustep`
  run agrees with `run_cmd` — finishes, panic EQUALS the Outcome's, output EQUALS `run_cmd`'s appended
  `w_output` (unwinds the LIFO defer forest under the `(prog, pa)` 2-mode, threading the last-raised panic;
  completion discharged by `cmd.run_cmd_terminates`); `cmd_to_ucmd_run_agrees` is the fuel-1 `no_defer` form. Supporting properties for a COMPLETING run on ANY `c`: `run_cmd_out_monotone`
  (output only APPENDS) + `run_cmd_no_panic_ret` (a panic-free run returns `ORet`). TERMINATION lives in `cmd.v`:
  `run_cmd_terminates` (returns `Some` for enough fuel, via a `defers_sz` measure — a pure `run_cmd` property).
  ⚠ chan/heap/spawn later. Zero axioms.
- **First behavioral-safety PROPERTIES + emission gate** — `GoSemSafe.v`: `panic_free_runs_ret` (a
  `CPan`-free command runs to `ORet` for enough fuel — defers included; `_ustep` lifts the guarantee to
  `ustep` via the general `bridge_agrees`).
  `panic_free_denotable p` = the program denotes to `c` AND `cmd_no_panic c` (cmd.v's authority — ANY `CPan`
  in the denotation, however the panic arises, is rejected by the one check); ONE DECIDABLE predicate;
  `panic_free_denotable_runs_ret`[`_ustep`] prove it entails the panic-free run, `_supported` that it
  implies `SupportedProgram`. `PanicFreeEmittable` REFINES GoEmit's `EmittableProgram` — the FIRST emission cert
  whose precondition is a proven panic-free RUN (`pfe_runs_ret`); `panic_free_gate` decides + certs-or-rejects
  (SOUND+COMPLETE); `emit_panic_free_gated` = end-to-end decide-then-emit (ancestor of a total `emit_safe`).
  ⚠ Since tier R2 the runtime-panic forms (OOB/runtime index, panicking elements) DENOTE to `CPan`, caught by
  `cmd_no_panic` (`panic_free_gate_slice` facts unchanged); NON-denotation rejects ABSENCE — no behavior judgment, and not only non-panic shapes: a syntactic `panic(<undenoted arg>)` also rejects there (`panic_free_gate_absent` pins both); `panic_free_gate_defer`/`_div`/`_arg_panic`
  pin the denotable-panic one (defer-println ACCEPTED+emitted; defer-panic, the determined divide-by-zero, and
  arg-panics supported+DENOTABLE yet rejected by `cmd_no_panic`) — does NOT gate main output, NOT full
  `BehaviorSafe`. Zero axioms.
- **Whole model axiom-free**: `Print Assumptions main_effect` empty; the three gates (below) assert their
  surfaces zero-axiom and fail the build on drift (`EXPECTED_ASSUMPTIONS.txt` empty).
- **Golden end-to-end**: `make check` diffs runtime output vs `expected_output.txt`.

## RED (not done — do not overclaim)

- **GoSem slice 1 only / behavioral cert is narrow + off the main path.** The blessed SYNTACTIC certificate
  is `SupportedProgram`; there is now ALSO a behavioral certificate `PanicFreeEmittable`/`emit_panic_free`
  (precondition = a proven panic-free RUN). Accepted iff the program denotes to `c` with `cmd_no_panic c` —
  any denotable panic is rejected there (since tier R2 that includes OOB/runtime-index panics with the
  exact `rt_index_oob i n` payloads); non-denotation rejects ABSENCE, not a behavior judgment — the absent side can include syntactic panic forms with not-yet-denoted args (`panic_free_gate_absent`). NOT full
  `BehaviorSafe` — nil deref / send-on-closed / race are unmodeled — and it does NOT gate main output.
- **gap #10:** the MiniML→Go plugin is trusted/unverified — no theorem relates emitted Go to the source term;
  golden tests are the only end-to-end check.
- **Main output is the legacy path:** `main.go` comes from the trusted plugin, not the certificate-gated
  emitter (`emit-demo` is a separate certified demo). GoPrint drives only the small live-bridged class above
  (construct trusted, print verified).
- **Map CONVERSIONS `map[K]V(x)` QUARANTINED** from `SupportedProgram` (valid `map[int]int(nil)` ledger-pinned;
  the unsupported-target CLASS sealed by gated `ctmap_conv_unsupported_target_rejected`). Map LITERALS graduated (GREEN).
- Latent typed-lowering residuals (e.g. an untyped `func(x any) any` lambda) remain dead but unproven.

## NEXT

- RUNTIME tier: the GTInt-FRAGMENT arc R1–R7 is complete; NEXT = the TYPED-runtime tier (plans/typed-runtime-tier.md — per-width carrier OPERATIONS — `^int64(len ..)`, conversion chains, mixed-count shifts supported-but-undenoted — `typed_runtime_{not,convchain,shift}_absent`); the GENERAL dyadic↔`SF*` theorem — each case shrinks the
  supported-but-undenoted gap (`denotable_*` ⊊ `supported_*`; `stmt_denotable_ok` is the proved direction),
  representatively witnessed by `undenoted_frontier` (a fixture list, NOT per-class coverage; no theorem bounds the gap).
- Extend the cmd↔unified bridge past the output/panic/return/defer fragment to chan/heap/spawn.
- Grow behavioral safety toward `BehaviorSafe` → `SafeProgram` (= EmittableProgram + BehaviorSafe) →
  `emit_safe`; wire the certified path to the main output.
- Widen the live GoPrint plugin bridge (postfix / atoms / calls) + grow `GoStmt` forms — gate-honestly.

## Known trust base (TCB)

Rocq kernel · the string→`.go` extraction step · the Go toolchain · trusted foreign imports · the whole
trusted plugin `plugin/go.ml` (gap #10) · and (once GoSem backs emission) the `GoSem`≈real-Go adequacy
assumption, heir to gap #10. The MODEL's logical trust base is empty (zero axioms); the plugin is separate.

## Current gates

Zero-axiom is gated by `Print Assumptions` in THREE flows (single-sourced here): **manifest**
(`manifest-axioms.sh` diffs the `dune build` `Axioms:` vs empty `EXPECTED_ASSUMPTIONS.txt`) covers
`main_effect` / `gosem_trust_surface` / `gosem_string_authority_surface` / `cmd.run_cmd_terminates` / the bridge
surfaces (`cmd_to_ucmd_run_agrees` / `bridge_agrees` / `run_cmd_out_monotone` / `run_cmd_no_panic_ret`) /
`gosem_panic_free_surface` / `builtins.slice_get_bounds_surface`; **printer** + **emit** (GoAst/GoPrint and GoTypes/GoSafe/GoEmit compiled
STANDALONE, grep `^Axioms:`) cover the spine. A `Print Assumptions` under none of the three is not gated.

- `make check` — Docker prover stage: re-extract, run, diff vs `expected_output.txt`; plus the three zero-axiom
  flows, the axiom-authority self-test, the fail-closed `negtests/` harness, the code-discipline gate (the
  structural checks enumerated in `plugin/smart-ctor-gate.sh`), `emit-demo`, gofmt, and `go vet`.
- `make emit-verify` / `make printer-verify` — local mirrors of the emit / printer gates.
- `make negtest` — local: each `negtests/*.v` ABORTS extraction at a fail-closed backend site.
- Pre-commit hook: re-extracts + auto-stages Go, and an anti-axiom DECLARATION scan over every tracked `.v`.
