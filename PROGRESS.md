# Fido — status

Live ledger, bytes under ~8 KB. Design: `ARCHITECTURE.md`; rules: `CLAUDE.md`; mistakes:
`LESSONS.md`; Go-spec: `SPEC_CONFORMANCE.md`. History is in git — **current** state only.

## The goal

Be **safer than Go's compiler can prove** — lift type/memory/concurrency safety to compile time —
while still lowering into ordinary Go. TARGET: prove, before emitting, that nil deref / OOB /
send-on-closed / failed assertion / data race / silent overflow cannot happen. ⚠️ TODAY the spine
gates STATIC compiler-admissibility (GoCompile: "this program would compile") on the main path;
behavioral safety is only the narrow off-main `emit_panic_free` seed.

**Honest claim:** *verified model components with a TRUSTED extraction backend* — NOT "formally
verified Go." No theorem relates emitted Go to its source term (gap #10). `emit_panic_free`
accepts iff the program denotes to `c` with `cmd_no_panic c` (any denotable panic rejected there;
an ABSENT program by non-denotation) — no full BehaviorSafe gate.

## Architecture (AST-first certified emission — `ARCHITECTURE.md` governs)

Spine: **GoAst** (syntactically valid) → **GoPrint** (round-trip/injectivity; SYNTAX only) →
**GoCompile** (STATIC compiler-admissibility: "would compile"; behavioral safety is a SEPARATE
layer — GoSemSafe/future GoSafe) → **GoEmit** (certificate-only emit). `GoTypes` = the shared
conservative classifier. **GoSem** gives semantics ATOP a compilable program (into `cmd.v`/`unified.v`).

**Live plugin bridge:** `plugin/go.ml` (trusted) still emits `main.go`; the extracted verified
printer prints a SMALL expression class on that path (binop trees over runtime locals, literals,
`^x`, plain field selectors, runtime numeric conversions, fixed-width bridging binops). The
plugin CONSTRUCTS the `GExpr`; only `gprint` is verified. NOT "verified Go."

## GREEN (proved / working)

- **Spine ZERO-AXIOM** (`make emit-verify`): digits / GoAst / GoPrint / GoTypes / GoCompile / GoEmit
  (digits.v = the shared decimal authority, compiled in both gated flows).
- **GoPrint round-trip + injectivity** over the expression core (all postfix forms, `EConv`,
  slice/map composite literals, exact-lexer strings) + the statement layer
  (`print_stmt_inj`/`print_program_inj`). `GsDefer` supported+emittable+denoted; `GsShortDecl`
  gate-admitted; the expression-level env evaluator exists; statement-level env denotation is
  NEXT — short-decl programs are currently supported-but-undenoted.
- **GoCompile** (`GoCompile`/`go_compile_check`) — the STATIC compiler-admissibility gate
  ("this program would compile"): closed type errors rejected via `ptype`; slice + integer-key
  map literals admitted structurally; quarantines ledger-pinned; locals `x := e` via the sealed
  `ScopeS` fold (declare-only binding, marked uses, unused rejected; decl-free agreement
  `body_okS_nil_declfree`).  STATIC admissibility only, NOT behavioral safety.  (`GoCompile p :=
  go_compile_check p = true` today; the proof-bearing declarative relation is Phase 2 —
  `plans/gocompile.md`.)
- **GoEmit** — certificate-only (`EmittableProgram`); `make emit-demo` go-builds a certified
  program.
- **GoSem slice 1** (SURFACES are the authority — no theorem inventory): partial AST → `Cmd`
  denotation (print/println / panic / return / blank-assign / defer / call args) over the
  exact-or-absent constant fold; the runtime int + typed-runtime tiers SEALED through ONE shared
  evaluator with dispatch authorities pinned and boundary rows pinned absent; float constants
  exact-or-reject behind `floats_checked` with checker completeness `fsf_checked_complete` +
  guard-unreachability `floats_checked_total` (guard KEPT, fail-closed); denotation ⊆
  `GoCompile` (`gosem_sound`) + compositional converses; surfaces topic-split +
  manifest-gated. NO BehaviorSafe; main output still legacy. Zero axioms.
- **Model layer** (proof-only): the split model modules (GoNumeric → GoRuntimeTypes →
  GoEffects/GoPanic → GoSlice/GoMap/GoChan/GoHeap → GoSession/GoString/GoSwitch/GoComplex;
  plans/builtins-split.md — `builtins.v` is DELETED), `cmd.v`, `unified.v`
  (race-freedom/liveness proved on `ustep`), `concurrency.v`.
- **cmd↔unified bridge** (`cmd_unified.v`): ONE bridge, `bridge_effects_agree` — any completing
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

- **The canonical relational syntax authority is the ACTIVE arc** (`plans/canonical-grammar.md`;
  checkpoint-50 order: syntax authority before spawn). Phases 1+2 landed (`CanonTy`/`CanonExpr`
  + `gprint_expr_canonical` + `lex_gprint_expr`); Phase 3a landed (`canon_ty_unique`, type-level
  token uniqueness, PARSER-FREE via `gttokens_ty_inj`); Phase 3b slices 1–2k-d landed (slice 1
  `bd`/`gtokens_balanced`; slices 2a–2j the `last0`/`bdip`/`fsep` split lemmas, `no_depth0_sep`,
  `gtokens_args_inj`, `gtokens_pairs_inj`, the paren/bare operand discrimination
  `bare_not_paren_group`/`gtparen_inj`, the operator-token injectivities
  `op_token_inj`/`prefix_token_inj`, the pure type-skipper `skip_gty`
  (`skip_gty_types` exactness + `skip_gty_lt` progress), slice 2j the EBn precedence-split LOCATOR
  `eb_find` (finds the rightmost depth-0 min-precedence infix op as a suffix split),
  slice 2k-c the OPERAND LAW `eb_operand` — the depth-0 dual of `eb_depth` proving the
  locator's rightmost-min split via pure combine algebra, the `EBn`-crux — and slice 2k-d `eb_find_gtokens
  : eb_find (gtokens ctx e) = eb_top ctx e`, THE `gtokens_inj` EBn discriminator (`eb_operand` at the empty
  suffix ⇒ a block's tokens locate their own top operator: `Some (R,o)` for an unwrapped `EBn`, `None`
  otherwise), with the `EBn`-node instance `eb_find_inner` its corollary; plus the two operator-bearing
  same-constructor DIAGONALS of `gtokens_inj`, both FULL: `gtokens_inj_ebn` (the EBn diagonal —
  `gtokens_ebn_inner`'s unwrapped-inner recursion promoted past the ctx-wrapper, with wrapped-vs-unwrapped
  mismatch discriminated via `eb_find_gtokens`) and `gtokens_eun_inner` (the EUn diagonal); plus the first
  cross-discriminator `nonatom_len` (atoms print to 1 token, every other form to ≥2 — the atom row/column
  of the destruct-e2 matrix); and — LANDED — the other EIGHT NON-ATOM, NON-OPERATOR same-constructor DIAGONALS:
  the five POSTFIX forms `gtokens_inj_esel`/`gtokens_inj_eindex`/`gtokens_inj_eassert`/`gtokens_inj_eslice`/
  `gtokens_inj_ecall` and the three type-led COMPOSITES `gtokens_inj_econv`/`gtokens_inj_eslicelit`/
  `gtokens_inj_emaplit` (so with `gtokens_inj_ebn`/`gtokens_eun_inner` above, all 10 non-atom diagonals are
  done) (base-or-type prefix + delimited group: `last0_group` pins the prefix length,
  `app_eq_length` splits it off — `gttokens_ty_inj`/`convty_ty_inj` recover the type — then `app_inj_tail`
  / `sep_split` (the `lo:hi` colon) / `gtokens_args_inj` / `gtokens_pairs_inj` peel the group)); and — LANDED —
  the FOUR ATOM ROWS `gtokens_inj_eid`/`gtokens_inj_eint`/`gtokens_inj_estr`/`gtokens_inj_ehex`, each a full
  matrix ROW (atom `e1` vs EVERY `e2`): the atom prints to ONE token, so an atom `e2` matches-or-discriminates
  by `congruence` and a non-atom `e2` is killed by `nonatom_len` (≥2 tokens vs 1) — so the atom-row diagonals
  AND all atom×non-atom cross-cells are closed; and — LANDED — the LAST-TOKEN cross-discriminator `olast`
  (last element as an `option`, via `fold_left`) with the eight `gtokens_olast_*` values (`EIndex`/`ESlice`
  → `TRB`, `ECall`/`EAssert`/`EConv` → `TRP`, `ESliceLit`/`EMapLit` → `TRC`, `ESel` → `TId f`) — an
  `f_equal olast` mismatch discriminates a delimited/postfix pair with DIFFERENT closers; and — LANDED — the
  FIRST-TOKEN discriminator (`hd_error`) `gtokens_hd_eun` (→ `prefix_token o`) / `gtokens_hd_eslicelit` (→
  `TLB`) / `gtokens_hd_emaplit` (→ `TMap`) + `gtokens_hd_ebn_wrapped` (a wrapped `EBn` leads `TLP`); and —
  ★LANDED — the TWO type-led composite rows `gtokens_inj_eslicelit_row` and `gtokens_inj_emaplit_row`
  (`ESliceLit`/`EMapLit` vs EVERY `e2`, fed the per-element/per-pair `Forall` IH): `nonatom_len` (atoms),
  first-token (EUn; and `TLB` vs `TMap` between the two composites), `eb_find_gtokens`+wrapped-`hd` (EBn
  unwrapped/wrapped), `olast` (the other delimited/postfix), the diagonal — proving the row pattern
  end-to-end. NEXT: keep building
  the `gtokens_inj` ASSEMBLY. Now LANDED: the shared LEAD-token fact `gtparen_hd_not_prefix` (a
  postfix/composite/atom form never leads with a bare `prefix_token` — a 14-case `gtparen` induction, the
  `EUn` cross-cell for every postfix row) + `gtokens_olast_ebn_wrapped` (a wrapped `EBn` ends `TRP`); and
  the THIRD full non-atom row `gtokens_inj_esel_row` (`ESel` vs EVERY `e2`). Six full rows now done (4 atoms
  + `ESliceLit`/`EMapLit`/`ESel`). REMAINING rows: `EIndex`/`ESlice` (now unlocked — `olast` `TRB` vs the
  others, `gtokens_eindex_neq_eslice` between them, lead fact for EUn, `eb_find`+wrapped-`olast` for EBn),
  the `TRP` trio `ECall`/`EAssert`/`EConv` (still need within-`TRP` discrimination — the conversion-vs-call
  ambiguity, likely a `skip_gty` next-token split; plus wrapped-`EBn`-vs-`TRP` needs the same), and the
  `EUn`/`EBn` rows. Then `induction e1` wires the rows together. Then `canon_expr_unique` (all
  parser-free); then reprove `gprint_inj` off `gtokens_inj` (retiring `parse_print_roundtrip`), then
  `CanonStmt`/`CanonProgram`.
- The cmd↔unified bridge (`plans/bridge-effects.md`): `CAlloc` AND the channel slice LANDED
  (typed zeros through the channel's own tag, gated obligations; `bridge_effects_agree` now
  exposes capacity agreement publicly). Spawn/select is the deferred capstone (design deferred
  until reached) — it waits behind the syntax authority.
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
