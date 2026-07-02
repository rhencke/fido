# The RUNTIME-value tier (B3 / Phase 5 "eval non-literals") — R1–R6 LANDED (the runtime arc is COMPLETE for the current fragment)

**Scope.** This arc covers the RUNTIME-classified subset of the supported-but-undenoted frontier
(R1 len/arith + R2 slice indexing + R3 width conversions + R4 bool comparisons + R5 map values +
R6 nonzero `%`/unary `-` ALL LANDED) — NOT the whole gap: the remaining classes are WITNESSED (non-exhaustively) in GoSem's
`undenoted_frontier`. In the CLOSED world the runtime forms are
fully DETERMINED (no inputs, no heap reads in the supported fragment) — `len([]int{len([]int{1})})` is
always 1 — so a deterministic runtime evaluator can denote them faithfully. This also brings the first
runtime OOB panic into denotation (`[]int{10,20}[<runtime 5>]` → the run PANICS), the gateway to full
`BehaviorSafe` (nil deref / OOB / race) per Phase 5's ordering.

## Live invariants (R1–R6 as landed)

- The runtime tier lives in `denote_expr` via `reval_int` (RVal | RPanic | None-absent), UNDER the same
  `floats_checked` boundary `eval_value` enforces; the terminal-flag/short-circuit machinery carries
  runtime panics unchanged.
- OOB payloads are the model's EXACT `rt_index_oob i n` (digits; negative form omits length — verified
  against gc via `go run`; length = the STRUCTURAL list/`sh_len` nat, never a round-trip through the
  wrapped `len`).
- R3 (LANDED): `int(x)` folds IN-fragment (`intwrap` identity); every other integer width EXITS at
  `denote_expr` via `wrap_runint` — the model's own per-width wraps (`u8wrap`…`u64wrap`, `i64wrap`,
  the new total `uintwrap`), Go's runtime truncation, agreement-by-construction; class theorems
  `denote_expr_conv_{runs,panic}`. Runtime FLOATS stay absent until the model-op evaluation extends
  (a fresh agreement question — do NOT smuggle); so do runtime-float→int truncations.

## Review-lesson checklist (apply from the start)
- Every new fold's upstream GATE rejection becomes load-bearing — probe nested/empty shapes at ptype
  level FIRST (the goty_supported episode).
- Class claims = gated ∀-theorems sealed to the gate's boundary; fixtures are witnesses.
- Quarantine valid-but-rejected in the ledger per surface; invalid companions in bad_programs.
- Witness succession (rule; the CURRENT witness state lives in the witness-succession section at the
  end of this file and in GoSem's pinned `undenoted_frontier`): folding a form kills its
  supported-but-undenoted witnesses — swap successors in the SAME commit; a totality claim for any
  fragment needs a THEOREM.
- Exact panic MESSAGES verified against real Go before modeling.
- Grep-verify batch edits before committing.

## Not this arc
Heap/chan/spawn denotation (needs AST statements first); the general dyadic↔SF* theorem; EFloat literals.

## Post-survey design (2026-07-02 — anchors the implementation window)

- The MODEL decides the semantics; the payload is now EXACT: `rt_index_oob i n` renders Go's real
  message (digits; a NEGATIVE index omits the length part — both verified against gc via go run; length
  boundary a `nat`). The wrap ops (`int_add = intwrap (intraw a + intraw b)` etc.) are the arithmetic
  authority. The runtime tier COMPUTES WITH THE MODEL'S OWN OPS on the carriers — single authority, no
  fold↔model agreement gap by construction (the float-arc lesson applied up front).
- Shape: `Inductive RRes := RVal (v : GoInt) | RPanic (p : GoAny).` and a recursive
  `reval_int : GExpr -> option RRes` sealed to the `GTInt`-classified runtime fragment (the boxed carrier
  for `GTInt` is `GoInt` via `intwrap`, tag `TInt64`). `None` = not-yet-denotable (absent);
  `RPanic` = the determined runtime panic. No world-threading needed — expression effects in this
  fragment are panics only.
- Slices: **R1** `len` of int-slice literals with runtime-evaluable elements (elements recursively
  `reval_int`'d; first panicking element aborts construction — matches the verified go-run behavior) +
  runtime `+ - *` via model ops, `/`/`%` with a ZERO runtime divisor → `RPanic rt_div_zero` (subsumes and
  RETIRES the shape-based `divisor_zero`, whose seal becomes a corollary). **R2** (LANDED) runtime slice INDEX:
  in-bounds → the element, OOB → `RPanic (rt_index_oob i n)` — the first runtime OOB panics in
  denotation, exact payloads.
  **R3** (LANDED) width conversions of runtime ints via the model wraps (`wrap_runint`; `int(x)` in-fragment).
  **R4** (LANDED) runtime bool COMPARISONS of int-fragment operands via the model's `int_eqb`/`int_ltb`/`int_leb`
  (`cmp_verdict`: `!=` = negation, `>`/`>=` = argument swap); `&&`/`||` stay absent (bool operands, not the fragment).
  **R5** (LANDED) map-`len` over RUNTIME map values (`reval_int`'s EMapLit arm: the fold's own side conditions,
  values through THE SHARED evaluator `reval_val_with` — `denote_expr` is now a thin wrapper over the same
  pipeline (fold → GTInt fragment → `rexit_with` R3/R4 exits), so converted/compared values construct exactly
  as they denote standalone; count via the checked `rval_len`/`rval_len_repr`). ⚠ Go leaves map-literal
  evaluation order UNSPECIFIED: a panic denotes ONLY when order-INDEPENDENT — sealed by the quantified
  walker theorems `rconstr_vals_{ok_iff,panic_sound,two_panics_absent}` (the fixture
  `runtime_maplen_ambiguous_absent` is a witness, not the authority).
  **R6** (LANDED) nonzero runtime `%` via the evidence-carrying `int_mod` (the `int_div` convoy) and runtime
  unary `-` via `int_neg`; the `^` complement of a platform int stays ABSENT (no model op — add `int_not`
  as a modelled Definition first if ever needed).
- `denote_expr` consumes `reval_int` (RVal → `CRet (anyt TInt64 v), false`; RPanic → `CPan p, true`);
  the computed-flag/short-circuit machinery carries panics unchanged. The `floats_checked` boundary stays
  at `eval_value`; `reval_int`'s constant leaf goes THROUGH `eval_value` (boundary preserved).
- Witness succession — CURRENT STATE (post-R6): every RUNTIME-classified witness DENOTES; the pinned
  `undenoted_frontier` WITNESS (non-exhaustive — known absent classes: runtime floats, the `^`
  complement of a platform int) is the multi-byte rune `runeconv_mb` alone. Any rule that lands FLIPS
  its member's pins — swap the successor in the same commit and sweep the stale-claim phrases
  repo-wide (the five recurring sites: frontier, out-boundary, the GoSemSafe absent pair, the
  dead-tail escape, the short-circuit trio). NOTE: `folded_arg` (né `denotable_arg`) is
  the EVAL-ONLY sufficient fragment; the runtime tier's own converse — and any THEOREM bounding the
  gap — is open work.
