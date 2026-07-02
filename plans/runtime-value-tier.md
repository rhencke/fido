# The RUNTIME-value tier (B3 / Phase 5 "eval non-literals") — R1+R2 LANDED; R3 (width conversions) next

**Why (pre-R1 framing; R1 closed the len/arith half).** This arc covers the RUNTIME-classified subset of
the supported-but-undenoted frontier (runtime slice indexing — R2; width conversions — R3; runtime map
values need their OWN rule) — NOT the whole gap: eval-partial constants (the multi-byte rune), the OOB
CONSTANT index, runtime conversions/comparisons are separate classes, WITNESSED (non-exhaustively) in
GoSem's `undenoted_frontier`. In the CLOSED world the runtime forms are
fully DETERMINED (no inputs, no heap reads in the supported fragment) — `len([]int{len([]int{1})})` is
always 1 — so a deterministic runtime evaluator can denote them faithfully. This also brings the first
runtime OOB panic into denotation (`[]int{10,20}[<runtime 5>]` → the run PANICS), the gateway to full
`BehaviorSafe` (nil deref / OOB / race) per Phase 5's ordering.

## Design sketch (decide precisely at implementation start)

- A RUNTIME evaluation tier inside `denote_expr` (Cmd-valued): evaluate a supported expression to either
  a value or a PANIC command — e.g. slice index with a runtime index evaluates index + whole literal,
  then in-bounds → element, OOB → `CPan` with Go's EXACT runtime message (verify the exact
  "index out of range [i] with length n" format with a real `go run` before modeling — rt_* constant in
  builtins like rt_div_zero).
- `int(x)`/width conversions of runtime ints: Go TRUNCATES at runtime (mod 2^w) — the model's `*wrap`
  ops ARE that semantics; fold via the model's own wraps (agreement-by-construction, no new guard tier
  needed for ints — wraps are the definition). Runtime FLOATS stay absent until the model-op evaluation
  extends (a fresh agreement question — do NOT smuggle).
- The float boundary (`floats_checked`) stays at `eval_value`'s top; the runtime tier must sit UNDER the
  same boundary discipline (a laundered float fold inside a runtime expression is already covered by the
  boundary's syntax recursion — verify with rows).
- Terminal flags: a runtime-panicking value is a KNOWN panic → the existing computed-flag/short-circuit
  machinery (denote_expr's bool) carries it; args/statements after it are gate-checked-not-denoted.

## Review-lesson checklist (apply from the start)
- Every new fold's upstream GATE rejection becomes load-bearing — probe nested/empty shapes at ptype
  level FIRST (the goty_supported episode).
- Class claims = gated ∀-theorems sealed to the gate's boundary; fixtures are witnesses.
- Quarantine valid-but-rejected in the ledger per surface; invalid companions in bad_programs.
- Witness succession (rule; the CURRENT witness state lives in the post-R1 section below and in GoSem's
  pinned `undenoted_frontier`): folding a form kills its supported-but-undenoted witnesses — swap
  successors in the SAME commit; a totality claim for any fragment needs a THEOREM.
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
  **R3** width conversions of runtime ints via the model wraps.
- `denote_expr` consumes `reval_int` (RVal → `CRet (anyt TInt64 v), false`; RPanic → `CPan p, true`);
  the computed-flag/short-circuit machinery carries panics unchanged. The `floats_checked` boundary stays
  at `eval_value`; `reval_int`'s constant leaf goes THROUGH `eval_value` (boundary preserved).
- Witness succession — CURRENT STATE (post-R2): `runlen_e`, `runidx_e`, the OOB constant index, and
  panicking-element constructions all DENOTE; the pinned `undenoted_frontier` WITNESSES
  (non-exhaustive) are `runconv_e` (a runtime width conversion — R3), a runtime bool COMPARISON (no
  rule yet), `maplen_runval_e` (map-value rule), and the multi-byte rune. Each tier that lands FLIPS
  its member's pin — swap the successor in the same commit. NOTE: `folded_arg` (né `denotable_arg`) is
  the EVAL-ONLY sufficient fragment; the runtime tier's own converse — and any THEOREM bounding the
  gap — is open work.
