# The RUNTIME-value tier (B3 / ARCHITECTURE Phase 5 "eval non-literals") — the next foundation arc

**Why.** The sole remaining supported-but-undenoted source is runtime-CLASSIFIED value forms (`len` over
runtime elements/values, `int(x)` of runtime `x`, runtime slice indexing). In the CLOSED world these are
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
- Witness succession: folding a form kills its supported-but-undenoted witnesses (runlen_e,
  maplen_runval_e, out_runtime_prog, the shortcircuit fixtures' undenoted pieces, converse-escape) — swap
  successors in the SAME commit. After this arc the undenoted frontier may be EMPTY for the output
  fragment → the completeness converse may become total on it (a major claim — state it only with the
  theorem).
- Exact panic MESSAGES verified against real Go before modeling.
- Grep-verify batch edits before committing.

## Not this arc
Heap/chan/spawn denotation (needs AST statements first); the general dyadic↔SF* theorem; EFloat literals.
