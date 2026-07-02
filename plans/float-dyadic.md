# Float constants go DYADIC — `PtFloatConst` carries a real float value (PROGRESS NEXT bullet 1)

**Why now / why this.** `PtFloatConst (t, z : Z)` carries an INTEGER, so (a) every float-CONSTANT
arithmetic op is ptype-REJECTED (`num_arith`'s last arm — even `float64(3)+float64(2)`, valid Go), and
(b) fractional values are uncarryable (`float64(3)/float64(2)` = 1.5). The bridge-to-chan/heap/spawn
NEXT bullet would land AHEAD of the AST (no send/recv/spawn statements exist) — premature by the
cleanup tenet — so floats are the right next foundation: single-layer (GoTypes+GoSem+GoSafe),
zero golden risk, closes real valid-Go incompleteness.

**Posture: exact-or-reject.** Dyadic value = `m * 2^e` (`m e : Z`, normalized: `m = 0 -> e = 0`, else
`m` odd). Go rounds typed float const ops to the type at each op; when the exact result IS representable,
IEEE correct rounding returns it exactly — so folding exactly and REJECTING non-representable results
(`1.0/3.0`) is faithful-or-absent, never wrong. Non-dyadic decimals (0.1) stay unrepresentable (no AST
change in this arc — `EFloat` is a separate, later arc needing printer/lexer round-trip work).

## Slices

- **FD1 — dyadic core (GoTypes; Definitions only, no-theorems policy holds).**
  `dy_norm : Z -> Z -> Z*Z` (strip 2-factors via `Z.abs_nat m` fuel), `dy_add/dy_sub/dy_mul/dy_neg`
  (always exact), `dy_div : ... -> option (Z*Z)` (exact iff odd(m2) | m1; None otherwise; zero divisor
  handled by the existing `is_zero_const` guard), `float_dyadic_repr t m e : bool` (normalized `|m| <
  2^53`/`2^24` + a CONSERVATIVE exponent window inside the always-exact finite range — under-acceptance
  is fail-loud-safe, over-acceptance is not).
- **FD2 — `PtFloatConst t m e` payload swap + consumers.**
  Int→float conv: `(z, 0)` normalized (subsumes `int_in_float_exact_interval` for the const path — keep
  it for `PtRunFloat`+int mixes). Float→int conv: integer-valued iff `e >= 0` → `m * 2^e`, repr-checked
  (faithful: Go requires an integer value). `EUn` negation → `dy_neg`. `is_zero_const` → `m =? 0`.
  `num_arith` learns float-const arms — parametrize with a dyadic fold alongside the `Z` fold (int-only
  ops pass a rejecting dfold): const∘const same-type → fold + `float_dyadic_repr`-check; const∘PtRunFloat
  same-type → `PtRunFloat`; PtIntConst mixes as `(z,0)`. `BDiv` float path via `dy_div`.
- **FD3 — GoSem `box_float t m e`.**
  The exact `spec_float` of `m * 2^e` (the S754_finite form of (sign m, |m|, e), renorm'd — check
  builtins' `sf_of_Z`/`renorm 53 1024`/`f32_lit` shapes); `eval_value_ptype` passes the payload through.
- **FD4 — fixtures.**
  eval rows: `float64(3)/float64(2)` → the model's exact 1.5 (+ float32 variant, add/sub/mul rows);
  new `rc_float_frac` category field (runs end-to-end through `run_cmd`).
  Fail-closed: `float64(1)/float64(3)` ptype-REJECTED (⚠ VALID Go that rounds — goes in
  `valid_unsupported_programs` with future path "graduates only with a correctly-rounding const model",
  its invalid companion = the existing const-zero-divisor row); width split (a value exact in float64,
  inexact in float32); overflow/underflow bounds outside `float_dyadic_repr`'s window.
- **FD5 — the SEAL (the hard proof; required before any headline claim).**
  ptype's dyadic fold must provably AGREE with the MODEL's spec_float arithmetic on the exact cases:
  `box_float` of `dy_add d1 d2` = the model's float-add of the boxed operands (and mul/div analogues) —
  else the folded constant and the emitted program's runtime arithmetic could diverge
  (plausible-but-wrong, the divisor_zero_eval precedent says Codex will demand this seal). If the
  general lemma is out of reach in one tick, pin per-op agreement on the fixture set FIRST (grouped,
  gated) and state the general seal as the class theorem to prove NEXT — never ship the fold ungated.

## Review-lesson checklist (apply from the start, not after the bounce)
- Class claims as gated ∀-theorems, fixtures only as witnesses.
- Valid-but-rejected (rounding cases) → `valid_unsupported_programs` with per-class future path +
  invalid companion; invalid Go (const zero divisor) stays in `bad_programs`.
- Any new gate condition the fold relies on (repr window) must be probed AT THE GATE (ptype=None ⇒
  unsupported ⇒ never emitted) incl. nested/empty shapes.
- One spelling per fixture expression; genericize doc enumerations; PROGRESS ≤150.
