# The general dyadic↔SF* agreement arc

GOAL (the frontier stated at `GoSem.v` `fsf_checked`'s header): prove ONCE that the gate's exact
dyadic folds agree with the model's `SF*` ops on the admitted class, so `fsf_checked`'s per-node
runtime re-verification (`sf_eqb_struct (f va vb) vr`) is provably total there — a CLASS theorem
replacing a per-expression check.  Everything is Z/positive arithmetic on `SpecFloat`'s own
definitions (`binary_round`/`shl_align`/`shr_fexp`) — NO Flocq, NO real-number semantics; the
value quotient is `dy_norm` (the odd-mantissa normal form), never ℝ.

## The two structural facts that make it tractable

- `sf_render GTFloat64 m e = Some (binary_normalize 53 1024 m e false)` — uniform in `m`
  (`sf_of_dyadic` + `renorm` compose to exactly `binary_normalize`, zero included).
- `SFadd`'s finite arm is `binary_normalize (EXACT aligned sum) (min exponent)` — SpecFloat
  aligns with exact left shifts (`shl_align`) and normalizes the exact integer sum.  `SFmul`'s
  arm is `binary_round` of the exact product.  So fold↔op agreement = "`binary_normalize` is
  VALUE-determined and EXACT in the `float_dyadic_repr` window".

## The ladder (each rung an independently green commit)

1. **NEG (f64) — LANDED with this plan**: `binary_round_opp` (the sign argument threads inertly
   through `binary_round_aux`) + `renorm_opp` ⇒ `sf_render_neg_general_f64`: for `m ≠ 0`,
   `sf_render GTFloat64 (-m) e = option_map SFopp (sf_render GTFloat64 m e)` — NO window premise.
   Plus the **signed-zero divergence pinned**: Go constants are exact rationals (NO `-0`) — gc
   folds `-(0.0)` to `+0` (go-run-verified `1/x = +Inf`) while the runtime op `SFopp` gives `-0`
   (`1/-z = -Inf`); the fold is the faithful side, the checker rejects the node
   (faithful-or-absent), pinned in `undenoted_frontier` (`negzero_const_e`).
2. **`shl_align` spec**: `T <= e -> shl_align m e T = (m * 2^(e-T), T)` (positive shift lemma).
3. **`binary_round` EXACTNESS in-window**: for odd `|m|` with the `float_dyadic_repr t m e`
   window, `binary_round s m e` returns the canonical finite with `dy_norm`-equal value
   (`shr_fexp` at `loc_Exact` on an aligned in-window mantissa is a no-op; `round_nearest_even`
   at `loc_Exact` is identity).  Corollary: `renorm` idempotence on canonical forms (unblocks
   the f32 row — `f32_neg` re-rounds through `f32_of_f64`).
4. **`binary_normalize` VALUE-determinism**: `dy_norm (m1,e1) = dy_norm (m2,e2) ->
   binary_normalize m1 e1 s = binary_normalize m2 e2 s` — via the one-step doubling lemma
   (`binary_round s m e = binary_round s (2m) (e-1)`: `digits2_pos` shifts by one, `fexp`
   target unchanged, `shl_align` lands on the same pair) + induction on the exponent gap.
5. **ADD/SUB (f64)**: `dy_add` is the exact sum at the min exponent (GoTypes-side value lemmas),
   `SFadd`'s aligned sum is the same value ⇒ rungs 3+4 close
   `sf_render (dy_add da db) = f64_add (render da) (render db)` under operand windows.
6. **MUL, then exact DIV** (f64): same shape (`SFmul` = `binary_round` of the exact product;
   `SFdiv` exact-quotient case via `dy_div`'s divisibility guard).
7. **The f32 row + cross-width conversions** (needs rung 3's idempotence for the `f32_round`
   wrappers; `f32_of_f64`/`f64_of_f32` agreement).
8. **The checker-completeness CLASS theorem**: on the admitted class `fsf_checked` ACCEPTS
   (never returns `None` by disagreement) — then decide whether the runtime re-check stays as
   defense-in-depth or is dropped (ARCHITECTURE call; dropping shrinks eval).

## Boundary honesty

- The `-0` divergence (rung 1) is REAL and stays: constant folding (exact rationals) and the
  runtime IEEE op genuinely differ at zero under negation; `x - x` shapes can hit it for
  ADD/SUB too (`0 - 0` folds `+0`; runtime `SFadd +0 -0 = +0` round-to-nearest — re-verify per
  rung).  Each rung states its zero/sign side conditions explicitly, go-run-verified.
- Window premises apply to OPERANDS (exactness of their renders); the RESULT needs none for
  determinism-based rungs (both sides round the same value) but `ptype`'s fold guard
  (`float_dyadic_repr`) keeps results exact anyway.
