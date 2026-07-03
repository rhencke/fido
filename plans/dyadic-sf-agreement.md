# The general dyadic↔SF* agreement arc

GOAL (the frontier stated at `GoSemCore.v` `fsf_checked`'s header): prove ONCE that the gate's
exact dyadic folds agree with the CONSTANT-op layer — `sf_const_binop`/`sf_const_neg`, the
checker's own verification ops (`sf_pos_zero` zero-sign erasure over the raw `SF*` model ops;
Go constants are exact rationals with no `-0`) — on the admitted class, so `fsf_checked`'s
per-node runtime re-verification (`sf_eqb_struct (f va vb) vr`) is provably total there — a
CLASS theorem replacing a per-expression check.  Where the raw op cannot sign a zero on
rendered operands the endpoint is stated RAW (`f64_add`/`f64_sub`, rung 5); where it can
(MUL's zero rows) the endpoint IS the erased layer (rung 6).  Everything is Z/positive
arithmetic on `SpecFloat`'s own
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

1. **NEG (f64) — LANDED with this plan**: `binary_normalize_opp` (THE one normalizer sign-flip
   authority, both widths; the sign threads inertly through `binary_round_aux` — the builtins
   ingredient `binary_round_opp` is consumed only inside it) ⇒ `sf_render_neg_general_f64`: for `m ≠ 0`,
   `sf_render GTFloat64 (-m) e = option_map SFopp (sf_render GTFloat64 m e)` — NO window premise.
   Plus **signed zero made EXACT at the checker for ALL const ops** (review rounds 2–3): Go
   constants are exact rationals (NO `-0`); the checker's verification ops are the CONSTANT-fold
   layer `sf_const_binop`/`sf_const_neg` — `sf_pos_zero` zero-sign erasure over the width's IEEE
   table (`SFmul +0 -1 = -0`, `SFdiv +0 -1 = -0`, `SFopp +0 = -0` are RUNTIME zero signs) — so
   `-(float64(0))`, `float64(0) * -float64(1)`, `float64(0) / -float64(1)`,
   `-(float64(0) * -float64(1))` and the f32 analogs all fold and DENOTE `+0` — pinned BY
   CONSTRUCTOR (`negzero_const_runs` + `signed_zero_folds_{eval,run}`) with the model-level
   reciprocal probe decisive (`reciprocal_sign_decisive`: model `1/+0 = +Inf`, `1/-0 = -Inf`,
   both widths); layer laws `sf_const_{binop,neg}_zero_erased`; ground-truthed against gc via
   go run during development (`1/x = +Inf` ×6, runtime contrast `-Inf`).  The neg ARM's
   zero row is `fsf_checked_neg_zero_total` (operand-acceptance premised — FULL class totality is
   rung 8, after rung 3's finite-render lemma; `fsf_checked_render` anchors it).
2. **`shl_align` spec — LANDED** (builtins): `digits2_pos_iter_xO`/`iter_xO_val` (exact left
   shifts add digits one-for-one and multiply by `2^d`), `shl_align_snd`/`shl_align_digits`
   (digits+exponent is SHIFT-INVARIANT)/`shl_align_fst_val` (value preserved).
3. **`binary_round` EXACTNESS in-window — LANDED** (builtins + GoSem, gated via
   `gosem_float_surface`), all three obligations:
   (a) the core `binary_round_exact` — for `digits2_pos m <= prec`, `emin <= e`,
   `digits+e <= emax`, `binary_round s m e` IS the canonical finite (the shifted mantissa at
   the `fexp` target), no rounding/underflow/overflow: both `shr_fexp` passes are ZERO shifts
   at `loc_Exact`; with `shl_align_fst_val` the value is exact.
   (b) the LIVE-BOUNDARY BRIDGE: every `PtFloatConst` construction site in `ptype` is
   repr-GUARDED (the two formerly-unguarded sites — UNeg reseal, int-interval conversion — now
   guard too; the guards never fire, defense-in-depth), giving the structural invariant
   `ptype_float_const_repr` and the gated endpoints `ptype_float_payload_{f64,f32}` (every
   ACCEPTED payload is ZERO or satisfies the exactness premises — the zero/nonzero split over
   `ptype` itself) + `box_float_gate` on the value path.  `sf_render` is RAW (renders anything);
   exactness on accepted payloads comes from the invariant, never from `sf_render`.
   (c) `renorm_binary_round_idem` — renorm idempotence on the in-window class (the output's
   digits+exponent reproduces the `fexp` target; re-alignment is `shl_align_id`), unblocking
   the f32 wrappers (`f32_neg` re-rounds through `f32_of_f64`).
4. **`binary_normalize` VALUE-determinism — LANDED** (gated
   `binary_normalize_wide_determined`): `dy_norm`-equal representations normalize to the SAME
   canonical float; window premises on the SHARED NORMAL FORM only, raw-side digits UNBOUNDED
   (via `binary_round_of_norm_wide`).  NO doubling induction: both sides reduce to closed
   canonical forms, digits+exponent is invariant under the odd-core split
   (`pos_odd_split_digits`), so the `fexp` targets coincide (`binary_round_of_norm`).
5. **ADD/SUB (f64) — CLOSED at binary64.**
   `dy_add` is the exact sum at the min exponent (GoTypes-side value lemmas); `SFadd`
   normalizes the RAW aligned sum, whose mantissa can exceed `prec` digits even for
   gate-ACCEPTED results — the CARRY shape `(2^53-1)+(2^53-1)`: raw sum `2^54-2` (54 digits),
   normalized `(2^53-1, 1)` accepted; mechanically pinned `add_carry_raw_wide_accepted`
   (which also computes the checker accepting end-to-end).  `ptype` guards only the NORMALIZED
   fold result, never the raw mantissa — and that gap is exactly what the LANDED bridge
   covers: 5a `iter_pos_shr1_zeros` (the zeros walk keeps round/sticky FALSE) and 5b
   `binary_round_of_norm_wide` (gated) — `binary_round` on a RAW mantissa whose ODD CORE is
   in-window equals `binary_round` of the core at the adjusted exponent, raw digits UNBOUNDED
   (the target-at-or-below-raw-exponent regime reduces to rung 4's `binary_round_of_norm`
   with DERIVED premises; the other regime consumes the appended zeros via 5a).
   ★ ADD at binary64 CLOSED (gated `sf_render_add_agrees_f64`): on the gate's windows —
   operands AND result — the LIVE render of `dy_add`'s exact fold IS the model's `f64_add` of
   the operands' renders, every shape (zero rows, cancellation, the raw-wide carry class).
   The assembly: `sf_render_signed_value_f64` (signed difference-form operand
   characterization) + `cond_Zopp_mul` value algebra identify `SFadd`'s raw aligned sum with
   the fold (`f64_add_finite_agrees`), the zero rows collapse via `dy_norm_value_unique`
   (`f64_add_zero_{left,right}_f64`), and `normalize_result_agrees_f64` (idempotence + wide
   determinism under the result's window) is the uniform endgame.
   SUB CLOSED too (gated `sf_render_sub_agrees_f64`): `SFsub_as_add_opp` (row-by-row, the
   finite arm by `Z.sub`-is-`add∘opp` conversion) + `bn_opp_f64` (rung 1 at the normalizer)
   transport the ADD closure through `dy_sub = dy_add ∘ dy_neg`; a zero subtrahend's `-0` is
   absorbed by `SFadd`'s sign-blind zero rows.
6. **MUL + exact DIV (f64) — CLOSED.**
   MUL CLOSED (gated `sf_render_mul_agrees_f64`, ⚠ a CONST-LAYER endpoint — `sf_pos_zero` of
   `f64_mul`, exactly `sf_const_binop`'s `BMul` row): IEEE `(+0)*(negative) = -0` is a
   runtime-only zero sign, so the ADD/SUB raw-op statement is FALSE on MUL's zero rows.
   `SFmul`'s finite arm is `binary_round_aux` on the RAW product of the canonical mantissas;
   `binary_round_aux_of_round` + `digits2_pos_mul_lower` (the fexp target never sits below
   the sum exponent for canonical renders — normal case ≥105 digits, emin cases by the
   window bounds) rewrite it to `binary_round`, `render_canonical_f64` (the render's
   digits+exponent IS the fexp fixpoint, via `shl_align_digits`) + `cond_Zopp_xorb_mul`
   align the product value to the fold, and `normalize_result_agrees_f64` closes.
   exact DIV CLOSED too (gated `sf_render_div_agrees_f64`, const-layer): `SFdiv_core_binary`
   scales the dividend to `s = (T1-T2) - e'` and divides; on `dy_div`-accepted folds the
   division is EXACT — the divisibility transports through the canonical shifts with the
   2-power margin `e' <= er` (NOT `e' <= e1-e2`, which can fail; the margin comes from the
   fexp arm of the min via the quotient digit bookkeeping `digits2_pos_shift`/`mul_upper`),
   the remainder is 0 (`div_eucl_exact`), the location `loc_Exact`, and the raw quotient IS
   the result mantissa shifted by `er - e'` — the signed value recovered by CANCELLATION
   (no sign case analysis), then the same aux→round→wide endgame as MUL.
7. **The f32 row + cross-width conversions — IN PROGRESS.**  The assembly kit is now
   PRECISION-GENERIC (`render_signed_value_gen`/`render_canonical_gen`/
   `normalize_result_agrees_gen`, the f64 lemmas thin wrappers) with the binary32 instances
   + `repr_window_split_f32` + the generic `binary_normalize_opp` landed.  ★ ADD at binary32 CLOSED (gated
   `sf_render_add_agrees_f32`, over the checker's OWN composite `f32val ∘ f32_add ∘ f32_lit`):
   the whole ADD stack went PRECISION-GENERIC (`SFadd_normalize_agrees_gen` + zero/finite
   sublemmas over split windows; the f64 endpoint is now an instance), the f32 render is the
   binary32 normalizer (`sf_render_f32_eq`), and `f32_round` is the IDENTITY on windowed
   renders (`f32_round_render_id` — rung 3c's idempotence peels the ops' outer re-round).
   REMAINING: SUB/MUL/DIV at binary32 (same recipe: genericize or instantiate the cores),
   and the `f32_of_f64`/`f64_of_f32` cross-width agreement.
8. **The checker-completeness CLASS theorem**: on the admitted class `fsf_checked` ACCEPTS
   (never returns `None` by disagreement) — then decide whether the runtime re-check stays as
   defense-in-depth or is dropped (ARCHITECTURE call; dropping shrinks eval).

## Boundary honesty

- The `-0` divergence (rung 1) is REAL and handled STRUCTURALLY: the checker verifies FOLDS, so
  every verification op routes through the constant layer (`sf_const_binop`/`sf_const_neg` —
  `sf_pos_zero`); raw `SF*` zero signs belong to runtime paths only.  ADD/SUB zero rows agree
  even unerased FOR CONSTANT-RENDERED OPERANDS (dyadic renders carry no `-0`, and an exact-zero
  sum of finite operands gets `+0` at round-to-nearest — NOT a claim about arbitrary raw
  `SFadd/SFsub` signed-zero inputs) — the erasure is uniform anyway, no per-op case analysis.  Each rung states its zero/sign side
  conditions explicitly, go-run-verified.
- Window premises apply to the NORMALIZER INPUTS on each side of an equation.  `SFadd`'s raw
  aligned sum is such an input and can be OUT-of-window even for accepted results (the rung-5
  carry shape) — the raw-normalization bridge covers exactly that gap.  `ptype`'s fold guard
  (`float_dyadic_repr`) constrains only the NORMALIZED fold result, nothing upstream of it.
