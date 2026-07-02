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
   through `binary_round_aux`) ⇒ `sf_render_neg_general_f64`: for `m ≠ 0`,
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
4. **`binary_normalize` VALUE-determinism — LANDED** (windowed; gated
   `binary_normalize_norm_determined`): `dy_norm`-equal representations normalize to the SAME
   canonical float.  NO doubling induction was needed: with rung 3, both sides reduce to
   closed canonical forms, digits+exponent is invariant under the odd-core split
   (`pos_odd_split_digits`), so the `fexp` targets coincide and the aligned mantissas are
   value-equal positives (`binary_round_of_norm`).  ⚠ rung 5 will ADDITIONALLY need
   right-shift-through-zeros exactness for wide-exponent-gap sums (the RAW aligned sum's
   digits can exceed `prec` even when its odd core is in-window — e.g. `1·2^0 + 1·2^-100`;
   `ptype` REJECTS such results at the repr guard, but `SFadd`'s internal path must still be
   shown to agree wherever the gate accepts).
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

- The `-0` divergence (rung 1) is REAL and handled STRUCTURALLY: the checker verifies FOLDS, so
  every verification op routes through the constant layer (`sf_const_binop`/`sf_const_neg` —
  `sf_pos_zero`); raw `SF*` zero signs belong to runtime paths only.  ADD/SUB zero rows agree
  even unerased FOR CONSTANT-RENDERED OPERANDS (dyadic renders carry no `-0`, and an exact-zero
  sum of finite operands gets `+0` at round-to-nearest — NOT a claim about arbitrary raw
  `SFadd/SFsub` signed-zero inputs) — the erasure is uniform anyway, no per-op case analysis.  Each rung states its zero/sign side
  conditions explicitly, go-run-verified.
- Window premises apply to OPERANDS (exactness of their renders); the RESULT needs none for
  determinism-based rungs (both sides round the same value) but `ptype`'s fold guard
  (`float_dyadic_repr`) keeps results exact anyway.
