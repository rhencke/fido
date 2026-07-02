# Float constants go DYADIC — COMPLETED (c675f5f + the sealing follow-up); one stated obligation remains

**Landed.** `PtFloatConst t d` carries a SEALED exact dyadic (`DyConst`: `m * 2^e`, the normalization
witnessed by a proof field in the image-of-`dy_norm` style of `builtins.mkF32` — an unnormalized payload
is unconstructable, so the `dy_div`-misbehaving states are impossible). Exact-or-reject arithmetic
(`+ - * /`, negation, conversions incl. cross-width; rounding cases quarantined in
`valid_unsupported_programs` with closed zero-divisor companions in `bad_programs` for BOTH widths and a
folded-zero divisor). `box_float` renders the dyadic directly (`sf_of_dyadic` = the `S754_finite` shape).

**The agreement discipline (live, not fixture prose).** Every float-const fold reaches denotation ONLY
through `float_fold_checked`/`float_neg_checked` — a per-instance guard comparing the folded value with
the MODEL's own `f64_*`/`f32_*` op on the boxed operands. The gated theorems
`float_fold_checked_agrees_{f64,f32}` / `float_neg_checked_agrees_{f64,f32}` prove every ACCEPTED fold IS
the model-op value (both widths; f32 at the observable `f32val` carrier). So the accepted fold surface is
the verified-agreement surface BY CONSTRUCTION; a disagreeing instance would be absent, never wrong.

**Remaining obligation (PROGRESS NEXT).** Prove the GENERAL dyadic↔`SF*` agreement class theorem
(exactly-representable operands and result ⟹ the model op returns the exact dyadic) — then the runtime
guard can be DROPPED as redundant. Until then the guard is the seal.

**Out of scope (separate future arcs).** Decimal float LITERALS (`EFloat` in GoAst — needs printer/lexer
round-trip work; non-dyadic decimals like `0.1` stay unrepresentable). A correctly-ROUNDING const model
(would graduate the quarantined `float64(1)/float64(3)` / cross-width rounding cases).
