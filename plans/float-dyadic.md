# Float constants go DYADIC — COMPLETED (c675f5f + the sealing follow-up); one stated obligation remains

**Landed.** `PtFloatConst t d` carries a SEALED exact dyadic (`DyConst`: `m * 2^e`, the normalization
witnessed by a proof field in the image-of-`dy_norm` style of `builtins.mkF32` — an unnormalized payload
is unconstructable, so the `dy_div`-misbehaving states are impossible). Exact-or-reject arithmetic
(`+ - * /`, negation, conversions incl. cross-width; rounding cases quarantined in
`valid_unsupported_programs` with closed zero-divisor companions in `bad_programs` for BOTH widths and a
folded-zero divisor). `box_float` renders the dyadic directly (`sf_of_dyadic` = the `S754_finite` shape).

**The agreement discipline (live, single-authority).** Every float-constant denotation goes through
`fsf_checked` — the ONE recursive checker (`eval_value_ptype`'s `PtFloatConst` arm boxes only when it
accepts; `eval_value` and `map_entries_evaluable` box only through `eval_value_ptype`) that re-verifies
EVERY fold at any depth (binops, negation, same/cross-width conversions — so a fold nested under
`float64(..)` or inside a map value cannot bypass it) against the MODEL's own `f64_*`/`f32_*`/`SFopp`/
`f32_of_f64`/`f64_of_f32` ops. The gated theorems `fsf_checked_{binop,neg,conv_same,conv_narrow,
conv_widen}_agrees` prove every ACCEPTED node is the model-op value. Accepted surface = verified surface
by construction; a disagreeing instance would be absent, never wrong.

**Remaining obligation (PROGRESS NEXT).** Prove the GENERAL dyadic↔`SF*` agreement class theorem
(exactly-representable operands and result ⟹ the model op returns the exact dyadic) — then the runtime
guard can be DROPPED as redundant. Until then the guard is the seal.

**Out of scope (separate future arcs).** Decimal float LITERALS (`EFloat` in GoAst — needs printer/lexer
round-trip work; non-dyadic decimals like `0.1` stay unrepresentable). A correctly-ROUNDING const model
(would graduate the quarantined `float64(1)/float64(3)` / cross-width rounding cases).
