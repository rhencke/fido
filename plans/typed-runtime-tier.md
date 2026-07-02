# The TYPED-runtime tier — non-GTInt runtime CARRIER OPERATIONS (the named next arc)

**Goal.** Operations on non-GTInt runtime carriers denote: `^int64(len ..)`, typed same-width
arithmetic/bitwise/shifts (`int64(x) + int64(y)`), typed comparisons, and conversion CHAINS through a
non-GTInt intermediate (`int64(uint8(len ..))`). All currently supported-but-undenoted, pinned:
`typed_runtime_not_absent` (the `^` class, three-wide), `typed_runtime_convchain_absent` (the chain),
representative `runnot_u8_e` in `undenoted_frontier`. Conversion EXITS **from GTInt operands** already
denote (`denote_expr_conv_*` — `reval_int a` is a hypothesis, so non-GTInt sources are outside it).

## Design (decided; implement in slices)

- **The shared evaluator becomes the fixpoint.** `reval_val_with (rec)` turns into `fix rv e` so the
  typed arms evaluate their operands at FULL power (`rv a` on strict subterms — the guard accepts
  pattern-bound subterm recursion; the `rconstr_vals_with (reval_val_with reval_int)` precedent).
  `rexit_with` folds INTO the fixpoint; its R3 arm generalizes from `rec a` (GTInt sources) to `rv a`
  (any typed runtime source — closing the conversion-CHAIN class in the same stroke).
  ⚠ This reshapes `denote_expr`'s unfolding: every conv/cmp class-lemma proof that `unfold rexit_with`
  needs the same mechanical rework as the shared-evaluator refactor (assert the sub-result, then the
  wrapper steps).
- **Typed dispatch tables, pinned TOTAL + QUALIFIED from the first commit** (the
  `cmp_verdict_complete` lesson): `typed_unop : UnaryOp -> GoTy -> GoAny -> option GoAny` and
  `typed_binop : BinOp -> GoTy -> GoAny -> GoAny -> option <result>` matching on `(t, tag)` convoys
  (the `unbox_int` pattern per width, local to each arm). Every branch equated against the fully
  qualified `Fido.builtins.*` op; every hole an explicit `None` covered by the all-constructor case
  theorem.
- **Slices.** T1 unary (`^` all fixed widths via `*_not`; `-` via `i64_neg`/`u64_neg` only — see
  holes). T2 conversion chains (the generalized R3 arm — `rv` sources). T3 same-width
  arithmetic/bitwise/shifts (`*_add/sub/mul/div/mod/and/or/xor/andnot/shl/shr` — div/mod are
  evidence-carrying with `rt_div_zero` on a zero divisor, the `int_div` convoy per width; shifts carry
  their own negative-shift panics — probe the model's `*_shl/_shr` signatures before wiring). T4 typed
  comparisons (`*_eqb/ltb/leb` + the negation/swap derivations, per width).
- **Witness succession per slice** (the standing rule): each landing flips its pins + the five-site
  sweep + class lemmas sealed to `ptype` (no caller-side totality premises) + non-identity pins
  (wrap/sign witnesses) in ONE commit.

## Op inventory (grepped from builtins.v, 2026-07-02 — the CODE is the authority; this table is a
survey snapshot, re-grep before wiring each slice)

- **u8 / i8 / u16 / i16 / u32 / i32 / i64 / u64** (all eight fixed widths): `add sub mul div mod`,
  `eqb neqb ltb leb gtb geb`, `and or xor andnot shl shr`, `not` — COMPLETE for T1/T3/T4.
- **neg**: `i64_neg`, `u64_neg`, `int_neg` ONLY — unary `-` on u8..i32 has NO model op (Go's `-x`
  there = `0 - x` wrapped; if wanted, model `*_neg` as Definitions first — never compose silently).
- **int** (GTInt, the R1–R7 fragment): `add sub mul div mod eqb ltb leb neg not` — no
  bitwise/shift ops (runtime `&`/`|`/`^`/`<<`/`>>` on PLAIN int are ptype-supported yet absent: a
  future GTInt-fragment slice needs `int_and`... as model Definitions first).
- **uint** (platform GoUint): `lit` only — EVERY runtime uint operation is absent until modelled.

## Not this arc
Runtime floats (the dyadic↔SF* agreement theorem first); `!` of runtime bool comparisons (needs a
runtime bool carrier rule); mixed-width anything (Go rejects it — ptype already does).
