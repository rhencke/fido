# The TYPED-runtime tier — non-GTInt runtime CARRIER OPERATIONS (the named next arc)

**Goal.** Operations on non-GTInt runtime carriers denote: `^int64(len ..)`, typed same-width
arithmetic/bitwise (`int64(x) + int64(y)`), typed comparisons, HETEROGENEOUS shifts (see T5), and
conversion CHAINS through a non-GTInt intermediate (`int64(uint8(len ..))`). All currently supported-but-undenoted, pinned:
`typed_unary_holes_absent` (now the GoUint/narrow-neg holes), `typed_runtime_convchain_absent` (the chain),
`typed_runtime_shift_absent` (the five-case shift SHAPE table), representative `runnot_uint_e` in
`undenoted_frontier`. Conversion EXITS **from GTInt operands** already
denote (`denote_expr_conv_*` — `reval_int a` is a hypothesis, so non-GTInt sources are outside it).

## Design (decided; implement in slices)

- **The shared evaluator becomes the fixpoint.** `reval_val_with (rec)` turns into `fix rv e` so the
  typed arms evaluate their operands at FULL power (`rv a` on strict subterms — the guard accepts
  pattern-bound subterm recursion; the `rconstr_vals_with (reval_val_with reval_int)` precedent).
  `rexit_with` takes the fixpoint (`rv`) as a parameter (landed with T1); the R3 conversion arm STILL
  uses `rec a` (GTInt sources) — generalizing it to `rv a` is T2, the point where conversion CHAINS
  close (they are pinned absent until then).
  ⚠ This reshapes `denote_expr`'s unfolding: every conv/cmp class-lemma proof that `unfold rexit_with`
  needs the same mechanical rework as the shared-evaluator refactor (assert the sub-result, then the
  wrapper steps).
- **Typed dispatch tables, pinned TOTAL + QUALIFIED from the first commit** (the
  `cmp_verdict_complete` lesson): `typed_unop : UnaryOp -> GoTy -> GoAny -> option GoAny` and
  `typed_binop : BinOp -> GoTy -> GoAny -> GoAny -> option <result>` matching on `(t, tag)` convoys
  (the `unbox_int` pattern per width, local to each arm). Every branch equated against the fully
  qualified `Fido.builtins.*` op; every hole an explicit `None` covered by the all-constructor case
  theorem.
- **Slices.** T1 unary — LANDED (`typed_unop`, the `EUn` arm in `rexit_with`, the evaluator fixpoint;
  live branches + holes pinned; class lemmas `denote_expr_typed_unop_{runs,panic}`). The WELL-TAGGEDNESS
  invariant is PROVEN (`reval_val_typed`, on `ptype_int_ok` — every classifier `PtRunInt`/`PtTIntConst`
  carries an int width) and the public theorem is SEALED (`denote_expr_typed_unop_runs_sealed` — no
  caller-side dispatch premise); all typed-unary holes pinned eight-wide (`typed_unary_holes_absent`). T2 conversion chains (the generalized R3 arm — `rv` sources). T3 same-width
  arithmetic/bitwise (`*_add/sub/mul/div/mod/and/or/xor/andnot` — div/mod evidence-carrying with
  `rt_div_zero` on a zero divisor, the `int_div` convoy per width). T4 typed comparisons
  (`*_eqb/ltb/leb` + the negation/swap derivations, per width). T5 SHIFTS — ⚠ NOT same-width binops:
  Go's shift is HETEROGENEOUS (`ptype`'s own `BShl|BShr` arm: the LEFT operand fixes the result width;
  the COUNT is an INDEPENDENT integer of any width, nonnegative — a signed negative count PANICS).
  A separate `typed_shift` dispatcher/evaluator: left operand at its width via `rv`, count evaluated
  independently (any integer runtime/const form), admissibility derived from `ptype`, never a caller
  promise; the model ops are heterogeneous too (small widths take `GoInt` counts, `i64/u64` raw `Z` —
  reconcile per width at the dispatch, fail-closed on any unmodelled pairing).  The five-case shift SHAPE table is
  pinned NOW (`typed_runtime_shift_absent` + `shift_case_shape` — both ops, a non-GTInt count,
  i64/u64 lefts, structurally checked) so the slice cannot silently land narrow.
- **Per-slice update obligations** (the standing rule): each landing flips its pins across the five
  recurring witness sites (`undenoted_frontier`, the out-boundary example, GoSemSafe's absent pair,
  the dead-tail escape, the arg-panic short-circuit trio) + class lemmas sealed to `ptype` (no
  caller-side totality premises) + non-identity pins (wrap/sign witnesses) in ONE commit, with a
  repo-wide stale-claim sweep.

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
