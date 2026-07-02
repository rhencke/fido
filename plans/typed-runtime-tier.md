# The TYPED-runtime tier — non-GTInt runtime CARRIER OPERATIONS (the named next arc)

**Goal.** Operations on non-GTInt runtime carriers denote: `^int64(len ..)`, typed same-width
arithmetic (`int64(x) + int64(y)`), typed comparisons — currently supported-but-undenoted (pinned:
`typed_runtime_not_absent`; representative `runnot_u8_e` in `undenoted_frontier`). Typed conversion
EXITS already denote (`denote_expr_conv_*` — values, not operations).

## Design (decided; implement in slices)

- **The shared evaluator becomes the fixpoint.** `reval_val_with (rec)` turns into `fix rv e` so the
  typed arms can evaluate their operands at FULL power (`rv a` on strict subterms — the guard accepts
  pattern-bound subterm recursion; the `rconstr_vals_with (reval_val_with reval_int)` precedent).
  `rexit_with` folds INTO the fixpoint (its R3/R4 arms keep consulting `rec` — GTInt sources only).
  ⚠ This reshapes `denote_expr`'s unfolding: every conv/cmp class-lemma proof that `unfold rexit_with`
  needs the same mechanical rework as the shared-evaluator refactor (assert the sub-result, then the
  wrapper steps).
- **Typed unary slice (T1).** New arm in the fixpoint: `EUn o a` with `ptype e = Some (PtRunInt t)`,
  `t ≠ GTInt` (the GTInt case stays in `reval_int`): evaluate `rv a`, unbox at `t`'s tag, apply the
  width's MODEL op, rebox. Dispatch `typed_unop : UnaryOp -> GoTy -> GoAny -> option GoAny` — pin the
  WHOLE table (the `cmp_verdict_complete` pattern: fully qualified `Fido.builtins.*`, all-constructor
  case theorem). Coverage: `^` via `u8_not/i8_not/u16_not/i16_not/u32_not/i32_not/i64_not/u64_not`
  (ALL 8 fixed widths exist); `-` via `i64_neg/u64_neg` ONLY. HOLES (fail-closed → absent + witness):
  `-` on u8..i32 (no model ops), both ops on `GTUint` (GoUint has NO not/neg — model them first or
  stay absent with a pinned witness).
- **Typed same-width arithmetic (T2).** `EBn` arm for `PtRunInt t`, `t ≠ GTInt`: operands via `rv`,
  unbox both at `t`, the width's `*_add/sub/mul/...` model ops. Inventory is PATCHY (u8/i8/i64/u64 adds
  confirmed; div/rem evidence-carrying only for some) — every hole is absent + quarantined, never an
  improvised wrap. Dispatch table pinned total, like `cmp_verdict_complete`.
- **Typed comparisons (T3).** The R4 exit generalizes: operands at width `t` via `rv` + the width's
  `*_eqb/ltb/leb` (holes: several widths lack ltb/leb — absent until modelled).
- **Unbox/rebox authority.** One `unbox_at (t : GoTy) (g : GoAny) : option <carrier>`-style helper per
  width is NOT scalable as 10 functions × proofs; instead a single `typed_unop`/`typed_binop` matching
  on `(t, tag)` pairs directly (GoAny's existT tag convoy — the `unbox_int` pattern per width, local
  to each dispatch arm). Keep the dispatch total-pinned so drift breaks the gate.
- **Witness succession on each slice.** T1 flips `runnot_u8_e`/`typed_runtime_not_absent` members that
  gain denotation (u8 ✓ i64 ✓; `^uint(..)` stays absent unless `uint_not` is modelled — it then needs a
  fresh witness + the five-site sweep). Class lemmas per slice in `gosem_trust_surface`, sealed to the
  gate boundary (derive is_int_goty/width facts from `ptype`, no caller-side totality premises), pins
  at non-identity values (the wrap/sign witnesses), repo-wide stale-claim sweep in the SAME commit.

## Op inventory (surveyed 2026-07-02)

| op | int | i64 | u64 | u8 | i8 | u16 | i16 | u32 | i32 | uint |
|----|-----|-----|-----|----|----|-----|-----|-----|-----|------|
| not | int_not | i64_not | u64_not | u8_not | i8_not | u16_not | i16_not | u32_not | i32_not | — |
| neg | int_neg | i64_neg | u64_neg | — | — | — | — | — | — | — |
| add/sub/mul | int_* | i64_* | u64_* | u8_* | i8_* | (check) | (check) | (check) | (check) | — |
| eqb/ltb/leb | int_* | i64_eqb/ltb | u64_eqb | u8_eqb | (check) | (check) | (check) | (check) | (check) | — |

(— = no model op: absent + quarantined witness until modelled as a Definition; never approximate.)

## Not this arc
Runtime floats (the dyadic↔SF* agreement theorem first); `!` of runtime bool comparisons (needs a
runtime bool carrier rule); mixed-width anything (Go rejects it — ptype already does).
