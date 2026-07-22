# ADR-0002 — Bounded DecimalFloat literal domain

- **Status:** PROPOSED — pending Rob. (Not accepted until Rob accepts it. The numeric model is NOT changed by
  the C4 repair that raised this; this ADR only records the decision to be made.)
- **Date:** 2026-07-22.
- **Scope ledger link:** `.review/UNSUPPORTED_AND_RESTRICTED_SCOPE.md` SR-009.
- **Source:** `Floats.v` (`decimal_max_coeff`, `decimal_max_exp`, the `DecimalFloat` canonicality/bound predicates).

## The restriction, stated directly

Fido's `DecimalFloat` literal domain is a bounded box: a canonical `coeff·10^exp10` with
`decimal_max_coeff = 10^40` (`|coeff| < 10^40`, at most 40 significant digits) and `decimal_max_exp = 4096`
(`-4096 ≤ exp10 ≤ 4096`). A source float literal outside this box is UNREPRESENTABLE in the AST.

## Exact source forms lost

- Float literals with **more than 40 significant digits** (Go parses and rounds arbitrarily long digit
  strings before applying its own constant bound).
- Float literals with **decimal exponent magnitude beyond ±4096** (e.g. `1e5000` — Go's float-constant
  overflow bound is far larger, ~1e400+ in magnitude with a much larger internal precision budget).

These are Go-VALID literals the pinned toolchain would accept (and round to an F32/F64 value); Fido cannot hold
them in the AST.

## Why current fixture coverage is not a sufficient reason

`Floats.v` records the caps were "chosen to cover every F32/F64 overflow (~e39/e309) and underflow (~e-330)
fixture WITH MARGIN." That is a FIXTURE-COVERAGE rationale: the bound is sized to the tests we happen to have,
not to a language fact or a toolchain limit. A restriction justified only by "covers our current fixtures" is
exactly the kind of magic bound a hostile review must flag — it is not faithful-or-fail-loud, it is a
convenient subset.

## The actual need for *a* bound (what genuinely requires one)

- **Canonicality/decidability:** `DecimalFloat` is intrinsically canonical (nonzero coefficient not divisible
  by ten) with decidable equality and a bounded-computation round-trip (`decode(render d) = Some d`). A bound
  makes the coefficient/exponent finite data with simple `Z` comparisons.
- **Rounding to F32/F64:** the value must round once to a `spec_float` at its format; the rounding is defined
  for any finite decimal, so it does not itself require *this* bound — a larger or toolchain-matched bound
  would still round.
So a bound aids canonicality/proof simplicity, but the SPECIFIC `10^40`/`4096` values are not forced by any
proof — only by fixture coverage.

## Alternatives considered

1. **Unbounded canonical decimal syntax** — represent any finite decimal `coeff·10^exp` (arbitrary-precision
   `Z`), canonical (no trailing-zero coefficient). Pro: faithful to Go's parser; con: unbounded data in the
   AST, and the rounding/round-trip proofs must handle arbitrary magnitudes.
2. **Toolchain/implementation-minimum bound** — set the box to Go's actual float-constant precision/exponent
   bounds (match `cmd/compile`'s constant handling). Pro: faithful to the pinned toolchain; con: those bounds
   are large and version-specific (ties into ADR-0001's pinned target).
3. **A larger, experimentally-pinned box** — raise the caps to a value validated by a differential experiment
   (Fido literal ↔ Go literal) with margin over any realistic F32/F64 source. Pro: cheap, covers more; con:
   still a magic bound, just a bigger one.
4. **Retain the current box as a deliberate language subset** — keep `10^40`/`4096`, but justify it as an
   intentional minimal float subset (like the admitted-fragment frontier), with an explicit reconsideration
   trigger. Pro: no model change; con: excludes Go-valid literals with a fixture-shaped bound.

## Guarantees the bound enables

- `DecimalFloat` canonicality + bound proofs; decidable equality; the exact float render/decode round-trip over
  the bounded domain; finite-data float literals.

## Enforcement

- `Floats.v`: `decimal_max_coeff = 10^40`, `decimal_max_exp = 4096`, the canonicality + bound predicates on
  `DecimalFloat`; `ARCHITECTURE.md` GoAST row (`|coeff|<10^40`, `|exp|≤4096`).

## Experiments to run before accepting

- A differential experiment: for float literals near/over the box, compare Fido's representability + rounded
  value against the pinned Go toolchain, to size a faithful bound (alternative 2/3).

## Reconsideration triggers

- Any real source float literal beyond the box that must be represented.
- A decision to match Go's float-constant bound exactly.
- A proof/round-trip that needs a larger domain.
- C5 or later numeric work touching float precision.

Do not set status ACCEPTED. Rob decides after review; the numeric model stays as-is until then.
