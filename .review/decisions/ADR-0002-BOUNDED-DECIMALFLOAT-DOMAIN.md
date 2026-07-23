# ADR-0002 — Bounded DecimalFloat literal domain

- **Status:** **REJECTED AS WRITTEN, then rewritten; the decision is OPEN.** The earlier draft was factually
  and conceptually wrong (see "What the earlier draft got wrong"); it is not accepted, and nothing here sets it
  accepted. The numeric model is NOT changed by the C4 repair that raised this — no float implementation change
  is authorized. This ADR only records an OPEN decision for Rob.
- **Date:** 2026-07-22.
- **Scope ledger link:** `.review/UNSUPPORTED_AND_RESTRICTED_SCOPE.md` SR-009 (classification: UNRESOLVED
  EXISTING RESTRICTION).
- **Source:** `Floats.v` (`decimal_max_coeff`, `decimal_max_exp`, the `DecimalFloat` canonicality/bound predicates).

## The restriction, stated directly

Fido's `DecimalFloat` literal domain is a bounded box: a canonical `coeff·10^exp10` with
`decimal_max_coeff = 10^40` (`|coeff| < 10^40`, at most 40 significant digits) and `decimal_max_exp = 4096`
(`-4096 ≤ exp10 ≤ 4096`). A source float literal outside this box is UNREPRESENTABLE in the AST.

## What the earlier draft got wrong (why it is REJECTED AS WRITTEN)

1. It claimed that **all** exponent-magnitude forms beyond ±4096 — including `1e5000` — are Go-valid programs
   the pinned toolchain **accepts and rounds** to an F32/F64 value. That is false in the represented use
   contexts. In today's fragment a float literal appears only as a `println` argument, i.e. either a
   **defaulted** untyped constant or an operand of an **F32/F64 conversion**. In both of those contexts `1e5000`
   **overflows the target float type and is REJECTED by `go build`** — it is not accepted-and-rounded. Only a
   literal whose *value* lands within finite F32/F64 range (which a huge exponent like `e5000` does not) is
   accepted and rounded.
2. It conflated four distinct notions that must be kept separate (below).
3. It claimed a bound is **required** for finite data and decidable equality. That is false: arbitrary Rocq `Z`
   coefficients and exponents are already finite values with decidable equality, and a canonical decimal built
   on them is canonical and round-trippable without any magnitude cap.

## The four notions this decision must keep separate

- **(a) Lexical / source representability.** What the Go *lexer* will read as a float literal token. Go accepts
  very long digit strings and large exponents lexically (the token is well-formed); this is independent of
  whether the resulting constant is usable.
- **(b) Untyped-constant representability.** Whether Go retains the value as an untyped constant. Go's untyped
  float constants carry a large but finite precision budget; an *unused* untyped package-level constant with a
  huge magnitude can be parsed and retained. **Current Fido has no such declaration form** — there is no
  untyped-constant declaration in the fragment, so this context does not arise for us today.
- **(c) Accepted current-fragment programs.** What actually compiles in *today's* fragment: a float literal is
  a `println` argument — a defaulted untyped constant or an F32/F64 conversion operand. Here a huge-magnitude
  literal (`1e5000`) **overflows and is rejected**; a literal near a finite magnitude but with a very long
  significand is **accepted and rounded**.
- **(d) Finite F32/F64 conversion.** The rounding of a finite decimal to a `spec_float` at its format. This is
  defined for any finite decimal regardless of the cap; the cap does not enable it.

The forms *actually lost* by the `10^40`/`4096` box are therefore, precisely: **(a)/(b)-representable literals
whose value is finite in F32/F64 but whose significand exceeds 40 significant digits or whose exponent exceeds
±4096** — e.g. a 60-significant-digit literal near a representable magnitude, which Go would round but Fido
cannot hold. A huge-exponent literal like `1e5000` is NOT a lost Go-valid program in the current fragment
(context (c) rejects it); it is lost only in the hypothetical (b) untyped-constant context, which the fragment
does not yet have.

## Is a bound required? (No — separate necessity from convenience)

- **Canonicality / decidability do NOT require a bound.** A canonical decimal `coeff·10^exp` over arbitrary
  Rocq `Z` (nonzero coefficient not divisible by ten) is already finite data with decidable equality and a
  bounded-computation render/decode round-trip. Removing the cap does not break canonicality or decidability.
- **What a bound *might* buy** (each a cost/benefit to be **measured**, not assumed): faster proof-term
  evaluation (`vm_compute` over smaller `Z`), a resource-limit guard against pathological literals, or
  implementation-performance headroom. None of these is established here; they are candidate justifications
  that require measurement before they can support the specific `10^40`/`4096` values.
- The current `Floats.v` rationale ("chosen to cover every F32/F64 overflow/underflow fixture WITH MARGIN") is a
  **fixture-coverage** rationale — sized to the tests we happen to have, not to a language fact, a toolchain
  limit, or a measured proof/resource cost. That is exactly the kind of magic bound a hostile review flags.

## Alternatives considered

1. **Unbounded canonical decimal syntax** — any finite `coeff·10^exp` over arbitrary-precision `Z`, canonical.
   Pro: faithful to Go's lexer/constant handling; canonicality + decidable equality hold with no cap. Con:
   unbounded data in the AST; rounding/round-trip proofs and proof-term evaluation must handle arbitrary
   magnitudes (a *measured* proof-evaluation cost, not a correctness obstacle).
2. **Toolchain/implementation-matched bound** — set the box to Go's actual untyped-float-constant precision /
   exponent budget. Pro: faithful to the pinned toolchain for context (b) if/when it arises. Con: large and
   version-specific (ties into ADR-0001's pinned target).
3. **A larger, experimentally-pinned box** — raise the caps to a value validated by a differential experiment
   with margin over any realistic finite-F32/F64 source. Pro: cheap, covers more real literals. Con: still a
   magic bound, just larger.
4. **Retain the current box as a deliberate language subset** — keep `10^40`/`4096`, justified as an
   intentional minimal float subset with an explicit reconsideration trigger. Pro: no model change. Con:
   excludes finite-valued Go literals with a fixture-shaped bound.

## Experiments/measurements to run before accepting

- A **differential experiment**: for float literals with long significands and for near-box exponents, compare
  Fido representability + rounded value against the pinned Go toolchain *in the fragment's actual contexts*
  (defaulted arg; F32/F64 conversion), to size a faithful bound (alternatives 2/3) — and confirm the (c)
  overflow-rejection behaviour for huge exponents.
- A **proof-evaluation measurement**: quantify the `vm_compute`/`Qed` cost of the unbounded canonical domain
  (alternative 1), so any bound is justified by a measured cost, not by fixture coverage.

## Reconsideration triggers

- Any real source float literal with a finite F32/F64 value that must be represented but exceeds the box.
- Introduction of an untyped-constant declaration form (context (b)) into the fragment.
- A measured proof-evaluation or resource cost that a bound demonstrably mitigates.
- C5 or later numeric work touching float precision.

Do not set status ACCEPTED. Rob decides after review; the numeric model stays as-is until then.
