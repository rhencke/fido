# NEXT_STEPS — active authority pointer

- **C4 — HUMAN IMPLEMENTATION REVIEW GREEN / ACCEPTED.** C4 (source type names, compiler resolution, unified
  numeric conversions, and the `byte`→uint8 / `rune`→int32 source aliases) is **ACCEPTED by Rob at
  `48c0b31beb547326b058748a4d38c6cc41013009`** (`review(final): C4 — freeze final exact acceptance candidate`). No
  remaining production-path, provenance, theorem-surface, diagnostic, gate, rendering, generated-output, or
  current-authority defect was found.
- **Accepted foundation (unchanged, now accepted):** one immutable `GoProgram` source authority; one retained
  `CompilationInput`; one proof-carrying `ExprWorkForest`; exact `WorkMember`/`SuffixMember` handles; exact
  `ConversionWork`/`ConversionStep` views; one total conversion semantic step over the exact operand suffix member;
  one `OutcomeAccumulator` indexed by the exact suffix; one intrinsic `OutcomeTrace` (exact predecessor accumulator +
  current member + `StepCause` + insertion); one `ForestOutcomeTable` pairing the final accumulator with the trace
  that built it; exact final-to-tail query preservation; exact success / local-failure / child-failure causes plus
  the public valid-chain success evidence; one dependent `ExpressionPhase` chain; facts and diagnostics projected
  from the same retained outcome object; exact `EOConvFail`→`DRInvalidConversion` field identity including retained
  annotation context; exact table-object sealing on successful elaboration; one source-name resolver and one
  `convert_const` authority; byte/rune source identity preserved while resolving to uint8/int32 semantics; unchanged
  canonical generated Go bytes; NO old conversion constructors, peer semantic path, raw operand lookup, fail-open
  outcome branch, post-hoc causal reconstruction, or C5 implementation.
- **Ranges:** full human C4 Implementation Review range `8c9212a..48c0b31`; full repair range `89b8e54..48c0b31`;
  repair-11 range `3ecf32e..48c0b31`. All eleven prior candidates ended **BLOCKING at `3ecf32e3`** (`89b8e54` ·
  `1c4a7de` · `806ce87` · `af2fc87` · `9d4aff5` · `3b4f40e` · `3a92d22` · `91e8dbb` · `a2a5b46` · `a8a4472` ·
  `3ecf32e3`). Repair 11 (final evidence and authority closeout) is **COMPLETE**. Automatic Codex review remained
  **DISABLED** throughout.
- **Functional contract:** `.review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md`.
- **Contract SHA-256:** `9ec55b38444e3a32eaf6cb024f72285527992ba1612dabfdc99ce6f89c8517b4`.
- **Accepted review basis:** `.review/REVIEW_BASIS.md`.
- **Original C4 baseline:** `8c9212a8c814c7a99a5e3ef1970a0ae32425a918`.
- **Next authorized activity:** contract design for a SEPARATE **post-C4 foundation consolidation / ruthless trim**
  checkpoint — deletion and abstraction consolidation WITHOUT changing C4's accepted guarantees, plus explicit
  identification of unresolved foundation-scope decisions. It requires its **own explicit contract and human review**
  before any implementation. **No C5 feature may enter the trim.**
- **C5 is FORBIDDEN** until the post-C4 trim checkpoint is separately reviewed and accepted AND explicit Rob
  authorization is given (C5 = `uintptr` + rune constants/literals, which reopens ADR-0001).
- **Scope decisions (UNCHANGED by this acceptance — separate human disposition recommended, not applied here):**
  ADR-0001 / SR-001 remains **PROPOSED** (recommended: accept the current Go 1.23 linux/amd64 target restriction for
  C4, with automatic reopening before C5 implements `uintptr`); ADR-0002 / SR-009 remains **REJECTED AS WRITTEN /
  OPEN** (do not accept the DecimalFloat bound); SR-005 and SR-006(b) remain **PROPOSED** (their module/file-name
  narrowing must be resolved or explicitly justified in a later foundation-scope checkpoint, not hidden inside the
  trim); every other PROPOSED ledger entry remains PROPOSED until Rob explicitly accepts it.
