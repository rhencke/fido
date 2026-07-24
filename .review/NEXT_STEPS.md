# NEXT_STEPS — active authority pointer

- **Active checkpoint:** C4 **exact standard work-member index repair 13 — ACTIVE.** The thirteenth C4
  Implementation Review is **BLOCKING** at `af7d5d3`. Repair 12's two assigned defects were closed and those results
  are **RETAINED**; the rewritten collection audit then exposed a NEW load-bearing foundation defect:
  `ExprWorkForest.ewf_items` is documented as an ordered list view that is not identity storage, but the production
  path `build_outcome_trace → build_conversion_step → build_conversion_work → forest_member_at` performs a `NodeKey`
  identity lookup by scanning that list with `List.find`, using `ewf_keys_nodup` as its uniqueness mechanism. That is
  the forbidden `list + NoDup` keyed-table pattern: it survives proof erasure, and it makes nested-conversion lookup
  avoidably quadratic. Repair 13 must replace the hidden list-key authority with an **exact standard-map-backed
  work-member index** (or an equally exact structural construction with no keyed list scan at all), keeping one
  immutable AST, one work discovery, one retained forest object, and one causal outcome path.
- **Retained repair-12 results (do NOT regress):** `StepCause_ok_conv_inv` returns a `ConversionStep` indexed by the
  EXACT source `TypeSyntax` and operand `GoExpr` supplied to the theorem; `retained_convsuccess_closure` and
  `nested_success_bundle` preserve that exact source-step identity; all four deep valid conversions expose the exact
  source `ConversionStep`; the stale `prog_conv_outcomes` / `TFun` collection-audit rows are gone.
- **Functional contract:** `.review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md`.
- **Contract SHA-256:** `9ec55b38444e3a32eaf6cb024f72285527992ba1612dabfdc99ce6f89c8517b4`.
- **Accepted review basis:** `.review/REVIEW_BASIS.md`.
- **Original C4 baseline:** `8c9212a8c814c7a99a5e3ef1970a0ae32425a918`.
- **Blocked C4 candidates (all thirteen):** `89b8e54` (1) · `1c4a7de` (2) · `806ce87` (3) · `af2fc87` (4) ·
  `9d4aff5` (5) · `3b4f40e` (6) · `3a92d22` (7) · `91e8dbb` (8) · `a2a5b46` (9) · `a8a4472` (10) · `3ecf32e` (11) ·
  `48c0b31` (12) · `af7d5d3e23c26850887c4fb178dad5f29c616385` (13 — **the current repair-13 baseline**).
- **Not a candidate:** commit `37c9597` (`review(accept): C4 — accept exact source-type conversion foundation`) is a
  **SUPERSEDED documentation-only acceptance closeout** based on the withdrawn GREEN disposition. It remains
  superseded in history and is NOT counted as an implementation candidate.
- **Repair authority:** `.review/C4_IMPLEMENTATION_REPAIR_13.md`.
- **Human repair authorization token:** `C4-standard-work-member-index-repair-13`.
- **Candidate ranges:** full human C4 Implementation Review range `8c9212a..`the repair-13 freeze commit; full repair
  range `89b8e54..`the repair-13 freeze commit; **repair-12 range `37c9597..af7d5d3`** (repair 12 was implemented on
  top of `37c9597`); **repair-13 range `af7d5d3..`the repair-13 freeze commit.**
- **State:** C4 Implementation Review **BLOCKING**; **exact standard work-member index repair 13 ACTIVE.** No new
  candidate exists until the repair-13 freeze commit is created and verified.
- **Scope decisions:** ADR-0001 remains **PROPOSED**. **ADR-0002 is REJECTED AS WRITTEN / OPEN.** SR-009 =
  UNRESOLVED EXISTING RESTRICTION. Every PROPOSED ledger entry stays PROPOSED until Rob accepts. The DecimalFloat
  decision work is not begun.
- **Automatic Codex review:** DISABLED (do NOT request or run a Codex review).
- **C5 is FORBIDDEN** until explicit Rob authorization (C5 = `uintptr` + rune constants/literals, which reopens
  ADR-0001).
- **Post-C4 simplification / trim is FORBIDDEN** until C4 is accepted (a separate ruthless trim checkpoint follows
  human C4 acceptance).
