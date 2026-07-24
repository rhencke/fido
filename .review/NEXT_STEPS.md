# NEXT_STEPS — active authority pointer

- **Active checkpoint:** C4 **exact standard work-member index repair 13 — candidate COMPLETE and FROZEN at this
  freeze commit; pending Rob's human C4 Implementation Review.** The thirteenth BLOCKING result is repaired. The
  defect was real production code: `ExprWorkForest.ewf_items` was documented as an ordered view that was not
  identity storage, but `forest_member_at` searched it with `List.find` on `nodekey_eqb`, keyed by `NodeKey`, using
  the carried `ewf_keys_nodup` field as its uniqueness mechanism — the forbidden `list + NoDup` keyed table — in the
  live path `build_outcome_trace → build_conversion_step → build_conversion_work → forest_member_at`, once per
  conversion, surviving proof erasure and rescanning the whole retained work list per lookup.
- **The repair.** `forest_member_at` and its `List.find` are DELETED. The identity role is now a separate carried
  field `ewf_index : ExprWorkIndex ewf_items`, backed ENTIRELY by the pinned-stdlib `GoIndex.NodeKeyMapBase`
  (`FMapAVL`): built ONCE by `build_work_index` from the ALREADY-BUILT item list (no second work discovery, no
  `ci_visit` re-traversal), OVERWRITE-FREE (`work_index_fresh` / `work_index_add_fresh` prove every `add` writes an
  absent key), TOTAL with no option/fallback/empty-default because the key-`NoDup` is a PROOF ARGUMENT, and EXACT in
  both directions (`work_index_exact` / `ewi_exact`). The record is INDEXED BY the item list and the field is
  dependent, so a foreign map is not pairable with a forest; `ewi_domain` and `ewi_key_inj` are DERIVED, never
  stored. `index_member_at` / `forest_index_member_at` are the TOTAL member queries — ONE `NodeKeyMapBase.find`,
  no stand-in member; `index_no_foreign` / `index_nonexpr_absent` exclude foreign and wrong-kind keys.
  `build_conversion_work` queries at the key of the operand `ExprRef` the item ALREADY CARRIES (`ew_conv`), not a
  separately computed `operand_key`. The ordered `ewf_items` keeps its SOURCE-ORDER role only.
- **Retained repair-12 results (unchanged):** `StepCause_ok_conv_inv` returns a `ConversionStep` indexed by the
  EXACT source `TypeSyntax` and operand `GoExpr`; `retained_convsuccess_closure` and `nested_success_bundle`
  preserve that exact source-step identity; all four deep valid conversions expose the exact source
  `ConversionStep`.
- **New direct fixtures:** `deep_nested_chain_index_evidence` (each of the four conversions recovers its exact
  operand member THROUGH the index, in the processed suffix, with the accepted outcomes) and
  `twin_expr_index_distinct` (two occurrences of the LITERALLY SAME expression value get distinct keys, distinct
  index entries, and each returns its own retained member).
- **Functional contract:** `.review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md`.
- **Contract SHA-256:** `9ec55b38444e3a32eaf6cb024f72285527992ba1612dabfdc99ce6f89c8517b4`.
- **Accepted review basis:** `.review/REVIEW_BASIS.md`.
- **Original C4 baseline:** `8c9212a8c814c7a99a5e3ef1970a0ae32425a918`.
- **Blocked C4 candidates (all thirteen):** `89b8e54` (1) · `1c4a7de` (2) · `806ce87` (3) · `af2fc87` (4) ·
  `9d4aff5` (5) · `3b4f40e` (6) · `3a92d22` (7) · `91e8dbb` (8) · `a2a5b46` (9) · `a8a4472` (10) · `3ecf32e` (11) ·
  `48c0b31` (12) · `af7d5d3e23c26850887c4fb178dad5f29c616385` (13 — **the repair-13 baseline**).
- **Not a candidate:** commit `37c9597` (`review(accept): C4 — accept exact source-type conversion foundation`) is a
  **SUPERSEDED documentation-only acceptance closeout** based on the withdrawn GREEN disposition. It remains
  superseded in history and is NOT counted as an implementation candidate.
- **Repair authority:** `.review/C4_IMPLEMENTATION_REPAIR_13.md`.
- **Human repair authorization token:** `C4-standard-work-member-index-repair-13`.
- **Candidate ranges (this freeze commit is the repair-13 candidate head; the report gives the exact SHA):** full
  human C4 Implementation Review range `8c9212a..`this freeze commit; full repair range `89b8e54..`this freeze
  commit; **repair-12 range `37c9597..af7d5d3`** (repair 12 was implemented on top of `37c9597`); **repair-13 range
  `af7d5d3..`this freeze commit.**
- **State:** C4 Implementation Review — **exact standard work-member index repair 13 COMPLETE and FROZEN** at this
  freeze commit (the thirteenth BLOCKING result repaired); **new human C4 Implementation Review pending.** All
  thirteen prior blocked candidates ended at `af7d5d3` (the repair-13 baseline); this freeze is the new candidate
  head. Readable gate 479/479 axiom-free; no production `List.find` key lookup remains.
- **Scope decisions:** ADR-0001 remains **PROPOSED**. **ADR-0002 is REJECTED AS WRITTEN / OPEN.** SR-009 =
  UNRESOLVED EXISTING RESTRICTION. Every PROPOSED ledger entry stays PROPOSED until Rob accepts. The DecimalFloat
  decision work is not begun. No numeric-model or scope change was made in repair 13.
- **Automatic Codex review:** DISABLED (do NOT request or run a Codex review).
- **C5 is FORBIDDEN** until explicit Rob authorization (C5 = `uintptr` + rune constants/literals, which reopens
  ADR-0001).
- **Post-C4 simplification / trim is FORBIDDEN** until C4 is accepted (a separate ruthless trim checkpoint follows
  human C4 acceptance). Noted for that trim, NOT done here: `GoIndex.nodekey_eqb` + `thm8_nodekey_eqb_spec` lost
  their last caller when `forest_member_at` was deleted (`NodeKey_OT.eq_dec` goes through `thm8_nodekey_eq_dec`).
  They remain a gated, axiom-free decidable-equality surface of the `NodeKey` domain in the C3-accepted `GoIndex`
  layer; removing them is out of repair-13 scope.
