# NEXT_STEPS — active authority pointer

- **Active checkpoint:** C4 **member-indexed causal outcome repair 8 — CANDIDATE COMPLETE, awaiting Rob's
  human C4 Implementation Review.** The eighth-BLOCKING defect (the final table carried the OLD raw-map
  `OutcomeCause`, a cause NOT indexed by the exact conversion `WorkMember` / processed suffix / exact operand
  `WorkMember` / exact suffix accumulator; `build_outcomes_forest` proved an operand in the tail, DISCARDED the
  member, and did a raw `find`; `phase_*_work_cause` rebuilt `ConversionWork` and translated the raw cause
  post-hoc) is REPAIRED by re-rooting the causal/outcome fold. The production root is now: `SuffixMember forest
  items` + `ConversionStep forest current rest ts x` (`cs_conversion : ConversionWork` + `cs_operand_suffix :
  SuffixMember forest rest` + `cs_operand_exact`); the proof-carrying `OutcomeAccumulator forest tnft items`
  (`oa_map`/`oa_covers`/`oa_domain`; total `oa_total : SuffixMember forest items -> ExprOutcome`); the
  member/suffix-indexed direct cause `StepCause` (`SCLeaf`/`SCConvOk`/`SCConvFail`/`SCChildFail`, each reading
  the operand outcome THROUGH `cs_operand_suffix` via `oa_total acc_rest`); `build_outcome_accumulator`'s
  conversion cons-step consumes ONE `ConversionStep`, queries the REST accumulator THROUGH `cs_operand_suffix`
  (NO raw `find`/`from_some`/`operand_key`/`conversion_*_ref`/re-run `ewf_operand_in_tail`/post-hoc
  `ConversionWork`), and calls `convert_const` ONCE; `ForestOutcomeTable` retains the exact insertion cause
  (`fot_acc`/`fot_causes`/`fot_match`), so `total_forest_outcome_cause` returns each member's exact
  `FinalMemberCause` (the `ewf_items = prefix ++ current :: rest` split + prior accumulator + `StepCause`),
  projected axiom-free by `StepCause_convfail_inv`/`_childfail_inv`/`_ok_conv_inv`; the source spec is the
  SEPARATE per-member `fot_match` (`stepcause_matches`). The raw `OutcomeCause`/`outcomes_caused`/
  `build_outcomes_forest`/`phase_*_cause`/`phase_*_work_cause` root is DELETED. The phase chain, objects,
  domains, sealing, alias/render/byte results, and scope-ledger wording are KEPT. **Post-C4 trim: FORBIDDEN
  until C4 is accepted.**
- **Functional contract:** `.review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md`.
- **Contract SHA-256:** `9ec55b38444e3a32eaf6cb024f72285527992ba1612dabfdc99ce6f89c8517b4`.
- **Accepted review basis:** `.review/REVIEW_BASIS.md`.
- **Original C4 baseline:** `8c9212a8c814c7a99a5e3ef1970a0ae32425a918`.
- **First blocked C4 candidate:** `89b8e54634e7012612a51990756ad29a579c1b0f`.
- **Second blocked C4 candidate:** `1c4a7de8e9e265b929a3ba9ce1c8fb1317ca98ca`.
- **Third blocked C4 candidate:** `806ce87373e29b6980e5c3d9d274ffa86580449b`.
- **Fourth blocked C4 candidate:** `af2fc87e7726a4fc68bb9480c53cf64faa83717b`.
- **Fifth blocked C4 candidate:** `9d4aff5d94d9aac293ff7fb98a7d9fdd59159022`.
- **Sixth blocked C4 candidate:** `3b4f40e1f14c501fd76333ec8a8cd3e582ed1598`.
- **Seventh blocked C4 candidate:** `3a92d22820705f55093c0e2b3ff18a0f8ad7f4dc`.
- **Eighth blocked C4 candidate / repair-8 baseline:** `91e8dbbcd24fc7df678e6b3d68eabb13b686efa1`
  (the repair-7 freeze; eighth BLOCKING — the final table's causal outcome was still the raw-map cause).
- **Repair authority:** `.review/C4_IMPLEMENTATION_REPAIR_8.md`.
- **Human repair authorization token:** `C4-member-indexed-causal-outcome-repair-8`.
- **Repair-8 candidate head:** the `review(final): C4 — freeze member-indexed causal outcome candidate` freeze
  commit (repository HEAD).
- **Full human C4 Implementation Review range:** `8c9212a..`<freeze> (original C4 baseline → candidate head).
- **Full repair range:** `89b8e54..`<freeze>.
- **Repair-8 range:** `91e8dbb..`<freeze>.
- **State:** C4 Implementation Review — **member-indexed causal outcome repair 8 candidate COMPLETE; all eight
  blocked candidates ended at `91e8dbb`; human C4 Implementation Review pending.**
- **Scope decisions:** ADR-0001 remains **PROPOSED** pending explicit Rob disposition. **ADR-0002 is REJECTED AS
  WRITTEN / OPEN — no numeric implementation change authorized.** SR-009 = UNRESOLVED EXISTING RESTRICTION. Every
  PROPOSED ledger entry uses a NEUTRAL classification (no REVIEWED) until Rob accepts.
- **Automatic Codex review:** DISABLED (do NOT request or run a Codex review).
- **C5 is FORBIDDEN** until explicit Rob authorization.
- **Post-C4 simplification / trim is FORBIDDEN** until C4 is accepted (a separate ruthless trim checkpoint
  follows human C4 acceptance).
