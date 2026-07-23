# NEXT_STEPS — active authority pointer

- **STATUS (repair 7 COMPLETE — pending Rob's HUMAN Implementation Review):** the C4 exact retained work-object
  repair-7 candidate is COMPLETE and FROZEN at this freeze commit (`review(final): C4 — freeze exact retained
  work-object candidate`). Original C4 baseline `8c9212a`; seven blocked candidates ending at `3a92d22`
  (repair-7 baseline); full human review range `8c9212a..<this freeze commit>`; full repair range
  `89b8e54..<this freeze commit>`; repair-7 range `3a92d22..<this freeze commit>`. Human C4 Implementation Review
  PENDING; ADR-0001 PROPOSED; ADR-0002 REJECTED AS WRITTEN / OPEN; automatic Codex review DISABLED (do NOT
  request/run Codex); C5 and every later checkpoint FORBIDDEN. Verification GREEN: `make prove` (readable gate
  443/443 axiom-free + whole-theory audit + self-tests A–E), `make e2e`, `make check` (working-tree generated
  byte-compare — no drift), `make regenerate` (no drift), `make regen-guard`, and the staged pre-commit hook.
- **The repair-7 task (now delivered):** replaced the remaining canonical-recomputation
  root: `prog_forest`/`prog_forest_blocks`/`prog_forest_awork` were pure canonical FUNCTIONS re-evaluated by every
  phase builder from `input` (each `proj1_sig` of a sigma whose proof is discarded and re-recovered later via a
  separate `proj2_sig`); `ep_work` is stored but consumed by nothing. Build ONE proof-carrying `ExprWorkForest`
  object (stored `ewf_blocks`/`ewf_items` + `= concat` + exact fwd/rev domain + key-NoDup + per-file/flat order +
  operand-in-suffix), a `WorkMember` membership handle, and a `ConversionWork` view carrying the exact operand
  `WorkMember` + suffix proof; index the outcome table by the FOREST OBJECT (`ForestOutcomeTable forest tnft`),
  do the live operand lookup by member/ref (NOT raw `operand_key`, no `conversion_*_ref` in the semantic step),
  retain an `AnnotatedExprWorkForest`, forest/ot-indexed facts + diagnostics, and make `ExpressionPhase` a
  DEPENDENT CHAIN (`ep_ot : ForestOutcomeTable ep_work ep_tnft`, …) with NO provenance-equality fields. Update the
  deep fixtures to query retained `WorkMember`s from `ep_work`. PLUS §13: correct the scope-ledger wording so
  `GoCompile == go build` reads as an EXTERNAL adequacy target (kernel-proved internal judgment soundness/
  completeness vs. differential evidence against pinned `cmd/go`), not an "EXACT" property (SR-001/SR-002).
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
- **Seventh blocked C4 candidate / repair-7 baseline:** `3a92d22820705f55093c0e2b3ff18a0f8ad7f4dc`.
  (A superseding freeze `c23a7c9` — a repair-6 post-freeze completeness fix — sits on top of `3a92d22` and carries
  the identical architectural defect; repair 7 proceeds from current HEAD forward, no history rewrite, and the
  repair-7 range is measured `3a92d22..final` per the directive.)
- **Repair authority:** `.review/C4_IMPLEMENTATION_REPAIR_7.md`.
- **Human repair authorization token:** `C4-exact-retained-work-object-repair-7`.
- **State:** C4 Implementation Review BLOCKING; exact retained work-object repair 7 active.
- **Scope decisions:** ADR-0001 remains **PROPOSED** pending explicit Rob disposition. **ADR-0002 is REJECTED AS
  WRITTEN / OPEN — no numeric implementation change authorized.** SR-009 = UNRESOLVED EXISTING RESTRICTION. Every
  PROPOSED ledger entry uses a NEUTRAL classification (no REVIEWED) until Rob accepts.
- **Automatic Codex review:** DISABLED (do NOT request or run a Codex review).
- **C5 is FORBIDDEN** until explicit Rob authorization.
