# NEXT_STEPS — active authority pointer

- **Active checkpoint:** C4 retained-table bottom-up repair 3 — replace the recursive/recomputing production root
  with one retained `TypeNameFactTable` object (built, consumed, sealed by identity) and one proof-carrying
  bottom-up outcome accumulator (operand read from the already-processed suffix; one `convert_const` per
  conversion occurrence). ACTIVE.
- **Functional contract:** `.review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md`.
- **Contract SHA-256:** `9ec55b38444e3a32eaf6cb024f72285527992ba1612dabfdc99ce6f89c8517b4`.
- **Accepted review basis:** `.review/REVIEW_BASIS.md`.
- **Original C4 baseline:** `8c9212a8c814c7a99a5e3ef1970a0ae32425a918`.
- **First blocked C4 candidate:** `89b8e54634e7012612a51990756ad29a579c1b0f`.
- **Second blocked C4 candidate:** `1c4a7de8e9e265b929a3ba9ce1c8fb1317ca98ca`.
- **Third blocked C4 code candidate:** `806ce87373e29b6980e5c3d9d274ffa86580449b`.
- **Current repair baseline:** `1b38b68c104bc987744ececc36e771d8977bdbf2`.
- **Repair authority:** `.review/C4_IMPLEMENTATION_REPAIR_3.md`.
- **Human repair authorization token:** `C4-retained-table-bottom-up-repair-3`.
- **State:** C4 Implementation Review BLOCKING; retained-table bottom-up repair active.
- **Automatic Codex review:** DISABLED (do NOT request or run a Codex review; the directive is the accepted
  human Contract Review; on completion freeze with `review(final): C4 — freeze retained-table bottom-up
  candidate` and stop for Rob's human Implementation Review).
- **C5 is FORBIDDEN** until explicit Rob authorization.
