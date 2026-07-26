# NEXT_STEPS — active authority pointer

- **Active work: C4 REPAIR 17 — the sole active C4 task.**
  Authority: `.review/C4_IMPLEMENTATION_REPAIR_17.md` (installed verbatim).
  Implementation base: the current head, a documentation-only descendant of the reviewed candidate. Do not
  reset or rewrite history.
- **Candidate status.** `12b1bc998a8a2a6b5ecd2360d734f7e2d56eac7c` is **BLOCKING** — the eighteenth
  blocked C4 implementation candidate. Repair 16 made real progress and did **not** close C4.
- **What repair 16 closed and must NOT regress.** `Compilable.Core` is abstract outside its sealed
  implementation; `MakeCore`, `CoreRepresentation`, `build_elaboration_core`, `MakeElaboration` and the internal
  mint helpers are absent from the client interface and covered by negative client compilation tests;
  `build_elaboration_core` folds package references directly from its retained `input_visit`; package
  diagnostics consume the exact retained package-reference map; the aggregate fixtures no longer state equality
  to `build_elaboration_core`; all 51 lower-case constructors were renamed; generated Go still builds and
  matches the reviewed goldens.
- **The five findings repair 17 must close.**
  1. **The direct capability fixtures do not prove the retained causal result.** Neither the accepted nor the
     rejected fixture exposes the retained work index, outcome table, trace, conversion causes, annotation
     context, raw diagnostics, safety retention or emission through the returned object. The detailed cause
     fixtures still stand over freshly rebuilt phases, and the gate prose calls them capability evidence.
  2. **The naming gate is still false-green.** Record fields are parsed only when the first character is
     already lower-case, so an upper-case field is invisible — the same pre-validation defect that previously
     hid lower-case constructors. And a selected text file that fails to decode or read is silently skipped.
  3. **`Emit.Image` has a public raw constructor**, although Charter §22 says its constructor is private and
     §24 says to seal its construction.
  4. **The coarse `LegacyClass` compatibility peer survives** with no production consumer, collapsing the
     structured `Outcome` and exact `DiagnosticReason` list into four tags.
  5. **The corpus does not state one truth** — REVIEW_REQUEST, the Roadmap, PROGRESS, SOURCE_FOREST_STATUS and
     the Charter disagree with the indexes; source comments still claim `Core` is transparent; `ARCHITECTURE.md`
     cites a deleted theorem and calls `Emit.MakeImage` public; `FIDO_FCB_MODEL_OPERATIONS.md` carries a
     corrupted sentence.
- **No new amendment is required.** A001, A005, `D-22`–`D-25`, Charter §§1, 3, 4, 22, 24, 25 and the
  no-compatibility law already decide the required result. If one of those must change, stop and propose the
  exact amendment rather than retaining the defect.
- **C4 is NOT accepted.** Only Rob accepts it. **C5, post-C4 features, the broad source cleanup and
  proof-module partitioning remain FORBIDDEN.**
- **Governing accepted amendments.** `A001` through `A005` remain **ACCEPTED**; Governance owns `D-01` through
  `D-25`.
- **Functional contract:** `.review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md`.
  **Accepted review basis:** `.review/REVIEW_BASIS.md`.
- **Original C4 baseline:** `8c9212a8c814c7a99a5e3ef1970a0ae32425a918`.
- **Blocked C4 implementation candidates (all eighteen):** `89b8e54` (1) · `1c4a7de` (2) · `806ce87` (3) ·
  `af2fc87` (4) · `9d4aff5` (5) · `3b4f40e` (6) · `3a92d22` (7) · `91e8dbb` (8) · `a2a5b46` (9) · `a8a4472` (10) ·
  `3ecf32e` (11) · `48c0b31` (12) · `af7d5d3` (13) · `9d5246e` (14) · `3386c02` (15) · `20c5ad5` (16) ·
  `deda8bd` (17) · `12b1bc998a8a2a6b5ecd2360d734f7e2d56eac7c` (18).
  Not candidates: `37c9597` (superseded documentation-only closeout), `c5b67495`, `25bcd7aa` and `c8ce2d8c`
  (documentation-only freezes), and the documentation/authority commits between them.
- **Retained results — do NOT regress.** Repair 16: the direct package chain, the sealed `Core`, the gate that
  parses constructors. Repair 15: the whole-elaboration core, the sealed capability, the one mint path.
  Repair 14: the retained core and the decision indexed by it. Repair 13: the exact standard work-member index,
  overwrite-free, total, exact in both directions, with zero production keyed list scan. Repair 12: exact
  source-step identity, no existential. A005: the module rename and byte-identical output.
- **Scope decision (reviewer, standing):** **do NOT delete `Index.Program` during a repair.**
- **Deferred process task (nonblocking):** the living-FCB Human Review Index generator required by Governance
  `D-07`. It must not expand repair 17.
- **Documentation basis:** the live Fido Conformance Basis is `.review/fcb/current/` (Git-canonical per **A002**,
  living-document form per **A003**; identity is `git rev-parse HEAD:.review/fcb/current`).
- **Scope decisions:** **ADR-0001 / SR-001 ACCEPTED FOR CURRENT BASIS** (Rob, 2026-07-25) — Go 1.23 on
  `linux/amd64` with `GOAMD64=v1`; `int`/`uint` 64-bit and distinct from fixed-width types. `uintptr` stays OUT.
  ADR-0002 remains REJECTED AS WRITTEN / OPEN. SR-009 remains an unresolved existing restriction. `LAT-X004` is
  settled as option (ii), the rounding-invariant accepted domain.
- **Open questions:** `.review/OPEN_QUESTIONS.md` — each entry names its owner, whether it blocks, and the
  default taken if nobody answers. It is not authority and overrides nothing.
- **Automatic Codex review:** DISABLED.
