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
- **All five findings are closed.**
  1. **The returned-object fixtures carry the retained causal history.** The four conversion causes with
     their operand predecessors and `Typing.convert_constant` steps, the retained work index exact both ways,
     the outcome table and trace, the exact empty raw and final diagnostics, `Safe.certify` retention and
     `Emit.of_safe` consumption — all through the object `compile` returned. Seventeen causal declarations plus
     two bundles were first restated over ANY retained `Input`/`Phase`; the obsolete builder-based peers are
     deleted, not kept in parallel.
  2. **The naming gate parses what it judges.** Record fields are read as general identifiers and then
     validated; a selected text file that cannot be decoded or read fails the gate by path. 47 controls,
     mutation-tested — with the defects restored, the five new ones fail.
  3. **The `Emit.Image` authority is sealed under A006 / D-26.** `Emit.Mint.Token` is opaque and indexed by
     the exact `Safe.Program` and exact bytes; `Mint.issue` is the sole authority-producing operation; the
     carrier stays reducible and its pack constructor is not a mint. `MakeImage` is deleted.
  4. **The coarse legacy result peer is gone**, with its whole classification closure; every fixture now
     asserts exact outcomes and exact diagnostic codes.
  5. **The corpus states one truth**, and the closure audit additionally sealed `Safe.Program`, which was the
     last publicly constructible capability.
- **Amendment A006 is ACCEPTED** (`FCB-A006-INTRINSIC-EMIT-IMAGE-MINT`, Rob, 2026-07-26), resolving Q-08.
  Otherwise A001, A005, `D-22`–`D-26`, Charter §§1, 3, 4, 22, 24, 25 and the
  no-compatibility law already decide the required result. If one of those must change, stop and propose the
  exact amendment rather than retaining the defect.
- **C4 is NOT accepted.** Only Rob accepts it. **C5, post-C4 features, the broad source cleanup and
  proof-module partitioning remain FORBIDDEN.**
- **Governing accepted amendments.** `A001` through `A006` remain **ACCEPTED**; Governance owns `D-01`
  through `D-26`.
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
