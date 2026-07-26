# NEXT_STEPS — active authority pointer

- **Current candidate: `12b1bc998a8a2a6b5ecd2360d734f7e2d56eac7c`.** C4 repair 16 is **IMPLEMENTED and
  COMPLETE**, awaiting Rob's human C4 Implementation Review.
  Authority: `.review/C4_IMPLEMENTATION_REPAIR_16.md` (installed verbatim).
- **All five reviewer findings are closed.**
  1. **Package provenance is direct.** `build_elaboration_core` folds the package map from its own retained
     `input_visit`; `package_bucket_diagnostics_from_refs` CONSUMES that stored map and names no builder. Every
     construction law holds by `eq_refl`. The canonical forms survive only as specification bridges.
  2. **`Compilable.Core` is abstract.** The raw record, `MakeCore`, `build_elaboration_core`, the `Elaboration`
     constructor, `decision_of_core` and `elaborate_at` never leave the sealed module. A client cannot assemble
     a peer core — the topology A001 exists to prevent — and `compile` remains the only mint.
  3. **The naming gate sees constructors.** Its parser took only already-uppercase names, so 51 live lower-case
     constructors were never examined and it reported a false green. Constructors are now parsed as general
     identifiers and judged; a second blind spot (the first constructor after `:=`) is fixed; 39 controls
     including the reviewer's exact declarations; and a coverage check fails closed unless every dune-declared
     root `.v` plus every `gate/` and `e2e/` source was actually parsed. All 51 renamed, no aliases.
  4. **The direct fixtures query only returned objects.** No fixture states or uses an equality to
     `build_elaboration_core`; the concrete work count goes through `core_work_count_source`, a SOURCE quantity.
  5. **The corpus states one current truth**, at this ref.
- **Verification at the candidate.** `make check` green: **523/523** readable surfaces axiom-free, whole-theory
  assumption audit, adversarial self-tests A–E, sealed-capability client self-tests **F–X** plus a positive
  control walking mint, `Outcome` destruct, accepted-core query, rejected-core query, certify and emit; the
  pinned-Go whole-tree `go build ./...` against the reviewed goldens; and a byte-exact generated-module compare.
  **Generated `go.mod` and `main.go` are byte-identical to the pre-repair-16 baseline.**
- **C4 is NOT accepted.** Only Rob accepts it, by a new human C4 Implementation Review against the candidate
  above. **C5, post-C4 features, the broad source cleanup and proof-module partitioning remain FORBIDDEN.**
- **Governing accepted amendments.** `A001` through `A005` remain **ACCEPTED**; Governance owns `D-01` through
  `D-25`. No new amendment was required for repair 16.
- **Functional contract:** `.review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md`.
  **Accepted review basis:** `.review/REVIEW_BASIS.md`.
- **Original C4 baseline:** `8c9212a8c814c7a99a5e3ef1970a0ae32425a918`.
- **Blocked C4 implementation candidates (all seventeen):** `89b8e54` (1) · `1c4a7de` (2) · `806ce87` (3) ·
  `af2fc87` (4) · `9d4aff5` (5) · `3b4f40e` (6) · `3a92d22` (7) · `91e8dbb` (8) · `a2a5b46` (9) · `a8a4472` (10) ·
  `3ecf32e` (11) · `48c0b31` (12) · `af7d5d3` (13) · `9d5246e` (14) · `3386c02` (15) · `20c5ad5` (16) ·
  `deda8bd91dbfebf75895c8786732a4ed9d7952f2` (17).
  The candidate above is the eighteenth; it is under review — neither blocked nor accepted.
  Not candidates: `37c9597` (superseded documentation-only closeout), `c5b67495` and `25bcd7aa`
  (documentation-only freezes), and the documentation/authority commits between them.
- **Retained results — do NOT regress.** Repair 16: the direct package chain, the sealed `Core`, the fixtures
  that ask only the returned object, and the gate that actually parses constructors. Repair 15: the
  whole-elaboration core, the sealed capability, the one mint path. Repair 14: the retained core and the
  decision indexed by it. Repair 13: the exact standard work-member index (`WorkIndex` / `forest_index`, built
  once, overwrite-free, total because the key-`NoDup` is a proof argument, exact in both directions),
  `index_member_at` / `forest_index_member_at`, and zero production keyed list scan. Repair 12: exact
  source-step identity, no existential. A005: the module rename and byte-identical output.
- **Scope decision (reviewer, standing):** **do NOT delete `Index.Program` during a repair.** It may remain
  only as the existing exact wrapper or projection; it must never become a parallel semantic authority.
- **Deferred process task (nonblocking, before the next accepted checkpoint):** implement the living-FCB Human
  Review Index generator required by Governance `D-07`. It must derive entries from named canonical statuses,
  produce the tracked Markdown deterministically, and FAIL both when the tracked index omits a live human act
  and when it retains a stale one. Until it lands the index carries a temporary hand-maintained disclaimer.
- **Documentation basis:** the live Fido Conformance Basis is `.review/fcb/current/` (Git-canonical per **A002**,
  living-document form per **A003**; identity is `git rev-parse HEAD:.review/fcb/current`).
- **Scope decisions:** **ADR-0001 / SR-001 ACCEPTED FOR CURRENT BASIS** (Rob, 2026-07-25) — Go 1.23 on
  `linux/amd64` with `GOAMD64=v1`; `int`/`uint` 64-bit and distinct from fixed-width types. `uintptr` stays OUT.
  ADR-0002 remains REJECTED AS WRITTEN / OPEN. SR-009 remains an unresolved existing restriction. `LAT-X004` is
  settled as option (ii), the rounding-invariant accepted domain.
- **Open questions:** `.review/OPEN_QUESTIONS.md` — each entry names its owner, whether it blocks, and the
  default taken if nobody answers. It is not authority and overrides nothing.
- **Automatic Codex review:** DISABLED.
