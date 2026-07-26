# NEXT_STEPS — active authority pointer

- **Active work: C4 REPAIR 16 — the sole active C4 task.**
  Authority: `.review/C4_IMPLEMENTATION_REPAIR_16.md` (installed verbatim).
  Implementation base: **the current repository head.** Do not reset, rebase, rewrite history, or discard
  retained repair-13, repair-14, repair-15, A001 or A005 work.
- **Candidate status.** `deda8bd91dbfebf75895c8786732a4ed9d7952f2` is **BLOCKING** — the seventeenth blocked
  C4 implementation candidate. `25bcd7aa6b53f1e506a32c5077990a884bea8574` is its **documentation-only
  freeze**, not a separate implementation candidate. Repair 15 made substantial, real progress; it did **not**
  close C4, and it is no longer described as complete.
- **The five findings repair 16 must close (reviewer, 2026-07-26).**
  1. **Package provenance still starts from a rerun.** `build_elaboration_core` builds the package map through
     `program_package_refs`, which calls `program_visit p` again instead of consuming the exact `input_visit`
     retained in the core input; `package_bucket_diagnostics` likewise rebuilds a package map rather than
     consuming the retained one. The stored equality connects the values extensionally, but the production
     causal chain still begins from a rerun — which A001 rejects as provenance.
  2. **`Compilable.Core` and `MakeCore` are still public.** A client cannot mint a `Program`, but can still
     construct an independently built peer `Core` — the exact topology A001 exists to prevent. The negative
     client fixtures cover `MakeProgram` / `MakeFailure` / `MakeFacts` and do not cover `MakeCore`.
  3. **The A005 naming gate is false-green for constructors.** Its parser extracts inductive and record
     constructors only when the first character is already uppercase, and `constructor` is not a casing-checked
     declaration kind — so the declarations it exists to reject are never seen. Verified directly:
     `Record BadRecord := make_bad_record { value : nat }.` and `Inductive Bad := make_bad : Bad.` are both
     accepted. Roughly 51 lower-case constructors are live in the tree. **A005 is NOT complete.**
  4. **The direct capability fixtures still reconstruct.** Both carry their results through an equality to
     `build_elaboration_core`, so they do not show that a client can obtain the result from the returned
     capability or failure itself.
  5. **The live FCB corpus contradicts itself.** The Roadmap and Architecture Charter still name repair 13/14
     as current work while the Index and this file described repair 15 as complete.
- **What must NOT regress.** The retained-elaboration core; the decision indexed by the exact core it judges;
  `Program` retaining the accepted core; `Failure` retaining the rejected core; `Facts` as an accepted view
  tied to the exact core and its acceptance evidence; `compile` as the sole capability mint; the deleted
  stripped `Result` peer and the deleted independent capability builder; repair 13's exact `WorkIndex`
  (overwrite-free, exact two-way domain, total lookup, no production keyed `List.find`); exact source-step
  identity; `Safe.Program` retaining the same capability and core; the sealed `Emit.Image`; working-tree AND
  staged-snapshot naming modes; staged-hook enforcement; the whole-theory assumption audit and adversarial
  self-tests; byte-identical generated `go.mod` and `.go`; and `Index.Program`, which stays.
- **No repair may restore an old name, compatibility alias, compatibility module, wrapper, fallback, copied
  view, or second semantic path.**
- **C4 is NOT accepted**, and repair 15 is not to be described as complete. Only Rob accepts C4, by a new human
  C4 Implementation Review. **C5, post-C4 features, the broad source cleanup, and proof-module partitioning
  remain FORBIDDEN** until C4 is accepted.
- **Governing accepted amendments.** `A001` through `A005` remain **ACCEPTED**; Governance owns `D-01` through
  `D-25`. `FCB-A001` / `D-22` — the opaque static capability must RETAIN the exact whole-elaboration object by
  construction; equality to a canonical rerun is never the production provenance. `FCB-A005` / `D-25` — names
  are owned by their scope. No new amendment is required for repair 16.
- **Functional contract:** `.review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md`.
  **Accepted review basis:** `.review/REVIEW_BASIS.md`.
- **Original C4 baseline:** `8c9212a8c814c7a99a5e3ef1970a0ae32425a918`.
- **Blocked C4 implementation candidates (all seventeen):** `89b8e54` (1) · `1c4a7de` (2) · `806ce87` (3) ·
  `af2fc87` (4) · `9d4aff5` (5) · `3b4f40e` (6) · `3a92d22` (7) · `91e8dbb` (8) · `a2a5b46` (9) · `a8a4472` (10) ·
  `3ecf32e` (11) · `48c0b31` (12) · `af7d5d3` (13) · `9d5246e` (14) · `3386c02` (15) · `20c5ad5` (16) ·
  `deda8bd91dbfebf75895c8786732a4ed9d7952f2` (17 — **blocked by this review**).
  Not candidates: `37c9597` (superseded documentation-only closeout), `c5b67495` and `25bcd7aa`
  (documentation-only freezes), and the documentation/authority commits between them.
- **Scope decision (reviewer, standing):** **do NOT delete `Index.Program` during a repair.** If the retained
  core makes it clearly redundant, record the exact redundancy and propose deletion under a separate explicit
  contract — preferably the post-C4 trim. It may remain only as the existing exact wrapper or projection; it
  must never become a parallel semantic authority.
- **Deferred process task (nonblocking, before the next accepted checkpoint):** implement the living-FCB Human
  Review Index generator required by Governance `D-07`. It must derive entries from named canonical statuses,
  produce the tracked Markdown deterministically, and FAIL both when the tracked index omits a live human act
  and when it retains a stale one. Until it lands the index carries a temporary hand-maintained disclaimer;
  `D-07` is not weakened. This task must not expand repair 16.
- **Documentation basis:** the live Fido Conformance Basis is `.review/fcb/current/` (Git-canonical per **A002**,
  living-document form per **A003** — no version suffixes, no checksum manifest; identity is
  `git rev-parse HEAD:.review/fcb/current`).
- **Scope decisions:** **ADR-0001 / SR-001 are ACCEPTED FOR CURRENT BASIS** (Rob, 2026-07-25) — Go 1.23 on
  `linux/amd64` with `GOAMD64=v1`; `int`/`uint` 64-bit and distinct from fixed-width types; reopen at C16 or any
  earlier explicit request for another target or `uintptr`. `uintptr` stays OUT until a separate reviewed scope
  change pays its price. ADR-0002 remains REJECTED AS WRITTEN / OPEN. SR-009 remains an unresolved existing
  restriction. `LAT-X004` is settled in the FCB as option (ii), the rounding-invariant accepted domain.
- **Open questions:** `.review/OPEN_QUESTIONS.md` — scoping calls and ambiguities raised from implementation
  that are neither a contract conflict nor a tracked human act. Each entry names its owner, whether it blocks,
  and **the default taken if nobody answers**. It is not authority and overrides nothing.
- **Automatic Codex review:** DISABLED.
