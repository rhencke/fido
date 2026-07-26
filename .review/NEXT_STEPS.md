# NEXT_STEPS — active authority pointer

This file alone owns the current checkpoint and candidate state.
`.review/fcb/current/FIDO_FCB_HUMAN_ACTS.tsv` alone owns the set of open human acts.

<!-- FIDO-HUMAN-ACT:C4-REVIEW -->

- **Active work: C4 REPAIR 18 — the sole active C4 task.**
  Authority: `.review/C4_IMPLEMENTATION_REPAIR_18.md` (installed verbatim).
  Human implementation authorization token: `C4-returned-cause-human-index-coherence-repair-18`.
  Implementation base: the reviewed freeze. Do not reset, rebase, rewrite history, or discard accepted
  `A001`–`A006` work.
- **Candidate status.** `92fc04e264b56d575e2fd1d65ae5d7940c93dc84` is **BLOCKING** — the nineteenth
  blocked C4 implementation candidate. `e15232d3ef894c2f478e36c736cd701533e224fe` is its
  **documentation-only freeze**, not a separate candidate.
- **What repair 17 achieved and must NOT regress.** The A006 authority commit landed before implementation;
  `Emit.Mint.Token` is opaque and indexed by the exact `Safe.Program` and exact bytes; `Emit.Mint.issue` is the
  sole authority-producing operation; `Emit.Image` is a reducible carrier whose pack constructor is not a mint;
  `Emit.MakeImage` is deleted; `Safe.Program` is abstract with `Safe.certify` its one mint;
  `Compilable.Core`/`Program`/`Failure`/`Facts` remain sealed; the legacy collapsed result peer and its support
  closure are deleted; the naming gate parses record fields before judging them and fails closed on read or
  decode errors; the causal fixtures are generalised over arbitrary retained `Input`/`Phase`; generated
  `go.mod` and `main.go` are byte-identical to the reviewed baseline.
- **The three findings repair 18 must close.**
  1. **The returned-object theorem topology understates and splits the guarantee.** The accepted evidence is
     spread across four theorems each binding its own existential `cp`, and the rejected evidence across three.
     No single public statement retains one exact returned object across the whole guarantee. The cause
     bundles restate consequences instead of naming the exact `RetainedMemberCause` projected from the exact
     retained trace; the index and outcome claims are point queries rather than whole-object exactness; and
     the rejected side proves `<> nil` where the contract requires the exact singleton reason.
     **The freeze prose claimed more than any one theorem statement carried — a green proof cannot upgrade a
     weaker statement.**
  2. **Governance `D-07` is accepted, due, and unimplemented.** ✅ **CLOSED.** The set of open human acts is
     now discovered from `.review/fcb/current/FIDO_FCB_HUMAN_ACTS.tsv`; the Human Review Index is its
     generated view and the temporary disclaimer is gone. `tools/human-review-index.py` writes and verifies
     it, `make human-acts` gates it in `make check` and in the pre-commit hook over the exported staged tree,
     and nineteen adversarial controls — each must-fail one pinned to the reason it must fail on — keep the
     checker from reporting a green it can no longer earn.
  3. **The live corpus does not state one truth and violates `D-24`.** Contradictory candidate and repair
     states across REVIEW_REQUEST, the Roadmap, PROGRESS and SOURCE_FOREST_STATUS; a stale gate count; C5
     misdescribed as `uintptr` plus rune literals; dangling operational paths; stale legacy-class comments.
- **No new amendment is required.** Repair 18 implements and enforces accepted `A001`–`A006`, Governance
  `D-07` and `D-22`–`D-26`, and the already-accepted repair-17 contract.
- **C4 is NOT accepted.** Only Rob accepts it. **C5, checkpoint-definition Step 0, post-C4 features, the broad
  source cleanup and proof-module partitioning remain FORBIDDEN.**
- **Governing accepted amendments.** `A001` through `A006` remain **ACCEPTED**; Governance owns `D-01` through
  `D-26`.
- **Functional contract:** `.review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md`.
  **Accepted review basis:** `.review/REVIEW_BASIS.md`.
- **Original C4 baseline:** `8c9212a8c814c7a99a5e3ef1970a0ae32425a918`.
- **Blocked C4 implementation candidates (all nineteen):** `89b8e54` (1) · `1c4a7de` (2) · `806ce87` (3) ·
  `af2fc87` (4) · `9d4aff5` (5) · `3b4f40e` (6) · `3a92d22` (7) · `91e8dbb` (8) · `a2a5b46` (9) · `a8a4472` (10) ·
  `3ecf32e` (11) · `48c0b31` (12) · `af7d5d3` (13) · `9d5246e` (14) · `3386c02` (15) · `20c5ad5` (16) ·
  `deda8bd` (17) · `12b1bc9` (18) · `92fc04e264b56d575e2fd1d65ae5d7940c93dc84` (19).
  Not candidates: `37c9597`, and the documentation-only freezes `c5b67495`, `25bcd7aa`, `c8ce2d8c` and
  `e15232d3ef894c2f478e36c736cd701533e224fe`.
- **Retained results — do NOT regress.** Repair 17: the A006 mint, the sealed `Safe.Program`, the corrected
  naming gate, the causal theorems over any retained phase. Repair 16: the direct package chain and the sealed
  `Core`. Repair 15: the whole-elaboration core, the sealed capability, the one mint path. Repair 13: the exact
  standard work-member index. Repair 12: exact source-step identity. A005: the module rename and
  byte-identical output.
- **Scope decision (reviewer, standing):** **do NOT delete `Index.Program` during a repair.**
- **Documentation basis:** the live Fido Conformance Basis is `.review/fcb/current/` (Git-canonical per **A002**,
  living-document form per **A003**; identity is `git rev-parse HEAD:.review/fcb/current`).
- **Scope decisions:** **ADR-0001 / SR-001 ACCEPTED FOR CURRENT BASIS** (Rob, 2026-07-25) — Go 1.23 on
  `linux/amd64` with `GOAMD64=v1`; `int`/`uint` 64-bit and distinct from fixed-width types. `uintptr` requires
  reopening ADR-0001 or adopting a replacement scope/target decision and paying its full inclusion price.
  ADR-0002 remains REJECTED AS WRITTEN / OPEN. SR-009 remains an unresolved existing restriction. `LAT-X004` is
  settled as option (ii), the rounding-invariant accepted domain.
- **Open questions:** `.review/OPEN_QUESTIONS.md`.
- **Automatic Codex review:** DISABLED.
