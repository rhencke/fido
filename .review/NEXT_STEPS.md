# NEXT_STEPS — active authority pointer

This file alone owns the current checkpoint and candidate state.
`.review/fcb/current/FIDO_FCB_HUMAN_ACTS.tsv` alone owns the set of open human acts.

<!-- FIDO-HUMAN-ACT:C4-REVIEW -->

- **C4 REPAIR 19 IS IMPLEMENTED AND COMPLETE.**
  Authority: `.review/C4_IMPLEMENTATION_REPAIR_19.md` (installed verbatim). <!-- FIDO-FCB-REF:REVIEW-C4-IMPLEMENTATION-REPAIR-19-MD -->
- **Candidate offered for human review.** `0ffdc5f7019204a868d75ef709a16fb69a9979d5` is the C4
  implementation candidate. `50c3bcc5b8eb2e47074352f5c9f0124e71509396` was the twentieth blocked candidate
  and is superseded. All six blocker classes are closed; the mandatory whole-system closure audit is
  `.review/C4_REPAIR_19_CLOSURE_AUDIT.md` <!-- FIDO-FCB-REF:REVIEW-C4-REPAIR-19-CLOSURE-AUDIT-MD --> and the
  obligation matrix `.review/C4_REPAIR_19_OBLIGATION_MATRIX.tsv` reads 19 of 19 closed.
- **C4 is still NOT accepted.** Only Rob accepts it. Awaiting his human C4 Implementation Review.
- **The six blocker classes repair 19 must close.**
  1. **`A005` is still incomplete.** The UpperCamelCase local notation aliases the naming migration rejected
     were still declared in `Compilable.v`, `Safe.v` and `Render.v`, five of them entirely unused, and the
     naming gate had no rule for the class. All eight are now deleted — `TypedProgram`, `Resolve`, `Stmt`,
     `Decl`, `File`, `SourceFile` and their duplicates — every use is qualified, and `make names` rejects the
     whole class rather than a list of those names.
  2. **The public cause theorems erase exact source occurrence identity.** The accepted and rejected proofs
     look up exact source locals (int8 at 11, int16 at 9, int32 at 7, int64 at 5) and then state only that
     SOME work member has a matching expression shape. A syntactically equal conversion at another occurrence
     satisfies the same public field. **The proofs know more than the theorem statements.**
  3. **The `Safe` and `Emit` constructor-opacity controls are vacuous.** The shared `sealed` helper imports
     only `Syntax` and `Compilable`, so controls Y, Z, AA, AE, AF and AG can pass because the module was never
     loaded rather than because the constructor is sealed.
  4. **The naming-gate unreadable-file self-test can print `SKIP`**, count that skipped control among the five
     read/enumeration controls, and still report all 47 passed.
  5. **`D-24` checks declared rows but never proves complete declaration.** Adding a new dangling operational
     path to the FCB Index leaves the gate green, which disproves the repair-18 claim as written.
  6. **Stale and weaker residue remains:** a live `legacy-class` comment, and an explicitly weaker theorem
     whose only named consumer was its own assumptions-gate line. Being gated is not a semantic purpose.
     Both are now deleted, and the weaker theorem is in the naming gate's deleted-surface table so it
     cannot return unnoticed.
- **Obligation tracking.** `.review/C4_REPAIR_19_OBLIGATION_MATRIX.tsv` holds one row per repair-19 obligation. <!-- FIDO-FCB-REF:REVIEW-C4-REPAIR-19-OBLIGATION-MATRIX-TSV -->
  `make claims` refuses to let `.review/REVIEW_REQUEST.md` request review while any row is open — freezing
  early is a gate failure, not a judgement call.
- **What repair 17 achieved and must NOT regress.** The A006 authority commit landed before implementation;
  `Emit.Mint.Token` is opaque and indexed by the exact `Safe.Program` and exact bytes; `Emit.Mint.issue` is the
  sole authority-producing operation; `Emit.Image` is a reducible carrier whose pack constructor is not a mint;
  `Emit.MakeImage` is deleted; `Safe.Program` is abstract with `Safe.certify` its one mint;
  `Compilable.Core`/`Program`/`Failure`/`Facts` remain sealed; the legacy collapsed result peer and its support
  closure are deleted; the naming gate parses record fields before judging them and fails closed on read or
  decode errors; the causal fixtures are generalised over arbitrary retained `Input`/`Phase`; generated
  `go.mod` and `main.go` are byte-identical to the reviewed baseline.
- **What repair 18 achieved and must NOT regress.**
  1. **The returned-object theorem topology understates and splits the guarantee.** ✅ **CLOSED.**
     `Compilable.deep_nested_compile_fixture` and `Compilable.deep_fail_compile_fixture` are one accepted and
     one rejected root, each over ONE exact returned object, carrying `AcceptedFixture cp Hcp` /
     `RejectedFixture fail`. `Hcp` is the `Compiled` branch's own source proof, not a fresh equation.
     `accepted_conversion_cause` / `rejected_conversion_cause` / `childfail_conversion_cause` take their suffix
     and tail accumulator as PROJECTIONS of `total_forest_outcome_cause`, so no foreign pair satisfies them;
     the index, outcome-domain and trace claims are whole-object laws over EVERY member and EVERY present key;
     and the rejected side pins the phase, RAW and FINAL diagnostic lists to the exact singleton
     `InvalidConversion` reason. `Emit.deep_nested_emit_fixture` destructs the accepted root ONCE and carries
     that same witness through certify and mint. No prohibited builder appears in either root's statement or
     proof. The split peers they absorbed are deleted.
  2. **Governance `D-07` is accepted, due, and unimplemented.** ✅ **CLOSED.** The set of open human acts is
     now discovered from `.review/fcb/current/FIDO_FCB_HUMAN_ACTS.tsv`; the Human Review Index is its
     generated view and the temporary disclaimer is gone. `tools/human-review-index.py` writes and verifies
     it, `make human-acts` gates it in `make check` and in the pre-commit hook over the exported staged tree,
     and nineteen adversarial controls — each must-fail one pinned to the reason it must fail on — keep the
     checker from reporting a green it can no longer earn.
  3. **The live corpus does not state one truth and violates `D-24`.** ✅ **CLOSED.** One thing owns each
     fact: this file owns the candidate and the active repair; `FIDO_FCB_HUMAN_ACTS.tsv` owns the open human
     acts; the Roadmap owns checkpoint order; `PROGRESS.md` and `ARCHITECTURE.md` own the proof and feature
     inventory; Git owns superseded narratives. `REVIEW_REQUEST.md`, the Roadmap, `PROGRESS.md` and
     `SOURCE_FOREST_STATUS.md` stopped restating candidate state; C5 is the permanent `Machine` base
     everywhere, with `uintptr` a priced scope change against the ADOPTED ADR-0001; the dangling
     repair-6 and evidence-sandbox paths are gone; the stale legacy-class comments are gone. `make fcb` now
     gates all three live-FCB documents, including the D-24 typed-reference manifest.
- **No new amendment is required.** Repair 19 implements and enforces accepted `A001`–`A006`, Governance
  `D-07` and `D-22`–`D-26`, and the already-accepted repair-18 contract. Repair 18's directive, matrix and
  closure audit are retired from the live tree; Git history is their archive.
- **C4 is NOT accepted.** Only Rob accepts it. **C5, checkpoint-definition Step 0, post-C4 features, the broad
  source cleanup and proof-module partitioning remain FORBIDDEN.**
- **Governing accepted amendments.** `A001` through `A006` remain **ACCEPTED**; Governance owns `D-01` through
  `D-26`.
- **Functional contract:** `.review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md`. <!-- FIDO-FCB-REF:REVIEW-C4-SOURCE-TYPE-NAME-CONVERSION-PLAN-MD -->
  **Accepted review basis:** `.review/REVIEW_BASIS.md`. <!-- FIDO-FCB-REF:REVIEW-REVIEW-BASIS-MD -->
- **Original C4 baseline:** `8c9212a8c814c7a99a5e3ef1970a0ae32425a918`.
- **Blocked C4 implementation candidates (all twenty):** `89b8e54` (1) · `1c4a7de` (2) · `806ce87` (3) ·
  `af2fc87` (4) · `9d4aff5` (5) · `3b4f40e` (6) · `3a92d22` (7) · `91e8dbb` (8) · `a2a5b46` (9) · `a8a4472` (10) ·
  `3ecf32e` (11) · `48c0b31` (12) · `af7d5d3` (13) · `9d5246e` (14) · `3386c02` (15) · `20c5ad5` (16) ·
  `deda8bd` (17) · `12b1bc9` (18) · `92fc04e` (19) ·
  `50c3bcc5b8eb2e47074352f5c9f0124e71509396` (20).
  Not candidates: `37c9597`, and the documentation-only freezes `c5b67495`, `25bcd7aa`, `c8ce2d8c`,
  `e15232d3` and `2b848871c7faf4a9586c8b20b4896e1ec543987c`.
- **Retained results — do NOT regress.** Repair 18: one accepted and one rejected root fixture over one
  exact returned object, the cause-owned predicates projecting their suffix and tail accumulator from
  `total_forest_outcome_cause`, the exact singleton rejected diagnostic, D-07, and the typed D-24 manifest.
  Repair 17: the A006 mint, the sealed `Safe.Program`, the corrected
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
