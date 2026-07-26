# NEXT_STEPS — active authority pointer

- **Active work: C4 REPAIR 15 — complete scoped names and retain the exact whole elaboration.**
  Authority: `.review/C4_IMPLEMENTATION_REPAIR_15.md` (installed verbatim).
  Human repair authorization token: `C4-complete-scoped-names-and-retained-elaboration-repair-15`.
  Implementation base: **the current repository head.** Do not reset, rebase, rewrite history, force-push, or
  revert the A005 migration.
- **Current candidate state.** `20c5ad5c499d5046563471624117b80c737c7157` (`refactor(names): make namespaces own
  their names`) is **BLOCKING** — the sixteenth blocked C4 implementation candidate. The freeze
  `c5b67495fb5f5af4bfc289fd50248f6436c1c376` is **documentation-only** and is not a separate candidate.
  **Repair 14 is NOT accepted; it is subsumed by repair 15.**
- **The three blocking classes (reviewer, 2026-07-26).**
  1. **A005 is not complete.** Forbidden old stems (`Index.expression_eq_dec`, `Index.key_equalb`, `Index.float_decimal_eq_dec`,
     `Compilable.elaboration_accepted_iff_admissible`, `Compilable.expression_all_ok_iff_typed_program`), numbered fixture names
     (`fixture_2001…2016`), type-derived theorem names, fake local aliases (`TypedProgram`, `Resolve`, `Stmt`,
     `Decl`, `File`, `SourceFile`), cryptic private `_T` names, and stale prose all survive. **The naming gate
     accepts several of them by design and can return a false green when Git enumeration fails** — it checks
     prefixes only at position zero, treats an embedded pseudo-qualifier as acceptable, misses lowercase
     compounds of retired types, does not enforce declaration-kind casing, misses multiline record fields,
     scans a limited extension set, ignores a `git ls-files` failure, omits untracked non-ignored files, and is
     **not run by the staged pre-commit hook**. A gate whose enumeration fails open is not a gate.
  2. **`Compilable.Core` does not retain the whole elaboration.** It stores only the input and the expression
     phase; package refs, root layout, build plan, raw diagnostics and final diagnostics are recomputed
     functions. A later equality to a source function is specification, not retained production identity.
  3. **The public failure discards the exact rejected core.** `Failure` stores a copied diagnostic list only,
     so the returned value cannot project the core that produced it. `Compilable.Facts` is likewise indexed
     only by program/index and has a public raw constructor, so it is not an opaque view of the exact core.
- **What the A005 candidate got right and must be kept.** The Go-domain file/module prefix is gone; the main
  public phase types use qualified scoped names; old modules were deleted rather than aliased; 17 files were
  renamed; the thirteen consumer-free Q-08 surfaces were deleted; generated Go bytes are unchanged; proof,
  e2e, regeneration and staged checks were green.
- **Governing accepted amendments.** `FCB-A001-INTRINSIC-STATIC-CAPABILITY-PROVENANCE` / `D-22` — the opaque
  static capability must RETAIN the exact successful whole-elaboration object by construction; equality to a
  canonical rerun is never the production provenance. `FCB-A005-SCOPED-NAME-OWNERSHIP` / `D-25` — names are
  owned by their scope. **No new amendment is required**; A001 and A005 already decide the correct result and
  repair 15 completes their implementation.
- **Functional contract:** `.review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md`.
  **Accepted review basis:** `.review/REVIEW_BASIS.md`.
- **Original C4 baseline:** `8c9212a8c814c7a99a5e3ef1970a0ae32425a918`.
- **Blocked C4 implementation candidates (all sixteen):** `89b8e54` (1) · `1c4a7de` (2) · `806ce87` (3) ·
  `af2fc87` (4) · `9d4aff5` (5) · `3b4f40e` (6) · `3a92d22` (7) · `91e8dbb` (8) · `a2a5b46` (9) · `a8a4472` (10) ·
  `3ecf32e` (11) · `48c0b31` (12) · `af7d5d3` (13) · `9d5246e` (14) · `3386c02` (15) ·
  `20c5ad5c499d5046563471624117b80c737c7157` (16 — **the candidate under review**).
  Not candidates: `37c9597` (superseded documentation-only closeout), `c5b67495` (documentation-only freeze),
  and the documentation/authority commits between them.
- **Retained results — do NOT regress.** Repair 13: the exact standard work-member index (`WorkIndex` /
  `forest_index`, built once, overwrite-free, total because the key-`NoDup` is a proof argument, exact in both
  directions), `index_member_at` / `forest_index_member_at`, and zero production keyed list scan. Repair 12:
  exact source-step identity — `Compilable.conversion_success_cause_yields_step`, `retained_convsuccess_closure` and
  `nested_success_bundle` return the `ConversionStep` at the EXACT source `ts`/`x`, no existential.
  A005: the module rename, the deleted old modules, the thirteen Q-08 deletions, and byte-identical output.
- **Scope decision (reviewer, standing):** **do NOT delete `Index.Program` during a repair.** If the retained
  core makes it clearly redundant, record the exact redundancy and propose deletion under a separate explicit
  contract — preferably the post-C4 trim. It may remain only as the existing exact wrapper or projection; it
  must never become a parallel semantic authority.
- **Deferred process task (nonblocking, before the next accepted checkpoint):** implement the living-FCB Human
  Review Index generator required by Governance `D-07`. It must derive entries from named canonical statuses,
  produce the tracked Markdown deterministically, and FAIL both when the tracked index omits a live human act
  and when it retains a stale one. The historical terminal-bundle stub must not be reused unchanged. Until it
  lands the index carries a temporary hand-maintained disclaimer; `D-07` is not weakened. This task must not
  expand repair 15.
- **Documentation basis:** the live Fido Conformance Basis is `.review/fcb/current/` (Git-canonical per **A002**,
  living-document form per **A003** — no version suffixes, no checksum manifest; identity is
  `git rev-parse HEAD:.review/fcb/current`). Governance owns `D-01` through `D-25`. Project libraries hold
  bootstrap shims only.
- **Scope decisions:** **ADR-0001 / SR-001 are ACCEPTED FOR CURRENT BASIS** (Rob, 2026-07-25) — Go 1.23 on
  `linux/amd64` with `GOAMD64=v1`; `int`/`uint` 64-bit and distinct from fixed-width types; reopen at C16 or any
  earlier explicit request for another target or `uintptr`. `uintptr` stays OUT until a separate reviewed scope
  change pays its price. ADR-0002 remains REJECTED AS WRITTEN / OPEN. SR-009 remains an unresolved existing
  restriction. `LAT-X004` is settled in the FCB as option (ii), the rounding-invariant accepted domain.
- **Open questions:** `.review/OPEN_QUESTIONS.md` — scoping calls and ambiguities raised from implementation
  that are neither a contract conflict nor a tracked human act. Each entry names its owner, whether it blocks,
  and **the default taken if nobody answers**. It is not authority and overrides nothing.
- **Automatic Codex review:** DISABLED.
- **C5 is FORBIDDEN** until C4 is accepted. **Post-C4 feature work and simplification / trim are FORBIDDEN**
  until C4 is accepted.

## History (not current state)

Repair 14 (`3386c02`) replaced the reconstruction root — `cp_prov`, the whole-equation scaffolding, and the
`elaborate_ok_seals_*` rebuilt-phase forms — with a retained core and a decision indexed by it.
That result is real and is kept, but it retained the exact core only on the accepted capability path and only
for the input and expression phase. Repair 15 finishes it. The A005 migration (`20c5ad5`) then renamed the
repository under `D-25`; its law is accepted and its first implementation is incomplete.
