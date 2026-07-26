# NEXT_STEPS — active authority pointer

- **Current candidate: `deda8bd91dbfebf75895c8786732a4ed9d7952f2`.** C4 repair 15 — complete scoped
  names and retained elaboration — is **IMPLEMENTED and COMPLETE**, awaiting Rob's human C4 Implementation
  Review. Authority: `.review/C4_IMPLEMENTATION_REPAIR_15.md` (installed verbatim).
  Human repair authorization token: `C4-complete-scoped-names-and-retained-elaboration-repair-15`.
- **Current state.** All three of the reviewer's blocking classes are closed.
  1. **A005 is complete and enforced.** The old compound stems, numbered fixtures, `_T` names, local aliases
     and stale prose are gone. `tools/naming-gate.py` is statement-aware, runs in working-tree AND staged
     snapshot mode, is wired into `make check` **and** the pre-commit hook, fails closed when enumeration
     fails, and carries 30 negative controls. A retired surface enters its table when it is deleted.
  2. **`Compilable.Core` retains the whole elaboration.** Package refs, root layout, fresh-build plan, raw
     diagnostics and final diagnostics are STORED once by `build_elaboration_core`, each beside the proof that
     it IS the canonical value. Nothing is recomputed on query.
  3. **Both capabilities retain the exact core.** `Compilable.Failure` holds the very `Core` the decision
     judged (no copied diagnostic list); `Compilable.Facts` is indexed BY the accepted core and its acceptance
     evidence; `Compilable.Program` holds the accepted core. All three are **sealed** — `Compilable.compile`
     is the only mint, enforced by nine build-level negative client fixtures (F–N) plus a positive control in
     `make prove`.
- **Verification at the candidate.** `make check` green: 517/517 readable surfaces axiom-free, the
  whole-theory assumption audit, adversarial self-tests A–E, sealed-capability self-tests F–N, the pinned-Go
  whole-tree `go build ./...` against the reviewed goldens, and a byte-exact generated-module compare. **Zero
  generated-byte change across the entire repair.**
- **C4 is NOT accepted.** Only Rob accepts it, by a new human C4 Implementation Review against the candidate
  above. **C5 is FORBIDDEN** until C4 is accepted, and so are **post-C4 feature work and simplification /
  trim**.
- **Governing accepted amendments.** `FCB-A001-INTRINSIC-STATIC-CAPABILITY-PROVENANCE` / `D-22` — the opaque
  static capability must RETAIN the exact successful whole-elaboration object by construction; equality to a
  canonical rerun is never the production provenance. `FCB-A005-SCOPED-NAME-OWNERSHIP` / `D-25` — names are
  owned by their scope. Both remain **ACCEPTED**. No new amendment is required.
- **Functional contract:** `.review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md`.
  **Accepted review basis:** `.review/REVIEW_BASIS.md`.
- **Original C4 baseline:** `8c9212a8c814c7a99a5e3ef1970a0ae32425a918`.
- **Blocked C4 implementation candidates (sixteen, in order):** `89b8e54` (1) · `1c4a7de` (2) · `806ce87` (3) ·
  `af2fc87` (4) · `9d4aff5` (5) · `3b4f40e` (6) · `3a92d22` (7) · `91e8dbb` (8) · `a2a5b46` (9) · `a8a4472` (10) ·
  `3ecf32e` (11) · `48c0b31` (12) · `af7d5d3` (13) · `9d5246e` (14) · `3386c02` (15) · `20c5ad5` (16).
  The candidate above is the seventeenth; it is under review — neither blocked nor accepted.
  Not candidates: `37c9597` (superseded documentation-only closeout), `c5b67495` (documentation-only freeze),
  and the documentation/authority commits between them.
- **Retained results — do NOT regress.** Repair 15: the whole-elaboration core, the sealed capability, the one
  mint path, and the three production fixtures that answer a capability only through itself. Repair 14: the
  retained core and the decision indexed by it. Repair 13: the exact standard work-member index (`WorkIndex` /
  `forest_index`, built once, overwrite-free, total because the key-`NoDup` is a proof argument, exact in both
  directions), `index_member_at` / `forest_index_member_at`, and zero production keyed list scan. Repair 12:
  exact source-step identity — `Compilable.conversion_success_cause_yields_step`,
  `retained_convsuccess_closure` and `nested_success_bundle` return the `ConversionStep` at the EXACT source
  `ts`/`x`, no existential. A005: the module rename, the deleted old modules, the thirteen Q-08 deletions, and
  byte-identical output.
- **Scope decision (reviewer, standing):** **do NOT delete `Index.Program` during a repair.** If the retained
  core makes it clearly redundant, record the exact redundancy and propose deletion under a separate explicit
  contract — preferably the post-C4 trim. It may remain only as the existing exact wrapper or projection; it
  must never become a parallel semantic authority.
- **Deferred process task (nonblocking, before the next accepted checkpoint):** implement the living-FCB Human
  Review Index generator required by Governance `D-07`. It must derive entries from named canonical statuses,
  produce the tracked Markdown deterministically, and FAIL both when the tracked index omits a live human act
  and when it retains a stale one. The historical terminal-bundle stub must not be reused unchanged. Until it
  lands the index carries a temporary hand-maintained disclaimer; `D-07` is not weakened.
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
