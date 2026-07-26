# NEXT_STEPS — active authority pointer

- **A005 SCOPED NAMING MIGRATION — COMPLETE AND FROZEN.** `FCB-A005-SCOPED-NAME-OWNERSHIP` is **ACCEPTED**
  (Governance `D-25`); Rob authorized it — *"Ruthlessly rename away."* — to run before the C4 review resumes.
  It is applied: **`20c5ad5c499d5046563471624117b80c737c7157` is the SIXTEENTH C4 implementation candidate**,
  and the C4 Implementation Review now resumes against it.
  - **Repair 14's semantic result is preserved exactly.** The retained `Compilable.Core`, the decision indexed
    by it, the capability retaining it, and the deleted reconstruction root are unchanged in substance; only
    names moved. The generated `go.mod` and `main.go` are **byte-identical** to the pre-migration baseline.
  - **What changed:** 17 files renamed, 1015 identifier renames across 16 modules, 37 constructors, and the
    thirteen consumer-free Q-08 surfaces deleted. No compatibility alias, wrapper or re-export anywhere — Git
    history is the only compatibility layer.
  - **Enforcement:** `tools/naming-gate.py` via `make names`, wired into `make check` ahead of the container
    work, with 22 negative controls proving it both fails and accepts correctly. It exists because the Rocq
    compiler already verifies code names for free, while documentation and source comments have no verifier.
  - **Two forced deviations, recorded not hidden.** Rocq refuses to seal a bare inductive against a
    `Parameter` ("a definition is expected"), so `Index.Snapshot`'s three records keep a distinct private name
    while the public surface obeys A005 in full. Record projections share one namespace, so `Syntax.ModuleSpec`
    takes `module_path`/`module_version` rather than colliding with `Syntax.FileNode.path`.
  - **Verified on this freeze:** `make names`, `make fmt`, `make prove` (486/486 axiom-free, whole-theory
    assumption audit, self-tests A–E), `make e2e`, `make check`, `make regenerate`, `make regen-guard`, and a
    byte comparison against the baseline captured at `52dd974`.
  - C4 is **NOT accepted**. C5 and post-C4 feature work remain **FORBIDDEN**.
- **Active checkpoint:** C4 **intrinsic retained elaboration repair 14 — IMPLEMENTED; awaiting human review.**
  The repair-14 candidate is `3386c023fe10df4ae433726044d61642f219309c` (the FIFTEENTH C4 implementation
  candidate). C4 stays **BLOCKING** until Rob's new human C4 Implementation Review dispositions it; repair 14
  closes the reviewer's finding but does not accept the checkpoint.
- **Rob's authorization, 2026-07-25 (exact):** *Begin `.review/C4_IMPLEMENTATION_REPAIR_14.md` implementation on
  the current `main` head. Do not reset to `9d5246e`. Preserve all out-of-band changes already recorded in
  `.review/NEXT_STEPS.md`. C5 and the post-C4 trim remain forbidden.* Implementation begins only after the
  documentation dispositions below are recorded, which this commit does.
- **Scope decision (reviewer, 2026-07-25):** **do NOT delete `Index.Program` during repair 14.** Repair 14 is
  limited to the final retained-elaboration boundary; deleting a capability-adjacent wrapper in the same repair
  would enlarge the review surface. If the retained `Compilable.Core` makes it clearly redundant, record the
  exact redundancy and the affected queries and theorems, keep the wrapper, and propose deletion under a
  separate explicit contract — preferably the post-C4 trim, unless a correctness conflict forces it earlier.
  `Index.Program` may remain only as the existing exact wrapper or projection; it must never become a parallel
  semantic authority.
- **Deferred process task (nonblocking, before the next accepted checkpoint):** implement the living-FCB Human
  Review Index generator required by Governance `D-07`. It must derive entries from named canonical statuses,
  produce the tracked Markdown deterministically, and FAIL both when the tracked index omits a live human act
  and when it retains a stale one. The historical terminal-bundle stub must not be reused unchanged — its
  schema is provenance, not the living-FCB schema. Until it lands the index carries a temporary
  hand-maintained disclaimer; `D-07` is not weakened, and softening it would require a named amendment. This
  task must not expand repair 14.
- **The finding (NEW, holistic review).** Repair 13 is correct and intact — one immutable source authority, one
  retained `Compilable.Input`, one proof-carrying `Compilable.WorkForest`, the exact standard-map-backed `Compilable.WorkIndex`,
  no production `List.find` key lookup, exact member/step identity, one `Compilable.Accumulator` and intrinsic
  `Compilable.Trace`, exact final-to-tail causal preservation. The blocker is **outside** that expression phase:
  `elaborate_indexed` builds one exact causal chain and then **discards it**. `Compilable.Facts` retains selected
  projections; `Compilable.Program` retains `Compilable.source`/`Compilable.program_index`/`Compilable.facts` plus
  `cp_prov : elaborate Compilable.source = …` — a **Prop equality to rerunning the elaborator**, erased, whose right-hand
  side holds only the already-stripped result. That is not the exact causal object and cannot project it, so the
  current "object identity" theorems must *rebuild* the phase and prove the copies equal. Future `Safe.Program`
  proofs and user extensions cannot consume the accepted C4 causal object; they must reconstruct it. No green
  proof or test command can repair a constructor topology that does not retain the object.
- **Repair authority:** `.review/C4_IMPLEMENTATION_REPAIR_14.md` (installed verbatim).
- **Human repair authorization token:** `C4-intrinsic-retained-elaboration-fcb-a001-repair-14`.
- **Governing FCB amendment:** `FCB-A001-INTRINSIC-STATIC-CAPABILITY-PROVENANCE`, **ACCEPTED** — the opaque static
  capability must RETAIN the exact successful whole-elaboration object by construction; public queries are
  projections from it; equality to a canonical rerun is permitted only as a separate specification/determinism
  theorem and is never the production provenance. Governance decision **D-22**: opacity restricts access, it never
  authorizes discarding and later rebuilding.
- **Functional contract:** `.review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md`.
- **Accepted review basis:** `.review/REVIEW_BASIS.md`.
- **Original C4 baseline:** `8c9212a8c814c7a99a5e3ef1970a0ae32425a918`.
- **Blocked C4 implementation candidates (all fourteen):** `89b8e54` (1) · `1c4a7de` (2) · `806ce87` (3) ·
  `af2fc87` (4) · `9d4aff5` (5) · `3b4f40e` (6) · `3a92d22` (7) · `91e8dbb` (8) · `a2a5b46` (9) · `a8a4472` (10) ·
  `3ecf32e` (11) · `48c0b31` (12) · `af7d5d3` (13) · `9d5246e` (14) ·
  `3386c023fe10df4ae433726044d61642f219309c` (15 — **the candidate under review**).
- **Not candidates:** `37c9597` (superseded documentation-only acceptance closeout) and the out-of-band commits
  below. Repair 14 is implemented **on top of the current head**, never by resetting to `9d5246e`.
- **Out-of-band commits since the blocked candidate** (all after `9d5246e`, none an implementation candidate):
  `ece4c1d` campaign persistence · `5d25c42` campaign bytecode hygiene · **`4754a4a` generated-header change** ·
  `96aa8e0` Git-canonical FCB · `e6acfac` `.editorconfig` · `e004e30` living documentation ·
  `7963c6b` doc-checksum/name-version retirement + `make fmt`.
  ⚠ **Two of those touched functional paths and the reviewer must know:** `4754a4a` changed the generated header
  to `// fido was here.  woof woof.  do not edit.` — that is `Render.header`, the output-policy gate, the sink
  test, a transport-rejection fixture, two Dockerfile checks, and **every generated byte** (7 files); it was made
  at Rob's direct request and verified by full `make check`. `7963c6b` added the `fmt` Makefile target and
  `tools/fmt-check.py` (2 files; no proof, gate, or generated-output change). Every other out-of-band commit is
  documentation only. So the repair-14 base is **not** byte-identical to `9d5246e` on the functional side.
- **Documentation basis:** the live Fido Conformance Basis is `.review/fcb/current/` (Git-canonical per **A002**,
  living-document form per **A003** — no version suffixes, no checksum manifest; identity is
  `git rev-parse HEAD:.review/fcb/current`). The FCB's own Human Review Index records `C4-REVIEW` as
  **BLOCKED / AWAITING REPAIR-14 CANDIDATE**. Project libraries hold bootstrap shims only.
- **Retained results — do NOT regress.** Repair 13: the exact standard work-member index (`Compilable.WorkIndex` /
  `Compilable.forest_index`, built once, overwrite-free, total because the key-`NoDup` is a proof argument, exact in both
  directions), `index_member_at` / `forest_index_member_at`, and zero production `List.find` key lookup. Repair 12:
  exact source-step identity — `StepCause_ok_conv_inv`, `retained_convsuccess_closure` and `nested_success_bundle`
  return the `ConversionStep` at the EXACT source `ts`/`x`, no existential.
- **State:** repair-14 **IMPLEMENTED and frozen at `3386c02`.** What landed, against
  `.review/C4_IMPLEMENTATION_REPAIR_14.md` §C2–C13:
  - **`Compilable.Core p`** — the retained `Compilable.Input` plus the `Compilable.Phase` indexed by it. Because
    the input retains `Compilable.indexed` and the phase is indexed by the input, those two fields retain the WHOLE causal
    chain: work forest, the repair-13 `Compilable.WorkIndex`, type-name facts, outcome table and trace, annotation,
    fact tables, diagnostics. Built ONCE by `build_elaboration_core`.
  - **`Compilable.Decision core`** — indexed BY that exact core, so an accepted decision cannot be about a
    different elaboration than the one held. `Compilable.Elaboration` is now `(Compilable.elaboration_core, Compilable.decision)`.
  - **`Compilable.Program`** retains `Compilable.core` + `Compilable.accepted` (the accepted evidence over THAT core). `Compilable.program_index`,
    `Compilable.facts`, `Compilable.program_phase` and `Compilable.program_input` are all
    PROJECTIONS (five further ones were retired by A005 Part D). `Compilable.Facts` survives as a constructed VIEW (`Compilable.facts = core_facts …`), which is
    `OPEN_QUESTIONS` Q-06's recorded default (a) — taken, and Q-06 retired with this commit.
  - **`outcome_of_elaboration` lost its `elaborate p = a` argument entirely**; `Compilable.compile` passes the exact
    object through. One reduction fact `Compilable.compile_on_core` replaces the whole shape-lemma chain.
  - **`Safe.Program` retains it too** — `Safe.core`, `certify_retains_capability`, `certify_retains_core`.
  - **Reconstruction root DELETED, not deprecated:** `cp_prov`, `compilable_prov`,
    `compilable_index_retained`, `elaboration_ok_full`, `elaborate_ok_whole`, `elaborate_failed_whole`,
    `elaborate_whole_failed_not_valid`, `go_compile_ok_shape`, `go_compile_failed_shape`, the four
    `outcome_of_elaboration_*` shape lemmas, and the `elaborate_ok_seals_*` rebuilt-phase forms (replaced by
    `core_seals_facts` / `core_seals_tnfacts` / `built_core_tnfacts_from_input`, all `reflexivity`).
  - **Fixtures project instead of rebuild:** `deep_nested_seals_eft` reads its fact table off the capability;
    `over_program_failure_carries_core_diags` reads the rejected diagnostics off the same core the decision
    judged.
  - **Retention theorems hold by `reflexivity`** — `compilable_retains_phase` / `_expr_facts` / `_tnfacts`.
    That is the substance of the repair: when the object is retained, identity stops being an argument.
  - **Verification:** `make check` green. Axiom-free gate **479 → 487** surfaces; whole-theory assumption audit
    over constants + inductives + named; adversarial self-tests A–E; e2e whole-tree `go build ./...`; generated
    module byte-identical (no generated byte changed). The pre-commit hook verified the STAGED snapshot.
  - **Scope honoured:** `Index.Program` was NOT deleted (reviewer scope decision). It survives as the exact
    wrapper `Compilable.core_indexed`/`Compilable.program_index` project through, never a parallel semantic authority. Repair 13's results are
    intact — `Compilable.WorkIndex`/`Compilable.forest_index` and zero production keyed list scan.
  - **Q-08 closed by deletion (A005 Part D).** All thirteen consumer-free surfaces are GONE, not renamed —
    the seven the reconstruction root orphaned, and the six repair 14 introduced and never used — together
    with the single gate entry that named one of them. The exact thirteen are the `DELETED_SURFACES` table in
    `tools/naming-gate.py`, which fails the build if any of them ever reappears. This dedicated repository-wide
    migration is a separate explicit contract, so the earlier scope reason for postponing the deletion no
    longer applies. `.review/OPEN_QUESTIONS.md` Q-08 is removed by this commit; Q-07 stands.
  - **Not done, and not in scope:** the Governance `D-07` living-FCB Human Review Index generator (deferred
    nonblocking task above) and any FCB regeneration, which is the reviewer's to author on acceptance. The FCB's
    own boundary section still names `9d5246e`; that is authored text and I did not rewrite it.
- **Scope decisions:** **ADR-0001 / SR-001 are ACCEPTED FOR CURRENT BASIS** (Rob, 2026-07-25) — Go 1.23 on
  `linux/amd64` with `GOAMD64=v1`; `int`/`uint` 64-bit and distinct from fixed-width types; reopen at C16 or any
  earlier explicit request for another target or `uintptr`. `uintptr` stays OUT until a separate reviewed scope
  change pays its price, and this acceptance authorizes neither C5 nor the post-C4 trim.
  ADR-0002 remains REJECTED AS WRITTEN / OPEN. SR-009 remains an unresolved existing restriction. `LAT-X004` is
  settled in the FCB as option (ii), the rounding-invariant accepted domain. No numeric-model or scope change was
  made by this authority install.
- **Open questions:** `.review/OPEN_QUESTIONS.md` — scoping calls and ambiguities raised from implementation
  that are neither a contract conflict nor a tracked human act. Each entry names its owner (reviewer or Rob),
  whether it blocks, and **the default I take if nobody answers**, so no question stalls the work silently. It
  is not authority and overrides nothing. All five questions raised on `d2fad7f` were answered on 2026-07-25
  and are removed. Q-06 (`Compilable.Facts` as a constructed view vs dissolved into projections) was taken at
  its recorded default (a) and retired with the repair-14 freeze. Q-07 stands as an informational note about
  scripted-edit discipline; it seeks no action.
- **Automatic Codex review:** DISABLED.
- **C5 is FORBIDDEN** until C4 is accepted. **Post-C4 simplification / trim is FORBIDDEN** until C4 is accepted.
