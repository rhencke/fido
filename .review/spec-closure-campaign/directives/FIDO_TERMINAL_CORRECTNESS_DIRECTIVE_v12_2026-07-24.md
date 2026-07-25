# FIDO — TERMINAL CORRECTNESS DIRECTIVE, v12 (SPEC-CLOSURE FAMILY, FINAL PASS — SELF-CONTAINED)

**Date:** 2026-07-24
**Issued by:** Rob (human authority). This file is the directive.
**Repair authorization token:** `SPEC-CLOSURE-terminal-repair-2` (unchanged)
**Version:** v12 — self-contained, sealing-only revision of v11. **This document alone is sufficient to execute and audit the repair. Earlier directives are provenance only, and no normative sentence below refers to any of them.**
**Supersedes (full hashes):** v11 `428c609766f08025686580ab88fa25c02e06fb339629c10ec6023ed9c77d7540`; v10 `d16c64d7db3cac6fd094c3d6aeeab045569cb34f2a0da59d4d5cb352e77d9685`; v9 `9f4e0ebcafba65db941c68fdf276c022e00fea6eae9cfcfe64df70a375215be2`; v8 `2173975c624f67fd892647ac76acfe1ed3eb6a70299ba6872d2f14ea0c67e994`; v7 `5c1996a5c2bffc8f0bad43e4f1c6fde328d997deb0bafeb2586e92ee60b0db15`; v6 `dc7a369120ab23c548998739111d1eb7ef7edcfac652dd9d634cfab494cc3562`; v5 `5a083bf157cd97644755517e7e7fa1a8f31c5bcd65fa9a4b5b4a39106d44d6c9`; v4 `eab3b1ed4b856157f7c784a6a7bcd35f5abe454cd558fb631b1f6772095648ff`; v3 `6a99418c02cba3063bc43e61a71c48197fe3a55889d5c18f0225d5b78dbc011b`; v2 `d8b2a9c71355ed0163b00bfa6a3aa9ca6dd6646a1ca80d30dd0596a022d560a2`; v1 `b30c03b8c16a09868763f891ec2fd92f3a03f2a0739c852b497a536b70502a34`.
**Baseline:** `FIDO_GO1_23_SPEC_CLOSURE_REVIEW_BUNDLE_R1_2026-07-23.zip`, SHA-256 `a01a7be5160b10e83bce11ed2161e353a94ca9bd86ef2843aca9fe29e1da303e`.
**Provenance:** Authored by Claude (Fable 5, external adversarial reviewer). Return-volley round 11 by ChatGPT under Rob's direct amended-archive instruction: `REOPENS(D-15)` — v11 moved the fixed-point manifest to the late-governance phase but its inventory rule still allowed only the audit JSON, freeze record, and SHA manifest; `REGRESSION(D-06)` — v11 identified its frozen live directive as “v10” inside the read-only evidence rule; `NEW` — the provenance paragraph called the self-reference class both its fifth occurrence and a count of four; `NEW` — the newly required verifier checks were not part of a closed check-function inventory. All four are corrected here, and each defect class now has a linter or package-validator regression check. The D-15 defect is the self-reference bug class's **fifth** occurrence; the self-reference bug-class count is **five**. No architecture, language-semantics, latitude-policy, or toolchain-policy change is made.

---

## AUTHORITY LIMITS (binding, complete)

1. Documentary artifacts, pins, scripts, fixtures, and recorded observations only. Compiling and executing probe fixtures against the pinned toolchain **to record evidence** is in scope. Modifying the Fido repository — source, `.v` files, build system, gates — is not.
2. Nothing produced by this repair may claim FIXED, accepted, closed, countersigned, spec-closed-in-implementation, or any score. Models record `APPLIED` at most.
3. Every countersign cell is created empty and remains Rob's alone.
4. This directive does not accept C4, does not authorize C5, and does not alter the active C4 repair authority or `NEXT_STEPS.md` state.
5. Normative text may not contain unpinned claims. World-knowledge is not evidence; pinned artifacts, hashes, and captured observations are.
6. One authority per meaning, for code, documents, and directives alike. Versions supersede by name and full hash; two live directives never coexist; a directive is self-contained, and phrases of the form "as in v8" are defects in normative text. The live-version identity is one checked tuple: filename, title, `Version` field, leading `Supersedes` entry, and every normative self-reference must agree.
7. Changes only under a T-row's authorization, at change granularity (T-0). External reviews, prior directives, and copied ADR records are read-only evidence: byte-identical unless one exact T-row expressly authorizes replacement.
8. The executor receives no discretion over protection strength: Appendix A is an exact normative table; the registry must equal it **field for field** (`fixed_point_registry_exact`); the selector specification defines what selectors mean and never chooses which selector a fixed point uses; amendments to Appendix A require a directive revision.

## FIXED POINTS (complete statements; protected per Appendix A; weakening any is a regression)

**ARCH-01.** The plan §1 deletion and generalization standard — the five retention tests and the prohibition list.
**ARCH-02.** The minimal `Machine` base (§2); no Go feature defines a second run relation.
**ARCH-03.** The one-owner-per-meaning authority chain (§3).
**ARCH-04.** The expression fact/use split (§5) — the use builder does not inspect the raw child again.
**ARCH-05.** The single type algebra (§6): `RuntimeType := SemanticType Empty_set`, alias non-identity, declaration-reference recursion.
**ARCH-06.** The static-slot / dynamic-place distinction (§11).
**ARCH-07.** Stack-only panic / defer / recover (§13) with `finishing_pushes_only_deferred_activations` and `above_finishing_iff_deferred_call`.
**ARCH-08.** Resource-local origins with proof-connected provenance (§15).
**ARCH-09.** Finite bad-prefix safety with liveness held separate (§17).
**ARCH-10.** Rejection of vacuous library safety from an empty start set (§19).
**ARCH-11.** The Do-Not-Do-Early list (§24), verbatim.
**ARCH-12.** The candidate-only acceptance stance (§26) with Rob as sole disposition owner.
**EVID-01.** Pinned spec SHA-256 `c47fb4b5b795b9732cbae0250dcb84f791df78bb98695b30fb3f7788d1c9b389`; pinned memory-model SHA-256 `366b995adeee8b57bd23547feea8252a7ee619baec91cb22cfb21b12208da2c6`; the pinned document bytes themselves.
**EVID-02.** Reproducible audit and latitude extraction: shipped scripts re-run to byte-identical frozen outputs; the frozen candidate manifest is preserved whole, header included; the freeze record's byte-reproduction claim is preserved verbatim.
**EVID-03.** Route A evaluation-order nondeterminism (plan §12.4) and its contract (`SC-20-EVAL-ORDER-LATITUDE`, plan §25.21) including the deterministic left-to-right call/method/receive fixture obligations stated inside that contract section.
**EVID-04.** The FMA both-branches model (latitude row LAT-121, STEP-NONDET) with its pinned-target observation recorded as adequacy evidence, never spec truth.
**EVID-05.** Select-choice (LAT-X002), map-iteration (closure row SPEC-X006), and scheduler (LAT-X003) nondeterminism as STEP-NONDET; `print`/`println` output as ADEQUACY-DEMOTION (closure row SPEC-X005).
**EVID-06.** BOUND-001..003 — emitted `go 1.23` directive equals the ledger language version; module path from the single ModulePath authority; no `toolchain` directive — and the recorded invocation contract (`GOTOOLCHAIN=local`, `GOENV=off`, `GOWORK=off`, `go version` verified before build).
**EVID-07.** The terminal observation tuple (plan §22.3): stdout bytes, stderr projection, exit status; `println` → stderr; fatal panic → exit 2 with first-line projection `panic: <value>`; runtime noise excluded explicitly.
**EVID-08.** APPLIED-only model provenance; empty Rob countersign columns; and the audit's split between machine-checkable claims and human judgment.
**EVID-09.** The synthesized-anchor flags in the heading manifest and the grammar counting rule (174 definitions / 173 names, metagrammar included, `Expression` twice) in the grammar manifest.
**EVID-10.** The NaN-map semantics row (SPEC-124) and struct-tag rows (SPEC-026: identity includes tags; conversion ignores tags per the pinned rule), each with their plan fixture obligations.
**EVID-11.** `SC-21-PROOF-COST-INTERNALS` at plan §25.22 — never overwritten, renumbered, or weakened.
**EVID-12.** `uintptr` remains OUT pending ADR-0001.

---

## T-0 — BLOCKING — BASELINE DELTA AND PRESERVATION

**Rule:** the terminal bundle is an authorized transformation of the exact R1 baseline; **every change has exactly one T-owner** at change granularity; files carry owner sets.

**Canonical artifacts.**

**A. File delta — `.review/FIDO_TERMINAL_FILE_DELTA_2026-07-23.tsv`** (`tools/generate_file_delta.py`). Columns: `baseline_path`, `terminal_path`, `baseline_kind`, `terminal_kind`, `baseline_sha256`, `terminal_sha256`, `action`, `owners`, `rationale`. Enums: `action ∈ {UNCHANGED, MODIFIED, ADDED, RENAMED, DELETED}`; `kind ∈ {MISSING, REGULAR_FILE}`. Regular files only; directory entries derive from paths. Paths relative to the bundle content root. RENAMED uses both path columns; ADDED leaves baseline cells empty; DELETED leaves terminal cells empty; `owners` = sorted set equal to the change-ledger derivation.

**B. Change ledger — `.review/FIDO_TERMINAL_CHANGE_LEDGER_2026-07-23.tsv`** (`tools/generate_change_ledger.py`). Columns: `change_id`, `path`, `selector_kind`, `selector`, `baseline_fragment_sha256`, `terminal_fragment_sha256`, `owner`, `rationale`. Each changed unit has exactly one owner.

**C. Fixed-point registry and manifest.** **One producer for both: `tools/generate_fixed_point_manifest.py`.** At step 6 it transcribes the registry `.review/FIDO_TERMINAL_FIXED_POINT_REGISTRY_2026-07-23.tsv` **by parsing Appendix A of the frozen in-bundle copy of this directive under the Canonical Transcription Rules — the sole source; no second embedded copy may exist** (D-13 repair). At step 11 — **after** the audit JSON and freeze record exist, so components whose terminal paths are those artifacts resolve without any cycle (D-01 repair) — it produces the manifest `.review/FIDO_TERMINAL_FIXED_POINT_MANIFEST_2026-07-23.tsv` = registry + verified `baseline_projection_sha256` + `terminal_projection_sha256`. The manifest is a **late governance artifact**: not a phase-1 input, never hashed by the audit JSON, checked in the terminal verifier. Registry columns: `fixed_point_id`, `component_id`, `baseline_path`, `terminal_path`, `selector_kind`, `selector`, `protected_projection`. Unique key `(fixed_point_id, component_id)`.

**D. Selector specification — `.review/FIDO_TERMINAL_SELECTOR_SPEC_2026-07-23.md`.** Defines, for every selector kind: syntax; parse rules; normalization; selected raw byte spans; selected semantic projection; canonical hash input; failure rules; overlap rules. Binding minimums:
- `whole-file`: raw file bytes; cannot coexist with any other content selector for that file.
- `markdown-heading`: the heading line only. `markdown-section`: the unique heading line whose text begins with the selector string, through the line before the next heading of equal or higher level; resolution fails unless exactly one heading matches.
- `anchored-region`: selector = `START…END` marker pair; both markers must occur exactly once; markers included; a single-line region uses identical START and END.
- `python-symbol`: via the Python AST; one top-level function, class, or named assignment; includes its decorators and any immediately preceding contiguous comment block.
- `json-pointer`: RFC 6901 against a canonical JSON encoding (sorted keys, UTF-8, LF).
- Tabular files: the spec declares each file's primary-key column (closure CSV → `id`; latitude ledger TSV → `latitude_id`; heading manifest → `anchor`; grammar manifest → `production` with ordinal disambiguation; the delta/ledger/registry → their stated keys). `table-row`: one keyed semantic row. `table-field`: one named field in one keyed row. `table-schema`: the ordered header and schema rules. Table projections use UTF-8, LF, one fixed escaping.
- `file-property`: metadata namespace (line ending, path, mode, generated status), separate from normalized content.
- **Projection kinds (closed):** `raw-bytes`; `normalized-section-text`; `anchored-normalized-text`; `named-fields` (listed field values of one keyed row); `key-presence` (a JSON key exists); `header-row` (a table's ordered header). Appendix A names one per component.
- **Orthogonality is a closed listed relation:** `file-property:*` ⟂ normalized semantic selectors; `table-schema` ⟂ `table-row`/`table-field` on existing fields; `whole-file` ⟂ nothing in the content namespace; `anchored-region` and `markdown-section` are not orthogonal where spans intersect. Content selectors' union must equal the complete structural diff: no uncovered change, no doubly owned change.
- All canonical TSVs: UTF-8, LF, no BOM, one fixed escaping, rows sorted by primary key.

**Audit obligations (step 9):**
- `baseline_delta_complete` — structural diff per the selector spec: every changed unit appears exactly once; exactly one owner each; no entry names an unchanged unit; orthogonality only per the closed relation; file-level owner sets equal change-level sets; no unlisted change, missing baseline file, or unlisted addition; no altered external review or prior directive.
- `fixed_point_registry_exact` — **every field of every registry row equals Appendix A as parsed from the frozen in-bundle directive under the Canonical Transcription Rules**, never a second embedded copy (runs at step 9 on the phase-1 registry).
- `fixed_point_manifest_complete` (terminal verifier) — parent-ID set exactly ARCH-01..12 ∪ EVID-01..12; every ID has ≥1 component; component-key set equals Appendix A; no key twice; each component resolves exactly once in the verified R1 baseline and exactly once in the terminal tree; every stored baseline hash matches a fresh recomputation from R1 bytes; the audit never trusts a written hash.
- `fixed_points_preserved` (terminal verifier) — per component, terminal projection hash equals the recomputed baseline projection hash.
- `check_artifact_graph_acyclic` (terminal verifier; new) — derives the realized containment graph (who hashes or covers whom, across every governance artifact) and proves it is a DAG. The five-occurrence self-reference bug class is thereby gated, not watched.
- `check_derived_governance_ownership` (terminal verifier; new; D-09 repair) — every derived governance file (change ledger, file delta, audit JSON, freeze record, fixed-point manifest, SHA manifest) carries owner **T-0 by rule**, was produced by its named hashed producer from frozen inputs, and no other file uses the exception.
- `check_late_artifact_inventory_consistent` (terminal verifier; new; D-15 regression gate) — proves that `late_governance_outputs`, the build order, inventory-completeness rule, scope exclusions, and `final_in_bundle` name the same exact artifact set.
- `check_live_directive_identity` (terminal verifier; new; D-06 regression gate) — proves that the in-bundle directive filename, title, `Version` field, leading `Supersedes` entry, read-only-evidence self-reference, and recorded directive SHA identify one live version.

**Set definitions (once; CR9 inventory correction):**
`phase1_inputs` = all ordinary inputs (tools, pins, fixtures, captured evidence, canonical tables, generated Markdown, plan, ADR records, T-disposition ledger, Human-Review Index, this directive) **+ selector spec + fixed-point registry + change ledger + file delta**.
`late_governance_outputs` = audit JSON + freeze record + **fixed-point manifest** + SHA manifest.
`final_in_bundle` = `phase1_inputs` + `late_governance_outputs`. The terminal verifier proves both equations and rejects any artifact that belongs to neither set.

**Scopes.** Change-ledger scope excludes: itself; the file delta; the audit JSON; the freeze record; the fixed-point manifest; the SHA manifest. File-delta scope excludes: itself; the audit JSON; the freeze record; the fixed-point manifest; the SHA manifest; it includes and hashes the completed selector spec, registry, and change ledger. The verifier assigns **every derived governance file** its owner by rule — change ledger, file delta, audit JSON, freeze record, fixed-point manifest, SHA manifest → T-0 — enforced by `check_derived_governance_ownership`; no other file may use this exception (D-09 repair).

**Read-only evidence rule.** External reviews, prior directives, and copied ADR records remain byte-identical. This v12 directive enters the bundle (ADDED, owner T-0) under its exact SHA-256, computed at delivery.

---

## PART 0 — FREEZE PROTOCOL, EVIDENCE CHAIN, AND CANONICAL ARCHIVE

**Acyclicity.** The audit JSON hashes only inputs (all `phase1_inputs`) — never itself, the freeze record, the SHA manifest, the ZIP, or the sidecar. The freeze record, generated from the audit JSON by `tools/generate_freeze_record.py`, lists predecessor ZIP hashes, the audit JSON hash, and the SHA manifest's filename and coverage rule (never its hash), **and emits verbatim the protected byte-reproduction claim block (Appendix A, EVID-02/byte-reproduction-claim)**. The SHA manifest (`tools/generate_sha_manifest.py`) hashes every in-bundle file except itself. The ZIP's SHA-256 exists only in the external sidecar, pinned format `<lowercase-sha256><two spaces><zip-filename><LF>`, written by `tools/write_zip_sidecar.py`.

**Producer inventory (shipped, hashable files; no unnamed shell commands):** `tools/audit_spec_closure_bundle.py`; `tools/verify_terminal_bundle.py`; `tools/extract_latitude.py`; `tools/render_ledger_md.py`; `tools/run_fixture.py`; `tools/generate_file_delta.py`; `tools/generate_change_ledger.py`; `tools/generate_fixed_point_manifest.py`; `tools/generate_freeze_record.py`; `tools/generate_sha_manifest.py`; `tools/generate_human_review_index.py`; `tools/build_deterministic_bundle.py`; `tools/write_zip_sidecar.py`. The audit JSON records every producer/verifier SHA-256, plus the Python implementation, version, and executable hash.

**Closed check-function inventory (names exact; every cited `check_*` function must appear here and every listed function must exist as one top-level `python-symbol`):**
- Audit: `check_row_totality`; `check_acceptance_alignment_trichotomy`; `check_acceptance_alignment_justifications`; `check_duplicate_representation_histogram`; `check_line_endings`; `check_ragged_rows`; `check_id_prefix_discipline`; `check_single_open_latitude`; `check_contract_definitions`; `check_baseline_delta_complete`; `check_fixed_point_registry_exact`; `check_distribution_members_match`; `check_local_distribution_manifest_complete`; `check_replay_generated_outputs`; `check_replay_probe_fixtures`; `check_index_versus_discovery`.
- Terminal verifier: `check_fixed_point_manifest_complete`; `check_fixed_points_preserved`; `check_artifact_graph_acyclic`; `check_derived_governance_ownership`; `check_late_artifact_inventory_consistent`; `check_live_directive_identity`; `check_freeze_claims_match`; `check_manifest_coverage_and_hashes`; `check_inventory_drift`; `check_final_in_bundle`; `check_archive_profile`; `check_post_extract_bytes`.

The directive linter rejects any cited `check_*` name absent from this inventory and any inventory entry that is never cited by the ownership split, build order, completion rule, or an audit obligation.

**Replay duties (step 9; temporary area only; frozen captures never rewritten):** re-run latitude extraction and byte-compare (`check_replay_generated_outputs`); re-render the ledger Markdown from canonical CSV/TSV and byte-compare (same check); re-run every probe fixture compare-only under the T-9 profile — fresh empty `GOCACHE`, `GOMODCACHE`, `GOPATH`, and temp per replay — comparing stdout, stderr, status, command record, and effective-environment record (`check_replay_probe_fixtures`).

**Distribution member proofs — typed.** `distribution_members_match ∈ {PASS-CONFIRMED, PENDING-PROVENANCE, FAIL}`. Confirmed: extract each pin's exact tar member path (from `PINS_MANIFEST.tsv`) out of the verified tarball; byte/mode/symlink-compare; record path and result; require PASS-CONFIRMED. Pending: PENDING-PROVENANCE with `local_distribution_manifest_complete = PASS`; every affected pin and observation `PROVENANCE-PENDING`. Covered pins at least: pinned spec HTML; pinned memory-model HTML; `go/bin/go` hash record; pinned cmd/go sources; pinned modfile source. Repo-tag pins name an exact external artifact and SHA-256. Audit top status ∈ {`PASS-CONFIRMED`, `PASS-WITH-PENDING-PROVENANCE`, `FAIL`}; pending is never called green.

**Tarball storage (decided):** the official `go1.23.2.linux-amd64.tar.gz` is an EXTERNAL-AUDIT-INPUT (`PINS_MANIFEST.tsv` row: origin URL, version, official SHA-256 or PENDING, exact expected local path). Confirmed mode verifies presence and hash there before extraction.

**Inventory completeness.** The audit JSON contains the complete set and SHA-256 of every `phase1_inputs` file. The verifier rejects any addition, deletion, or byte change; only the exact members of `late_governance_outputs` may be added after the phase-1 audit.

**Canonical archive profile (all constants pinned; CR9-5):** built only by `tools/build_deterministic_bundle.py`. Exactly one root `FIDO_GO1_23_SPEC_CLOSURE_REVIEW_BUNDLE_TERMINAL_2026-07-23/`. **No directory entries at all** — every entry is a regular file whose path carries the root prefix; directories are implied. Entry order: bytewise lexicographic by full path. Timestamp `1980-01-01 00:00:00`. Compression `ZIP_STORED`; compressed size must equal uncompressed size per entry; ZIP64 forbidden. Creator system `3` (Unix); version-made-by `20`; version-needed `20`; general-purpose flags `0x0000` (entry paths must be ASCII); internal attributes `0x0000`; external attributes `0x81A40000` (regular file, mode 0644). Archive comment empty; entry comments empty; extra fields empty (local and central); central-directory and local-header fields must agree. Builder and verifier share every constant above. Step 14 additionally verifies each entry's stated sizes against the staged expected file sizes **before** any extraction.

**Build order — eighteen steps, 0–17:**
0. Verify the R1 baseline ZIP SHA-256 (`a01a7be5160b10e83bce11ed2161e353a94ca9bd86ef2843aca9fe29e1da303e`).
1. Extract the baseline into a clean tree.
2. Create the terminal working tree.
3. Apply all substantive T-row changes, recorded at change granularity.
4. Produce all ordinary phase-1 inputs, including the selector spec, the T-disposition ledger, and this directive's frozen copy.
5. Generate the Human-Review Index from the completed T/F/R/ADR sources (`tools/generate_human_review_index.py`).
6. Generate the fixed-point registry (`tools/generate_fixed_point_manifest.py`, parsing the frozen directive; must equal Appendix A field-for-field).
7. Generate the change ledger.
8. Generate the file delta.
9. Run the phase-2 audit; write the frozen audit JSON.
10. Generate the freeze record from the audit JSON.
11. Generate the fixed-point manifest (registry + both trees + the now-existing late artifacts).
12. Generate the in-bundle SHA manifest.
13. Run the terminal verifier against the staged tree (writes nothing; nonzero on failure) — including the fixed-point, acyclicity, and derived-ownership checks.
14. Build the ZIP per the canonical archive profile.
15. Inspect the archive directly, **before writing any extracted file**: one exact root; no duplicate normalized names; no absolute paths; no `.`/`..`; no symlinks or unsupported types; no directory entries; sorted entries; timestamp, attributes, flags, versions, STORED, size equality per the profile; empty comments and extra fields; central/local agreement; the exact expected entry set; per-entry stated sizes versus staged sizes.
16. Extract with a safe extractor into a clean directory; run the terminal verifier there; compare extracted bytes against the in-bundle manifest.
17. Write the external sidecar in the pinned format. Rob verifies it externally.

**Two-script split.** Audit (step 9) owns: `check_row_totality`; `check_acceptance_alignment_trichotomy`; `check_acceptance_alignment_justifications`; `check_duplicate_representation_histogram`; `check_line_endings`; `check_ragged_rows`; `check_id_prefix_discipline`; `check_single_open_latitude`; `check_contract_definitions`; `check_baseline_delta_complete`; `check_fixed_point_registry_exact`; `check_distribution_members_match`; `check_local_distribution_manifest_complete`; `check_replay_generated_outputs`; `check_replay_probe_fixtures`; `check_index_versus_discovery`. Terminal verifier (steps 13, 15–16) owns: `check_fixed_point_manifest_complete`; `check_fixed_points_preserved`; `check_artifact_graph_acyclic`; `check_derived_governance_ownership`; `check_late_artifact_inventory_consistent`; `check_live_directive_identity`; `check_freeze_claims_match`; `check_manifest_coverage_and_hashes`; `check_inventory_drift`; `check_final_in_bundle`; `check_archive_profile`; `check_post_extract_bytes`.

---

## PART A — SUBSTANTIVE REPAIRS (complete)

### T-1 — BLOCKING — Acceptance alignment

**Background.** Eleven "Implementation restriction" latitude rows share one justification claiming compile-time acceptance "does not vary the meaning of a program." That claim is false for Fido's differential obligation: the fresh-build preflight makes pinned-gc acceptance part of the pipeline's health, so a Fido-accepts / gc-rejects divergence is a Fido correctness failure. The preflight is the last line of defense, not the mechanism.

**ADR-0003 (PROPOSED, for Rob; verbatim in the ADR log; cited from every acceptance row):**

> **ADR-0003 — Authority ordering (PROPOSED).**
> 1. Where the pinned Go specification is definite, the specification governs meaning.
> 2. Where the specification grants latitude, is silent, or is hand-wavy, the pinned gc toolchain (go1.23.2) governs, and **Fido's acceptance must be a subset of pinned-gc acceptance**. Fido explicitly targets the official gc implementation only; no other Go implementation is a target.
> 3. Where pinned gc demonstrably contradicts definite specification text (a toolchain bug), the divergence is recorded as a ledger row and dispositioned by Rob; it is never silently adopted in either direction.
>
> **Interpretation clause.** In tier 2, "pinned gc governs" governs the supported **acceptance profile** and **pinned-toolchain adequacy claims**. It does not reduce a formal behavior set that definite specification latitude requires `GoMachine` to admit. Route A evaluation order, FMA alternatives, select choice, map iteration order, and scheduler choice remain fixed points unless a separately countersigned ledger disposition states otherwise. A permitted-set model is required because the pinned specification grants both branches. Current linux/amd64 evidence records only one target observation; other platform observations require their own pinned evidence and ledger revision.

**Requirements:**
1. Disposition kind **`ACCEPTANCE-ALIGNMENT`**: fields = pinned-toolchain acceptance observation (per T-9), Fido elaboration obligation, named contract, **individual** justification. Audit: no two ACCEPTANCE-ALIGNMENT justification strings identical.
2. **Classification trichotomy**, audit-enforced over every implementation-restriction candidate: `ACCEPTANCE-ALIGNMENT` (in-scope accepted-language restriction); `OUT-COVERED` (feature priced out — LAT-180 and LAT-181 both land here, resolving their inconsistency); `NOT-LATITUDE` (exposition or deterministic prohibition only — LAT-118 is a prohibition guaranteeing deterministic wrap, owned by SC-05; LAT-214 is exposition; both receive accurate individual justifications).
3. Re-disposition individually under the trichotomy: LAT-019, LAT-049, LAT-077, LAT-085, LAT-134, LAT-148, LAT-171, LAT-177, LAT-180, LAT-181, LAT-118, LAT-214, and any other implementation-restriction candidate.
4. New contract **`SC-22-ACCEPTANCE-ALIGNMENT` at plan §25.23** (§25.22 is `SC-21-PROOF-COST-INTERNALS` and is untouched): states `fido_accepts_subset_pinned_gc` as a standing obligation **frozen here and discharged at the checkpoints that implement its restriction cases**. Three claims separated: **Formal** — `CompilableProgram` satisfies every accepted ledger restriction (future theorem, per checkpoint); **External** — a publishable `DirectoryImage` passes the pinned-gc preflight (enforced at publication); **Evidence** — pinned-gc probes record the selected acceptance profile (this pass). A finite probe set does not prove the global theorem.
5. **Evidence now / gates later.** Per ACCEPTANCE-ALIGNMENT row, this pass: **runs** the pinned-gc fixture and captures raw stdout, stderr, and exit status per T-9; **freezes** the future Fido half — exact fixture source, expected diagnostic ID, expected diagnostic text-or-shape, owner, implementing checkpoint — marked **`PENDING-IMPLEMENTATION`**; and **never claims** a Fido-produced diagnostic. First frozen instances: unused local variables; constant acceptance bounds (probe pinned gc's limits); duplicate constant switch cases.
6. **Constant VALUE semantics — LAT-X004, ownership frozen.** Spec-permitted rounding during untyped constant folding can change an *accepted* constant's value (array lengths, comparisons, emitted output); acceptance rows cannot own that. Ownership fixed now — Rob's open decision concerns the **policy**, never the owning layer: **owning closure row SPEC-096 (Constant expressions); semantic owner: `ExprFact`, the constant expression's intrinsic exact value; contract: `SC-05-EXPR-FACT-USE-EVAL` at plan §25.6.** `SC-22` owns only entry into `CompilableProgram`; `SC-02-CONSTANTS-LITERALS` (plan §25.3) owns representation primitives and may support the proof without owning folding results. Latitude columns on every row: `decision_status`, `rob_choice`, `rob_countersign`; all rows `DISPOSITIONED` except `LAT-X004: HUMAN-CHOICE-OPEN` with empty choice and countersign; audit: the open set equals exactly `{LAT-X004}`. Menu for Rob, inside the fixed owner: (i) admit all specification-permitted rounded values; (ii) prove accepted constants invariant under the permitted rounding latitude — including the domain-restriction variant tying to the constant acceptance bounds so exact and pinned-gc values provably coincide; (iii) implement the exact pinned-gc constant profile as an explicit Rob-approved refinement. **Advisory recommendation, labeled as such (both reviewers, independently): option (ii), domain-restriction variant.** Process: the terminal bundle ships with LAT-X004 open; Rob's selection — informed by this pass's constant-bound probes — triggers regeneration, re-audit, and re-freeze as the first step of the FCB transformation. The freeze record states the open decision explicitly.

### T-2 — REQUIRED — Pinned distribution execution; confirmed/pending modes

Delete the 13.8 MB in-bundle executor (`.review/pins/go1.23.2-linux-amd64`). A binary cannot self-attest; `go` delegates to `pkg/tool/linux_amd64/compile` and `link` and consumes the standard library under `GOROOT`, so hashing only `bin/go` does not pin the compiler that judges the fixture.

**Confirmed mode** (required for `TERMINAL-REPAIR-CANDIDATE`): the official tarball **bytes** are present at the recorded external path; the official SHA-256 is confirmed; the tarball's hash matches. The runner **always extracts the verified bytes into a fresh sandbox and runs that tree**; the member `go/bin/go` hash is a secondary check.

**Pending mode** (tarball bytes unavailable): copy the local Go distribution into the fixed sandbox; create a complete manifest of regular files, symlink targets, and executable modes; hash that manifest; run only from that copied sandbox; mark **every** observation and **every unproved pin** `PROVENANCE-PENDING`; record the local-tree manifest in the evidence and the audit JSON; completion cannot be claimed. An official hash without the bytes populates the expected pin value but cannot convert pending evidence into confirmed evidence.

Pending provenance is listed in the Human-Review Index and forces `OPEN-REVIEW-CANDIDATE`. The evidence doc keeps the provenance chain (official tarball hash, member paths, local hashes).

### T-3 — REQUIRED — Racy-run modeling scope: option (b)

Option (a) (havoc at-and-after the first race) is rejected: `step : State -> Label -> State -> Prop` receives no trace, so (a) requires race history in `State`, a taint field, an operational detector beside the trace-based definition, or a second run rule — each adds state or a second authority, violating the no-trace-in-state law. Therefore: LAT-217, LAT-218, LAT-219, LAT-224 remain STEP-NONDET, modeling the memory-model latitude directly; `DataRace` remains a derived finite BadPrefix; plan §27 gains the reserve, in substance verbatim: *sub-value and machine-word access granularity is deliberate proof cost that affects condemned runs, not reachable safe-run behavior; it may be narrowed only by a future countersigned ledger disposition*; the four rows' contract citations name only the owning channel/race contract, and the copied `SC-20-EVAL-ORDER-LATITUDE` tails are removed.

### T-4 — REQUIRED — Template drift measurable

Populate `template: lexical-only` on the 48 OP- and 25 KEY- rows and any other justified shared-text rows; no unflagged shared representation text may remain. The audit emits the **full** duplicate-representation histogram, sorted by count then text hash, into the frozen JSON. The old-template regex check stays.

---

## PART B — SHOWROOM ITEMS (complete; N = non-substantive, still required)

- **T-5. Line endings.** Every tabular artifact (CSV and TSV) is LF; the audit checks uniformity; the closure CSV is currently CRLF and must be normalized; its change-ledger entry is `file-property` / `line-ending` / owner T-5, orthogonal to table-level entries.
- **T-6. Contract definitions audited, not token text.** The plan gains the full mapping table SC-00 = §25.1 … SC-20 = §25.21, SC-21 = §25.22 (pre-existing), SC-22 = §25.23 (new). `check_contract_definitions` parses the actual `### 25.N \`SC-XX-…\`` headings and proves: exactly one §25 definition per SC identifier; exactly one identifier per heading; the table is a byte-for-byte projection of the headings; contiguity SC-00..SC-22; every ledger citation names a defined heading; no defined contract uncited without an explicit stated reason. Citation relevance is fixed by hand this pass.
- **T-7. ID discipline.** `LAT-###` are stable manifest ordinals, never renumbered; hand-added rows use `LAT-X###` (next: LAT-X004). `BOUND-###` are live boundary rows; `BOUND-X###` are priced exclusions. The audit checks prefixes.
- **T-8. Freeze claims emitted, not typed.** Every count in the freeze record is read from the audit JSON; `freeze_claims_match` runs in the terminal verifier.
- **T-9. Closed probe environment, one canonical profile.** One runner, `tools/run_fixture.py`, executing per T-2 (verified sandbox distribution only), starting from an **empty environment** and applying exactly **`.review/tools/PROBE_ENVIRONMENT.tsv`**, which defines the **complete** allowed key set — unknown keys fail the audit: `GOROOT` (verified sandbox root), `PATH` (fixed, minimal), `HOME`, `TMPDIR`, `GOCACHE`, `GOMODCACHE`, `GOPATH` (all sandbox; caches fresh and empty per replay), `LANG`, `LC_ALL`, `TZ`, `GODEBUG` (empty), `GOTRACEBACK`, `GOOS=linux`, `GOARCH=amd64`, `GOAMD64=v1` (any other value is an explicit target decision), `CGO_ENABLED=0`, `GOFLAGS=""`, `GOPROXY=off`, `GOTOOLCHAIN=local`, `GOENV=off`, `GOWORK=off`. The profile also states the process umask, the fixed sandbox root, and the path-normalization rule for path-bearing output. The runner records the exact command and effective `go env` per run; raw stdout, stderr, and exit status are retained beside each fixture. Flagged as a proposed BOUND-003 strengthening for the implementing checkpoint — no repo change now.
- **T-10. Pins manifest.** `.review/pins/PINS_MANIFEST.tsv`: filename, upstream origin (**exact tar member path**, or repo path at tag as an exact external artifact with SHA-256, or EXTERNAL-AUDIT-INPUT for the tarball), version, SHA-256 (or PENDING per T-2). Naming convention `<artifact>_<version>.<ext>`; the freeze references the manifest.
- **T-11. One canonical source per table.** The closure CSV and the Latitude Ledger TSV are canonical; `tools/render_ledger_md.py` consumes both and generates the entire ledger Markdown headed `GENERATED FROM CSV/TSV — DO NOT EDIT`; step 9 regenerates and byte-compares.
- **T-12. Ragged-row detection** across all TSV/CSV files.
- **T-13. Self-describing audit.** The audit JSON records: a schema version; the SHA-256 of every producer and verifier tool in Part 0's inventory; the Python provenance record; the typed top status. The schema **retains** the keys `checkable_only` and `judgment_not_certified` (protected by Appendix A, EVID-08).
- **T-14. Platform-pending note.** One sentence in the closure ledger header and the evidence doc: the platform target set is under pending ADR-0004 (multi-platform 64-bit); all current toolchain evidence is `go1.23.2 linux/amd64` scope; no platform rows in this pass.
- **T-15 (N). Root README** listing every bundle file with a one-line purpose.
- **T-16 (N). Supersession chain, acyclic.** The freeze record lists predecessor ZIP hashes (original bundle; R1 `a01a7be5160b10e83bce11ed2161e353a94ca9bd86ef2843aca9fe29e1da303e`), the frozen audit JSON hash, and the SHA manifest's filename and coverage rule — never its own ZIP's hash, which lives only in the external sidecar. Names this the final bundle under the spec-closure family name.
- **T-17 (N). FMA margin note, verbatim, placed in a NEW evidence-doc section `## 5. Margin notes` — outside every protected projection:** "The one-bit `x*y+z` vs `math.FMA` discrepancy doubles as a CPU-feature parlor trick: a pure-Go fingerprint of fused-multiply-add hardware paths. Recorded here for delight; not load-bearing."
- **T-18 (REQUIRED). Human-Review Index — discovery-based.** Generated at step 5 by `tools/generate_human_review_index.py` from completed sources; discovers every unresolved human act, never hardcoded: T rows from the canonical T-19 TSV; F and R rows from their existing frozen sources; every empty Rob countersign; every ADR with status PROPOSED, OPEN, PENDING, or REJECTED-AS-WRITTEN/OPEN; every open latitude decision; every pending pin or provenance confirmation; every row explicitly marked as requiring a human act. Minimum terminal contents: ADR-0001 (PROPOSED), ADR-0002 (REJECTED AS WRITTEN / OPEN), ADR-0003 (PROPOSED), ADR-0004 (pending), LAT-X004, all empty F-/R-/T- countersigns, toolchain provenance if pending. Every cited ADR exists in-bundle as a frozen read-only record or is named as an external authority with exact path and SHA-256. `check_index_versus_discovery` fails on omissions and stale rows. Carried into the FCB transformation.
- **T-19 (REQUIRED). Canonical T-disposition ledger.** `.review/FIDO_TERMINAL_CORRECTNESS_DISPOSITIONS_2026-07-23.tsv`, columns: `id`, `severity`, `model_record`, `artifact_locations`, `applied_change`, `rob_countersign`. Rows: T-0 through T-19; values: `model_record = APPLIED`, `rob_countersign` empty. Sole T-disposition authority; a generated Markdown view is permitted; the Human-Review Index discovers T rows from this TSV only.

---

## COMPLETION (exact status values)

- **`TERMINAL-REPAIR-CANDIDATE`**: every T-deliverable (T-0..T-19; N-items included); T-0's five artifacts complete with `check_baseline_delta_complete`, `check_fixed_point_registry_exact`, `check_fixed_point_manifest_complete`, and `check_fixed_points_preserved` green; the eighteen-step order (0–17) followed with archive inspection before extraction, `check_artifact_graph_acyclic`, `check_derived_governance_ownership`, `check_late_artifact_inventory_consistent`, and `check_live_directive_identity` green in the terminal verifier; producer inventory, replay checks, and `check_index_versus_discovery` green; `distribution_members_match = PASS-CONFIRMED` and audit top status `PASS-CONFIRMED`; ADR-0003 present verbatim and PROPOSED; **LAT-X004 the sole open Latitude Ledger disposition** (other open human acts are enumerated by the Human-Review Index, never denied); all PENDING-IMPLEMENTATION rows carry frozen future-Fido fixture specs with no claimed Fido observations; every terminal-verifier run exits successfully without rewriting any frozen artifact; T-19 all `APPLIED` with empty countersigns; nothing claims acceptance, closure, FIXED status, or a score.
- **`OPEN-REVIEW-CANDIDATE`**: identical except provenance — `distribution_members_match = PENDING-PROVENANCE`, `local_distribution_manifest_complete = PASS`, top status `PASS-WITH-PENDING-PROVENANCE`, no failed checks, exactly the declared pending items, every affected pin and observation `PROVENANCE-PENDING`, and the freeze record stating explicitly that completion is blocked and why.

Deliver `FIDO_GO1_23_SPEC_CLOSURE_REVIEW_BUNDLE_TERMINAL_2026-07-23.zip` plus its external sidecar. Rob's countersigns — indexed by T-18 from T-19 and the frozen F/R sources, with his LAT-X004 policy choice at the FCB regeneration — end the correctness volleys.

---

## APPENDIX A — NORMATIVE FIXED-POINT COMPONENT REGISTRY (exact; `fixed_point_registry_exact` compares every field)

Legend: `PLAN` = `.review/FIDO_GO1_23_SPEC_CLOSURE_ARCHITECTURE_PLAN_2026-07-23.md`; `LTSV` = `.review/FIDO_GO1_23_LATITUDE_LEDGER_2026-07-23.tsv` (key `latitude_id`); `CCSV` = `.review/FIDO_GO1_23_SPEC_CLOSURE_LEDGER_2026-07-23.csv` (key `id`); `EVD` = `.review/FIDO_GO1_23_PINNED_TOOLCHAIN_EVIDENCE_R1_2026-07-23.md` (terminal path: its T-2/T-14-updated successor, same filename); `FRZ` = `.review/FIDO_GO1_23_SPEC_CLOSURE_FREEZE_R1_2026-07-23.md` → terminal `.review/FIDO_GO1_23_SPEC_CLOSURE_FREEZE_TERMINAL_2026-07-23.md`; `AJSON` = `.review/FIDO_GO1_23_SPEC_CLOSURE_AUDIT_R1_2026-07-23.json` → terminal `.review/FIDO_GO1_23_SPEC_CLOSURE_AUDIT_TERMINAL_2026-07-23.json`. Where one path is shown, baseline_path = terminal_path.

| fixed_point_id/component_id | path(s) | selector_kind | selector | protected_projection |
|---|---|---|---|---|
| ARCH-01/charter | PLAN | markdown-section | `## 1. Standard` | normalized-section-text |
| ARCH-02/charter | PLAN | markdown-section | `## 2. Permanent Public Semantic Base` | normalized-section-text |
| ARCH-03/charter | PLAN | markdown-section | `## 3. Complete Authority Chain` | normalized-section-text |
| ARCH-04/charter | PLAN | markdown-section | `## 5. Facts Depend on Exact Source Roles` | normalized-section-text |
| ARCH-05/charter | PLAN | markdown-section | `## 6. One Type Algebra` | normalized-section-text |
| ARCH-06/charter | PLAN | markdown-section | `## 11. Static Bindings and Dynamic Cells Are Different` | normalized-section-text |
| ARCH-07/charter | PLAN | markdown-section | `## 13. Panic, Defer, and Recover` | normalized-section-text |
| ARCH-08/charter | PLAN | markdown-section | `## 15. One Structured Label per Transition` | normalized-section-text |
| ARCH-09/charter | PLAN | markdown-section | `## 17. Safety Is a Finite Bad-Prefix Property` | normalized-section-text |
| ARCH-10/charter | PLAN | markdown-section | `## 19. Starts` | normalized-section-text |
| ARCH-11/charter | PLAN | markdown-section | `## 24. Current Repository Reconciliation` | normalized-section-text |
| ARCH-12/charter | PLAN | markdown-section | `## 26. Acceptance and Freeze Rule` | normalized-section-text |
| EVID-01/spec-pin-bytes | `.review/pins/go_spec_go1.23.html` | whole-file | — | raw-bytes |
| EVID-01/memmodel-pin-bytes | `.review/pins/go_mem_2022-06-06.html` | whole-file | — | raw-bytes |
| EVID-02/extractor-script | `.review/tools/extract_latitude.py` | whole-file | — | raw-bytes |
| EVID-02/frozen-candidate-manifest | `.review/FIDO_GO1_23_LATITUDE_MANIFEST_2026-07-23.tsv` | whole-file | — | raw-bytes |
| EVID-02/byte-reproduction-claim | FRZ | anchored-region | `The audit byte-reproduces` … `SHA-256 manifest.` | anchored-normalized-text |
| EVID-03/order-model | PLAN | markdown-section | `### 12.4 Order-of-evaluation latitude` | normalized-section-text |
| EVID-03/order-contract | PLAN | markdown-section | `### 25.21 \`SC-20-EVAL-ORDER-LATITUDE\`` | normalized-section-text |
| EVID-04/fma-row-core | LTSV | table-row | `LAT-121` | named-fields {disposition, owner_row, contract, justification} |
| EVID-04/fma-observation | EVD | markdown-section | `## 1. Ordinary multiply-add is not fused by default` | normalized-section-text |
| EVID-05/select-choice | LTSV | table-row | `LAT-X002` | named-fields {disposition, owner_row, contract} |
| EVID-05/map-iteration | CCSV | table-row | `SPEC-X006` | named-fields {disposition, owner, test} |
| EVID-05/scheduler-choice | LTSV | table-row | `LAT-X003` | named-fields {disposition, owner_row, contract} |
| EVID-05/print-println-demotion | CCSV | table-row | `SPEC-X005` | named-fields {disposition, owner, test} |
| EVID-06/bound-001 | CCSV | table-row | `BOUND-001` | named-fields {disposition, representation} |
| EVID-06/bound-002 | CCSV | table-row | `BOUND-002` | named-fields {disposition, representation} |
| EVID-06/bound-003 | CCSV | table-row | `BOUND-003` | named-fields {disposition, representation} |
| EVID-06/invocation-contract | EVD | anchored-region | `The adequacy invocation uses` … `workspace selection.` | anchored-normalized-text |
| EVID-07/tuple-section | PLAN | markdown-section | `### 22.3 Terminal observation tuple` | normalized-section-text |
| EVID-08/f-disposition-rule | `.review/FIDO_ARCHITECTURE_F_DISPOSITIONS_2026-07-23.md` | anchored-region | `**Disposition rule:**` … `plan §26.` | anchored-normalized-text |
| EVID-08/checkable-claims-key | AJSON | json-pointer | `/checkable_only` | key-presence |
| EVID-08/judgment-key | AJSON | json-pointer | `/judgment_not_certified` | key-presence |
| EVID-09/heading-manifest | `.review/FIDO_GO1_23_SPEC_HEADING_MANIFEST_2026-07-23.tsv` | whole-file | — | raw-bytes |
| EVID-09/grammar-manifest | `.review/FIDO_GO1_23_SPEC_GRAMMAR_MANIFEST_2026-07-23.tsv` | whole-file | — | raw-bytes |
| EVID-10/nan-map-row | CCSV | table-row | `SPEC-124` | named-fields {disposition, representation} |
| EVID-10/struct-tag-row | CCSV | table-row | `SPEC-026` | named-fields {disposition, representation} |
| EVID-10/struct-tag-fixtures | PLAN | anchored-region | `Required struct-tag fixtures:` … `pinned rule permits it.` | anchored-normalized-text |
| EVID-10/nan-map-fixture | PLAN | anchored-region | `- a NaN-keyed map entry is insertable` … `removed by \`clear\`;` | anchored-normalized-text |
| EVID-11/sc21-contract | PLAN | markdown-section | `### 25.22 \`SC-21-PROOF-COST-INTERNALS\`` | normalized-section-text |
| EVID-12/uintptr-pre-row | CCSV | table-row | `PRE-22` | named-fields {disposition, price} |

**Total: 41 components** (12 ARCH + 29 EVID). **Canonical Transcription Rules (normative; D-13 repair):** the Legend's aliases are definitions — each expands to its exact quoted path; `A → B` means baseline_path A and terminal_path B; a single path means baseline_path = terminal_path; `—` means the empty selector, permitted only with `whole-file`; backslash-backtick escapes denote literal backticks in selectors; `named-fields {a, b}` denotes projection kind `named-fields` with the listed field names in order. Notes, normative: EVID-03's §25.21 full section text includes its deterministic left-to-right fixture obligations, which is why no weaker sub-block component exists; forty-one has no authority of its own — the set may grow by directive revision but never shrink; the terminal audit JSON filename is fixed above so EVID-08's terminal pointers are exact; `late_governance_outputs` is the sole late-artifact authority and includes the fixed-point manifest; where `EVD`/`FRZ`/`AJSON` show baseline→terminal path pairs, the selector is identical on both sides and the freeze generator is bound (Part 0) to emit the EVID-02 protected claim block verbatim.
