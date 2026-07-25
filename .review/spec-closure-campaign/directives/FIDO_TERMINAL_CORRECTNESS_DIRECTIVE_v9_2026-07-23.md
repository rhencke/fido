# FIDO — TERMINAL CORRECTNESS DIRECTIVE, v9 (SPEC-CLOSURE FAMILY, FINAL PASS — SELF-CONTAINED)

**Date:** 2026-07-23
**Issued by:** Rob (human authority). This file is the directive.
**Repair authorization token:** `SPEC-CLOSURE-terminal-repair-2` (unchanged)
**Version:** v9 — self-contained. **This document alone is sufficient to execute and audit the repair. Earlier directives are provenance only.**
**Supersedes (full hashes):** v8 `2173975c624f67fd892647ac76acfe1ed3eb6a70299ba6872d2f14ea0c67e994`; v7 `5c1996a5c2bffc8f0bad43e4f1c6fde328d997deb0bafeb2586e92ee60b0db15`; v6 `dc7a369120ab23c548998739111d1eb7ef7edcfac652dd9d634cfab494cc3562`; v5 `5a083bf157cd97644755517e7e7fa1a8f31c5bcd65fa9a4b5b4a39106d44d6c9`; v4 `eab3b1ed4b856157f7c784a6a7bcd35f5abe454cd558fb631b1f6772095648ff`; v3 `6a99418c02cba3063bc43e61a71c48197fe3a55889d5c18f0225d5b78dbc011b`; v2 `d8b2a9c71355ed0163b00bfa6a3aa9ca6dd6646a1ca80d30dd0596a022d560a2`; v1 `b30c03b8c16a09868763f891ec2fd92f3a03f2a0739c852b497a536b70502a34`.
**Baseline:** `FIDO_GO1_23_SPEC_CLOSURE_REVIEW_BUNDLE_R1_2026-07-23.zip`, SHA-256 `a01a7be5160b10e83bce11ed2161e353a94ca9bd86ef2843aca9fe29e1da303e`.
**Provenance:** Authored by Claude (Fable 5, external adversarial reviewer). Co-review round 8 by ChatGPT (Sol 5.6): two BLOCKING (CR8-1 fixed-point component granularity; CR8-2 undefined selector algebra), one REQUIRED (CR8-3 inspect-before-extract), enum/encoding closures — **all adopted**. v8's hash verified (match). Self-reference bug-class count remains **four**; round 8 introduced none. Per the co-reviewer: no architecture, semantics, evidence-policy, or governance round remains; v9 changes only the sealing normal form.

---

## AUTHORITY LIMITS (binding, complete)

1. Documentary artifacts, pins, scripts, fixtures, and recorded observations only. Compiling and executing probe fixtures against the pinned toolchain **to record evidence** is in scope. Modifying the Fido repository — source, `.v` files, build system, gates — is not.
2. Nothing produced by this repair may claim FIXED, accepted, closed, countersigned, spec-closed-in-implementation, or any score. Models record `APPLIED` at most.
3. Every countersign cell is created empty and remains Rob's alone.
4. This directive does not accept C4, does not authorize C5, and does not alter the active C4 repair authority or `NEXT_STEPS.md` state.
5. Normative text may not contain unpinned claims. World-knowledge is not evidence; pinned artifacts, hashes, and captured observations are.
6. One authority per meaning, for code, documents, and directives alike. Versions supersede by name and full hash; two live directives never coexist; a directive is self-contained.
7. Changes only under a T-row's authorization, at change granularity (T-0). External reviews, prior directives, and copied ADR records are read-only evidence.
8. The executor receives no discretion over protection strength: fixed-point components are enumerated by this directive's normative Appendix A; the registry must equal it exactly; amendments require a directive revision.

## FIXED POINTS

The 24 fixed-point IDs are ARCH-01…ARCH-12 and EVID-01…EVID-12 as defined in v8 and unchanged in meaning. Their protection is realized through the **component registry** (T-0.C) whose exact component set is **Appendix A** of this directive. Summary (full statements as in v8; the appendix binds their protected form): ARCH-01 deletion/generalization standard; ARCH-02 minimal Machine base; ARCH-03 one-owner table; ARCH-04 fact/use split; ARCH-05 single type algebra; ARCH-06 slots/places; ARCH-07 stack-only panic/defer/recover with the two named lemmas; ARCH-08 resource-local origins; ARCH-09 finite bad-prefix safety; ARCH-10 no vacuous library safety; ARCH-11 Do-Not-Do-Early list; ARCH-12 candidate-only acceptance. EVID-01 pinned spec/memory-model hashes (`c47fb4b5…`, `366b995a…`); EVID-02 reproducible extraction; EVID-03 Route A order model, contract, and deterministic-order fixtures; EVID-04 FMA both-branches with adequacy-only observation; EVID-05 select/map/scheduler STEP-NONDET and println ADEQUACY-DEMOTION; EVID-06 BOUND-001..003 and the invocation contract; EVID-07 the §22.3 observation tuple; EVID-08 APPLIED-only provenance; EVID-09 synthesized-anchor flags and the grammar counting rule; EVID-10 NaN-map and struct-tag rows with fixtures; EVID-11 `SC-21-PROOF-COST-INTERNALS` at §25.22 untouched; EVID-12 `uintptr` OUT pending ADR-0001.

---

## T-0 — BLOCKING — BASELINE DELTA AND PRESERVATION

**Rule:** the terminal bundle is an authorized transformation of the exact R1 baseline; **every change has exactly one T-owner** at change granularity; files carry owner sets.

**Canonical artifacts (named generators):**

**A. File delta — `.review/FIDO_TERMINAL_FILE_DELTA_2026-07-23.tsv`** (`tools/generate_file_delta.py`). Columns: `baseline_path`, `terminal_path`, `baseline_kind`, `terminal_kind`, `baseline_sha256`, `terminal_sha256`, `action`, `owners`, `rationale`. Enums (CR8-2 closure): `action ∈ {UNCHANGED, MODIFIED, ADDED, RENAMED, DELETED}`; `kind ∈ {MISSING, REGULAR_FILE}`. The delta compares **regular files only**; directory entries derive from file paths. Paths relative to the bundle content root; RENAMED uses both path columns; ADDED leaves baseline cells empty; DELETED leaves terminal cells empty; `owners` = sorted set equal to the change-ledger derivation.

**B. Change ledger — `.review/FIDO_TERMINAL_CHANGE_LEDGER_2026-07-23.tsv`** (`tools/generate_change_ledger.py`). Columns: `change_id`, `path`, `selector_kind`, `selector`, `baseline_fragment_sha256`, `terminal_fragment_sha256`, `owner`, `rationale`. Each changed unit has exactly one owner.

**C. Fixed-point registry and manifest (CR8-1, adopted).**
- **Registry — `.review/FIDO_TERMINAL_FIXED_POINT_REGISTRY_2026-07-23.tsv`**: columns `fixed_point_id`, `component_id`, `baseline_path`, `terminal_path`, `selector_kind`, `selector`, `protected_projection`. Unique key `(fixed_point_id, component_id)`. **Its exact component set is Appendix A — no more, no fewer.**
- **Manifest — `.review/FIDO_TERMINAL_FIXED_POINT_MANIFEST_2026-07-23.tsv`** (`tools/generate_fixed_point_manifest.py`): the registry plus verified `baseline_projection_sha256` and `terminal_projection_sha256`.

**D. Selector specification — `.review/FIDO_TERMINAL_SELECTOR_SPEC_2026-07-23.md` (CR8-2, adopted).** One canonical document defining, for every selector kind: syntax; parse rules; normalization; selected raw byte spans; selected semantic projection; canonical hash input; failure rules; overlap rules. Binding minimums:
- `whole-file` selects raw file bytes and **cannot coexist with any other content selector for that file**.
- `markdown-heading` selects only the heading line. **`markdown-section` is added**: the heading line through the line before the next heading of equal or higher level.
- `anchored-region`: exact unique start and end markers; inclusion rule stated (markers included); resolution fails unless each marker occurs exactly once.
- `python-symbol`: via the Python AST; one top-level function, class, or named assignment; **includes its decorators and any immediately preceding contiguous comment block**.
- `json-pointer`: RFC 6901; hashes a canonical JSON encoding (sorted keys, UTF-8, LF).
- Each tabular file **declares its primary-key column** in the spec; `table-row` selects one keyed semantic row; `table-field` one named field in one keyed row; `table-schema` the ordered header and schema rules. Table semantic projections use UTF-8, LF, and one fixed escaping/canonical encoding.
- `file-property` operates in a **metadata namespace** separate from normalized content; `line-ending` hashes the declared serialization property, not content bytes.
- **Orthogonality is a closed, explicit relation**: the audit permits only listed pairs (e.g., `file-property:line-ending` ⟂ normalized semantic table selectors; `file-property:mode` ⟂ content; `whole-file` ⟂ nothing in the content namespace; `anchored-region` and `markdown-section` are **not** orthogonal where spans intersect). Every content selector yields raw spans or exact semantic fields; **their union must equal the complete structural diff — no uncovered change, no doubly owned change.**
- All canonical TSV files: UTF-8, LF, no BOM, one fixed field-escaping rule, one fixed row order (sorted by primary key).

**Audit obligations (step 9):**
- `baseline_delta_complete` — structural diff per the selector spec proving: every changed unit appears exactly once; every changed unit has exactly one owner; no ledger entry names an unchanged unit; orthogonality only per the closed relation; file-level owner sets equal change-level owner sets; no unlisted change, missing baseline file, or unlisted addition; no altered external review or prior directive.
- `fixed_point_manifest_complete` — proves: the parent-ID set is exactly the 24; **every ID has at least one component; the exact component-key set equals Appendix A**; no component key twice; each component resolves exactly once in the verified R1 baseline and exactly once in the terminal tree; every stored baseline hash matches a **fresh recomputation from the R1 bytes**; every terminal component matches its verified baseline projection. Empty or partial registries fail; vacuous passes are impossible.
- `fixed_points_preserved` — terminal projection hash equals recomputed baseline projection hash, per component.

**Scopes.** Change-ledger scope excludes: itself; the file delta; the audit JSON; the freeze record; the SHA manifest. File-delta scope excludes: itself; the audit JSON; the freeze record; the SHA manifest; it includes and hashes the completed change ledger, registry, manifest, and selector spec. The terminal verifier assigns the two self-excluded T-0 files their owner by rule (change ledger → T-0; file delta → T-0); **no other file may use this exception**.

**Final-set equation (acyclic), proved by the terminal verifier:** final in-bundle set = ordinary phase-1 inputs + selector spec + fixed-point registry + fixed-point manifest + change ledger + file delta + audit JSON + freeze record + SHA manifest.

**Read-only evidence rule.** External reviews, prior directives, and copied ADR records remain byte-identical. This v9 directive enters the bundle as a frozen read-only authority (ADDED, owner T-0) under its exact SHA-256, computed at delivery.

---

## PART 0 — FREEZE PROTOCOL, EVIDENCE CHAIN, AND CANONICAL ARCHIVE

**Acyclicity.** The audit JSON hashes only inputs (including the completed T-0 artifacts) — never itself, the freeze record, the SHA manifest, the ZIP, or the sidecar. The freeze record, generated from the audit JSON, lists predecessor ZIP hashes, the audit JSON hash, and the manifest's filename and coverage rule (never its hash). The SHA manifest hashes every in-bundle file except itself. The ZIP's SHA-256 exists only in the external sidecar, whose pinned format is: `<lowercase-sha256><two spaces><zip-filename><LF>`.

**Producer inventory (shipped, hashable files; no unnamed shell commands):** `tools/audit_spec_closure_bundle.py`; `tools/verify_terminal_bundle.py`; `tools/extract_latitude.py`; `tools/render_ledger_md.py`; `tools/run_fixture.py`; `tools/generate_file_delta.py`; `tools/generate_change_ledger.py`; `tools/generate_fixed_point_manifest.py`; `tools/generate_freeze_record.py`; `tools/generate_sha_manifest.py`; `tools/generate_human_review_index.py`; `tools/build_deterministic_bundle.py`; `tools/write_zip_sidecar.py`. The audit JSON records every producer/verifier SHA-256 plus Python implementation, version, and executable hash.

**Replay duties (step 9; temporary area only; frozen captures never rewritten):** re-run latitude extraction and byte-compare; re-render the ledger Markdown from canonical CSV/TSV and byte-compare; re-run every probe fixture compare-only under the T-9 profile with fresh empty `GOCACHE`/`GOMODCACHE`/`GOPATH`/temp per replay, comparing stdout, stderr, status, command record, and effective-environment record.

**Distribution member proofs — typed.** `distribution_members_match ∈ {PASS-CONFIRMED, PENDING-PROVENANCE, FAIL}`. Confirmed: extract each pin's **exact tar member path from `PINS_MANIFEST.tsv`** out of the verified tarball; byte/mode/symlink-compare; record path and result; require PASS-CONFIRMED. Pending: PENDING-PROVENANCE with `local_distribution_manifest_complete = PASS`; every affected pin and observation `PROVENANCE-PENDING`. Covered pins at least: pinned spec HTML; pinned memory-model HTML; `go/bin/go` (hash record); pinned cmd/go sources; pinned modfile source. Repo-tag pins name an exact external artifact and SHA-256. **Audit top status ∈ {PASS-CONFIRMED, PASS-WITH-PENDING-PROVENANCE, FAIL}**; pending is never called green.

**Tarball storage (decided):** the official `go1.23.2.linux-amd64.tar.gz` is an EXTERNAL-AUDIT-INPUT (`PINS_MANIFEST.tsv` row: origin URL, version, official SHA-256 or PENDING, exact expected local path). Confirmed mode verifies presence and hash there before extraction.

**Inventory completeness.** The audit JSON contains the complete set and SHA-256 of every phase-1 file. The verifier rejects any addition, deletion, or byte change; only the audit JSON, freeze record, and SHA manifest may be added later.

**Canonical archive form (constants):** built only by `tools/build_deterministic_bundle.py`; exactly one root `FIDO_GO1_23_SPEC_CLOSURE_REVIEW_BUNDLE_TERMINAL_2026-07-23/`; regular files and directories only; no symlinks, absolute paths, `.`/`..` components, or duplicate entry names; normalized POSIX paths; sorted entries; timestamp `1980-01-01 00:00:00`; directory mode `0755`; regular-file mode `0644`; `ZIP_STORED`; **empty archive and entry comments; empty extra fields; fixed creator system and flag values; central-directory and local-header agreement** — builder and verifier share all constants.

**Build order — seventeen steps, 0–16 (CR8-3 order):**
0. Verify the R1 baseline ZIP SHA-256 (`a01a7be5160b10e83bce11ed2161e353a94ca9bd86ef2843aca9fe29e1da303e`).
1. Extract the baseline into a clean tree.
2. Create the terminal working tree.
3. Apply all substantive T-row changes, recorded at change granularity.
4. Produce all ordinary phase-1 inputs: tools, pins, fixtures, captured evidence, canonical tables, generated Markdown, plan, ADR records, T-disposition ledger, selector spec.
5. Generate the Human-Review Index from the completed T/F/R/ADR sources.
6. Generate the fixed-point registry (must equal Appendix A) and manifest.
7. Generate the change ledger.
8. Generate the file delta.
9. Run the phase-2 audit; write the frozen audit JSON.
10. Generate the freeze record from the audit JSON.
11. Generate the in-bundle SHA manifest.
12. Run the terminal verifier against the staged tree (writes nothing; nonzero on failure).
13. Build the ZIP in canonical form.
14. **Inspect the archive directly, before writing any extracted file**: one exact root; no duplicate normalized names; no absolute paths; no `.`/`..`; no symlinks or unsupported types; sorted entries; directory-entry rule honored; timestamp, modes, ZIP_STORED; empty comments and extra fields; fixed creator system and flags; central-directory/local-header agreement; the exact expected entry set.
15. **Extract with a safe extractor** into a clean directory and run the terminal verifier there; compare extracted bytes against the in-bundle manifest.
16. Write the external sidecar with `tools/write_zip_sidecar.py` in the pinned format. Rob verifies it externally.

**Two-script split.** Audit (step 9) owns input-only checks: row totality; T-1 trichotomy; ACCEPTANCE-ALIGNMENT justification uniqueness; the full duplicate-representation histogram sorted by count then text hash; line-ending uniformity; ragged rows; ID-prefix discipline; single-open-latitude (open set exactly `{LAT-X004}`); T-6 contract-definition checks; `baseline_delta_complete`; `fixed_point_manifest_complete`; `fixed_points_preserved`; `distribution_members_match`; `local_distribution_manifest_complete`; regeneration and replay comparisons; index-versus-discovery. Verifier (steps 12, 14–15) owns `freeze_claims_match`; manifest coverage and hash verification; inventory-drift rejection; the final-set equation and meta-file exclusions; T-0-owner-by-rule; archive inspection (step 14 checklist) and post-extraction byte comparison.

---

## PART A — SUBSTANTIVE REPAIRS

### T-1 — BLOCKING — Acceptance alignment
As in v8, in full force: the false shared justification; **ADR-0003 verbatim** —

> **ADR-0003 — Authority ordering (PROPOSED).**
> 1. Where the pinned Go specification is definite, the specification governs meaning.
> 2. Where the specification grants latitude, is silent, or is hand-wavy, the pinned gc toolchain (go1.23.2) governs, and **Fido's acceptance must be a subset of pinned-gc acceptance**. Fido explicitly targets the official gc implementation only; no other Go implementation is a target.
> 3. Where pinned gc demonstrably contradicts definite specification text (a toolchain bug), the divergence is recorded as a ledger row and dispositioned by Rob; it is never silently adopted in either direction.
>
> **Interpretation clause.** In tier 2, "pinned gc governs" governs the supported **acceptance profile** and **pinned-toolchain adequacy claims**. It does not reduce a formal behavior set that definite specification latitude requires `GoMachine` to admit. Route A evaluation order, FMA alternatives, select choice, map iteration order, and scheduler choice remain fixed points unless a separately countersigned ledger disposition states otherwise. A permitted-set model is required because the pinned specification grants both branches. Current linux/amd64 evidence records only one target observation; other platform observations require their own pinned evidence and ledger revision.

— plus: the `ACCEPTANCE-ALIGNMENT` disposition with individual justifications (audit-enforced uniqueness); the classification trichotomy over every implementation-restriction candidate (`ACCEPTANCE-ALIGNMENT` / `OUT-COVERED` with LAT-180+LAT-181 unified / `NOT-LATITUDE` with LAT-118 and LAT-214 individually corrected); individual re-dispositions of LAT-019, LAT-049, LAT-077, LAT-085, LAT-134, LAT-148, LAT-171, LAT-177, LAT-180, LAT-181, LAT-118, LAT-214; **`SC-22-ACCEPTANCE-ALIGNMENT` at §25.23** with `fido_accepts_subset_pinned_gc` frozen here, discharged at implementing checkpoints; the Formal/External/Evidence separation; evidence-now/gates-later with `PENDING-IMPLEMENTATION` and the three first instances (unused local variables; constant acceptance bounds; duplicate constant switch cases); and **LAT-X004** with ownership frozen — owning closure row SPEC-096; semantic owner `ExprFact` intrinsic exact value; contract `SC-05-EXPR-FACT-USE-EVAL` §25.6; SC-22 acceptance-only; SC-02 (§25.3) supporting — governance columns `decision_status`/`rob_choice`/`rob_countersign` on every latitude row, open set exactly `{LAT-X004}` (`HUMAN-CHOICE-OPEN`), the three-option menu with the labeled advisory (option ii, domain-restriction variant), and the re-freeze at the FCB transformation.

### T-2 — REQUIRED — Pinned distribution execution
As in v8: delete the in-bundle executor; **Confirmed mode** (tarball bytes at the recorded external path, official SHA-256 confirmed, hash match; always extract into a fresh sandbox; member `go/bin/go` hash secondary); **Pending mode** (sandbox copy of the local distribution with a complete file/symlink/mode manifest, hashed and recorded; every observation and unproved pin `PROVENANCE-PENDING`; completion cannot be claimed); pending provenance in the Human-Review Index; the evidence doc keeps the provenance chain.

### T-3 — REQUIRED — Racy-run scope: option (b)
As in v8: LAT-217/218/219/224 remain STEP-NONDET; `DataRace` a derived finite BadPrefix; the §27 reserve in substance verbatim; citations name only the owning channel/race contract; SC-20 tails removed.

### T-4 — REQUIRED — Template drift measurable
As in v8: `template: lexical-only` on the 48 OP- and 25 KEY- rows; the full duplicate-representation histogram; the old-template regex stays.

---

## PART B — SHOWROOM ITEMS (N = non-substantive, still required)

T-5 LF everywhere (closure CSV normalized; ledger entry `file-property`/`line-ending`/T-5). T-6 contract-definition audit with the full SC-00..SC-22 mapping (SC-21 = §25.22 pre-existing; SC-22 = §25.23 new; headings parsed, bijection, contiguity, projection, citation existence; relevance by hand). T-7 ID discipline (`LAT-###` ordinals; `LAT-X###` hand-added; `BOUND-###` live; `BOUND-X###` priced). T-8 freeze claims emitted (`freeze_claims_match` in the verifier). T-9 closed probe environment via `.review/tools/PROBE_ENVIRONMENT.tsv` as the **complete** allowed key set (unknown keys fail): `GOROOT`, `PATH`, `HOME`, `TMPDIR`, `GOCACHE`, `GOMODCACHE`, `GOPATH` (sandbox; caches fresh per replay), `LANG`, `LC_ALL`, `TZ`, `GODEBUG` (empty), `GOTRACEBACK`, `GOOS=linux`, `GOARCH=amd64`, `GOAMD64=v1`, `CGO_ENABLED=0`, `GOFLAGS=""`, `GOPROXY=off`, `GOTOOLCHAIN=local`, `GOENV=off`, `GOWORK=off`; plus umask, sandbox root, path-normalization rule; command and effective `go env` recorded per run; flagged as proposed BOUND-003 strengthening. T-10 pins manifest (exact tar member paths; `<artifact>_<version>.<ext>`; EXTERNAL-AUDIT-INPUT row for the tarball). T-11 CSV+TSV canonical; Markdown fully generated and byte-compared. T-12 ragged-row detection. T-13 self-describing audit (schema version; producer/verifier hashes; Python provenance; typed top status). T-14 platform-pending note (ADR-0004; linux/amd64 scope). T-15 (N) root README. T-16 (N) acyclic supersession chain (full R1 hash; ZIP hash only in the sidecar). T-17 (N) the FMA margin note, verbatim. T-18 Human-Review Index, discovery-based (T rows from T-19's TSV; F/R from frozen sources; all PROPOSED/OPEN/PENDING/REJECTED-AS-WRITTEN-OPEN ADRs — minimum ADR-0001..0004 — LAT-X004; empty countersigns; pending provenance; cited ADRs in-bundle or external with path+SHA; audit fails on omissions and stale rows). T-19 canonical T-disposition ledger (`id`, `severity`, `model_record`, `artifact_locations`, `applied_change`, `rob_countersign`; rows T-0..T-19; `APPLIED`; countersigns empty; sole T-authority).

---

## COMPLETION (exact status values)

- **`TERMINAL-REPAIR-CANDIDATE`**: every T-deliverable (T-0..T-19); T-0's five artifacts (selector spec, registry, manifest, change ledger, file delta) complete with `baseline_delta_complete`, `fixed_point_manifest_complete`, and `fixed_points_preserved` green; the seventeen-step order (0–16) followed with **archive inspection before extraction**; producer inventory, replays, and index-versus-discovery green; `distribution_members_match = PASS-CONFIRMED`, top status `PASS-CONFIRMED`; ADR-0003 verbatim and PROPOSED; **LAT-X004 the sole open Latitude Ledger disposition**; all PENDING-IMPLEMENTATION rows frozen with no claimed Fido observations; verifier runs clean without rewriting frozen artifacts; T-19 all `APPLIED`, countersigns empty; no acceptance/closure/FIXED/score claims anywhere.
- **`OPEN-REVIEW-CANDIDATE`**: identical except provenance — `distribution_members_match = PENDING-PROVENANCE`, `local_distribution_manifest_complete = PASS`, top status `PASS-WITH-PENDING-PROVENANCE`, no failed checks, exactly the declared pending items, every affected pin and observation `PROVENANCE-PENDING`, freeze record stating explicitly that completion is blocked and why.

Deliver `FIDO_GO1_23_SPEC_CLOSURE_REVIEW_BUNDLE_TERMINAL_2026-07-23.zip` plus its external sidecar in the pinned format. Rob's countersigns — indexed by T-18 from T-19 and the frozen F/R sources, with his LAT-X004 policy choice at the FCB regeneration — end the correctness volleys.

---

## APPENDIX A — NORMATIVE FIXED-POINT COMPONENT SET (registry must equal exactly)

Format: `fixed_point_id/component_id — path — selector_kind — protected projection (summary)`.

**ARCH-01..ARCH-12** — one component each, `charter`: plan — `markdown-section` on the section named in the fixed-point statement (§1, §2, §3, §5, §6, §11, §13, §15, §17, §19, §24, §26) — normalized section text. (12 components.)

**EVID-01/spec-hash-pin** — PINS_MANIFEST.tsv — table-row (key: go_spec pin) — sha256 field.
**EVID-01/memmodel-hash-pin** — PINS_MANIFEST.tsv — table-row (key: go_mem pin) — sha256 field.
**EVID-02/extractor-script** — tools/extract_latitude.py — whole-file — raw bytes.
**EVID-02/extraction-terms** — latitude manifest — anchored-region (header comment block) — pinned hashes and term list.
**EVID-03/order-model** — plan — markdown-section §12.4 — normalized text.
**EVID-03/order-contract** — plan — markdown-section §25.21 — normalized text.
**EVID-03/left-to-right-fixtures** — plan — anchored-region (the deterministic-ordering fixture block within §25.21) — normalized text.
**EVID-04/fma-row-core** — latitude TSV — table-row LAT-121 — fields {disposition, owner_row, contract, justification}.
**EVID-04/fma-observation** — toolchain evidence doc — anchored-region (FMA observation block) — normalized text.
**EVID-05/select-choice** — latitude TSV — table-row LAT-X002 — fields {disposition, owner_row, contract}.
**EVID-05/map-iteration** — closure CSV — table-row SPEC-X006 — fields {disposition, owner, test}.
**EVID-05/scheduler-choice** — latitude TSV — table-row LAT-X003 — fields {disposition, owner_row, contract}.
**EVID-05/print-println-demotion** — closure CSV — table-row SPEC-X005 — fields {disposition, owner, test}.
**EVID-06/bound-001** — closure CSV — table-row BOUND-001 — fields {disposition, representation}.
**EVID-06/bound-002** — closure CSV — table-row BOUND-002 — fields {disposition, representation}.
**EVID-06/bound-003** — closure CSV — table-row BOUND-003 — fields {disposition, representation}.
**EVID-06/invocation-contract** — toolchain evidence doc — anchored-region (invocation contract block) — normalized text.
**EVID-07/tuple-section** — plan — markdown-section §22.3 — normalized text.
**EVID-08/f-ledger-applied-rule** — F-dispositions record — anchored-region (APPLIED-only/countersign rule block) — normalized text.
**EVID-08/r-ledger-applied-rule** — R-dispositions record — anchored-region (APPLIED-only/countersign rule block) — normalized text.
**EVID-09/synthesized-heading-flags** — heading manifest — anchored-region (synthesized-column header note) — normalized text.
**EVID-09/grammar-counting-rule** — grammar manifest — anchored-region (counting-rule header block) — normalized text.
**EVID-10/nan-map-row** — closure CSV — table-row SPEC-124 — fields {disposition, representation}.
**EVID-10/struct-tag-row** — closure CSV — table-row SPEC-026 — fields {disposition, representation}.
**EVID-10/struct-tag-fixtures** — plan — anchored-region (struct-tag fixture block, §25.5) — normalized text.
**EVID-10/nan-map-fixture** — plan — anchored-region (NaN-map fixture block) — normalized text.
**EVID-11/sc21-contract** — plan — markdown-section §25.22 — normalized text.
**EVID-12/uintptr-pre-row** — closure CSV — table-row PRE-22 — fields {disposition, price}.

(Total: 12 + 28 = **40 components.** Exact selectors — anchor strings, primary keys — are fixed by the selector spec at execution; the component set itself may not change without a directive revision.)
