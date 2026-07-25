# FIDO — TERMINAL CORRECTNESS DIRECTIVE, v7 (SPEC-CLOSURE FAMILY, FINAL PASS — SELF-CONTAINED)

**Date:** 2026-07-23
**Issued by:** Rob (human authority). This file is the directive.
**Repair authorization token:** `SPEC-CLOSURE-terminal-repair-2` (unchanged)
**Version:** v7 — self-contained. **This document alone is sufficient to execute and audit the repair. Earlier directives are provenance only.**
**Supersedes (full hashes):**
- v6 `dc7a369120ab23c548998739111d1eb7ef7edcfac652dd9d634cfab494cc3562`
- v5 `5a083bf157cd97644755517e7e7fa1a8f31c5bcd65fa9a4b5b4a39106d44d6c9`
- v4 `eab3b1ed4b856157f7c784a6a7bcd35f5abe454cd558fb631b1f6772095648ff`
- v3 `6a99418c02cba3063bc43e61a71c48197fe3a55889d5c18f0225d5b78dbc011b`
- v2 `d8b2a9c71355ed0163b00bfa6a3aa9ca6dd6646a1ca80d30dd0596a022d560a2`
- v1 `b30c03b8c16a09868763f891ec2fd92f3a03f2a0739c852b497a536b70502a34`

**Baseline:** `FIDO_GO1_23_SPEC_CLOSURE_REVIEW_BUNDLE_R1_2026-07-23.zip`, SHA-256 `a01a7be5160b10e83bce11ed2161e353a94ca9bd86ef2843aca9fe29e1da303e` (this full form is used wherever a build or verification step consumes it).

**Provenance:** Authored by Claude (Fable 5, external adversarial reviewer). Co-review round 6 by ChatGPT (Sol 5.6): one BLOCKING finding (CR6-1, T-0 ownership granularity and delta timing — a correction of the co-reviewer's own round-5 design; its second self-correction of the exchange), three REQUIRED (CR6-2 typed provenance outcomes, CR6-3 canonical T-disposition ledger, CR6-4 exact mechanics) — **all adopted**. v6's hash verified (match). Recurring-defect note for the record: the self-reference bug class (a sealing artifact containing knowledge of things generated after it, or of itself) has now appeared three times in this exchange — the v2 freeze/manifest cycle, the v3 audit-checks-freeze contradiction, and v6's delta carrying its own hash — and was caught before execution each time. Round-over-round finding order remains strictly decreasing; per the co-reviewer, no architecture, semantics, or evidence-policy round remains.

---

## AUTHORITY LIMITS (binding, complete)

1. Documentary artifacts, pins, scripts, fixtures, and recorded observations only. Compiling and executing probe fixtures against the pinned toolchain **to record evidence** is in scope. Modifying the Fido repository — source, `.v` files, build system, gates — is not.
2. Nothing produced by this repair may claim FIXED, accepted, closed, countersigned, spec-closed-in-implementation, or any score. Models record `APPLIED` at most.
3. Every countersign cell is created empty and remains Rob's alone.
4. This directive does not accept C4, does not authorize C5, and does not alter the active C4 repair authority or `NEXT_STEPS.md` state.
5. Normative text may not contain unpinned claims. World-knowledge is not evidence; pinned artifacts, hashes, and captured observations are.
6. One authority per meaning, for code, documents, and directives alike. New directive versions supersede by name and full hash; two live directives may never coexist. A directive must be self-contained.
7. The repair may change only what a T-row authorizes, at **change granularity** (see T-0). External reviews, prior repair directives, and copied ADR records are read-only evidence: byte-identical unless one exact T-row expressly authorizes their replacement.

## FIXED POINTS (complete; weakening any is a regression; protected by the T-0 fixed-point manifest as **projections**, not whole-row bytes)

**(A) The twelve architectural fixed points** (from the original strict review's "What Must Not Change"):
1. The §1 deletion and generalization standard — the five retention tests and the prohibition list.
2. The minimal `Machine` base (§2) and the rule that no Go feature defines a second run relation.
3. The one-owner-per-meaning table (§3).
4. The expression fact/use split (§5) — "the use builder does not inspect the raw child again."
5. The single type algebra (§6): `RuntimeType := SemanticType Empty_set`, alias non-identity, declaration-reference recursion.
6. The static-slot / dynamic-place distinction (§11).
7. Stack-only panic / defer / recover (§13) with `finishing_pushes_only_deferred_activations` and `above_finishing_iff_deferred_call`.
8. Resource-local origins with proof-connected provenance (§15).
9. Finite bad-prefix safety with liveness held separate (§17).
10. Rejection of vacuous library safety from an empty start set (§19).
11. The Do-Not-Do-Early list (§24), verbatim.
12. The candidate-only acceptance stance (§26) with Rob as sole disposition owner.

**(B) The twelve evidence-and-model fixed points:**
1. Pinned spec SHA-256 `c47fb4b5b795b9732cbae0250dcb84f791df78bb98695b30fb3f7788d1c9b389`; pinned memory-model SHA-256 `366b995adeee8b57bd23547feea8252a7ee619baec91cb22cfb21b12208da2c6`.
2. Reproducible audit and latitude extraction (shipped scripts re-run to byte-identical frozen outputs).
3. Route A evaluation-order nondeterminism (plan §12.4; `SC-20-EVAL-ORDER-LATITUDE` at §25.21); the spec-specified lexical left-to-right ordering of calls, methods, and receives as a deterministic obligation with fixtures.
4. The FMA both-branches model (LAT-121, STEP-NONDET), pinned-target observation recorded as adequacy evidence, never spec truth. Protected projection: disposition = STEP-NONDET; owner; contract; both-branches representation; adequacy-only target observation. Governance columns may be added.
5. Select-choice, map-iteration (SPEC-X006), scheduler nondeterminism as STEP-NONDET; `print`/`println` output as ADEQUACY-DEMOTION (SPEC-X005).
6. BOUND-001..003: emitted `go 1.23` directive equals the ledger language version; module path from the single ModulePath authority; no `toolchain` directive; invocation `GOTOOLCHAIN=local`, `GOENV=off`, `GOWORK=off`, `go version` verified before build.
7. The §22.3 terminal observation tuple; `println` → stderr; fatal panic → exit 2 with first-line projection `panic: <value>`; runtime noise excluded explicitly, owned by BOUND-X009.
8. APPLIED-only provenance; empty countersign columns; the audit's split of machine-checkable versus judgment claims.
9. Synthesized-anchor flags; the grammar counting rule (174 definitions / 173 names, metagrammar included, `Expression` twice) in the artifact header.
10. NaN-map row (SPEC-124) and struct-tag rows (SPEC-026) with their fixtures.
11. **`SC-21-PROOF-COST-INTERNALS` at §25.22** — never overwrite, renumber, or weaken.
12. `uintptr` remains OUT pending ADR-0001.

---

## T-0 — BLOCKING — BASELINE DELTA AND PRESERVATION (CR6-1 replacement; executes before all else)

**Rule:** the terminal bundle is an **authorized transformation of the exact R1 baseline**. The enforced invariant is: **every change has exactly one T-owner** — not the false rule that every changed file has one owner. Files legitimately change under many T-rows (the plan under T-1/T-3/T-6/T-14/T-16; the audit script under most rows; the latitude table under several); ownership lives at change granularity so no unrelated edit can hide under a file's named owner.

**Three canonical artifacts (with named generators):**

**A. File delta — `.review/FIDO_TERMINAL_FILE_DELTA_2026-07-23.tsv`** (generator `tools/generate_file_delta.py`). Columns: `baseline_path`, `terminal_path`, `baseline_kind`, `terminal_kind`, `baseline_sha256`, `terminal_sha256`, `action`, `owners`, `rationale`. Rules: paths are relative to the bundle content root (the ZIP root directory is not part of the comparison path); `RENAMED` uses both path columns; `ADDED` leaves baseline path and hash empty; `DELETED` leaves terminal path and hash empty; `owners` is the **sorted set** of T-rows owning changes within the file and must equal the owner set derived from the change ledger.

**B. Change ledger — `.review/FIDO_TERMINAL_CHANGE_LEDGER_2026-07-23.tsv`** (generator `tools/generate_change_ledger.py`). Columns: `change_id`, `path`, `selector_kind`, `selector`, `baseline_fragment_sha256`, `terminal_fragment_sha256`, `owner`, `rationale`. Each changed unit has **exactly one owner**. Selector kinds by file type: `markdown-heading`, `markdown-block`, `table-row`, `table-field`, `json-pointer`, `whole-file`. Examples: plan / §22.4 / T-1; plan / §27 reserve / T-3; latitude row LAT-134 / disposition field / T-1; audit script / acceptance-alignment check / T-1; audit script / baseline-delta check / T-0.

**C. Fixed-point manifest — `.review/FIDO_TERMINAL_FIXED_POINT_MANIFEST_2026-07-23.tsv`** (generator `tools/generate_fixed_point_manifest.py`). Columns: `fixed_point_id`, `path`, `selector_kind`, `selector`, `protected_projection`, `baseline_projection_sha256`. Prose fixed points protect the exact named block; table fixed points protect exactly the meaning-bearing fields, so governance columns (`decision_status`, `rob_choice`, `rob_countersign`) may be added without touching protected fields.

**Audit obligations (phase-2):**
- `baseline_delta_complete` — computes a structural diff and proves: every changed unit appears exactly once in the change ledger; no changed unit lacks an owner; no ledger entry names an unchanged unit; overlapping entries never assign two owners to one change; the file-level owner sets equal the change-level owner sets; no unlisted file change; no missing baseline file; no unlisted added file; no altered external review or prior directive.
- `fixed_points_preserved` — for every fixed-point manifest row, the terminal projection hash equals the baseline projection hash.

**Acyclic delta scope.** The file delta compares the baseline bundle against the **phase-1 terminal inputs**, excluding exactly four files, named in the delta header and enforced by the terminal verifier: the file-delta artifact itself, the later audit JSON, the later freeze record, and the later SHA manifest. Generation order within phase 1: change ledger and fixed-point manifest first (both appear in the file delta as ADDED, owner T-0, with hashes), then the file delta. The audit JSON hashes the file delta. The final manifest hashes all governance files except itself under the existing manifest rule. The terminal verifier proves: **final in-bundle set = phase-1 set + audit JSON + freeze record + SHA manifest.**

**Read-only evidence rule.** External reviews, prior repair directives, and copied ADR records remain byte-identical. **This v7 directive enters the terminal bundle as a frozen read-only authority**, listed in the phase-1 inventory and file delta (ADDED, owner T-0) under its exact SHA-256, computed at delivery.

---

## PART 0 — FREEZE PROTOCOL, EVIDENCE CHAIN, AND CANONICAL ARCHIVE (complete)

**Acyclicity rule.** The audit JSON hashes only audit **inputs**. It does not hash itself, the freeze record, the in-bundle SHA manifest, the final ZIP, or the sidecar. The freeze record is generated from the frozen audit JSON and lists: predecessor ZIP hashes, the frozen audit JSON hash, and the in-bundle manifest's **filename and coverage rule** — never the manifest's hash. The in-bundle SHA manifest hashes every bundle file except itself, including the audit JSON and the freeze record. The final ZIP's SHA-256 exists only in the external `.zip.sha256` sidecar.

**Producer inventory (complete; every producer is a shipped file that can receive a hash — no unnamed shell commands).** `tools/audit_spec_closure_bundle.py`; `tools/verify_terminal_bundle.py`; `tools/extract_latitude.py`; `tools/render_ledger_md.py`; `tools/run_fixture.py`; `tools/generate_file_delta.py`; `tools/generate_change_ledger.py`; `tools/generate_fixed_point_manifest.py`; `tools/generate_freeze_record.py`; `tools/generate_sha_manifest.py`; `tools/generate_human_review_index.py`; `tools/build_deterministic_bundle.py`; `tools/write_zip_sidecar.py`. The audit JSON records the SHA-256 of every producer and verifier, plus the Python implementation, version, and executable hash (producer provenance, not semantic authority).

**Phase-2 replay duties.** The audit replays evidence, writing only to a temporary comparison area, never rewriting frozen captures: re-run latitude extraction against the pinned documents and byte-compare; re-render the ledger Markdown from the canonical CSV/TSV and byte-compare; re-run **every** probe fixture in compare-only mode under the T-9 profile — each replay with fresh, empty `GOCACHE`, `GOMODCACHE`, `GOPATH`, and temporary directory — comparing stdout, stderr, exit status, command record, and effective-environment record to the frozen captures.

**Distribution member proofs — typed outcomes (CR6-2, adopted).** Phase-2 check `distribution_members_match` returns exactly one of: `PASS-CONFIRMED` | `PENDING-PROVENANCE` | `FAIL`. In **Confirmed mode**, for every pin whose stated origin is a Go distribution member, the audit extracts the named member from the verified tarball, byte-compares to the bundled pin, compares executable mode and symlink target where relevant, and records member path and result in the audit JSON; result must be `PASS-CONFIRMED`. In **Pending mode**, result is `PENDING-PROVENANCE`, `local_distribution_manifest_complete` must be `PASS`, and **every** affected pin and observation carries `PROVENANCE-PENDING`. The pins covered include at least the pinned spec HTML, the pinned memory-model HTML, `go/bin/go` (hash record), the pinned cmd/go source files, and the pinned modfile source; **the exact tar member path of each is recorded in `PINS_MANIFEST.tsv` and is the path the audit extracts** — no approximate member naming. Repo-tag-sourced pins name an exact external artifact and SHA-256. **Audit top status** is one of `PASS-CONFIRMED` | `PASS-WITH-PENDING-PROVENANCE` | `FAIL`; a pending provenance outcome is never called green.

**Tarball storage (decision made, not left to the executor):** the official `go1.23.2.linux-amd64.tar.gz` is an **external audit input**, not an in-bundle pin (the canonical archive stays ~1 MB; the tarball is reproducible from origin by hash). Its `PINS_MANIFEST.tsv` row records: origin (the official download URL), version, official SHA-256 (or PENDING), and storage = EXTERNAL-AUDIT-INPUT with the exact expected local path. In Confirmed mode the audit verifies presence and hash at that path before any extraction.

**Inventory completeness rule.** The audit JSON contains the complete file set and SHA-256 of every phase-1 file. The terminal verifier rejects any addition, deletion, or byte change in that set. The only later in-bundle files permitted are the audit JSON, the generated freeze record, and the generated SHA manifest.

**Canonical archive form.** Built only by `tools/build_deterministic_bundle.py`: **exactly one root directory, named `FIDO_GO1_23_SPEC_CLOSURE_REVIEW_BUNDLE_TERMINAL_2026-07-23/`** — the archive verifier rejects any other root and any second root; regular files and directories only; no symlinks; no absolute paths; no `.` or `..` components; no duplicate entry names; normalized POSIX paths; sorted entries; fixed timestamps; fixed modes; no host-specific extra fields; **`ZIP_STORED`**.

**Build order — thirteen steps, numbered 0–12 (CR6-4 count corrected):**
0. Verify the R1 baseline ZIP SHA-256 (`a01a7be5160b10e83bce11ed2161e353a94ca9bd86ef2843aca9fe29e1da303e`).
1. Extract it into a clean baseline tree.
2. Create a separate terminal working tree; apply only changes authorized by T-rows, recorded at change granularity.
3. Generate the change ledger and fixed-point manifest; then generate the file delta (T-0 scope and exclusions).
4. Produce all remaining canonical inputs (ledgers, generated Markdown, evidence, fixtures with captured outputs, human-review index, T-disposition ledger).
5. Run the phase-2 audit; write the frozen audit JSON.
6. Generate the freeze record from the audit JSON.
7. Generate the in-bundle SHA manifest.
8. Run the terminal verifier against the staged tree (writes nothing; exits nonzero on failure).
9. Build the ZIP in canonical form.
10. Extract the ZIP into a clean directory and run the terminal verifier there.
11. Inspect the ZIP's entries directly, apart from extraction: prove the archive entry multiset equals the canonical expected entry set; then compare extracted file bytes against the in-bundle manifest.
12. Write the external `.zip.sha256` sidecar with `tools/write_zip_sidecar.py`. Rob verifies the sidecar externally.

**Two-script split.** `tools/audit_spec_closure_bundle.py` (step 5; writes the frozen audit JSON; owns all input-only checks: row totality; the T-1 trichotomy; ACCEPTANCE-ALIGNMENT justification uniqueness; duplicate-representation histogram; line-ending uniformity; ragged-row detection; ID-prefix discipline; single-open-latitude rule, open set exactly `{LAT-X004}`; T-6 contract-definition checks; `baseline_delta_complete`; `fixed_points_preserved`; `distribution_members_match` (typed); `local_distribution_manifest_complete` (pending mode); regeneration and replay comparisons; T-18 index-versus-discovery). `tools/verify_terminal_bundle.py` (steps 8, 10–11; writes nothing; nonzero on failure; owns `freeze_claims_match`, manifest coverage and hash verification, inventory-drift rejection, the T-0 final-set equation, delta-exclusion enforcement, archive root/entry-multiset/extracted-byte checks).

---

## PART A — SUBSTANTIVE REPAIRS (complete)

### T-1 — BLOCKING — Acceptance alignment

**Background.** Eleven "Implementation restriction" latitude rows share one justification claiming compile-time acceptance "does not vary the meaning of a program." That claim is false for Fido's differential obligation: the fresh-build preflight makes pinned-gc acceptance part of the pipeline's definition of health, so a Fido-accepts / gc-rejects divergence is a Fido correctness failure. The preflight is the last line of defense, not the mechanism.

**ADR-0003 (PROPOSED, for Rob's disposition; quote verbatim in the ADR log; cite from every acceptance row):**

> **ADR-0003 — Authority ordering (PROPOSED).**
> 1. Where the pinned Go specification is definite, the specification governs meaning.
> 2. Where the specification grants latitude, is silent, or is hand-wavy, the pinned gc toolchain (go1.23.2) governs, and **Fido's acceptance must be a subset of pinned-gc acceptance**. Fido explicitly targets the official gc implementation only; no other Go implementation is a target.
> 3. Where pinned gc demonstrably contradicts definite specification text (a toolchain bug), the divergence is recorded as a ledger row and dispositioned by Rob; it is never silently adopted in either direction.
>
> **Interpretation clause.** In tier 2, "pinned gc governs" governs the supported **acceptance profile** and **pinned-toolchain adequacy claims**. It does not reduce a formal behavior set that definite specification latitude requires `GoMachine` to admit. Route A evaluation order, FMA alternatives, select choice, map iteration order, and scheduler choice remain fixed points unless a separately countersigned ledger disposition states otherwise. A permitted-set model is required because the pinned specification grants both branches. Current linux/amd64 evidence records only one target observation; other platform observations require their own pinned evidence and ledger revision.

**Requirements:**
1. Disposition kind **`ACCEPTANCE-ALIGNMENT`**: fields = pinned-toolchain acceptance observation (captured per T-9), Fido elaboration obligation, named contract, **individual** justification (audit: no two identical).
2. **Classification trichotomy**, audit-enforced over every implementation-restriction candidate: `ACCEPTANCE-ALIGNMENT` (in-scope accepted-language restriction); `OUT-COVERED` (feature priced out — LAT-180 and LAT-181 both land here); `NOT-LATITUDE` (exposition or deterministic prohibition only — LAT-118 as wrap-guaranteeing prohibition owned by SC-05; LAT-214 as exposition; accurate individual justifications).
3. Re-disposition individually: LAT-019, LAT-049, LAT-077, LAT-085, LAT-134, LAT-148, LAT-171, LAT-177, LAT-180, LAT-181, LAT-118, LAT-214, and any other candidate.
4. New contract **`SC-22-ACCEPTANCE-ALIGNMENT` at §25.23** (§25.22 = `SC-21-PROOF-COST-INTERNALS`, untouched): `fido_accepts_subset_pinned_gc` **frozen here, discharged at the checkpoints implementing its restriction cases**. Three claims separated: **Formal** — `CompilableProgram` satisfies every accepted ledger restriction (future theorem, per checkpoint); **External** — a publishable `DirectoryImage` passes the pinned-gc preflight (at publication); **Evidence** — pinned-gc probes record the selected acceptance profile (this pass). A finite probe set does not prove the global theorem.
5. **Evidence now / gates later.** Per ACCEPTANCE-ALIGNMENT row: **run** the pinned-gc fixture (raw stdout, stderr, status per T-9); **freeze** the future Fido half — exact fixture source, expected diagnostic ID, expected diagnostic text-or-shape, owner, implementing checkpoint — marked **`PENDING-IMPLEMENTATION`**; **never claim** a Fido-produced diagnostic. First frozen instances: unused local variables; constant acceptance bounds (probe pinned gc's limits); duplicate constant switch cases.
6. **Constant VALUE semantics — LAT-X004, ownership frozen.** Spec-permitted rounding during untyped constant folding can change an *accepted* constant's value; acceptance rows cannot own that. Ownership fixed now — Rob's open decision concerns the **policy**, never the owning layer: **owning closure row SPEC-096 (Constant expressions); semantic owner: `ExprFact`, the constant expression's intrinsic exact value; contract: `SC-05-EXPR-FACT-USE-EVAL` at §25.6** (verified: SPEC-096 already cites SC-05 — restoration, not invention). `SC-22` owns only entry into `CompilableProgram`; `SC-02-CONSTANTS-LITERALS` (§25.3) owns representation primitives and supports the proof without owning folding results. Latitude columns on every row: `decision_status`, `rob_choice`, `rob_countersign`; all `DISPOSITIONED` except `LAT-X004: HUMAN-CHOICE-OPEN`, empty choice and countersign; audit: open set = `{LAT-X004}` exactly. Menu (inside the fixed owner): (i) admit all specification-permitted rounded values; (ii) prove accepted constants invariant under the permitted rounding latitude — including the domain-restriction variant tying to the constant acceptance bounds so exact and pinned-gc values provably coincide; (iii) exact pinned-gc constant profile as an explicit Rob-approved refinement. **Advisory recommendation, labeled (both reviewers, independently): option (ii), domain-restriction variant.** Process: the terminal bundle ships with LAT-X004 open; Rob's selection — informed by this pass's constant-bound probes — triggers regeneration, re-audit, and re-freeze as the first step of the FCB transformation. The freeze record states the open decision explicitly.

### T-2 — REQUIRED — Pinned distribution execution; confirmed/pending modes

Delete the 13.8 MB in-bundle executor. A binary cannot self-attest; `go` delegates to `pkg/tool/linux_amd64/compile` and `link` and consumes the standard library under `GOROOT`.

**Confirmed mode** (required for `TERMINAL-REPAIR-CANDIDATE`): official tarball **bytes** present at the recorded external path; official SHA-256 confirmed; hash matches. The runner **always extracts the verified bytes into a new sandbox and runs that tree** (the pre-existing-GOROOT branch is removed — it adds no value when the verified tarball is present; CR6-2); member `go/bin/go` hash is a secondary check.

**Pending mode** (tarball bytes unavailable): copy the local Go distribution into the fixed sandbox; create a complete manifest of regular files, symlink targets, and executable modes; hash that manifest; run only from that copied sandbox; mark **every** observation and **every unproved pin** `PROVENANCE-PENDING`; record the local-tree manifest in evidence and audit JSON; completion cannot be claimed. An official hash without the bytes populates the expected pin value only.

Pending provenance is listed in the Human-Review Index and forces `OPEN-REVIEW-CANDIDATE` status. `PINS_MANIFEST.tsv` carries the tarball row per Part 0's storage decision. The evidence doc keeps the provenance chain.

### T-3 — REQUIRED — Racy-run scope: option (b)

`step : State -> Label -> State -> Prop` receives no trace; havoc-after-race would require race history in `State`, a taint field, an operational detector beside the trace-based definition, or a second run rule. Therefore: LAT-217, LAT-218, LAT-219, LAT-224 remain STEP-NONDET; `DataRace` remains a derived finite BadPrefix; §27 gains, in substance verbatim: *sub-value and machine-word access granularity is deliberate proof cost that affects condemned runs, not reachable safe-run behavior; it may be narrowed only by a future countersigned ledger disposition*; the four rows cite only the owning channel/race contract; copied `SC-20-EVAL-ORDER-LATITUDE` tails removed.

### T-4 — REQUIRED — Template drift measurable

`template: lexical-only` on the 48 OP- and 25 KEY- rows (and other justified shared-text rows); duplicate-representation histogram (top N with counts) in the frozen JSON; old-template regex stays.

---

## PART B — SHOWROOM ITEMS (complete; N = non-substantive, still required)

- **T-5. Line endings.** Every tabular artifact LF; audit checks; the closure CSV is currently CRLF and must be normalized.
- **T-6. Contract definitions audited, not token text.** Full mapping table SC-00 = §25.1 … SC-20 = §25.21, SC-21 = §25.22 (pre-existing), SC-22 = §25.23 (new). Audit parses actual `### 25.N \`SC-XX-…\`` headings: exactly one definition per identifier; exactly one identifier per heading; the table is a byte-for-byte projection; contiguity SC-00..SC-22; every citation names a defined heading; no defined contract uncited without stated reason. Relevance fixed by hand this pass.
- **T-7. ID discipline.** `LAT-###` stable manifest ordinals; hand-added `LAT-X###` (next: LAT-X004); `BOUND-###` live; `BOUND-X###` priced exclusions. Audit checks prefixes.
- **T-8. Freeze claims emitted.** Every freeze count read from the audit JSON; `freeze_claims_match` in the terminal verifier.
- **T-9. Closed probe environment, one canonical profile.** One runner, `tools/run_fixture.py`, per T-2 (verified sandbox distribution only), starting from an **empty environment** and applying exactly **`.review/tools/PROBE_ENVIRONMENT.tsv`** — the runner reads the file, never repeats values internally. **The profile defines the complete allowed key set; unknown keys fail the audit** (CR6-4 — no "at least"). The set: `GOROOT` (verified sandbox root), `PATH` (fixed, minimal), `HOME`, `TMPDIR`, `GOCACHE`, `GOMODCACHE`, `GOPATH` (all sandbox; caches fresh per replay), `LANG`, `LC_ALL`, `TZ`, `GODEBUG` (empty), `GOTRACEBACK`, `GOOS=linux`, `GOARCH=amd64`, `GOAMD64=v1` (any other value is an explicit target decision), `CGO_ENABLED=0`, `GOFLAGS=""`, `GOPROXY=off`, `GOTOOLCHAIN=local`, `GOENV=off`, `GOWORK=off`. The profile also states: process umask; fixed sandbox root; path-normalization rule. The runner records the exact command and effective `go env` per run; raw stdout, stderr, exit status retained beside each fixture. Flagged as a proposed BOUND-003 strengthening for the implementing checkpoint.
- **T-10. Pins manifest.** `.review/pins/PINS_MANIFEST.tsv`: filename, upstream origin (**exact tar member path**, or repo path at tag as an exact external artifact with SHA-256, or EXTERNAL-AUDIT-INPUT for the tarball), version, SHA-256 (or PENDING). One naming convention; the freeze references the manifest.
- **T-11. One canonical source per table.** Closure CSV and Latitude TSV canonical; `tools/render_ledger_md.py` consumes both, generates the entire ledger Markdown headed `GENERATED FROM CSV/TSV — DO NOT EDIT`; phase 2 regenerates and byte-compares.
- **T-12. Ragged-row detection** across all TSV/CSV files.
- **T-13. Self-describing audit.** Audit JSON: schema version; every producer and verifier hash per Part 0; Python provenance record; typed top status per Part 0.
- **T-14. Platform-pending note.** One sentence in ledger header and evidence doc: platform set under pending ADR-0004; all current evidence `go1.23.2 linux/amd64` scope; no platform rows this pass.
- **T-15 (N). Root README** listing every bundle file with a one-line purpose.
- **T-16 (N). Supersession chain, acyclic.** Freeze lists predecessor ZIP hashes (original bundle; R1 `a01a7be5160b10e83bce11ed2161e353a94ca9bd86ef2843aca9fe29e1da303e`), the frozen audit JSON hash, and the manifest's filename and coverage rule; the terminal ZIP hash lives only in the external sidecar. Names this the final bundle under the spec-closure family name.
- **T-17 (N). FMA margin note, verbatim, in the evidence doc's FMA section:** "The one-bit `x*y+z` vs `math.FMA` discrepancy doubles as a CPU-feature parlor trick: a pure-Go fingerprint of fused-multiply-add hardware paths. Recorded here for delight; not load-bearing."
- **T-18 (REQUIRED). Human-Review Index — discovery-based.** Generated by `tools/generate_human_review_index.py`; discovers every unresolved human act from canonical sources, never hardcoded: every F, R, and T disposition row (**T rows from the canonical TSV of T-19**; F and R rows from their existing frozen sources); every empty Rob countersign; every ADR with status PROPOSED, OPEN, PENDING, or REJECTED-AS-WRITTEN/OPEN; every open latitude decision; every pending pin or provenance confirmation; every row explicitly marked as requiring a human act. Minimum terminal contents: ADR-0001 (PROPOSED), ADR-0002 (REJECTED AS WRITTEN / OPEN), ADR-0003 (PROPOSED), ADR-0004 (pending), LAT-X004, all empty F-/R-/T- countersigns, toolchain provenance if pending. Every cited ADR exists in-bundle as a frozen read-only record or is named as an external authority with exact path and SHA-256. The audit compares the generated index against the discovered set, failing on omissions and stale rows. Carried into the FCB transformation.
- **T-19 (REQUIRED, NEW). Canonical T-disposition ledger (CR6-3, adopted).** `.review/FIDO_TERMINAL_CORRECTNESS_DISPOSITIONS_2026-07-23.tsv`, columns: `id`, `severity`, `model_record`, `artifact_locations`, `applied_change`, `rob_countersign`. Required rows: **T-0 through T-19**; required values: `model_record = APPLIED`, `rob_countersign` empty. **This TSV is the sole T-disposition authority**; a generated Markdown view is permitted; the Human-Review Index discovers T rows from this TSV only.

---

## COMPLETION (exact status values)

Exactly one status, stated verbatim in the freeze record:

- **`TERMINAL-REPAIR-CANDIDATE`** — documentary completion. Requires: every T-item's deliverables (T-0 through T-19; N-items included); T-0's three artifacts complete with `baseline_delta_complete` and `fixed_points_preserved` green at change granularity; the thirteen-step build order (0–12) followed and stated in the freeze record, including post-ZIP extraction verification and the direct archive entry-multiset and single-root checks; producer inventory, replay comparisons, and index-versus-discovery green in the frozen audit JSON; **`distribution_members_match = PASS-CONFIRMED` and audit top status `PASS-CONFIRMED`**; ADR-0003 present verbatim and PROPOSED; **LAT-X004 the sole open Latitude Ledger disposition**; all PENDING-IMPLEMENTATION rows carry frozen future-Fido fixture specs with no claimed Fido observations; every terminal-verifier run exits successfully without rewriting any frozen artifact; T-19 records `APPLIED` per row with empty countersigns; nothing claims acceptance, closure, FIXED status, or a score.
- **`OPEN-REVIEW-CANDIDATE`** — valid deliverable in Pending mode: identical requirements except provenance, with `distribution_members_match = PENDING-PROVENANCE`, `local_distribution_manifest_complete = PASS`, audit top status **`PASS-WITH-PENDING-PROVENANCE`**, no failed checks, exactly the declared pending-provenance items, every affected pin and observation `PROVENANCE-PENDING`, and the freeze record **stating explicitly that completion is blocked and why**.

Deliver `FIDO_GO1_23_SPEC_CLOSURE_REVIEW_BUNDLE_TERMINAL_2026-07-23.zip` (single root `FIDO_GO1_23_SPEC_CLOSURE_REVIEW_BUNDLE_TERMINAL_2026-07-23/`) in canonical archive form plus its external `.zip.sha256` sidecar. Rob's countersigns — indexed by T-18 from T-19 and the frozen F/R sources, decided row by row, with his LAT-X004 policy choice at the FCB regeneration — end the correctness volleys.
