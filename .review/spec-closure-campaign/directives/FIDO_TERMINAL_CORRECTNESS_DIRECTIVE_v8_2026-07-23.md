# FIDO — TERMINAL CORRECTNESS DIRECTIVE, v8 (SPEC-CLOSURE FAMILY, FINAL PASS — SELF-CONTAINED)

**Date:** 2026-07-23
**Issued by:** Rob (human authority). This file is the directive.
**Repair authorization token:** `SPEC-CLOSURE-terminal-repair-2` (unchanged)
**Version:** v8 — self-contained. **This document alone is sufficient to execute and audit the repair. Earlier directives are provenance only.**
**Supersedes (full hashes):**
- v7 `5c1996a5c2bffc8f0bad43e4f1c6fde328d997deb0bafeb2586e92ee60b0db15`
- v6 `dc7a369120ab23c548998739111d1eb7ef7edcfac652dd9d634cfab494cc3562`
- v5 `5a083bf157cd97644755517e7e7fa1a8f31c5bcd65fa9a4b5b4a39106d44d6c9`
- v4 `eab3b1ed4b856157f7c784a6a7bcd35f5abe454cd558fb631b1f6772095648ff`
- v3 `6a99418c02cba3063bc43e61a71c48197fe3a55889d5c18f0225d5b78dbc011b`
- v2 `d8b2a9c71355ed0163b00bfa6a3aa9ca6dd6646a1ca80d30dd0596a022d560a2`
- v1 `b30c03b8c16a09868763f891ec2fd92f3a03f2a0739c852b497a536b70502a34`

**Baseline:** `FIDO_GO1_23_SPEC_CLOSURE_REVIEW_BUNDLE_R1_2026-07-23.zip`, SHA-256 `a01a7be5160b10e83bce11ed2161e353a94ca9bd86ef2843aca9fe29e1da303e`.

**Provenance:** Authored by Claude (Fable 5, external adversarial reviewer). Co-review round 7 by ChatGPT (Sol 5.6): one BLOCKING finding in three parts (CR7-1, sealing order and change-ledger self-coverage), two REQUIRED (CR7-2 selector algebra, CR7-3 mechanical fixed-point completeness), three small constants — **all adopted**. v7's hash verified (match). Self-reference bug-class count, for the record: **four** (v2 freeze↔manifest cycle; v3 audit-checks-freeze; v6 delta carrying its own hash; v7 change ledger required to cover itself) — each caught before execution. The findings of rounds 5–7 all live inside the sealing subsystem itself, which is expected: provenance machinery is the one part of a bundle that must reason about itself, and self-reference is its native predator. Per the co-reviewer: no architecture, semantics, or evidence-policy round remains; v8 changes only the sealing process.

---

## AUTHORITY LIMITS (binding, complete)

1. Documentary artifacts, pins, scripts, fixtures, and recorded observations only. Compiling and executing probe fixtures against the pinned toolchain **to record evidence** is in scope. Modifying the Fido repository — source, `.v` files, build system, gates — is not.
2. Nothing produced by this repair may claim FIXED, accepted, closed, countersigned, spec-closed-in-implementation, or any score. Models record `APPLIED` at most.
3. Every countersign cell is created empty and remains Rob's alone.
4. This directive does not accept C4, does not authorize C5, and does not alter the active C4 repair authority or `NEXT_STEPS.md` state.
5. Normative text may not contain unpinned claims. World-knowledge is not evidence; pinned artifacts, hashes, and captured observations are.
6. One authority per meaning, for code, documents, and directives alike. New directive versions supersede by name and full hash; two live directives may never coexist. A directive must be self-contained.
7. The repair may change only what a T-row authorizes, at **change granularity** (T-0). External reviews, prior repair directives, and copied ADR records are read-only evidence: byte-identical unless one exact T-row expressly authorizes replacement.

## FIXED POINTS (complete; protected by the T-0 fixed-point manifest as **projections** with stable IDs)

**(A) Architectural — `ARCH-01` … `ARCH-12`** (from the original strict review's "What Must Not Change"):
- ARCH-01 The §1 deletion and generalization standard — the five retention tests and the prohibition list.
- ARCH-02 The minimal `Machine` base (§2); no Go feature defines a second run relation.
- ARCH-03 The one-owner-per-meaning table (§3).
- ARCH-04 The expression fact/use split (§5) — "the use builder does not inspect the raw child again."
- ARCH-05 The single type algebra (§6): `RuntimeType := SemanticType Empty_set`, alias non-identity, declaration-reference recursion.
- ARCH-06 The static-slot / dynamic-place distinction (§11).
- ARCH-07 Stack-only panic / defer / recover (§13) with `finishing_pushes_only_deferred_activations` and `above_finishing_iff_deferred_call`.
- ARCH-08 Resource-local origins with proof-connected provenance (§15).
- ARCH-09 Finite bad-prefix safety with liveness held separate (§17).
- ARCH-10 Rejection of vacuous library safety from an empty start set (§19).
- ARCH-11 The Do-Not-Do-Early list (§24), verbatim.
- ARCH-12 The candidate-only acceptance stance (§26) with Rob as sole disposition owner.

**(B) Evidence-and-model — `EVID-01` … `EVID-12`:**
- EVID-01 Pinned spec SHA-256 `c47fb4b5b795b9732cbae0250dcb84f791df78bb98695b30fb3f7788d1c9b389`; pinned memory-model SHA-256 `366b995adeee8b57bd23547feea8252a7ee619baec91cb22cfb21b12208da2c6`.
- EVID-02 Reproducible audit and latitude extraction (shipped scripts re-run to byte-identical frozen outputs).
- EVID-03 Route A evaluation-order nondeterminism (plan §12.4; `SC-20-EVAL-ORDER-LATITUDE` §25.21); spec-specified lexical left-to-right call/method/receive ordering deterministic with fixtures.
- EVID-04 The FMA both-branches model (LAT-121, STEP-NONDET); pinned-target observation as adequacy evidence only. Protected projection: disposition; owner; contract; both-branches representation; adequacy-only target observation. Governance columns may be added.
- EVID-05 Select-choice, map-iteration (SPEC-X006), scheduler nondeterminism as STEP-NONDET; `print`/`println` output as ADEQUACY-DEMOTION (SPEC-X005).
- EVID-06 BOUND-001..003: emitted `go 1.23` directive equals the ledger language version; module path from the single ModulePath authority; no `toolchain` directive; invocation `GOTOOLCHAIN=local`, `GOENV=off`, `GOWORK=off`, `go version` verified before build.
- EVID-07 The §22.3 terminal observation tuple; `println` → stderr; fatal panic → exit 2 with first-line projection `panic: <value>`; runtime noise excluded explicitly, owned by BOUND-X009.
- EVID-08 APPLIED-only provenance; empty countersign columns; the audit's machine-checkable/judgment split.
- EVID-09 Synthesized-anchor flags; the grammar counting rule (174 definitions / 173 names, metagrammar included, `Expression` twice) in the artifact header.
- EVID-10 NaN-map row (SPEC-124) and struct-tag rows (SPEC-026) with their fixtures.
- EVID-11 **`SC-21-PROOF-COST-INTERNALS` at §25.22** — never overwrite, renumber, or weaken.
- EVID-12 `uintptr` remains OUT pending ADR-0001.

---

## T-0 — BLOCKING — BASELINE DELTA AND PRESERVATION (CR7-1 order; executes before all else)

**Rule:** the terminal bundle is an **authorized transformation of the exact R1 baseline**; the enforced invariant is **every change has exactly one T-owner** at change granularity; files carry owner **sets**.

**Three canonical artifacts (named generators):**

**A. File delta — `.review/FIDO_TERMINAL_FILE_DELTA_2026-07-23.tsv`** (`tools/generate_file_delta.py`). Columns: `baseline_path`, `terminal_path`, `baseline_kind`, `terminal_kind`, `baseline_sha256`, `terminal_sha256`, `action`, `owners`, `rationale`. Paths relative to the bundle content root (the ZIP root directory is not part of the comparison path); `RENAMED` uses both path columns; `ADDED` leaves baseline path/hash empty; `DELETED` leaves terminal path/hash empty; `owners` is the sorted set of T-rows owning changes within the file and must equal the set derived from the change ledger.

**B. Change ledger — `.review/FIDO_TERMINAL_CHANGE_LEDGER_2026-07-23.tsv`** (`tools/generate_change_ledger.py`). Columns: `change_id`, `path`, `selector_kind`, `selector`, `baseline_fragment_sha256`, `terminal_fragment_sha256`, `owner`, `rationale`. Each changed unit has **exactly one owner**.

**Selector kinds (closed algebra; CR7-2, adopted):** `markdown-heading`; `markdown-block`; `table-row`; `table-field`; `table-schema` (column additions, removals, ordering); `json-pointer`; `python-symbol` (one top-level function, class, or named constant — **each T-owned audit check lives in a named function so `python-symbol` gives it one stable owner**); `anchored-region` (an exact unique start/end block where no syntax-level selector exists); `file-property` (serialization facts: line ending, path, mode, generated status); `whole-file`. **Normalization rule:** semantic row/field diffs for tables are computed after normalizing both inputs to LF; the raw CRLF→LF change is recorded separately as `file-property` / `line-ending` / owner T-5. **Overlap policy:** the audit rejects overlap within one projection type and permits orthogonal changes to one file (e.g., `file-property: line-ending` alongside `table-field: LAT-134.disposition`).

**C. Fixed-point manifest — `.review/FIDO_TERMINAL_FIXED_POINT_MANIFEST_2026-07-23.tsv`** (`tools/generate_fixed_point_manifest.py`). Columns: `fixed_point_id`, `path`, `selector_kind`, `selector`, `protected_projection`, `baseline_projection_sha256`. Prose fixed points protect the exact named block; table fixed points protect exactly the meaning-bearing fields, so governance columns may be added without touching protected fields.

**Audit obligations (phase-2):**
- `baseline_delta_complete` — structural diff proving: every changed unit appears exactly once in the change ledger; no changed unit lacks an owner; no ledger entry names an unchanged unit; no two owners for one change; orthogonal-overlap policy respected; file-level owner sets equal change-level owner sets; no unlisted file change; no missing baseline file; no unlisted added file; no altered external review or prior directive.
- `fixed_point_manifest_complete` (CR7-3, adopted) — proves: the row set is **exactly** the 24 IDs ARCH-01..ARCH-12 and EVID-01..EVID-12; no ID occurs twice; every selector resolves exactly once in the verified R1 baseline; every selector resolves exactly once in the terminal tree; the audit **recomputes** each baseline projection hash from the R1 bytes; the stored `baseline_projection_sha256` matches the recomputed hash; the terminal projection matches the verified baseline projection. **The audit never trusts the hash written in the manifest.** An empty or partial manifest fails; vacuous passes are impossible.
- `fixed_points_preserved` — for every manifest row, terminal projection hash equals the recomputed baseline projection hash.

**Scopes (exact; the meta-file exclusions):**
- Change-ledger scope excludes: the change ledger itself; the file delta; the audit JSON; the freeze record; the SHA manifest.
- File-delta scope excludes: the file delta itself; the audit JSON; the freeze record; the SHA manifest. **The file delta includes and hashes the completed change ledger.**
- The terminal verifier assigns the two self-excluded T-0 files their owner **by rule**: change ledger → T-0; file delta → T-0. **No other file may use this exception.**

**Final-set equation (acyclic), proved by the terminal verifier:**
final in-bundle set = ordinary phase-1 inputs + fixed-point manifest + change ledger + file delta + audit JSON + freeze record + SHA manifest.

**Read-only evidence rule.** External reviews, prior repair directives, and copied ADR records remain byte-identical. **This v8 directive enters the terminal bundle as a frozen read-only authority**, in the ordinary phase-1 inputs and the file delta (ADDED, owner T-0) under its exact SHA-256, computed at delivery.

---

## PART 0 — FREEZE PROTOCOL, EVIDENCE CHAIN, AND CANONICAL ARCHIVE (complete)

**Acyclicity rule.** The audit JSON hashes only audit **inputs** — including the completed file delta — never itself, the freeze record, the SHA manifest, the ZIP, or the sidecar. The freeze record is generated from the frozen audit JSON and lists: predecessor ZIP hashes, the frozen audit JSON hash, and the manifest's **filename and coverage rule** (never its hash). The SHA manifest hashes every in-bundle file except itself, including the audit JSON and freeze record. The final ZIP's SHA-256 exists only in the external `.zip.sha256` sidecar.

**Producer inventory (every producer is a shipped, hashable file; no unnamed shell commands):** `tools/audit_spec_closure_bundle.py`; `tools/verify_terminal_bundle.py`; `tools/extract_latitude.py`; `tools/render_ledger_md.py`; `tools/run_fixture.py`; `tools/generate_file_delta.py`; `tools/generate_change_ledger.py`; `tools/generate_fixed_point_manifest.py`; `tools/generate_freeze_record.py`; `tools/generate_sha_manifest.py`; `tools/generate_human_review_index.py`; `tools/build_deterministic_bundle.py`; `tools/write_zip_sidecar.py`. The audit JSON records every producer/verifier SHA-256 plus the Python implementation, version, and executable hash.

**Phase-2 replay duties.** Replay, never merely hash, writing only to a temporary area: re-run latitude extraction and byte-compare; re-render the ledger Markdown from the canonical CSV/TSV and byte-compare; re-run **every** probe fixture in compare-only mode under the T-9 profile — fresh, empty `GOCACHE`, `GOMODCACHE`, `GOPATH`, and temp dir per replay — comparing stdout, stderr, exit status, command record, and effective-environment record to frozen captures.

**Distribution member proofs — typed outcomes.** `distribution_members_match` ∈ {`PASS-CONFIRMED`, `PENDING-PROVENANCE`, `FAIL`}. Confirmed mode: for every pin whose origin is a distribution member, extract the member named by its **exact tar member path in `PINS_MANIFEST.tsv`** from the verified tarball; byte-compare; compare mode/symlink target where relevant; record path and result; require `PASS-CONFIRMED`. Pending mode: `PENDING-PROVENANCE` with `local_distribution_manifest_complete = PASS` and every affected pin and observation `PROVENANCE-PENDING`. Covered pins include at least: the pinned spec HTML, the pinned memory-model HTML, `go/bin/go` (hash record), the pinned cmd/go source files, the pinned modfile source. Repo-tag pins name an exact external artifact and SHA-256. **Audit top status** ∈ {`PASS-CONFIRMED`, `PASS-WITH-PENDING-PROVENANCE`, `FAIL`}; pending is never called green.

**Tarball storage (decided):** the official `go1.23.2.linux-amd64.tar.gz` is an **external audit input** (storage = EXTERNAL-AUDIT-INPUT in its `PINS_MANIFEST.tsv` row: origin URL, version, official SHA-256 or PENDING, exact expected local path). Confirmed mode verifies presence and hash at that path before any extraction.

**Inventory completeness rule.** The audit JSON contains the complete file set and SHA-256 of every phase-1 file (ordinary inputs + the three T-0 artifacts). The terminal verifier rejects any addition, deletion, or byte change in that set; the only later in-bundle files are the audit JSON, freeze record, and SHA manifest.

**Canonical archive form (constants pinned; CR7 small corrections):** built only by `tools/build_deterministic_bundle.py`; **exactly one root directory `FIDO_GO1_23_SPEC_CLOSURE_REVIEW_BUNDLE_TERMINAL_2026-07-23/`** (verifier rejects any other or second root); regular files and directories only; no symlinks; no absolute paths; no `.`/`..` components; no duplicate entry names; normalized POSIX paths; sorted entries; **timestamp `1980-01-01 00:00:00`; directory mode `0755`; regular-file mode `0644`; compression `ZIP_STORED`** — builder and verifier use the same constants.

**Build order — seventeen steps, numbered 0–16 (CR7-1, adopted):**
0. Verify the R1 baseline ZIP SHA-256 (`a01a7be5160b10e83bce11ed2161e353a94ca9bd86ef2843aca9fe29e1da303e`).
1. Extract the baseline into a clean tree.
2. Create the terminal working tree.
3. Apply all substantive T-row changes, recorded at change granularity.
4. Produce all ordinary phase-1 inputs: tools, pins, fixtures, captured evidence, canonical tables, generated Markdown, plan, ADR records, T-disposition ledger.
5. Generate the Human-Review Index from the completed T/F/R/ADR sources.
6. Generate the fixed-point manifest.
7. Generate the change ledger (its scope excludes itself, the file delta, and the three later governance files).
8. Generate the file delta (its scope excludes itself and the three later governance files; it includes and hashes the completed change ledger).
9. Run the phase-2 audit; write the frozen audit JSON.
10. Generate the freeze record from the audit JSON.
11. Generate the in-bundle SHA manifest.
12. Run the terminal verifier against the staged tree (writes nothing; nonzero on failure).
13. Build the ZIP in canonical form.
14. Extract the ZIP into a clean directory and run the terminal verifier there.
15. Inspect the archive entries directly: prove the entry multiset equals the canonical expected set; then compare extracted bytes against the in-bundle manifest.
16. Write the external `.zip.sha256` sidecar with `tools/write_zip_sidecar.py`. Rob verifies the sidecar externally.

**Two-script split.** `tools/audit_spec_closure_bundle.py` (step 9; writes the frozen audit JSON; owns input-only checks: row totality; T-1 trichotomy; ACCEPTANCE-ALIGNMENT justification uniqueness; the **full** duplicate-representation histogram sorted by count then text hash (no "top N"); line-ending uniformity; ragged rows; ID-prefix discipline; single-open-latitude rule, open set exactly `{LAT-X004}`; T-6 contract-definition checks; `baseline_delta_complete`; `fixed_point_manifest_complete`; `fixed_points_preserved`; `distribution_members_match` (typed); `local_distribution_manifest_complete`; regeneration and replay comparisons; T-18 index-versus-discovery). `tools/verify_terminal_bundle.py` (steps 12, 14–15; writes nothing; nonzero on failure; owns `freeze_claims_match`, manifest coverage and hash verification, inventory-drift rejection, the T-0 final-set equation and meta-file-exclusion enforcement, T-0-owner-by-rule assignment for the two self-excluded files, archive root/entry-multiset/extracted-byte checks).

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
1. Disposition kind **`ACCEPTANCE-ALIGNMENT`**: pinned-toolchain acceptance observation (per T-9), Fido elaboration obligation, named contract, **individual** justification (audit: no two identical).
2. **Classification trichotomy**, audit-enforced over every implementation-restriction candidate: `ACCEPTANCE-ALIGNMENT` (in-scope accepted-language restriction); `OUT-COVERED` (feature priced out — LAT-180 and LAT-181 both land here); `NOT-LATITUDE` (exposition or deterministic prohibition only — LAT-118 as wrap-guaranteeing prohibition owned by SC-05; LAT-214 as exposition; accurate individual justifications).
3. Re-disposition individually: LAT-019, LAT-049, LAT-077, LAT-085, LAT-134, LAT-148, LAT-171, LAT-177, LAT-180, LAT-181, LAT-118, LAT-214, and any other candidate.
4. New contract **`SC-22-ACCEPTANCE-ALIGNMENT` at §25.23** (§25.22 = `SC-21-PROOF-COST-INTERNALS`, untouched): `fido_accepts_subset_pinned_gc` **frozen here, discharged at the checkpoints implementing its restriction cases**. Three claims: **Formal** — `CompilableProgram` satisfies every accepted ledger restriction (future theorem, per checkpoint); **External** — a publishable `DirectoryImage` passes the pinned-gc preflight (at publication); **Evidence** — pinned-gc probes record the selected acceptance profile (this pass). A finite probe set does not prove the global theorem.
5. **Evidence now / gates later.** Per row: **run** the pinned-gc fixture (raw stdout, stderr, status per T-9); **freeze** the future Fido half — exact fixture source, expected diagnostic ID, expected diagnostic text-or-shape, owner, implementing checkpoint — marked **`PENDING-IMPLEMENTATION`**; **never claim** a Fido-produced diagnostic. First frozen instances: unused local variables; constant acceptance bounds (probe pinned gc's limits); duplicate constant switch cases.
6. **Constant VALUE semantics — LAT-X004, ownership frozen.** Spec-permitted rounding during untyped constant folding can change an *accepted* constant's value; acceptance rows cannot own that. Ownership fixed now — Rob's open decision concerns the **policy**, never the owning layer: **owning closure row SPEC-096 (Constant expressions); semantic owner: `ExprFact`, the constant expression's intrinsic exact value; contract: `SC-05-EXPR-FACT-USE-EVAL` at §25.6** (verified: SPEC-096 already cites SC-05 — restoration, not invention). `SC-22` owns only entry into `CompilableProgram`; `SC-02-CONSTANTS-LITERALS` (§25.3) owns representation primitives, supporting the proof without owning folding results. Latitude columns on every row: `decision_status`, `rob_choice`, `rob_countersign`; all `DISPOSITIONED` except `LAT-X004: HUMAN-CHOICE-OPEN`, empty choice and countersign; audit: open set = `{LAT-X004}` exactly. Menu (inside the fixed owner): (i) admit all specification-permitted rounded values; (ii) prove accepted constants invariant under the permitted rounding latitude — including the domain-restriction variant tying to the constant acceptance bounds so exact and pinned-gc values provably coincide; (iii) exact pinned-gc constant profile as an explicit Rob-approved refinement. **Advisory recommendation, labeled (both reviewers, independently): option (ii), domain-restriction variant.** Process: the terminal bundle ships with LAT-X004 open; Rob's selection — informed by this pass's constant-bound probes — triggers regeneration, re-audit, and re-freeze as the first step of the FCB transformation. The freeze record states the open decision explicitly.

### T-2 — REQUIRED — Pinned distribution execution; confirmed/pending modes

Delete the 13.8 MB in-bundle executor. A binary cannot self-attest; `go` delegates to `pkg/tool/linux_amd64/compile` and `link` and consumes the standard library under `GOROOT`.

**Confirmed mode** (required for `TERMINAL-REPAIR-CANDIDATE`): official tarball **bytes** present at the recorded external path; official SHA-256 confirmed; hash matches. The runner **always extracts the verified bytes into a new sandbox and runs that tree**; member `go/bin/go` hash is a secondary check.

**Pending mode** (tarball bytes unavailable): copy the local Go distribution into the fixed sandbox; create a complete manifest of regular files, symlink targets, and executable modes; hash that manifest; run only from that copied sandbox; mark **every** observation and **every unproved pin** `PROVENANCE-PENDING`; record the local-tree manifest in evidence and audit JSON; completion cannot be claimed. An official hash without the bytes populates the expected pin value only.

Pending provenance is listed in the Human-Review Index and forces `OPEN-REVIEW-CANDIDATE`. The evidence doc keeps the provenance chain.

### T-3 — REQUIRED — Racy-run scope: option (b)

`step : State -> Label -> State -> Prop` receives no trace; havoc-after-race would require race history in `State`, a taint field, an operational detector beside the trace-based definition, or a second run rule. Therefore: LAT-217, LAT-218, LAT-219, LAT-224 remain STEP-NONDET; `DataRace` remains a derived finite BadPrefix; §27 gains, in substance verbatim: *sub-value and machine-word access granularity is deliberate proof cost that affects condemned runs, not reachable safe-run behavior; it may be narrowed only by a future countersigned ledger disposition*; the four rows cite only the owning channel/race contract; copied `SC-20-EVAL-ORDER-LATITUDE` tails removed.

### T-4 — REQUIRED — Template drift measurable

`template: lexical-only` on the 48 OP- and 25 KEY- rows (and other justified shared-text rows); the **full** duplicate-representation histogram, sorted by count then text hash, in the frozen JSON; old-template regex stays.

---

## PART B — SHOWROOM ITEMS (complete; N = non-substantive, still required)

- **T-5. Line endings.** Every tabular artifact LF; audit checks; the closure CSV is currently CRLF and must be normalized. Its change-ledger entry is `file-property` / `line-ending` / T-5, orthogonal to table-level entries.
- **T-6. Contract definitions audited, not token text.** Full mapping table SC-00 = §25.1 … SC-20 = §25.21, SC-21 = §25.22 (pre-existing), SC-22 = §25.23 (new). Audit parses actual `### 25.N \`SC-XX-…\`` headings: exactly one definition per identifier; exactly one identifier per heading; the table is a byte-for-byte projection; contiguity SC-00..SC-22; every citation names a defined heading; no defined contract uncited without stated reason. Relevance fixed by hand this pass.
- **T-7. ID discipline.** `LAT-###` stable manifest ordinals; hand-added `LAT-X###` (next: LAT-X004); `BOUND-###` live; `BOUND-X###` priced exclusions. Audit checks prefixes.
- **T-8. Freeze claims emitted.** Every freeze count read from the audit JSON; `freeze_claims_match` in the terminal verifier.
- **T-9. Closed probe environment, one canonical profile.** One runner, `tools/run_fixture.py`, per T-2 (verified sandbox distribution only), starting from an **empty environment** and applying exactly **`.review/tools/PROBE_ENVIRONMENT.tsv`**, which **defines the complete allowed key set — unknown keys fail the audit**: `GOROOT` (verified sandbox root), `PATH` (fixed, minimal), `HOME`, `TMPDIR`, `GOCACHE`, `GOMODCACHE`, `GOPATH` (all sandbox; caches fresh per replay), `LANG`, `LC_ALL`, `TZ`, `GODEBUG` (empty), `GOTRACEBACK`, `GOOS=linux`, `GOARCH=amd64`, `GOAMD64=v1` (any other value is an explicit target decision), `CGO_ENABLED=0`, `GOFLAGS=""`, `GOPROXY=off`, `GOTOOLCHAIN=local`, `GOENV=off`, `GOWORK=off`. The profile also states: process umask; fixed sandbox root; path-normalization rule. The runner records the exact command and effective `go env` per run; raw stdout, stderr, exit status retained beside each fixture. Flagged as a proposed BOUND-003 strengthening for the implementing checkpoint.
- **T-10. Pins manifest.** `.review/pins/PINS_MANIFEST.tsv`: filename, upstream origin (**exact tar member path**, or repo path at tag as an exact external artifact with SHA-256, or EXTERNAL-AUDIT-INPUT for the tarball), version, SHA-256 (or PENDING). **Naming convention `<artifact>_<version>.<ext>`, restored explicitly**; the freeze references the manifest.
- **T-11. One canonical source per table.** Closure CSV and Latitude TSV canonical; `tools/render_ledger_md.py` consumes both, generates the entire ledger Markdown headed `GENERATED FROM CSV/TSV — DO NOT EDIT`; phase 2 regenerates and byte-compares.
- **T-12. Ragged-row detection** across all TSV/CSV files.
- **T-13. Self-describing audit.** Audit JSON: schema version; every producer and verifier hash; Python provenance record; typed top status.
- **T-14. Platform-pending note.** One sentence in ledger header and evidence doc: platform set under pending ADR-0004; all current evidence `go1.23.2 linux/amd64` scope; no platform rows this pass.
- **T-15 (N). Root README** listing every bundle file with a one-line purpose.
- **T-16 (N). Supersession chain, acyclic.** Freeze lists predecessor ZIP hashes (original bundle; R1 `a01a7be5160b10e83bce11ed2161e353a94ca9bd86ef2843aca9fe29e1da303e`), the frozen audit JSON hash, and the manifest's filename and coverage rule; the terminal ZIP hash lives only in the external sidecar. Names this the final bundle under the spec-closure family name.
- **T-17 (N). FMA margin note, verbatim, in the evidence doc's FMA section:** "The one-bit `x*y+z` vs `math.FMA` discrepancy doubles as a CPU-feature parlor trick: a pure-Go fingerprint of fused-multiply-add hardware paths. Recorded here for delight; not load-bearing."
- **T-18 (REQUIRED). Human-Review Index — discovery-based.** Generated at step 5 by `tools/generate_human_review_index.py` from **completed** sources; discovers every unresolved human act, never hardcoded: T rows from the canonical T-19 TSV; F and R rows from their existing frozen sources; every empty Rob countersign; every ADR with status PROPOSED, OPEN, PENDING, or REJECTED-AS-WRITTEN/OPEN; every open latitude decision; every pending pin or provenance confirmation; every row explicitly marked as requiring a human act. Minimum terminal contents: ADR-0001 (PROPOSED), ADR-0002 (REJECTED AS WRITTEN / OPEN), ADR-0003 (PROPOSED), ADR-0004 (pending), LAT-X004, all empty F-/R-/T- countersigns, toolchain provenance if pending. Every cited ADR exists in-bundle as a frozen read-only record or is named as an external authority with exact path and SHA-256. The audit compares the generated index against the discovered set, failing on omissions and stale rows. Carried into the FCB transformation.
- **T-19 (REQUIRED). Canonical T-disposition ledger.** `.review/FIDO_TERMINAL_CORRECTNESS_DISPOSITIONS_2026-07-23.tsv`, columns: `id`, `severity`, `model_record`, `artifact_locations`, `applied_change`, `rob_countersign`. Rows: **T-0 through T-19**; values: `model_record = APPLIED`, `rob_countersign` empty. **Sole T-disposition authority**; generated Markdown view permitted; the Human-Review Index discovers T rows from this TSV only.

---

## COMPLETION (exact status values)

Exactly one status, stated verbatim in the freeze record:

- **`TERMINAL-REPAIR-CANDIDATE`** — documentary completion. Requires: every T-item's deliverables (T-0 through T-19; N-items included); T-0's three artifacts complete with `baseline_delta_complete`, `fixed_point_manifest_complete`, and `fixed_points_preserved` green at change granularity; the seventeen-step build order (0–16) followed and stated in the freeze record, including post-ZIP extraction verification, the direct entry-multiset check, and the single-root check; producer inventory, replay comparisons, and index-versus-discovery green in the frozen audit JSON; **`distribution_members_match = PASS-CONFIRMED` and audit top status `PASS-CONFIRMED`**; ADR-0003 present verbatim and PROPOSED; **LAT-X004 the sole open Latitude Ledger disposition**; all PENDING-IMPLEMENTATION rows carry frozen future-Fido fixture specs with no claimed Fido observations; every terminal-verifier run exits successfully without rewriting any frozen artifact; T-19 records `APPLIED` per row with empty countersigns; nothing claims acceptance, closure, FIXED status, or a score.
- **`OPEN-REVIEW-CANDIDATE`** — valid deliverable in Pending mode: identical except provenance, with `distribution_members_match = PENDING-PROVENANCE`, `local_distribution_manifest_complete = PASS`, audit top status **`PASS-WITH-PENDING-PROVENANCE`**, no failed checks, exactly the declared pending-provenance items, every affected pin and observation `PROVENANCE-PENDING`, and the freeze record **stating explicitly that completion is blocked and why**.

Deliver `FIDO_GO1_23_SPEC_CLOSURE_REVIEW_BUNDLE_TERMINAL_2026-07-23.zip` (single root `FIDO_GO1_23_SPEC_CLOSURE_REVIEW_BUNDLE_TERMINAL_2026-07-23/`, canonical constants: timestamp `1980-01-01 00:00:00`, dir mode `0755`, file mode `0644`, `ZIP_STORED`) plus its external `.zip.sha256` sidecar. Rob's countersigns — indexed by T-18 from T-19 and the frozen F/R sources, decided row by row, with his LAT-X004 policy choice at the FCB regeneration — end the correctness volleys.
