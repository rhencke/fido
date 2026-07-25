# FIDO — TERMINAL CORRECTNESS DIRECTIVE, v6 (SPEC-CLOSURE FAMILY, FINAL PASS — SELF-CONTAINED)

**Date:** 2026-07-23
**Issued by:** Rob (human authority). This file is the directive.
**Repair authorization token:** `SPEC-CLOSURE-terminal-repair-2` (unchanged)
**Version:** v6 — self-contained. **This document alone is sufficient to execute and audit the repair. Earlier directives are provenance only.**
**Supersedes (full hashes):**
- v5 `5a083bf157cd97644755517e7e7fa1a8f31c5bcd65fa9a4b5b4a39106d44d6c9`
- v4 `eab3b1ed4b856157f7c784a6a7bcd35f5abe454cd558fb631b1f6772095648ff`
- v3 `6a99418c02cba3063bc43e61a71c48197fe3a55889d5c18f0225d5b78dbc011b`
- v2 `d8b2a9c71355ed0163b00bfa6a3aa9ca6dd6646a1ca80d30dd0596a022d560a2`
- v1 `b30c03b8c16a09868763f891ec2fd92f3a03f2a0739c852b497a536b70502a34`

**Baseline:** `FIDO_GO1_23_SPEC_CLOSURE_REVIEW_BUNDLE_R1_2026-07-23.zip`, SHA-256 `a01a7be5160b10e83bce11ed2161e353a94ca9bd86ef2843aca9fe29e1da303e`.

**Provenance:** Authored by Claude (Fable 5, external adversarial reviewer). Co-review round 5 by ChatGPT (Sol 5.6): one BLOCKING finding (CR5-1, baseline-delta preservation), three REQUIRED (CR5-2 LAT-X004 ownership, CR5-3 distribution member proofs, CR5-4 canonical probe profile), one status correction — **all adopted**. Verified before adoption: v5's full hash (match); `SC-02-CONSTANTS-LITERALS` at §25.3 and `SC-05-EXPR-FACT-USE-EVAL` at §25.6 in the frozen plan (match); and that frozen ledger row SPEC-096 (Constant expressions) already cites SC-05 as its owner — the CR5-2 assignment is a restoration of existing ownership, not an invention. Round-over-round finding order remains strictly decreasing; per the co-reviewer, this is the last authority-and-preservation pass before the work begins.

---

## AUTHORITY LIMITS (binding, complete)

1. Documentary artifacts, pins, scripts, fixtures, and recorded observations only. Compiling and executing probe fixtures against the pinned toolchain **to record evidence** is in scope. Modifying the Fido repository — source, `.v` files, build system, gates — is not.
2. Nothing produced by this repair may claim FIXED, accepted, closed, countersigned, spec-closed-in-implementation, or any score. Models record `APPLIED` at most.
3. Every countersign cell is created empty and remains Rob's alone.
4. This directive does not accept C4, does not authorize C5, and does not alter the active C4 repair authority or `NEXT_STEPS.md` state.
5. Normative text may not contain unpinned claims. World-knowledge is not evidence; pinned artifacts, hashes, and captured observations are.
6. One authority per meaning, for code, documents, and directives alike. New directive versions supersede by name and full hash; two live directives may never coexist. A directive must be self-contained: importing binding content from a superseded version is a defect.
7. The repair may change only what a T-row authorizes (see T-0). External reviews, prior repair directives, and copied ADR records are read-only evidence: byte-identical unless one exact T-row expressly authorizes replacement.

## FIXED POINTS (complete; weakening any is a regression)

**(A) The twelve architectural fixed points** (adopted as "What Must Not Change" in the original strict review of the architecture plan; restated here in full because a self-contained directive may not omit them):
1. The §1 deletion and generalization standard — the five retention tests and the prohibition list.
2. The minimal `Machine` base (§2) and the rule that no Go feature defines a second run relation.
3. The one-owner-per-meaning table (§3).
4. The expression fact/use split (§5) — "the use builder does not inspect the raw child again."
5. The single type algebra (§6): `RuntimeType := SemanticType Empty_set`, alias non-identity, declaration-reference recursion.
6. The static-slot / dynamic-place distinction (§11).
7. Stack-only panic / defer / recover (§13) with the named lemmas `finishing_pushes_only_deferred_activations` and `above_finishing_iff_deferred_call`.
8. Resource-local origins with proof-connected provenance (§15).
9. Finite bad-prefix safety with liveness held separate (§17).
10. Rejection of vacuous library safety from an empty start set (§19).
11. The Do-Not-Do-Early list (§24), verbatim.
12. The candidate-only acceptance stance (§26) with Rob as sole disposition owner.

**(B) The twelve evidence-and-model fixed points** (from the R1 review and rounds 1–4):
1. Pinned spec SHA-256 `c47fb4b5b795b9732cbae0250dcb84f791df78bb98695b30fb3f7788d1c9b389`; pinned memory-model SHA-256 `366b995adeee8b57bd23547feea8252a7ee619baec91cb22cfb21b12208da2c6`.
2. Reproducible audit and latitude extraction (shipped scripts re-run to byte-identical frozen outputs).
3. Route A evaluation-order nondeterminism (plan §12.4; `SC-20-EVAL-ORDER-LATITUDE` at §25.21): `step` admits every spec-permitted unspecified order via ordinary Actions; the spec-specified lexical left-to-right ordering of calls, methods, and receives is a deterministic obligation with fixtures.
4. The FMA both-branches model (LAT-121, STEP-NONDET), pinned-target observation recorded as adequacy evidence, never spec truth.
5. Select-choice, map-iteration (SPEC-X006), and scheduler nondeterminism as STEP-NONDET; `print`/`println` output as ADEQUACY-DEMOTION (SPEC-X005).
6. BOUND-001..003: emitted `go 1.23` directive equals the ledger language version; module path from the single ModulePath authority; no `toolchain` directive; invocation `GOTOOLCHAIN=local`, `GOENV=off`, `GOWORK=off`, `go version` verified before build.
7. The §22.3 terminal observation tuple: (stdout bytes, stderr projection, exit status); `println` → stderr; fatal panic → exit 2 with first-line projection `panic: <value>`; runtime noise excluded explicitly, owned by BOUND-X009.
8. APPLIED-only provenance; empty countersign columns; the audit's split of machine-checkable versus judgment claims.
9. Synthesized-anchor flags; the grammar counting rule (174 definitions / 173 names, metagrammar included, `Expression` twice) in the artifact header.
10. NaN-map row (SPEC-124) and struct-tag rows (SPEC-026) with their fixtures.
11. **`SC-21-PROOF-COST-INTERNALS` at §25.22** — never overwrite, renumber, or weaken.
12. `uintptr` remains OUT pending ADR-0001.

---

## T-0 — BLOCKING — BASELINE DELTA AND PRESERVATION (CR5-1, adopted; executes before all else)

**Rule:** the terminal bundle is an **authorized transformation of the exact R1 baseline**, not merely a self-consistent new bundle. Internal consistency does not prove legitimacy of change.

**Prepended build steps:**
0. Verify the R1 ZIP SHA-256 (`a01a7be5…da303e`).
1. Extract it into a clean baseline tree.
2. Create a separate terminal working tree.
3. Apply only changes authorized by exactly one T-row of this directive.
4. Generate and audit the complete baseline-to-terminal delta.

**Canonical delta file:** `.review/FIDO_TERMINAL_BASELINE_DELTA_2026-07-23.tsv`, columns: `path`, `baseline_kind`, `baseline_sha256`, `terminal_kind`, `terminal_sha256`, `action`, `owner`, `rationale`. Allowed actions: `UNCHANGED`, `MODIFIED`, `ADDED`, `RENAMED`, `DELETED`. Every changed path names exactly one T-owner (e.g., T-1, T-2, T-11). Renames identify both paths. Added files name their creating T-row. Deleted files name the rule making deletion valid (e.g., the executor binary under T-2).

**New audit checks:**
- `baseline_delta_complete` — rejects: any unlisted change; any change without exactly one T-owner; any missing baseline file; any unlisted added file; any altered external review or prior directive.
- `fixed_points_preserved` — mechanical form: the fixed-point clauses above are enumerated with their plan/ledger anchors; for each anchor, the containing section is byte-identical to baseline in the delta, **or** its delta row's owner is expressly permitted to touch it — and no T-row in this directive grants permission to touch any fixed-point clause, so in this pass every fixed-point anchor must be `UNCHANGED` or its modification limited to additions the owning T-row states (e.g., T-6's mapping table insertion adjacent to, never inside, §25.22).

**Read-only evidence rule:** external reviews, prior repair directives, and copied ADR records remain byte-identical. **This v6 directive itself enters the terminal bundle as a frozen read-only authority**, listed in the phase-1 inventory under its exact SHA-256 (computed at delivery and recorded in the delta as ADDED, owner T-0).

---

## PART 0 — FREEZE PROTOCOL, EVIDENCE CHAIN, AND CANONICAL ARCHIVE (complete)

**Acyclicity rule.** The audit JSON hashes only audit **inputs**. It does not hash itself, the freeze record, the in-bundle SHA manifest, the final ZIP, or the sidecar. The freeze record is generated from the frozen audit JSON and lists: predecessor ZIP hashes, the frozen audit JSON hash, and the in-bundle manifest's **filename and coverage rule** — never the manifest's hash. The in-bundle SHA manifest hashes every bundle file except itself, including the audit JSON and the freeze record. The final ZIP's SHA-256 exists only in the external `.zip.sha256` sidecar.

**Producer inventory (complete).** Every tool that creates or determines frozen content is a named, hashed phase-2 input: `tools/audit_spec_closure_bundle.py`, `tools/verify_terminal_bundle.py`, `tools/extract_latitude.py`, `tools/render_ledger_md.py`, `tools/run_fixture.py`, the baseline-delta generator, the freeze-record generator, the SHA-manifest generator, the human-review-index generator, **`tools/build_deterministic_bundle.py`** (the ZIP builder — always a shipped project script), and the sidecar-writing command or script, recorded so the deliverable chain has no unnamed producer. The audit JSON also records the **Python implementation, version, and executable hash** used to run the evidence tools (producer provenance, not semantic authority) (CR5-4).

**Phase-2 replay duties.** The audit replays evidence rather than merely hashing it, writing only to a temporary comparison area, never rewriting frozen captures: re-run latitude extraction against the pinned documents and byte-compare; re-render the ledger Markdown from the canonical CSV/TSV and byte-compare; re-run **every** probe fixture in compare-only mode under the T-9 closed environment — each replay uses a fresh, empty `GOCACHE`, `GOMODCACHE`, `GOPATH`, and temporary directory, so replay is a fresh run through the pinned distribution, never cache reuse — comparing stdout, stderr, exit status, command record, and effective-environment record to the frozen captures.

**Distribution member proofs (CR5-3, adopted).** New phase-2 check `distribution_members_match`: for every pin whose stated origin is a Go distribution member, the audit extracts the named member from the **verified tarball**, byte-compares it to the bundled pin, compares executable mode and symlink target where relevant, and records the member path and result in the audit JSON. This includes at least: `doc/go_spec.html` (as `go/doc/go_spec.html` or the distribution's actual member path), `doc/go_mem.html`, `go/bin/go` (hash record), the pinned cmd/go source files, and the pinned modfile source. A pin sourced from a repository tag rather than the distribution names an exact external artifact and SHA-256 in its manifest row. **In pending mode (T-2), every pin whose official origin has not been proved carries `PROVENANCE-PENDING` — the pins themselves, not only the probe observations.** A pin's provenance is checked, never merely written.

**Inventory completeness rule.** The audit JSON contains the complete file set and SHA-256 of every phase-1 file. The terminal verifier rejects any addition, deletion, or byte change in that set. The only later in-bundle files permitted are the audit JSON, the generated freeze record, and the generated SHA manifest.

**Canonical archive form.** The ZIP is built only by `tools/build_deterministic_bundle.py`, enforcing: one fixed root directory; regular files and directories only; no symlinks; no absolute paths; no `.` or `..` path components; no duplicate entry names; normalized POSIX paths; sorted entries; fixed timestamps; fixed modes; no host-specific extra fields; **`ZIP_STORED`** (a pinned compression level does not guarantee equal bytes across compressor versions).

**Build order (T-0 steps 0–4, then):**
5. Run the phase-2 audit; write the frozen audit JSON.
6. Generate the freeze record from the audit JSON.
7. Generate the in-bundle SHA manifest.
8. Run the terminal verifier against the staged tree (writes nothing; exits nonzero on failure).
9. Build the ZIP in canonical form.
10. Extract the ZIP into a clean directory and run the terminal verifier there — the artifact Rob receives is what gets verified.
11. Inspect the ZIP's entries directly, apart from extraction: prove the archive entry multiset equals the canonical expected entry set; then compare extracted file bytes against the in-bundle manifest.
12. Write the external `.zip.sha256` sidecar with the recorded sidecar producer. Rob verifies the sidecar externally.

**Two-script split.** `tools/audit_spec_closure_bundle.py` (phase 2; writes the frozen audit JSON; owns all input-only checks: row totality; the T-1 classification trichotomy; ACCEPTANCE-ALIGNMENT justification uniqueness; the duplicate-representation histogram; line-ending uniformity; ragged-row detection; ID-prefix discipline; the single-open-latitude rule, open set exactly `{LAT-X004}`; the T-6 contract-definition checks; `baseline_delta_complete`; `fixed_points_preserved`; `distribution_members_match`; regeneration and replay comparisons; the T-18 index-versus-discovery comparison). `tools/verify_terminal_bundle.py` (phases 8 and 10–11; writes nothing; exits nonzero on failure; owns `freeze_claims_match`, manifest coverage and hash verification, inventory-drift rejection, archive entry-multiset and extracted-byte checks).

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
1. Add disposition kind **`ACCEPTANCE-ALIGNMENT`** to the Latitude Ledger. Row fields: the pinned-toolchain acceptance observation (captured per T-9), the Fido elaboration obligation, the named contract, and an **individual** justification. Audit: no two ACCEPTANCE-ALIGNMENT justification strings identical.
2. **Classification trichotomy**, audit-enforced over every implementation-restriction candidate: `ACCEPTANCE-ALIGNMENT` (in-scope accepted-language restriction); `OUT-COVERED` (feature priced out — LAT-180 and LAT-181 both land here); `NOT-LATITUDE` (exposition or deterministic prohibition only — LAT-118 as a wrap-guaranteeing prohibition owned by SC-05; LAT-214 as exposition; both with accurate individual justifications).
3. Re-disposition individually: LAT-019, LAT-049, LAT-077, LAT-085, LAT-134, LAT-148, LAT-171, LAT-177, LAT-180, LAT-181, LAT-118, LAT-214, and any other implementation-restriction candidate.
4. New contract **`SC-22-ACCEPTANCE-ALIGNMENT` at §25.23** (§25.22 = `SC-21-PROOF-COST-INTERNALS`, untouched). States `fido_accepts_subset_pinned_gc` as a standing obligation **frozen here and discharged at the checkpoints that implement its restriction cases**. Three claims separated: **Formal** — `CompilableProgram` satisfies every accepted ledger restriction (future theorem, per checkpoint); **External** — a publishable `DirectoryImage` passes the pinned-gc preflight (enforced at publication); **Evidence** — pinned-gc probes record the selected acceptance profile (this pass). A finite probe set does not prove the global theorem.
5. **Evidence now / gates later.** Per ACCEPTANCE-ALIGNMENT row, this pass **runs** the pinned-gc fixture (raw stdout, stderr, status per T-9), **freezes** the future Fido half — exact fixture source, expected diagnostic ID, expected diagnostic text-or-shape, owner, implementing checkpoint — marked **`PENDING-IMPLEMENTATION`**, and **never claims** a Fido-produced diagnostic. First frozen instances: unused local variables; constant acceptance bounds (probe pinned gc's limits); duplicate constant switch cases.
6. **Constant VALUE semantics — LAT-X004, ownership frozen (CR5-2, adopted).** Spec-permitted rounding during untyped constant folding can change an *accepted* constant's value; acceptance rows cannot own that. Create **LAT-X004** with ownership fixed **now** — Rob's open decision concerns which constant-value **policy** Fido adopts, never which layer owns constant meaning: **owning closure row SPEC-096 (Constant expressions); semantic owner: `ExprFact`, the constant expression's intrinsic exact value; contract: `SC-05-EXPR-FACT-USE-EVAL` at §25.6** (verified: SPEC-096 already cites SC-05 in the frozen ledger — this is restoration, not invention). `SC-22-ACCEPTANCE-ALIGNMENT` owns only whether a source program enters `CompilableProgram`; `SC-02-CONSTANTS-LITERALS` (§25.3) owns literal/constant representation primitives and may support the proof but does not own folding results. Latitude-ledger columns on every row: `decision_status`, `rob_choice`, `rob_countersign`; all rows `DISPOSITIONED` except `LAT-X004: HUMAN-CHOICE-OPEN` with empty choice and countersign; audit: open set equals exactly `{LAT-X004}`. Menu for Rob, inside the fixed owner: (i) admit all specification-permitted rounded values; (ii) prove accepted constants invariant under the permitted rounding latitude — including the domain-restriction variant tying to the constant acceptance bounds so exact and pinned-gc values provably coincide; (iii) implement the exact pinned-gc constant profile as an explicit Rob-approved refinement. **Advisory recommendation, labeled (both reviewers, independently): option (ii), domain-restriction variant.** Process: the terminal bundle ships with LAT-X004 open; Rob's selection — informed by this pass's constant-bound probes — triggers regeneration, re-audit, and re-freeze as the first step of the FCB transformation. The freeze record states the open decision explicitly.

### T-2 — REQUIRED — Pinned **distribution** execution, with exact confirmed/pending modes

Delete the 13.8 MB in-bundle executor (`.review/pins/go1.23.2-linux-amd64`). A binary cannot self-attest. `go` delegates to `pkg/tool/linux_amd64/compile` and `link` and consumes the standard library under `GOROOT`; hashing only `bin/go` does not pin the compiler that judges the fixture.

**Confirmed mode** (required for `TERMINAL-REPAIR-CANDIDATE` status): official `go1.23.2.linux-amd64.tar.gz` **bytes** present; official SHA-256 confirmed; tarball hash matches. The runner verifies the tarball hash, extracts into the fixed evidence sandbox, sets `GOROOT` to that root, invokes that root's `go/bin/go`; the member `go/bin/go` hash is a secondary check. A pre-existing `GOROOT` is accepted only if its complete file manifest (regular files, symlink targets, executable modes) is proved equal to one derived from the verified tarball.

**Pending mode** (tarball bytes unavailable): copy the local Go distribution into the fixed sandbox; create a complete manifest of regular files, symlink targets, and executable modes; hash that manifest; run only from that copied sandbox; mark **every** observation and **every unproved pin** `PROVENANCE-PENDING`; record the local-tree manifest in evidence and audit JSON; **forbid any completion claim**. An official hash without the bytes populates the expected pin value but cannot convert pending evidence into confirmed evidence.

Pending toolchain provenance is listed in the Human-Review Index and blocks completion. `PINS_MANIFEST.tsv` gains a row for the distribution tarball (origin, version, SHA-256 or PENDING). The evidence doc keeps the provenance chain.

### T-3 — REQUIRED — Racy-run scope: option (b)

`step : State -> Label -> State -> Prop` receives no trace; havoc-after-race would require race history in `State`, a taint field, an operational detector beside the trace-based definition, or a second run rule — each adds state or a second authority. Therefore: LAT-217, LAT-218, LAT-219, LAT-224 remain STEP-NONDET; `DataRace` remains a derived finite BadPrefix; §27 gains, in substance verbatim: *sub-value and machine-word access granularity is deliberate proof cost that affects condemned runs, not reachable safe-run behavior; it may be narrowed only by a future countersigned ledger disposition*; the four rows cite only the owning channel/race contract; copied `SC-20-EVAL-ORDER-LATITUDE` tails removed.

### T-4 — REQUIRED — Template drift measurable

`template: lexical-only` on the 48 OP- and 25 KEY- rows (and other justified shared-text rows); duplicate-representation histogram (top N with counts) in the frozen JSON; the old-template regex check stays.

---

## PART B — SHOWROOM ITEMS (complete; N = non-substantive, still required)

- **T-5. Line endings.** Every tabular artifact LF; audit checks; the closure CSV is currently CRLF and must be normalized.
- **T-6. Contract definitions audited, not token text.** Plan gains the full mapping table SC-00 = §25.1 … SC-20 = §25.21, SC-21 = §25.22 (PROOF-COST-INTERNALS, pre-existing), SC-22 = §25.23 (new). The audit parses actual `### 25.N \`SC-XX-…\`` headings and proves: exactly one §25 definition per SC identifier; exactly one SC identifier per contract heading; the mapping table is a byte-for-byte projection of the headings; contiguity SC-00 through SC-22; every ledger citation names one defined heading; no defined contract uncited without an explicit stated reason. Citation *relevance* is fixed by hand this pass.
- **T-7. ID discipline documented.** `LAT-###` stable manifest ordinals, never renumbered; hand-added `LAT-X###` (next: LAT-X004). `BOUND-###` live boundary rows; `BOUND-X###` priced exclusions. Audit checks prefixes.
- **T-8. Freeze claims emitted, not typed.** Every freeze count is read from the audit JSON; `freeze_claims_match` runs in the terminal verifier.
- **T-9. Exact closed probe environment, one canonical profile artifact (CR5-4, adopted).** One runner, `tools/run_fixture.py`, executing per T-2 (verified sandbox distribution only), starting from an **empty environment** and applying exactly the profile in **`.review/tools/PROBE_ENVIRONMENT.tsv`** — the runner reads that file and never repeats values internally. The profile pins exact values for at least: `GOAMD64` (**`v1`** for the current generic amd64 target; any other value is an explicit target decision, not an implementation detail), `LANG`, `LC_ALL`, `TZ`, `GOTRACEBACK`, `PATH`, `GOOS=linux`, `GOARCH=amd64`, `CGO_ENABLED=0`, `GOFLAGS=""`, `GOPROXY=off`, `GOTOOLCHAIN=local`, `GOENV=off`, `GOWORK=off`, `GODEBUG` (empty), plus `GOROOT` (verified sandbox root), `HOME`, `TMPDIR`, `GOCACHE`, `GOMODCACHE`, `GOPATH` (all sandbox; caches fresh and empty per replay). The profile also states: the process umask; the fixed sandbox root; the path-normalization rule for path-bearing output. The runner records the exact command and effective `go env` per run; raw stdout, stderr, and exit status retained beside each fixture. Flagged as a proposed BOUND-003 strengthening for the implementing checkpoint — no repo change now.
- **T-10. Pins manifest.** `.review/pins/PINS_MANIFEST.tsv`: filename, upstream origin (distribution member path, or repo path at tag as an exact external artifact with SHA-256), version, SHA-256 (or PENDING per T-2). One filename convention; the freeze references the manifest.
- **T-11. One canonical source per table.** Closure CSV and Latitude TSV canonical; `tools/render_ledger_md.py` consumes both and generates the entire ledger Markdown, headed `GENERATED FROM CSV/TSV — DO NOT EDIT`; phase 2 regenerates and byte-compares.
- **T-12. Ragged-row detection** across all TSV/CSV files.
- **T-13. Self-describing audit.** Audit JSON: schema version; its own script's SHA-256; SHA-256 of every producer and verifier tool in Part 0's inventory; the Python provenance record (implementation, version, executable hash).
- **T-14. Platform-pending note.** One sentence in the ledger header and evidence doc: platform set under pending ADR-0004; all current evidence `go1.23.2 linux/amd64` scope; no platform rows this pass.
- **T-15 (N). Root README** listing every bundle file with a one-line purpose.
- **T-16 (N). Supersession chain, acyclic.** Freeze lists predecessor ZIP hashes (original bundle; R1 `a01a7be5…da303e`), the frozen audit JSON hash, and the manifest's filename and coverage rule — never its own ZIP's hash (external sidecar only). Names this the final bundle under the spec-closure family name.
- **T-17 (N). FMA margin note, verbatim, in the evidence doc's FMA section:** "The one-bit `x*y+z` vs `math.FMA` discrepancy doubles as a CPU-feature parlor trick: a pure-Go fingerprint of fused-multiply-add hardware paths. Recorded here for delight; not load-bearing."
- **T-18 (REQUIRED). Human-Review Index — discovery-based.** A generated file (named generator in the producer inventory) listing every unresolved human act, **discovered** from canonical sources, never hardcoded: every F, R, and T disposition row; every empty Rob countersign field; every ADR whose status is PROPOSED, OPEN, PENDING, or REJECTED-AS-WRITTEN/OPEN; every open latitude decision; every pending pin or provenance confirmation; every row explicitly marked as requiring a human act. Minimum terminal contents: **ADR-0001 (PROPOSED), ADR-0002 (REJECTED AS WRITTEN / OPEN), ADR-0003 (PROPOSED), ADR-0004 (pending), LAT-X004, all empty F-/R-/T- countersigns, toolchain provenance if pending.** Every ADR cited by the plan or ledger must exist in-bundle as a frozen read-only decision record or be named as an external authority with exact path and SHA-256. Each entry points to its frozen source row and reports its countersign state. The audit compares the generated index against the discovered open-act set and fails on omissions and stale extra rows. Carried into the FCB transformation.

---

## COMPLETION (with exact status values; CR5 status correction adopted)

Exactly one of two statuses is claimed, stated verbatim in the freeze record:

- **`TERMINAL-REPAIR-CANDIDATE`** — documentary completion. Requires all of: every T-item's deliverables exist (T-0 through T-18; N-items included); T-0's baseline delta is complete, every change owned by exactly one T-row, `baseline_delta_complete` and `fixed_points_preserved` green; the twelve-step build order was followed and is stated in the freeze record, including post-ZIP extraction verification and the direct archive entry-multiset check; the producer inventory, replay comparisons, `distribution_members_match`, and index-versus-discovery comparison are green in the frozen audit JSON; ADR-0003 with its interpretation clause present verbatim and PROPOSED; **LAT-X004 is the sole open Latitude Ledger disposition** (other open human acts are enumerated by the Human-Review Index, never denied); all PENDING-IMPLEMENTATION rows carry frozen future-Fido fixture specs with no claimed Fido observations; **toolchain provenance in Confirmed mode**; every phase-2 audit check green; every terminal-verifier run exits successfully without rewriting any frozen artifact; the repair ledger records `APPLIED` per T-row with empty countersign cells; nothing anywhere claims acceptance, closure, FIXED status, or a score.
- **`OPEN-REVIEW-CANDIDATE`** — a valid deliverable when toolchain provenance is Pending: identical requirements except provenance, with every affected pin and observation marked `PROVENANCE-PENDING`, and the freeze record **stating explicitly that completion is blocked** and why.

Deliver `FIDO_GO1_23_SPEC_CLOSURE_REVIEW_BUNDLE_TERMINAL_2026-07-23.zip` in canonical archive form plus its external `.zip.sha256` sidecar. Rob's countersigns — indexed by T-18, decided row by row, with his LAT-X004 policy choice at the FCB regeneration — end the correctness volleys.
