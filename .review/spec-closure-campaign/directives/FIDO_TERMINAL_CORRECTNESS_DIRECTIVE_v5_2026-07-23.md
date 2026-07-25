# FIDO — TERMINAL CORRECTNESS DIRECTIVE, v5 (SPEC-CLOSURE FAMILY, FINAL PASS — SELF-CONTAINED)

**Date:** 2026-07-23
**Issued by:** Rob (human authority). This file is the directive.
**Repair authorization token:** `SPEC-CLOSURE-terminal-repair-2` (unchanged)
**Version:** v5 — self-contained consolidation. **This document alone is sufficient to execute and audit the repair. Earlier directives are provenance only.**
**Supersedes (full hashes):**
- v4 `eab3b1ed4b856157f7c784a6a7bcd35f5abe454cd558fb631b1f6772095648ff`
- v3 `6a99418c02cba3063bc43e61a71c48197fe3a55889d5c18f0225d5b78dbc011b`
- v2 `d8b2a9c71355ed0163b00bfa6a3aa9ca6dd6646a1ca80d30dd0596a022d560a2`
- v1 `b30c03b8c16a09868763f891ec2fd92f3a03f2a0739c852b497a536b70502a34`

**Baseline:** `FIDO_GO1_23_SPEC_CLOSURE_REVIEW_BUNDLE_R1_2026-07-23.zip`, SHA-256 `a01a7be5160b10e83bce11ed2161e353a94ca9bd86ef2843aca9fe29e1da303e` (co-reviewer's reported baseline hash independently re-computed and confirmed).

**Provenance:** Authored by Claude (Fable 5, external adversarial reviewer). Co-review round 4 by ChatGPT (Sol 5.6): four findings (CR4-1..CR4-4), **all adopted**. CR4-1 (BLOCKING) found that v4 imported binding content from superseded v3 via "unchanged from v3" — the directive enforcing one-authority-per-meaning had made a superseded document a hidden second authority for its own commands; that defect is the author's. Before adoption, the following co-reviewer claims were independently verified: v4's hash (match), the R1 baseline ZIP hash (match), and the existence of ADR-0002 in the repository family (`ADR-0002-BOUNDED-…`, status REJECTED AS WRITTEN / OPEN — confirmed by grep of the frozen `.review` tree). Round-over-round finding order remains strictly decreasing (architecture → process → mechanics → document normal form); per the co-reviewer, no semantic change waits behind these edits.

---

## AUTHORITY LIMITS (binding, complete)

1. Documentary artifacts, pins, scripts, fixtures, and recorded observations only. Compiling and executing probe fixtures against the pinned toolchain **to record evidence** is in scope. Modifying the Fido repository — source, `.v` files, build system, gates — is not.
2. Nothing produced by this repair may claim FIXED, accepted, closed, countersigned, spec-closed-in-implementation, or any score. Models record `APPLIED` at most.
3. Every countersign cell is created empty and remains Rob's alone.
4. This directive does not accept C4, does not authorize C5, and does not alter the active C4 repair authority or `NEXT_STEPS.md` state.
5. Normative text may not contain unpinned claims. World-knowledge is not evidence; pinned artifacts, hashes, and captured observations are.
6. One authority per meaning, for code, documents, and directives alike. New directive versions supersede by name and full hash; two live directives may never coexist. A directive must be self-contained: importing binding content from a superseded version is a defect (this rule is the codified lesson of CR4-1).

## FIXED POINTS (complete; weakening any is a regression)

From the independent R1 review's verified list and subsequent rounds:
1. Pinned spec SHA-256 `c47fb4b5b795b9732cbae0250dcb84f791df78bb98695b30fb3f7788d1c9b389` and pinned memory-model SHA-256 `366b995adeee8b57bd23547feea8252a7ee619baec91cb22cfb21b12208da2c6` (both verified byte-exact against the go1.23.2 distribution's `doc/` files).
2. Reproducible audit and latitude extraction (shipped scripts re-run to byte-identical frozen outputs).
3. Route A evaluation-order nondeterminism: `step` admits every spec-permitted unspecified order via ordinary Actions, no synthetic choice label; spec-specified lexical left-to-right ordering of calls, methods, and receives is a deterministic obligation with fixtures (plan §12.4, contract `SC-20-EVAL-ORDER-LATITUDE` at §25.21).
4. The FMA both-branches model (LAT-121, STEP-NONDET) with its pinned-target observation recorded as adequacy evidence, never spec truth.
5. Select-choice, map-iteration (SPEC-X006), and scheduler nondeterminism as STEP-NONDET; `print`/`println` output as ADEQUACY-DEMOTION (SPEC-X005).
6. BOUND-001..003: emitted `go 1.23` directive equals the ledger language version; module path from the single ModulePath authority; no `toolchain` directive; invocation contract `GOTOOLCHAIN=local`, `GOENV=off`, `GOWORK=off` with `go version` verified before build.
7. The §22.3 terminal observation tuple: (stdout bytes, stderr projection, exit status); `println` → stderr; fatal panic → exit 2 with first-line projection `panic: <value>`; runtime noise excluded explicitly and owned by BOUND-X009.
8. APPLIED-only provenance; empty countersign columns; the audit's split of machine-checkable versus judgment claims.
9. Synthesized-anchor flags on the three constructed heading anchors; the grammar counting rule (174 definitions / 173 names, metagrammar included, `Expression` twice) in the artifact header.
10. NaN-map row (SPEC-124: insertable, len-counted, unretrievable, undeletable, cleared by `clear`) and struct-tag rows (SPEC-026: identity includes tags; conversion ignores tags per the pinned rule) with their fixtures.
11. **`SC-21-PROOF-COST-INTERNALS` at §25.22** — the asymmetric vow (public base fixed, internals disposable). Never overwrite, renumber, or weaken it.
12. `uintptr` remains OUT pending ADR-0001.

---

## PART 0 — FREEZE PROTOCOL, EVIDENCE CHAIN, AND CANONICAL ARCHIVE (complete)

**Acyclicity rule.** The audit JSON hashes only audit **inputs**. It does not hash itself, the freeze record, the in-bundle SHA manifest, the final ZIP, or the sidecar. The freeze record is generated from the frozen audit JSON and lists: predecessor ZIP hashes, the frozen audit JSON hash, and the in-bundle manifest's **filename and coverage rule** — never the manifest's hash. The in-bundle SHA manifest hashes every bundle file except itself, including the audit JSON and the freeze record. The final ZIP's SHA-256 exists only in the external `.zip.sha256` sidecar.

**Producer inventory (complete; CR3-2 + CR4-4).** Every tool that creates or determines frozen content is a named, hashed phase-2 input: `tools/audit_spec_closure_bundle.py`, `tools/verify_terminal_bundle.py`, `tools/extract_latitude.py`, `tools/render_ledger_md.py`, `tools/run_fixture.py`, the freeze-record generator, the SHA-manifest generator, the human-review-index generator, **`tools/build_deterministic_bundle.py` (the ZIP builder — always a shipped project script; no external or unpinned packer may build the bundle)**, and the sidecar-writing command or script, which is recorded so the deliverable chain has no unnamed producer.

**Phase-2 replay duties.** The audit replays evidence rather than merely hashing it, writing only to a temporary comparison area and never rewriting frozen captures: re-run latitude extraction against the pinned documents and byte-compare to the frozen manifest; re-render the ledger Markdown from the canonical CSV/TSV and byte-compare; re-run **every** probe fixture in compare-only mode under the T-9 closed environment — **each replay uses a fresh, empty `GOCACHE`, `GOMODCACHE`, `GOPATH`, and temporary directory, so replay is a fresh run through the pinned distribution, never cache reuse (CR4-3)** — comparing stdout, stderr, exit status, command record, and effective-environment record to the frozen captures.

**Inventory completeness rule.** The audit JSON contains the complete file set and SHA-256 of every phase-1 file. The terminal verifier rejects any addition, deletion, or byte change in that set. The only later in-bundle files permitted are the audit JSON, the generated freeze record, and the generated SHA manifest.

**Canonical archive form (CR4-4, adopted).** The ZIP is built only by `tools/build_deterministic_bundle.py`, enforcing: one fixed root directory; regular files and directories only; no symlinks; no absolute paths; no `.` or `..` path components; no duplicate entry names; normalized POSIX paths; sorted entries; fixed timestamps; fixed modes; no host-specific extra fields; one fixed compression rule — **`ZIP_STORED`** for cross-environment byte reproducibility (a pinned compression level does not guarantee equal compressed bytes across compressor versions).

**Build order (nine steps):**
1. Produce canonical inputs (ledgers, generated Markdown, evidence, fixtures with captured outputs, human-review index).
2. Run the phase-2 audit; write the frozen audit JSON.
3. Generate the freeze record from the audit JSON.
4. Generate the in-bundle SHA manifest.
5. Run the terminal verifier against the staged tree (writes nothing; exits nonzero on failure).
6. Build the ZIP with `tools/build_deterministic_bundle.py` in canonical form.
7. Extract the ZIP into a clean directory and run the terminal verifier there — the artifact Rob receives is what gets verified.
8. **Inspect the ZIP's entries directly, apart from extraction: prove the archive entry multiset equals the canonical expected entry set (catching duplicates, path tricks, symlinks, and normalization collisions that extraction can mask); then** compare extracted file bytes against the in-bundle manifest.
9. Write the external `.zip.sha256` sidecar with the recorded sidecar producer. Rob verifies the sidecar externally.

**Two-script split.** `tools/audit_spec_closure_bundle.py` (phase 2; writes the frozen audit JSON; owns all input-only checks: row totality; the T-1 classification trichotomy; ACCEPTANCE-ALIGNMENT justification uniqueness; the duplicate-representation histogram; line-ending uniformity; ragged-row detection; ID-prefix discipline; the single-open-latitude rule, open set exactly `{LAT-X004}`; the T-6 contract-definition checks; regeneration and replay comparisons; the T-18 index-versus-discovery comparison). `tools/verify_terminal_bundle.py` (phases 5 and 7–8; writes nothing; exits nonzero on failure; owns `freeze_claims_match`, manifest coverage and hash verification, inventory-drift rejection, archive entry-multiset and extracted-byte checks).

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
1. Add disposition kind **`ACCEPTANCE-ALIGNMENT`** to the Latitude Ledger. Row fields: the pinned-toolchain acceptance observation (captured per T-9), the Fido elaboration obligation, the named contract, and an **individual** justification. Audit check: no two ACCEPTANCE-ALIGNMENT justification strings are identical.
2. **Classification trichotomy**, audit-enforced over every implementation-restriction candidate — each falls into exactly one case: `ACCEPTANCE-ALIGNMENT` (an in-scope accepted-language restriction); `OUT-COVERED` (the whole feature is already priced out — LAT-180 and LAT-181 both land here, resolving their inconsistency); `NOT-LATITUDE` (exposition or a deterministic prohibition only — LAT-118 is a prohibition guaranteeing deterministic wrap, owned by SC-05; LAT-214 is exposition; both receive accurate individual justifications).
3. Re-disposition individually under the trichotomy: LAT-019, LAT-049, LAT-077, LAT-085, LAT-134, LAT-148, LAT-171, LAT-177, LAT-180, LAT-181, LAT-118, LAT-214, and any other implementation-restriction candidate.
4. New contract **`SC-22-ACCEPTANCE-ALIGNMENT` at §25.23** (§25.22 is the pre-existing `SC-21-PROOF-COST-INTERNALS` and is untouched). The contract states `fido_accepts_subset_pinned_gc` as a standing obligation **frozen here and discharged at the checkpoints that implement its restriction cases** — not in this documentary pass. The plan separates three claims: **Formal** — `CompilableProgram` satisfies every accepted ledger restriction (future theorem, per checkpoint); **External** — a publishable `DirectoryImage` passes the pinned-gc preflight (enforced at publication); **Evidence** — pinned-gc probes record the selected acceptance profile (this pass). A finite probe set does not prove the global theorem.
5. **Evidence now / gates later.** For each ACCEPTANCE-ALIGNMENT row, this pass: **runs** the pinned-gc fixture and captures raw stdout, stderr, and exit status per T-9; **freezes** the future Fido half — exact fixture source, expected diagnostic ID, expected diagnostic text-or-shape, owner, and implementing checkpoint — marked **`PENDING-IMPLEMENTATION`**; and **never claims** a Fido-produced diagnostic. First frozen instances: unused local variables; constant acceptance bounds (probe pinned gc's limits); duplicate constant switch cases.
6. **Constant VALUE semantics — LAT-X004.** Spec-permitted rounding during untyped constant folding can change an *accepted* constant's value (array lengths, comparisons, emitted output); acceptance rows cannot own that. Create **LAT-X004** with one owner and one contract. Add latitude-ledger columns to every row: `decision_status`, `rob_choice`, `rob_countersign`. All rows carry `decision_status = DISPOSITIONED` except `LAT-X004: decision_status = HUMAN-CHOICE-OPEN` with `rob_choice` and `rob_countersign` empty. Audit: the open set equals exactly `{LAT-X004}`. Menu for Rob: (i) admit all specification-permitted rounded values; (ii) prove accepted constants invariant under the permitted rounding latitude — including the domain-restriction variant, tying to the constant acceptance bounds so exact and pinned-gc values provably coincide; (iii) implement the exact pinned-gc constant profile as an explicit Rob-approved refinement. **Advisory recommendation, labeled as such (both reviewers, independently): option (ii), domain-restriction variant.** Process: the terminal bundle ships with LAT-X004 open; Rob's selection — informed by this pass's constant-bound probes — triggers regeneration, re-audit, and re-freeze **as the first step of the FCB transformation**. A countersign alone cannot settle an open row under an old SHA. The freeze record states the open decision explicitly.

### T-2 — REQUIRED — Pinned **distribution** execution, with exact confirmed/pending modes (CR3-1 + CR4-3)

Delete the 13.8 MB in-bundle executor (`.review/pins/go1.23.2-linux-amd64`). A binary cannot self-attest. Probe evidence derives its validity from the distribution, not the front-end binary: `go` delegates to `pkg/tool/linux_amd64/compile` and `link` and consumes the standard library under `GOROOT`, so hashing only `bin/go` does not pin the compiler that judges the fixture.

**Confirmed mode** (required for completion): the official `go1.23.2.linux-amd64.tar.gz` **bytes** are present; the official SHA-256 is confirmed; the tarball's hash matches. The runner verifies the tarball hash, extracts it into the fixed evidence sandbox, sets `GOROOT` to that extracted root, and invokes that root's `go/bin/go`; the member `go/bin/go` hash is a secondary check. A pre-existing `GOROOT` is accepted only if its complete file manifest (regular files, symlink targets, executable modes) is proved equal to one derived from the verified tarball.

**Pending mode** (when official tarball bytes are unavailable): copy the local Go distribution into the fixed sandbox; create a complete manifest of its regular files, symlink targets, and executable modes; hash that manifest; run only from that copied sandbox; mark **every** resulting observation `PROVENANCE-PENDING`; record the local-tree manifest in the evidence and the audit JSON; **forbid any completion claim**. An official hash supplied without the tarball bytes can populate the expected pin value but cannot convert pending evidence into confirmed evidence: confirmation requires the actual bytes, or a complete local tree proved equal to a manifest derived from those verified bytes.

Pending toolchain provenance is listed in the Human-Review Index (T-18) and blocks completion; the bundle then ships explicitly as an open review candidate. `PINS_MANIFEST.tsv` gains a row for the distribution tarball (origin, version, SHA-256 or PENDING). The evidence doc keeps the provenance chain (official tarball hash, member path, local hashes).

### T-3 — REQUIRED — Racy-run modeling scope: option (b) selected

Option (a) (havoc at-and-after the first race) is rejected: `step : State -> Label -> State -> Prop` receives no trace, so (a) requires race history in `State`, a taint field, an operational detector beside the trace-based definition, or a second run rule — each adds state or a second authority, violating the no-trace-in-state law. Therefore: LAT-217, LAT-218, LAT-219, LAT-224 **remain STEP-NONDET**, modeling the memory-model latitude directly; `DataRace` remains a derived finite BadPrefix; §27 gains the reserve, in substance verbatim: *sub-value and machine-word access granularity is deliberate proof cost that affects condemned runs, not reachable safe-run behavior; it may be narrowed only by a future countersigned ledger disposition*; the four rows' contract citations name only the owning channel/race contract, and the copied `SC-20-EVAL-ORDER-LATITUDE` tails are removed.

### T-4 — REQUIRED — Make template drift measurable

Populate `template: lexical-only` on the 48 OP- and 25 KEY- rows (and any other justified shared-text rows). The audit emits a duplicate-representation histogram (top N with counts) into the frozen JSON. The old-template regex check stays.

---

## PART B — SHOWROOM ITEMS (complete; N = non-substantive, still required)

- **T-5. Line endings.** Every tabular artifact (CSV and TSV) is LF; the audit checks uniformity. The closure CSV is currently CRLF and must be normalized.
- **T-6. Contract definitions audited, not token text.** The plan gains the full mapping table SC-00 = §25.1 … SC-20 = §25.21, SC-21 = §25.22 (PROOF-COST-INTERNALS, pre-existing), SC-22 = §25.23 (ACCEPTANCE-ALIGNMENT, new). The audit parses the actual `### 25.N \`SC-XX-…\`` headings and proves: each SC identifier has exactly one §25 definition; each §25 contract heading has exactly one SC identifier; the mapping table is a byte-for-byte projection of those headings; identifiers are contiguous SC-00 through SC-22; every ledger citation names one defined heading; no defined contract remains uncited without an explicit stated reason. Citation *relevance* is fixed by hand this pass (remove the copy-paste SC-20 tails on LAT-176, LAT-188, LAT-217, LAT-224 and any others); the audit checks structure, not relevance.
- **T-7. ID discipline documented.** Latitude header: `LAT-###` are stable manifest ordinals, never renumbered; hand-added rows use `LAT-X###` (next: LAT-X004). Closure header: `BOUND-###` are live boundary rows; `BOUND-X###` are priced exclusions. The audit checks prefix discipline.
- **T-8. Freeze claims emitted, not typed.** Every count in the freeze record is read from the audit JSON; `freeze_claims_match` runs in the phase-5 verifier.
- **T-9. Exact closed probe environment.** One runner, `tools/run_fixture.py`, executing per T-2 (verified sandbox distribution only), starting from an **empty environment** and setting exactly one closed list: `GOROOT` (the verified sandbox root), `PATH` (fixed, minimal), `HOME` (sandbox), `TMPDIR` (sandbox), `GOCACHE` (sandbox; fresh and empty per fixture replay), `GOMODCACHE` (sandbox; fresh per replay), `GOPATH` (sandbox; fresh per replay), `LANG`/`LC_ALL` (fixed), `TZ` (fixed), `GODEBUG` (empty), `GOTRACEBACK` (fixed), `GOOS=linux`, `GOARCH=amd64`, `GOAMD64` (explicit, recorded), `CGO_ENABLED=0`, `GOFLAGS=""`, `GOPROXY=off`, `GOTOOLCHAIN=local`, `GOENV=off`, `GOWORK=off`. All path-bearing output uses one fixed sandbox root or a stated normalization rule. The runner records the exact command and the effective `go env` per run; raw stdout, stderr, and exit status are retained as files beside each fixture. Flagged as a proposed BOUND-003 strengthening for the checkpoint that implements it — no repo change now.
- **T-10. Pins manifest.** `.review/pins/PINS_MANIFEST.tsv`: one row per pin — filename, upstream origin (repo path at tag, or distribution + member path), version, SHA-256 (or PENDING per T-2). One filename convention `<artifact>_<version>.<ext>`; rename pins to match; the freeze references the manifest rather than repeating it.
- **T-11. One canonical source per table.** The closure CSV **and** the Latitude Ledger TSV are canonical; `tools/render_ledger_md.py` consumes **both** and generates the entire ledger Markdown — closure and latitude sections — headed `GENERATED FROM CSV/TSV — DO NOT EDIT`; no hand-written section remains; phase 2 regenerates and byte-compares.
- **T-12. Ragged-row detection** across all TSV/CSV files.
- **T-13. Self-describing audit.** The audit JSON records: a schema version; its own script's SHA-256; and the SHA-256 of **every producer and verifier tool** named in Part 0's inventory, as inputs.
- **T-14. Platform-pending note.** One sentence in the closure ledger header and the evidence doc: the platform target set is under pending ADR-0004 (multi-platform 64-bit); all current toolchain evidence is `go1.23.2 linux/amd64` scope; no platform rows in this pass.
- **T-15 (N). Root README** listing every bundle file with a one-line purpose (precursor of the FCB index).
- **T-16 (N). Supersession chain, acyclic.** The freeze record lists predecessor ZIP hashes (original bundle; R1 = `a01a7be5160b10e83bce11ed2161e353a94ca9bd86ef2843aca9fe29e1da303e`), the frozen audit JSON hash, and the in-bundle manifest's filename and coverage rule — never its own ZIP's hash, which lives only in the external sidecar. Names this the final bundle under the spec-closure family name.
- **T-17 (N). FMA margin note, verbatim, in the evidence doc's FMA section:** "The one-bit `x*y+z` vs `math.FMA` discrepancy doubles as a CPU-feature parlor trick: a pure-Go fingerprint of fused-multiply-add hardware paths. Recorded here for delight; not load-bearing."
- **T-18 (REQUIRED). Human-Review Index — discovery-based (CR4-2, adopted).** A **generated** file, produced by a named generator in the producer inventory, listing every unresolved human act across the document family. The generator **discovers** its domain from canonical sources — it does not hardcode a list: every F, R, and T disposition row; every empty Rob countersign field; every ADR whose status is PROPOSED, OPEN, PENDING, or REJECTED-AS-WRITTEN/OPEN; every open latitude decision; every pending pin or provenance confirmation; every row explicitly marked as requiring a human act. At minimum the terminal index must therefore include **ADR-0001 (PROPOSED), ADR-0002 (REJECTED AS WRITTEN / OPEN — existence verified in the frozen repository family), ADR-0003 (PROPOSED), ADR-0004 (pending), LAT-X004, all empty F-/R-/T- countersigns, and toolchain provenance if pending**. Every ADR cited by the plan or ledger must either exist inside the bundle as a frozen read-only decision record, or be named as an external authority with an exact path and SHA-256 — a bare reference to a missing ADR file is insufficient for the future FCB. Each index entry points to its frozen source row and reports its current countersign state. The audit compares the generated index against the discovered open-act set and **fails on both omissions and stale extra rows**. The index does not replace the source ledgers; it indexes them, and it is carried into the FCB transformation so empty countersigns cannot silently disappear under the rename.

---

## COMPLETION

Complete when: every T-item's deliverables exist (N-items included — N means non-substantive, not optional); the nine-step build order was followed and is stated in the freeze record, including post-ZIP extraction verification and the direct archive entry-multiset check (steps 7–8); the producer inventory, replay comparisons, and index-versus-discovery comparison are green in the frozen audit JSON; ADR-0003 with its interpretation clause is present verbatim and PROPOSED; **LAT-X004 is the sole open Latitude Ledger disposition** (exact phrase — other open human acts exist and are enumerated by the Human-Review Index, never denied by the freeze); all PENDING-IMPLEMENTATION rows carry frozen future-Fido fixture specs with no claimed Fido observations; **toolchain provenance is in Confirmed mode — or the bundle is delivered explicitly as an open review candidate with provenance PENDING and completion not claimed**; every phase-2 audit check is green in the frozen audit JSON, and every terminal-verifier run (phases 5 and 7–8) exits successfully without rewriting any frozen artifact; the repair ledger records `APPLIED` per T-row with empty countersign cells; and nothing claims acceptance, closure, FIXED status, or a score. Deliver `FIDO_GO1_23_SPEC_CLOSURE_REVIEW_BUNDLE_TERMINAL_2026-07-23.zip` in canonical archive form plus its external `.zip.sha256` sidecar. Rob's countersigns — indexed by T-18, decided row by row, with his LAT-X004 choice at the FCB regeneration — end the correctness volleys.
