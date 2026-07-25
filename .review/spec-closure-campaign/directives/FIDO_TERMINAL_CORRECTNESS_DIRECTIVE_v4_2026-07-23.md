# FIDO — TERMINAL CORRECTNESS DIRECTIVE, v4 (SPEC-CLOSURE FAMILY, FINAL PASS)

**Date:** 2026-07-23
**Issued by:** Rob (human authority). This file is the directive.
**Repair authorization token:** `SPEC-CLOSURE-terminal-repair-2` (unchanged)
**Version:** v4. **Supersedes** v3 (SHA-256 `6a99418c02cba3063bc43e61a71c48197fe3a55889d5c18f0225d5b78dbc011b`), v2 (`d8b2a9c7…`), v1 (`b30c03b8…`). Execute only this version.
**Provenance:** Authored by Claude (Fable 5, external adversarial reviewer). Co-review round 3 by ChatGPT (Sol 5.6): five findings (CR3-1..CR3-5), **all adopted**; all five were defects or under-specifications in the reviewer-authored machinery of v3. The co-reviewer opened by confirming v3's full SHA-256 — the hash handshake is now standing protocol and it works. Round-over-round finding order is strictly decreasing (architecture → process → mechanics); per the co-reviewer, no further semantic or architecture round is expected.
**Baseline:** `FIDO_GO1_23_SPEC_CLOSURE_REVIEW_BUNDLE_R1_2026-07-23.zip` as frozen.

**Authority limits and fixed points:** unchanged from v3 (documentary + probe evidence only; no repo changes; nothing claims FIXED/accepted/scored; countersigns Rob's alone; `SC-21-PROOF-COST-INTERNALS` §25.22 untouched; Route A, FMA both-branches, select/map/scheduler nondeterminism, BOUND-001..003, §22.3 tuple all fixed).

---

## PART 0 — NON-CIRCULAR FREEZE PROTOCOL, EVIDENCE CHAIN, AND ARCHIVE VERIFICATION

Acyclicity rule (unchanged from v3): audit JSON hashes only inputs; freeze record generated from audit JSON and lists predecessor ZIP hashes, the frozen audit JSON hash, and the manifest's **filename and coverage rule** (never its hash); manifest hashes every in-bundle file except itself; the final ZIP hash exists only in the external sidecar.

**Producer inventory (CR3-2, adopted).** Every tool that creates or determines frozen content is a named, hashed phase-2 input: `audit_spec_closure_bundle.py`, `verify_terminal_bundle.py`, `extract_latitude.py`, `render_ledger_md.py`, `run_fixture.py`, the freeze-record generator, the SHA-manifest generator, the human-review-index generator (T-18), and the ZIP builder when it is a project script. Recording only the audit and verifier is insufficient.

**Phase-2 replay duties (CR3-2, adopted).** The audit does not merely hash evidence; it **replays** it, writing only to a temporary comparison area and never rewriting frozen captures:
- re-run latitude extraction against the pinned documents and byte-compare to the frozen manifest;
- re-render the ledger Markdown from the canonical CSV/TSV and byte-compare;
- re-run **every** probe fixture in compare-only mode under the T-9 closed environment and compare stdout, stderr, exit status, command record, and effective-environment record to the frozen captures.

**Inventory completeness rule (CR3-2, adopted).** The audit JSON contains the complete file set and SHA-256 of every phase-1 file. The terminal verifier rejects any addition, deletion, or byte change in that set. The only later in-bundle files permitted are the audit JSON, the generated freeze record, and the generated SHA manifest.

**Build order (CR3-3, adopted; nine steps):**
1. Produce canonical inputs (ledgers, generated Markdown, evidence, fixtures with captured outputs, human-review index).
2. Run phase-2 audit; write the frozen audit JSON.
3. Generate the freeze record from the audit JSON.
4. Generate the in-bundle SHA manifest.
5. Run the terminal verifier against the staged tree (writes nothing; nonzero on failure).
6. Build the ZIP with a **deterministic builder**: sorted entries, fixed timestamps, fixed modes, fixed compression settings.
7. **Extract the ZIP into a clean directory and run the terminal verifier there** — the artifact Rob receives is what gets verified, not only the staging tree.
8. Confirm the archive's file set and bytes against the in-bundle manifest.
9. Write the external `.zip.sha256` sidecar. Rob verifies the sidecar externally.

---

## PART A — SUBSTANTIVE REPAIRS

### T-1 — BLOCKING — Acceptance alignment
Unchanged from v3 in full: ADR-0003 with interpretation clause (PROPOSED, for Rob); `ACCEPTANCE-ALIGNMENT` disposition with per-row individual justifications (audit-enforced uniqueness); the classification trichotomy over all implementation-restriction candidates; **`SC-22-ACCEPTANCE-ALIGNMENT` at §25.23** (the co-reviewer has independently confirmed §25.22 is occupied by SC-21-PROOF-COST-INTERNALS); the three-claims separation (Formal / External / Evidence); evidence-now / gates-later with **PENDING-IMPLEMENTATION** future-Fido fixture specs, never claimed observations; LAT-X004 with `decision_status` / `rob_choice` / `rob_countersign` columns, audit rule that the open set equals exactly `{LAT-X004}`, the labeled advisory recommendation (option ii, domain-restriction variant), and the re-freeze folded into the FCB transformation.

### T-2 — REQUIRED — Pinned **distribution** execution (CR3-1, adopted; replaces v3's executor-only rule)
Delete the 13.8 MB in-bundle executor. Probe evidence is valid **only** when `run_fixture.py` executes from a complete Go distribution rooted in the official `go1.23.2.linux-amd64.tar.gz`: the runner verifies the external tarball SHA-256 against the pinned value, extracts it into the fixed evidence sandbox, sets `GOROOT` to that extracted root, and invokes that root's `go/bin/go`; the member `go/bin/go` hash is a secondary check. A pre-existing `GOROOT` is accepted only if its complete file manifest is proved equal to one derived from the verified tarball. Rationale: `go` delegates to `pkg/tool/linux_amd64/compile` and `link` and consumes the standard library under `GOROOT`; hashing only `bin/go` does not pin the compiler that judges the fixture.

**Provenance-pending rule (CR3-1, adopted).** The official tarball hash must be confirmed before terminal completion. A placeholder ("to be confirmed by Rob") may appear in a review candidate but sets **toolchain provenance = PENDING**, is listed in the Human-Review Index (T-18), and **blocks completion** — no second open item may hide outside LAT-X004's declared state. Fallback if the official tarball is unreachable from the execution environment: Rob supplies the tarball or its official hash out-of-band; absent that, probes may run against the local `/usr/local/go` only with every resulting observation marked `PROVENANCE-PENDING`, and the bundle ships as an open review candidate, not a completed one.

### T-3 — REQUIRED — Racy-run scope: option (b). Unchanged from v3.

### T-4 — REQUIRED — Template drift measurable. Unchanged from v3.

---

## PART B — SHOWROOM NITPICKS (N = non-substantive, still required)

- **T-5.** LF everywhere; audit checks. Unchanged.
- **T-6. Contract definitions audited, not token text (CR3-5, adopted).** The audit parses the actual `### 25.N \`SC-XX-…\`` headings and proves: each SC identifier has exactly one §25 definition; each §25 contract heading has exactly one SC identifier; the mapping table is a byte-for-byte projection of those headings; identifiers are contiguous SC-00 through SC-22; every ledger citation names one defined heading; no defined contract remains uncited without an explicit stated reason. SC-22 = §25.23 thereby becomes a checked fact. Citation *relevance* remains a hand-fix this pass.
- **T-7.** ID discipline documented; audit checks prefixes. Unchanged.
- **T-8.** Freeze claims emitted; `freeze_claims_match` in the phase-5 verifier. Unchanged.
- **T-9. Exact closed probe environment (CR3-1, adopted; replaces v3's "at minimum"/allowlist wording).** One runner, `run_fixture.py`, per T-2's pinned-distribution rule, starting from an **empty environment** and setting exactly one closed list: `GOROOT` (the verified sandbox root), `PATH` (fixed, minimal), `HOME` (sandbox), `TMPDIR` (sandbox), `GOCACHE` (sandbox), `GOMODCACHE` (sandbox), `GOPATH` (sandbox), `LANG`/`LC_ALL` (fixed), `TZ` (fixed), `GODEBUG` (empty), `GOTRACEBACK` (fixed), `GOOS=linux`, `GOARCH=amd64`, `GOAMD64` (explicit, recorded), `CGO_ENABLED=0`, `GOFLAGS=""`, `GOPROXY=off`, `GOTOOLCHAIN=local`, `GOENV=off`, `GOWORK=off`. Fixed sandbox root for all path-bearing output, or a stated normalization rule. The runner records the exact command and effective `go env` per run; raw stdout, stderr, and exit status are retained beside each fixture. Flagged (unchanged) as a proposed BOUND-003 strengthening for the implementing checkpoint.
- **T-10.** `PINS_MANIFEST.tsv` gains a row for the official distribution tarball (origin, version, SHA-256 or PENDING per T-2). Otherwise unchanged.
- **T-11.** CSV and Latitude TSV canonical; Markdown fully generated; phase-2 regenerates and diffs. Unchanged (replay duty now in Part 0).
- **T-12.** Ragged-row detection. Unchanged.
- **T-13.** Self-describing audit: schema version plus the SHA-256 of **every producer and verifier tool** per Part 0's inventory. Extended per CR3-2.
- **T-14.** Platform-pending note. Unchanged.
- **T-15 (N).** Root README. Unchanged.
- **T-16 (N).** Supersession chain, acyclic, per Part 0. Unchanged.
- **T-17 (N).** FMA margin note, verbatim. Unchanged.
- **T-18 (NEW, REQUIRED) — Human-Review Index (CR3-4, adopted).** A **generated** file listing every unresolved human act across the document family, each entry pointing to its frozen source row and reporting its current countersign state: F-1…F-19; R-1…R-6; T-1…T-18; ADR-0003; ADR-0004; LAT-X004; toolchain-provenance confirmation if pending. It is produced by a named generator (in the producer inventory), audited in phase 2, and **carried into the FCB transformation** so that empty countersigns cannot silently disappear when the family is renamed. It does not replace the source ledgers; it indexes them.

---

## COMPLETION (CR3-4 language, adopted)

Complete when: every T-item's deliverables exist (N-items included); the nine-step build order was followed and is stated in the freeze record, **including post-ZIP extraction verification (steps 7–8)**; the producer inventory and replay checks are green in the frozen audit JSON; ADR-0003 is present verbatim and PROPOSED; **LAT-X004 is the sole open Latitude Ledger disposition** (exact phrase — other open human acts exist and are enumerated by the Human-Review Index, not denied by the freeze); all PENDING-IMPLEMENTATION rows carry frozen future-Fido fixture specs with no claimed Fido observations; **toolchain provenance is confirmed — or the bundle is delivered explicitly as an open review candidate with provenance PENDING and completion not claimed**; every phase-2 audit check is green in the frozen audit JSON, and every phase-5/7 terminal-verifier run exits successfully without rewriting any frozen artifact; the repair ledger records `APPLIED` per T-row with empty countersign cells; and nothing claims acceptance, closure, FIXED status, or a score. Deliver `FIDO_GO1_23_SPEC_CLOSURE_REVIEW_BUNDLE_TERMINAL_2026-07-23.zip` plus its external `.zip.sha256` sidecar. Rob's countersigns — indexed by T-18, decided row by row, with his LAT-X004 choice at the FCB regeneration — end the correctness volleys.
