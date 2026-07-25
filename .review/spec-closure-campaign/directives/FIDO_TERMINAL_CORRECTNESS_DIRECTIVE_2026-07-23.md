# FIDO — TERMINAL CORRECTNESS DIRECTIVE (SPEC-CLOSURE FAMILY, FINAL PASS)

**Date:** 2026-07-23
**Issued by:** Rob (human authority). This file is the directive.
**Repair authorization token:** `SPEC-CLOSURE-terminal-repair-2`
**Supersedes:** `FIDO_SPEC_CLOSURE_R1_REVIEW_AND_REPAIR_2_DIRECTIVE_2026-07-23.md` (drafted, never dispatched). That file must not be executed separately; its findings are incorporated here. Execute only this directive.
**Baseline:** `FIDO_GO1_23_SPEC_CLOSURE_REVIEW_BUNDLE_R1_2026-07-23.zip` as frozen (all 28 SHAs verified by independent review; audit and extractor re-runs reproduce frozen outputs byte-exactly).
**Role note:** This is the LAST correctness pass on the spec-closure document family under its current name. After Rob countersigns the resulting bundle, the family is transformed into the Fido Conformance Basis (FCB) reference set under a separate transformation guide. Do not begin the transformation in this pass.

**Authority limits (binding, unchanged):** documentary only; no code, `.v`, build, or gate changes; nothing may claim FIXED, accepted, closed, or scored; every countersign cell is created empty and remains Rob's alone; this directive does not accept C4 or authorize C5.

**Fixed points:** every item in Section 1 ("VERIFIED — attacked and held") of the independent R1 review is a fixed point. In particular: pinned spec/memory-model hashes; reproducible audit and extractor; Route A evaluation order; the FMA both-branches model with pinned-target observation; BOUND-001..003 and the invocation contract; the §22.3 terminal observation tuple; APPLIED-only provenance with empty countersigns; synthesized-anchor flags; the grammar counting rule; NaN-map and struct-tag rows. Weakening any of these is a regression.

---

## PART A — SUBSTANTIVE REPAIRS

### T-1 — BLOCKING — Acceptance alignment (the missing fourth disposition)

Eleven "Implementation restriction" latitude rows share one justification claiming compile-time acceptance "does not vary the meaning of a program." That claim is false for Fido's differential obligation: the fresh-build preflight makes pinned-gc acceptance part of the pipeline's definition of health, so a Fido-accepts / gc-rejects divergence is a Fido correctness failure. The preflight is the last line of defense, not the mechanism.

**Governing law (new ADR, drafted here for Rob's disposition as ADR-0003 — quote it verbatim in the ADR log and cite it from every acceptance row):**

> **ADR-0003 — Authority ordering (PROPOSED).**
> 1. Where the pinned Go specification is definite, the specification governs meaning.
> 2. Where the specification grants latitude, is silent, or is hand-wavy, the pinned gc toolchain (go1.23.2) governs, and **Fido's acceptance must be a subset of pinned-gc acceptance**. Fido explicitly targets the official gc implementation only; no other Go implementation is a target.
> 3. Where pinned gc demonstrably contradicts definite specification text (a toolchain bug), the divergence is recorded as a ledger row and dispositioned by Rob; it is never silently adopted in either direction.

**Required changes:**
1. Add disposition kind **`ACCEPTANCE-ALIGNMENT`** to the Latitude Ledger. Row fields: the pinned-toolchain acceptance observation (a compiled fixture; accept or reject; exact diagnostic text — in the style of the existing FMA/println/panic observations), the Fido elaboration obligation, the named contract, and an individual justification. **No two ACCEPTANCE-ALIGNMENT rows may share a justification string**; the audit gains this check.
2. Re-disposition individually: LAT-019, LAT-049, LAT-077, LAT-085, LAT-134, LAT-148, LAT-171, LAT-177, LAT-181 (and any other Implementation-restriction row). For each: run the fixture against pinned gc, record the observation, and state the elaboration rule.
3. State the standing obligation in the plan (§22): `fido_accepts_subset_pinned_gc` — discharged per restriction by elaboration-time rejection with an exact diagnostic (unrepresentable where the architecture allows), plus a fixture pair per restriction: rejected by Fido elaboration AND observed rejected by pinned gc.
4. First instances with full fixture pairs now: **unused local variables** (gc rejects; this row alone is BLOCKING); **constant precision bounds** (observe pinned gc's limits; bound admitted constants or reject oversize constants with an exact diagnostic); **duplicate constant switch cases** (gc rejects).
5. Corrections: LAT-118 is an implementation *prohibition* guaranteeing deterministic wrap — NOT-LATITUDE with a justification saying exactly that, owned by SC-05. LAT-214 is exposition — NOT-LATITUDE with an accurate justification. LAT-180 and LAT-181 (same anchor, same subject) must carry the same disposition.

### T-2 — REQUIRED — Remove the 13.8 MB executor binary

Delete `.review/pins/go1.23.2-linux-amd64` from the bundle. A binary cannot self-attest; the hash does the work. In the pinned-toolchain evidence doc, keep the executor hash and add the provenance chain: the official `go1.23.2.linux-amd64.tar.gz` distribution SHA-256 as published in the Go release manifest, the member path (`go/bin/go`), and the statement that the local executor hashes to the recorded value. The four pinned source files stay. Expected bundle size after: ~1 MB.

### T-3 — REQUIRED — Decide the racy-run modeling scope

LAT-217/218/219 (word-tearing) and LAT-224 (racy-read visibility) currently commit `step` to modeling access granularity in runs that `GoSafe` already condemns via the DataRace BadPrefix. Choose deliberately and record which: **(a)** re-disposition to one condemned-run rule — in a run containing a data race, reads at and after the race may yield havoc; the machine does not model sub-value granularity — or **(b)** keep STEP-NONDET and add an explicit §27 reserve stating this proof cost buys no reachable-safe-run semantics. Update the affected contract citations to match the choice.

### T-4 — REQUIRED — Make template drift measurable

Populate `template: lexical-only` on the 48 OP- and 25 KEY- rows that permissibly share representation text (and any other justified shared-text rows). Extend the audit to emit a duplicate-representation histogram (top N with counts) into the frozen JSON so any future incantation announces itself. The old-template regex check stays.

---

## PART B — SHOWROOM NITPICKS (all REQUIRED unless marked N)

These are the nitpickiest-of-nitpicky items, gathered from independent inspection. They are content and consistency fixes that survive the coming rename; cosmetic/naming polish happens after transformation.

- **T-5. Line endings.** The closure CSV is CRLF; the TSVs are LF. Normalize every tabular artifact to LF. Audit gains a line-ending uniformity check.
- **T-6. Contract cross-reference integrity.** Add an explicit SC↔§25 mapping table to the plan (SC-00 = §25.1 … SC-20 = §25.21). Audit gains: every SC token cited in any ledger `test`/`contract` field exists in the plan; and a **citation-relevance pass** — several latitude rows (e.g., LAT-176, LAT-188, LAT-217, LAT-224) cite `SC-20-EVAL-ORDER-LATITUDE` as a trailing second contract where evaluation order is not the subject; remove copy-paste contract tails so each citation is minimal and correct.
- **T-7. ID discipline, documented.** State in the Latitude Ledger header: `LAT-###` ids are stable manifest ordinals and are never renumbered; hand-added rows use `LAT-X###`. State in the closure ledger header: numbered `BOUND-###` rows are live boundary rows; `BOUND-X###` are priced exclusions. Audit checks prefix discipline.
- **T-8. Freeze claims are emitted, not typed.** Every count appearing in the freeze record's tables must be read from the audit JSON. Audit gains `freeze_claims_match`: parse the freeze record, compare each numeric claim to the JSON, fail on mismatch.
- **T-9. Re-runnable evidence.** The evidence doc's fixture programs (FMA probe, println probe, panic probe, and every new T-1 acceptance fixture) become files under `.review/tools/fixtures/`, each with a one-line rerun instruction. Inline snippets remain as excerpts, not as the only copy.
- **T-10. Pins manifest.** Add `.review/pins/PINS_MANIFEST.tsv`: one row per pin — filename, upstream origin (repo path at tag, or distribution + member path), version, SHA-256. Adopt one filename convention `<artifact>_<version>.<ext>` and rename pins to match. The freeze references the manifest instead of repeating the table.
- **T-11. One canonical tabular source.** Declare the closure CSV canonical; the closure ledger Markdown becomes **generated** by a new `tools/render_ledger_md.py`, with a header line `GENERATED FROM CSV — DO NOT EDIT`. Audit verifies CSV↔MD row-for-row equivalence by regenerating and diffing.
- **T-12. Ragged-row detection.** Audit checks every TSV/CSV for uniform column counts (the heading manifest grew columns this round; nothing may be ragged).
- **T-13. Self-describing audit.** The audit JSON gains: audit script SHA-256, input file hashes, and a schema version.
- **T-14. Platform-pending note.** One sentence in the closure ledger header and the evidence doc: the platform target set is under a pending ADR (multi-platform 64-bit); all current toolchain evidence is `go1.23.2 linux/amd64` scope. Do not retrofit platform rows in this pass.
- **T-15 (N). Root README.** The bundle-root README lists every file with a one-line purpose. This is the precursor of the FCB master index.
- **T-16 (N). Supersession chain.** The freeze record lists the full bundle lineage (original → R1 → this terminal bundle) with hashes, and names this as the final bundle under the spec-closure family name.
- **T-17 (N). Margin note, verbatim, in the evidence doc's FMA section:** "The one-bit `x*y+z` vs `math.FMA` discrepancy doubles as a CPU-feature parlor trick: a pure-Go fingerprint of fused-multiply-add hardware paths. Recorded here for delight; not load-bearing."

---

## COMPLETION

Complete when: every T-item's deliverables exist; ADR-0003 text is present verbatim and marked PROPOSED for Rob; all new audit checks run green and their results are in the frozen JSON; the binary is out and the provenance chain is in; all artifacts re-frozen with new SHAs; the repair ledger records `APPLIED` per T-row with empty Rob countersign cells; and nothing claims acceptance, closure, FIXED status, or a score. Deliver as `FIDO_GO1_23_SPEC_CLOSURE_REVIEW_BUNDLE_TERMINAL_2026-07-23.zip`. This is the last bundle under this family name; Rob's countersign, per row, ends the correctness volleys.
