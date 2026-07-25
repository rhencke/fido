# FIDO — TERMINAL CORRECTNESS DIRECTIVE, v2 (SPEC-CLOSURE FAMILY, FINAL PASS)

**Date:** 2026-07-23
**Issued by:** Rob (human authority). This file is the directive.
**Repair authorization token:** `SPEC-CLOSURE-terminal-repair-2` (unchanged)
**Version:** v2. **Supersedes** Terminal Directive v1 (SHA-256 `b30c03b8c16a09868763f891ec2fd92f3a03f2a0739c852b497a536b70502a34`). Execute only this version.
**Provenance:** Authored by Claude (Fable 5, external adversarial reviewer). Co-reviewed by ChatGPT (Sol 5.6, adversarial co-reviewer); its four material findings and all minor corrections are ADOPTED and incorporated below (marked CR-1..CR-4). Per the model-operations rule, this stamp is normative.
**Baseline:** `FIDO_GO1_23_SPEC_CLOSURE_REVIEW_BUNDLE_R1_2026-07-23.zip` as frozen (all SHAs verified; audit and extractor re-runs reproduce frozen outputs byte-exactly).
**Role note:** LAST correctness pass under the spec-closure family name. After Rob countersigns the resulting bundle, the family transforms into the Fido Conformance Basis (FCB) under a separate guide. Do not begin the transformation in this pass.

**Authority limits (binding):** documentary artifacts, pins, scripts, fixtures, and recorded observations only. No repository source, `.v`, build, or gate changes. **Clarification (adopting co-review):** compiling and executing probe fixtures against the pinned toolchain to *record evidence* is in scope; modifying the Fido repository is not. Nothing may claim FIXED, accepted, closed, or scored; every countersign cell is created empty and remains Rob's alone; this directive does not accept C4 or authorize C5.

**Fixed points:** every item in Section 1 of the independent R1 review, explicitly including: pinned spec/memory-model hashes; reproducible audit and extractor; Route A evaluation-order nondeterminism; the FMA both-branches model; select-choice, map-iteration, and scheduler nondeterminism; BOUND-001..003 and the invocation contract; the §22.3 terminal observation tuple; APPLIED-only provenance; synthesized-anchor flags; the grammar counting rule; NaN-map and struct-tag rows. Weakening any is a regression.

---

## PART 0 — NON-CIRCULAR FREEZE PROTOCOL (CR-1, adopted)

The freeze machinery must be acyclic. Binding rule:

> The audit JSON hashes **only audit inputs** (ledgers, manifests, pins, tools). It does not hash itself, the freeze record, the in-bundle SHA manifest, the final ZIP, or the ZIP sidecar. The freeze record is **generated from** the frozen audit JSON. The in-bundle SHA manifest covers every bundle file **except itself**, including the audit JSON and the freeze record. The final ZIP's SHA-256 exists only in an external `.zip.sha256` sidecar. The freeze record lists **predecessor** ZIP hashes and the terminal **in-bundle manifest** hash; it never lists its own ZIP's hash.

Mandatory build order: (1) produce canonical source artifacts; (2) run audit, write audit JSON; (3) generate freeze record from audit JSON; (4) generate in-bundle SHA manifest; (5) run final verification without rewriting the audit JSON; (6) build ZIP; (7) write external ZIP SHA sidecar. T-8, T-13, and T-16 below are subordinate to this protocol.

---

## PART A — SUBSTANTIVE REPAIRS

### T-1 — BLOCKING — Acceptance alignment (with CR-2 scope rule and CR-4 value split)

Eleven "Implementation restriction" latitude rows share one justification claiming compile-time acceptance "does not vary the meaning of a program." False for Fido's differential obligation: the fresh-build preflight makes pinned-gc acceptance part of the pipeline's health. A Fido-accepts / gc-rejects divergence is a Fido correctness failure. The preflight is the last line of defense, not the mechanism.

**Governing law — ADR-0003, drafted for Rob's disposition; quote verbatim in the ADR log; cite from every acceptance row:**

> **ADR-0003 — Authority ordering (PROPOSED).**
> 1. Where the pinned Go specification is definite, the specification governs meaning.
> 2. Where the specification grants latitude, is silent, or is hand-wavy, the pinned gc toolchain (go1.23.2) governs, and **Fido's acceptance must be a subset of pinned-gc acceptance**. Fido explicitly targets the official gc implementation only; no other Go implementation is a target.
> 3. Where pinned gc demonstrably contradicts definite specification text (a toolchain bug), the divergence is recorded as a ledger row and dispositioned by Rob; it is never silently adopted in either direction.
>
> **Interpretation clause (CR-2, adopted).** In tier 2, "pinned gc governs" governs the supported **acceptance profile** and **pinned-toolchain adequacy claims**. It does not reduce a formal behavior set that definite specification latitude requires `GoMachine` to admit. Route A evaluation order, FMA alternatives, select choice, map iteration order, and scheduler choice remain fixed points unless a separately countersigned ledger disposition states otherwise. This clause is not a softening: under ADR-0004's platform matrix, one pinned gc exhibits *different* branches on different targets (e.g., FMA on arm64, none on amd64), so a permitted-set model is the only reading under which tier 2 is even coherent.

**Required changes:**
1. Add disposition kind **`ACCEPTANCE-ALIGNMENT`** to the Latitude Ledger. Row fields: pinned-toolchain acceptance observation (fixture; accept or reject; exact diagnostic), the Fido elaboration obligation, the named contract, and an individual justification. **No two ACCEPTANCE-ALIGNMENT rows may share a justification string**; the audit gains this check.
2. **Classification trichotomy (CR-minor, adopted).** Not every implementation-restriction row becomes ACCEPTANCE-ALIGNMENT. Each candidate must fall into exactly one stated case, and the audit enforces the trichotomy over all implementation-restriction candidates:
   - `ACCEPTANCE-ALIGNMENT` — an in-scope accepted-language restriction;
   - `OUT-COVERED` — the whole feature is already priced out (e.g., import-path charset under the closed-world import rows: LAT-180 and LAT-181 both land here, resolving their inconsistency);
   - `NOT-LATITUDE` — exposition or a deterministic prohibition only (e.g., LAT-118: an implementation *prohibition* guaranteeing deterministic wrap, owned by SC-05; LAT-214: exposition).
3. Re-disposition individually under the trichotomy: LAT-019, LAT-049, LAT-077, LAT-085, LAT-134, LAT-148, LAT-171, LAT-177, LAT-180, LAT-181, LAT-118, LAT-214, and any other implementation-restriction candidate. For each ACCEPTANCE-ALIGNMENT row: run the fixture against pinned gc, record the observation per the capture contract (T-9), state the elaboration rule.
4. State the standing obligation in the plan (§22) and as new contract **`SC-21-ACCEPTANCE-ALIGNMENT` (§25.22)**: `fido_accepts_subset_pinned_gc` — discharged per restriction by elaboration-time rejection with an exact diagnostic (unrepresentable where the architecture allows), plus a fixture pair per restriction: rejected by Fido elaboration AND observed rejected by pinned gc.
5. First instances with full fixture pairs now: **unused local variables** (gc rejects; BLOCKING on its own); **constant acceptance bounds** (observe pinned gc's limits; reject over-limit constants with an exact diagnostic); **duplicate constant switch cases** (gc rejects).
6. **Constant VALUE semantics — split from acceptance (CR-4, adopted).** LAT-019/LAT-134 do more than vary acceptance: spec-permitted rounding during untyped constant folding can change the **value** of an *accepted* constant (array lengths, comparisons, emitted output). Acceptance rows cannot own that. Create supplemental row **LAT-X004 — constant-expression value under permitted rounding latitude**, with one owner and one contract, presenting exactly this menu for **Rob's countersigned choice** (a model recommendation may accompany, clearly labeled):
   - (i) the formal constant fact admits all specification-permitted rounded values;
   - (ii) prove accepted constants are invariant under the permitted rounding latitude — including the variant: restrict the accepted constant domain (via T-1.5's acceptance bounds) so that exact and pinned-gc-profile values provably coincide;
   - (iii) implement and prove the exact pinned-gc constant profile as an explicit Rob-approved refinement.
   The audit gains: no ACCEPTANCE-ALIGNMENT justification may claim to own constant values; until LAT-X004 is countersigned, constant precision is **open**, and the freeze record must say so.

### T-2 — REQUIRED — Remove the 13.8 MB executor binary

Delete `.review/pins/go1.23.2-linux-amd64`. A binary cannot self-attest; the hash does the work. In the pinned-toolchain evidence doc, keep the executor hash and add the provenance chain: the official `go1.23.2.linux-amd64.tar.gz` SHA-256 recorded as **"to be confirmed by Rob against the official Go release manifest"** if not verifiable from the execution environment — never invented — plus member path (`go/bin/go`) and the statement that the local executor hashes to the recorded value. The four pinned source files stay. Expected bundle size after: ~1 MB.

### T-3 — REQUIRED — Racy-run modeling scope: **option (b) is selected** (CR-3, adopted)

Option (a) (havoc at-and-after the first race) is rejected: `step : State -> Label -> State -> Prop` receives no trace, so (a) requires race history in `State`, a taint field, an operational detector beside the trace-based definition, or a second run rule — each adds state or a second authority, violating the no-trace-in-state law. Therefore:
- LAT-217, LAT-218, LAT-219, LAT-224 **remain STEP-NONDET**, modeling the memory-model latitude directly;
- `DataRace` remains a derived finite BadPrefix;
- §27 gains the reserve, verbatim in substance: *sub-value and machine-word access granularity is deliberate proof cost that affects condemned runs, not reachable safe-run behavior; it may be narrowed only by a future countersigned ledger disposition*;
- their contract citations name only the owning channel/race contract; the copied `SC-20-EVAL-ORDER-LATITUDE` tails are removed (see T-6).

### T-4 — REQUIRED — Make template drift measurable

Populate `template: lexical-only` on the 48 OP- and 25 KEY- rows (and any other justified shared-text rows). Audit emits a duplicate-representation histogram (top N with counts) into the frozen JSON. The old-template regex check stays.

---

## PART B — SHOWROOM NITPICKS (N = non-substantive, **still required**; CR-minor adopted — the completion clause covers every T-item)

- **T-5. Line endings.** Closure CSV is CRLF; TSVs are LF. Normalize all tabular artifacts to LF. Audit checks uniformity.
- **T-6. Contract cross-reference integrity.** Add the SC↔§25 mapping table to the plan, covering every contract **including the one this directive creates**: SC-00 = §25.1 … SC-20 = §25.21, **SC-21 = §25.22**. Audit: every SC token cited in any `test`/`contract` field exists in the plan. Hand-fix the citation-relevance pass this round (remove copy-paste contract tails, e.g., SC-20 on LAT-176/188/217/224); the audit checks existence only — relevance is judgment.
- **T-7. ID discipline, documented.** Latitude header: `LAT-###` are stable manifest ordinals, never renumbered; hand-added rows use `LAT-X###` (next stable: LAT-X004). Closure header: `BOUND-###` live boundary rows; `BOUND-X###` priced exclusions. Audit checks prefix discipline.
- **T-8. Freeze claims are emitted, not typed.** Every count in the freeze record is read from the audit JSON; audit gains `freeze_claims_match`. Subordinate to Part 0: the check parses the *generated* freeze record against the JSON it was generated from, in build-order step 5.
- **T-9. Re-runnable evidence with a fixed capture contract (CR-minor, adopted).** All fixture programs (FMA, println, panic, and every acceptance fixture) live under `.review/tools/fixtures/` with per-fixture rerun instructions. Diagnostic capture contract, binding for every observation: fixed fixture filenames; fixed working directory (bundle root, fixed relative fixture dir); fixed environment (exactly the pinned invocation contract: `GOTOOLCHAIN=local`, `GOENV=off`, `GOWORK=off`); the exact command recorded; raw stdout, stderr, and exit status retained as files beside the fixture. No temporary paths may appear in "exact" diagnostics.
- **T-10. Pins manifest.** `.review/pins/PINS_MANIFEST.tsv`: filename, upstream origin (repo path at tag, or distribution + member path), version, SHA-256. One filename convention `<artifact>_<version>.<ext>`; rename pins to match. The freeze references the manifest.
- **T-11. One canonical source per table (CR-minor, adopted).** The closure CSV **and** the Latitude Ledger TSV are canonical. `tools/render_ledger_md.py` consumes **both** and generates the *entire* ledger Markdown — closure sections and latitude sections — headed `GENERATED FROM CSV/TSV — DO NOT EDIT`. No hand-written section remains in the generated file. Audit regenerates and diffs.
- **T-12. Ragged-row detection.** Audit checks every TSV/CSV for uniform column counts.
- **T-13. Self-describing audit.** Audit JSON gains: audit script SHA-256, **input** file hashes (per Part 0's input-only rule), and a schema version.
- **T-14. Platform-pending note.** One sentence in the closure ledger header and the evidence doc: the platform target set is under pending ADR-0004 (multi-platform 64-bit); all current toolchain evidence is `go1.23.2 linux/amd64` scope. Do not retrofit platform rows in this pass.
- **T-15 (N). Root README** listing every file with a one-line purpose (precursor of the FCB index).
- **T-16 (N). Supersession chain, non-circular.** The freeze record lists predecessor ZIP hashes (original, R1) and the terminal **in-bundle manifest** hash, and names this the final bundle under the spec-closure family name. Per Part 0, it never contains its own ZIP's hash; the terminal ZIP hash lives only in the external sidecar.
- **T-17 (N). Margin note, verbatim, in the evidence doc's FMA section:** "The one-bit `x*y+z` vs `math.FMA` discrepancy doubles as a CPU-feature parlor trick: a pure-Go fingerprint of fused-multiply-add hardware paths. Recorded here for delight; not load-bearing."

---

## COMPLETION

Complete when: every T-item's deliverables exist (N-items included); Part 0's build order was followed and is stated in the freeze record; ADR-0003 with its interpretation clause is present verbatim and marked PROPOSED; LAT-X004 exists with its menu and an OPEN status the freeze record acknowledges; all new audit checks run green in the frozen JSON; the binary is out and the provenance chain is in (unverifiable hashes marked for Rob, never invented); all artifacts re-frozen per Part 0; the repair ledger records `APPLIED` per T-row with empty Rob countersign cells; and nothing claims acceptance, closure, FIXED status, or a score. Deliver as `FIDO_GO1_23_SPEC_CLOSURE_REVIEW_BUNDLE_TERMINAL_2026-07-23.zip` plus its external `.zip.sha256` sidecar. This is the last bundle under this family name; Rob's countersign, per row, ends the correctness volleys.
