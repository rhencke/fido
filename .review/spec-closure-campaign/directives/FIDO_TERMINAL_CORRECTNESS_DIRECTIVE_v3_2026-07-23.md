# FIDO — TERMINAL CORRECTNESS DIRECTIVE, v3 (SPEC-CLOSURE FAMILY, FINAL PASS)

**Date:** 2026-07-23
**Issued by:** Rob (human authority). This file is the directive.
**Repair authorization token:** `SPEC-CLOSURE-terminal-repair-2` (unchanged)
**Version:** v3. **Supersedes** v2 (SHA-256 `d8b2a9c71355ed0163b00bfa6a3aa9ca6dd6646a1ca80d30dd0596a022d560a2`), which superseded v1 (`b30c03b8c16a09868763f891ec2fd92f3a03f2a0739c852b497a536b70502a34`). Execute only this version.
**Provenance:** Authored by Claude (Fable 5, external adversarial reviewer). Co-review round 2 by ChatGPT (Sol 5.6): seven findings (CR2-1..CR2-7), **all adopted**. CR2-1 corrects the co-reviewer's own round-1 freeze rule, which v2 adopted unverified; CR2-2 was independently verified against the frozen R1 plan before adoption (`### 25.22 SC-21-PROOF-COST-INTERNALS` exists; the collision was real). Standing practice from this round: **adopted fixes receive the same adversarial verification as fresh text.**
**Baseline:** `FIDO_GO1_23_SPEC_CLOSURE_REVIEW_BUNDLE_R1_2026-07-23.zip` as frozen.
**Role note:** LAST correctness pass under the spec-closure family name; the FCB transformation follows separately and begins with the regeneration that closes LAT-X004 (Part A, T-1.6).

**Authority limits (binding):** documentary artifacts, pins, scripts, fixtures, and recorded observations only. Compiling and executing probe fixtures against the pinned toolchain to record evidence is in scope; modifying the Fido repository (source, `.v`, build, gates) is not. Nothing may claim FIXED, accepted, closed, or scored; every countersign cell is created empty and remains Rob's alone; this directive does not accept C4 or authorize C5.

**Fixed points:** every item in Section 1 of the independent R1 review, explicitly including Route A evaluation-order nondeterminism, the FMA both-branches model, select/map/scheduler nondeterminism, BOUND-001..003, the §22.3 tuple, APPLIED-only provenance — **and `SC-21-PROOF-COST-INTERNALS` at §25.22, which this directive must not overwrite, renumber, or weaken.**

---

## PART 0 — NON-CIRCULAR FREEZE PROTOCOL (CR2-1, corrected and adopted)

Acyclicity rule, binding:

> The **audit JSON** hashes only audit **inputs** (ledgers, manifests-of-record, pins, fixtures, and **both scripts** named below). It does not hash itself, the freeze record, the in-bundle SHA manifest, the final ZIP, or the sidecar.
> The **freeze record** is generated from the frozen audit JSON. It lists: predecessor ZIP hashes, the frozen audit JSON hash, and the in-bundle manifest's **filename and coverage rule** — never the manifest's hash.
> The **in-bundle SHA manifest** hashes every bundle file except itself, including the audit JSON and the freeze record.
> The **external `.zip.sha256` sidecar** is the only place the final ZIP's hash exists.

Two-script split (CR2-3, adopted):
- `tools/audit_spec_closure_bundle.py` — **phase 2**. Writes the frozen audit JSON. Owns all input-only checks: row totality; the T-1 classification trichotomy; ACCEPTANCE-ALIGNMENT justification uniqueness; the duplicate-representation histogram; line-ending uniformity; ragged-row detection; ID-prefix discipline; the single-open-latitude rule (open set must equal exactly `{LAT-X004}`); SC-token existence against the plan; regeneration-diff of the generated ledger Markdown against its canonical sources.
- `tools/verify_terminal_bundle.py` — **phase 5**. Writes nothing; exits nonzero on failure. Owns: `freeze_claims_match` (generated freeze vs frozen JSON); manifest coverage and hash verification; assertion that no frozen artifact was rewritten after phase 2.

Mandatory build order: (1) produce canonical source artifacts, including generated Markdown, evidence files, fixtures and their captured outputs; (2) run audit, write audit JSON; (3) generate freeze record from the audit JSON; (4) generate the in-bundle SHA manifest; (5) run the terminal verifier; (6) build ZIP; (7) write the external sidecar. Rob verifies the sidecar externally.

---

## PART A — SUBSTANTIVE REPAIRS

### T-1 — BLOCKING — Acceptance alignment

Eleven "Implementation restriction" rows share one false justification; pinned-gc acceptance is part of Fido's differential obligation; the preflight is the last line of defense, not the mechanism.

**ADR-0003 (PROPOSED, for Rob; quote verbatim in the ADR log; cite from every acceptance row):**

> 1. Where the pinned Go specification is definite, the specification governs meaning.
> 2. Where the specification grants latitude, is silent, or is hand-wavy, the pinned gc toolchain (go1.23.2) governs, and **Fido's acceptance must be a subset of pinned-gc acceptance**. Fido explicitly targets the official gc implementation only.
> 3. Where pinned gc demonstrably contradicts definite specification text, the divergence is recorded as a ledger row and dispositioned by Rob; never silently adopted in either direction.
>
> **Interpretation clause (CR-2/CR2-6 form).** In tier 2, "pinned gc governs" governs the supported **acceptance profile** and **pinned-toolchain adequacy claims**. It does not reduce a formal behavior set that definite specification latitude requires `GoMachine` to admit. Route A evaluation order, FMA alternatives, select choice, map iteration order, and scheduler choice remain fixed points unless a separately countersigned ledger disposition states otherwise. A permitted-set model is required because the pinned specification grants both branches; current linux/amd64 evidence records only one target observation, and other platform observations require their own pinned evidence and ledger revision. *(No unpinned platform claims in normative text; any expected per-target behaviors belong, marked unpinned, in ADR-0004's draft notes only.)*

**Required changes:**
1. Add disposition kind **`ACCEPTANCE-ALIGNMENT`**: fields = pinned-toolchain acceptance observation (per the T-9 capture contract), Fido elaboration obligation, named contract, individual justification. Audit: no two ACCEPTANCE-ALIGNMENT justifications identical.
2. **Classification trichotomy**, audit-enforced over all implementation-restriction candidates: `ACCEPTANCE-ALIGNMENT` (in-scope accepted-language restriction) / `OUT-COVERED` (feature priced out — LAT-180 and LAT-181 both land here) / `NOT-LATITUDE` (exposition or deterministic prohibition only — LAT-118 as a wrap-guaranteeing prohibition owned by SC-05; LAT-214 as exposition).
3. Re-disposition individually under the trichotomy: LAT-019, LAT-049, LAT-077, LAT-085, LAT-134, LAT-148, LAT-171, LAT-177, LAT-180, LAT-181, LAT-118, LAT-214, and any other candidate.
4. New contract **`SC-22-ACCEPTANCE-ALIGNMENT` at §25.23** (CR2-2, adopted; verified: §25.22 is the pre-existing `SC-21-PROOF-COST-INTERNALS` and is untouched). The contract states `fido_accepts_subset_pinned_gc` as a standing obligation that is **frozen here and discharged at the checkpoints that implement its restriction cases** — not in this documentary pass. The plan separates three claims (CR2-4, adopted): **Formal** — `CompilableProgram` satisfies every accepted ledger restriction (future theorem, per checkpoint); **External** — a publishable `DirectoryImage` passes the pinned-gc preflight (enforced at publication); **Evidence** — pinned-gc probes record the selected acceptance profile (this pass). A finite probe set does not prove the global theorem.
5. **Evidence now / gates later (CR2-4, adopted).** For each ACCEPTANCE-ALIGNMENT row, this pass: **runs** the pinned-gc fixture and captures raw stdout, stderr, and status; **freezes** the future Fido half — exact fixture source, expected diagnostic ID, expected diagnostic text-or-shape, owner, and implementing checkpoint — marked **`PENDING-IMPLEMENTATION`**; and **never claims** a Fido-produced diagnostic. First frozen instances: unused local variables; constant acceptance bounds (probe pinned gc's limits); duplicate constant switch cases.
6. **Constant VALUE semantics — LAT-X004 (CR-4 + CR2-5, adopted).** Spec-permitted rounding during untyped constant folding can change an *accepted* constant's value; acceptance rows cannot own that. Create **LAT-X004** with one owner, one contract, and new latitude-ledger columns applied to every row: `decision_status`, `rob_choice`, `rob_countersign`. All rows carry `decision_status = DISPOSITIONED` except `LAT-X004: decision_status = HUMAN-CHOICE-OPEN`, `rob_choice` and `rob_countersign` empty. The audit permits exactly one open decision: open set = `{LAT-X004}`; any other open row fails. Menu for Rob: (i) admit all specification-permitted rounded values; (ii) prove accepted constants invariant under the permitted rounding latitude — including the domain-restriction variant, tying to T-1.5's constant bounds so exact and pinned-gc values provably coincide; (iii) implement the exact pinned-gc constant profile as an explicit Rob-approved refinement. **Advisory recommendation, labeled as such (both reviewers, independently): option (ii), domain-restriction variant** — deterministic retained facts, no compile-time nondeterminism, no target-specific second constant semantics. **Process (CR2-5, adopted): the terminal bundle ships with LAT-X004 open**; Rob's selection — informed by this pass's constant-bound probes — triggers regeneration, re-audit, and re-freeze **as the first step of the FCB transformation** (which regenerates everything regardless). A countersign alone cannot settle an open row under an old SHA. The freeze record states the open decision explicitly.

### T-2 — REQUIRED — Remove the 13.8 MB executor binary
Delete `.review/pins/go1.23.2-linux-amd64`. Keep the executor hash in the evidence doc; add the provenance chain: official `go1.23.2.linux-amd64.tar.gz` SHA-256 recorded as **"to be confirmed by Rob against the official Go release manifest"** if unverifiable from the execution environment — never invented — plus member path and the local-hash statement. Pinned source files stay.

### T-3 — REQUIRED — Racy-run scope: option (b) selected (CR-3)
LAT-217/218/219/224 remain STEP-NONDET; `DataRace` remains a derived finite BadPrefix; §27 gains the reserve (*sub-value/word granularity is deliberate proof cost affecting condemned runs, not reachable safe-run behavior; narrowable only by a future countersigned disposition*); citations name only the owning channel/race contract; SC-20 copy-paste tails removed.

### T-4 — REQUIRED — Template drift measurable
`template: lexical-only` on the 48 OP- and 25 KEY- rows (and other justified shared-text rows); duplicate-representation histogram in the frozen JSON; old-template regex stays.

---

## PART B — SHOWROOM NITPICKS (N = non-substantive, still required)

- **T-5. Line endings.** All tabular artifacts LF; audit checks uniformity.
- **T-6. Contract mapping and citation hygiene.** Plan gains the full table: SC-00 = §25.1 … SC-20 = §25.21, **SC-21 = §25.22 (PROOF-COST-INTERNALS, pre-existing)**, **SC-22 = §25.23 (ACCEPTANCE-ALIGNMENT, new)**. Audit: every cited SC token exists. Citation *relevance* is fixed by hand this pass; the audit checks existence only.
- **T-7. ID discipline documented.** `LAT-###` stable manifest ordinals; hand-added `LAT-X###` (next: LAT-X004). `BOUND-###` live boundary rows; `BOUND-X###` priced exclusions. Audit checks prefixes.
- **T-8. Freeze claims emitted, not typed.** Every freeze count is read from the audit JSON; `freeze_claims_match` runs in the **phase-5 verifier** per Part 0.
- **T-9. Re-runnable evidence with full environment closure (CR2-7, adopted).** All fixtures under `.review/tools/fixtures/` with per-fixture rerun instructions, executed only through one runner (`tools/run_fixture.py`) that: verifies the external executor's SHA-256 before each run; starts from a cleared environment or explicit allowlist; pins at minimum `GOOS=linux`, `GOARCH=amd64`, an explicit `GOAMD64` (record the chosen value), `CGO_ENABLED=0`, empty `GOFLAGS`, plus `GOTOOLCHAIN=local`, `GOENV=off`, `GOWORK=off`; uses fixed bundle-local `GOCACHE` and temp paths; disables module network access (`GOPROXY=off`) for fixtures needing none; records the exact command and the effective `go env`; runs from the fixed relative fixture directory; retains raw stdout, stderr, and exit status as files beside the fixture. This strengthened contract governs **probe evidence in this pass** and is FLAGGED as a proposed strengthening of BOUND-003's invocation contract for the checkpoint that implements it — no repo change now.
- **T-10. Pins manifest.** `PINS_MANIFEST.tsv` (filename, upstream origin, version, SHA-256); one naming convention; freeze references the manifest.
- **T-11. One canonical source per table.** Closure CSV **and** Latitude TSV are canonical; `tools/render_ledger_md.py` consumes **both** and generates the entire ledger Markdown, headed `GENERATED FROM CSV/TSV — DO NOT EDIT`; audit regenerates and diffs (phase 2).
- **T-12. Ragged-row detection** across all TSV/CSV (phase 2).
- **T-13. Self-describing audit.** Audit JSON records: its own script's SHA-256 **and the verifier script's SHA-256 as inputs**, all input file hashes, and a schema version.
- **T-14. Platform-pending note.** One sentence in the ledger header and evidence doc: platform set under pending ADR-0004; all current evidence is `go1.23.2 linux/amd64` scope; no platform rows this pass.
- **T-15 (N). Root README** listing every file with a one-line purpose.
- **T-16 (N). Supersession chain, acyclic.** Freeze lists predecessor ZIP hashes (original, R1), the frozen audit JSON hash, and the in-bundle manifest's **filename and coverage rule** — never its hash; the terminal ZIP hash lives only in the external sidecar.
- **T-17 (N). FMA margin note, verbatim:** "The one-bit `x*y+z` vs `math.FMA` discrepancy doubles as a CPU-feature parlor trick: a pure-Go fingerprint of fused-multiply-add hardware paths. Recorded here for delight; not load-bearing."

---

## COMPLETION

Complete when: every T-item's deliverables exist (N-items included); Part 0's build order was followed and is stated in the freeze record; ADR-0003 with its interpretation clause is present verbatim and PROPOSED; LAT-X004 exists as the **only** open decision, with the new columns present on every row and the freeze record acknowledging the open state; all PENDING-IMPLEMENTATION rows carry frozen future-Fido fixture specs and no claimed Fido observations; **every phase-2 audit check is green in the frozen audit JSON, and every phase-5 terminal-verifier check exits successfully without rewriting any frozen artifact**; the binary is out and the provenance chain is in (unverifiable hashes marked for Rob, never invented); the repair ledger records `APPLIED` per T-row with empty countersign cells; and nothing claims acceptance, closure, FIXED status, or a score. Deliver `FIDO_GO1_23_SPEC_CLOSURE_REVIEW_BUNDLE_TERMINAL_2026-07-23.zip` plus its external `.zip.sha256` sidecar. Rob's countersign, per row — and his LAT-X004 choice at the FCB regeneration — end the correctness volleys.
