# FIDO — VOLLEY ADJUDICATION BRIEF (Round 10 Pause)

**Date:** 2026-07-24 · **Authority:** Rob · **Prepared by:** Claude (external adversarial reviewer)

The round-10 return (ChatGPT) declared three `REOPENS` findings, triggering an S-1 PAUSE. Rob's instruction of 2026-07-24 — "fix and add safeties against regression" — is recorded as the adjudication below.

## Dispositions

**1. REOPENS(D-01) → RATIFIED AS REGRESSION(D-01).** D-01 (acyclic sealing graph) stands unamended. v10's step-6 fixed-point manifest required terminal hashes of the step-9/10 audit JSON and freeze record, which hash the manifest — a cycle; the self-reference class's **fifth** occurrence, author's defect, caught by the co-reviewer performing the S-2 acyclicity pass. **Repair (v11, sealing-only):** the fixed-point manifest becomes a *late governance artifact* generated at step 11, after its dependencies; the audit JSON never hashes it; fixed-point checks move to the terminal verifier; new named check `check_artifact_graph_acyclic` gates the class permanently.

**2. REOPENS(D-09) → RATIFIED AS REGRESSION(D-09).** D-09 (every change has exactly one owner) stands. v10 left the audit JSON, freeze record, and SHA manifest owner-less. **Repair:** owner-by-rule extends to all six derived governance files (→ T-0); new named check `check_derived_governance_ownership` proves each came from its named hashed producer and rejects any other use of the exception.

**3. REOPENS(D-13) → RATIFIED AS REGRESSION(D-13).** D-13 (zero executor discretion) stands. Appendix A's aliases/arrows/shorthand had no canonical reading, and the check could compare a generator's copy against itself. **Repair:** normative Canonical Transcription Rules added; the registry is derived **only** by parsing the frozen in-bundle directive; no second embedded copy may exist.

**4. Three EXPECTED-BY-AUDIT projection conflicts** (whole-file/anchored coexistence on the latitude manifest; T-17's note inside EVID-04's protected section; T-2's provenance edit inside EVID-06's protected section) — correctly classed under S-3; repaired in the same v11 pass (extraction-terms component removed, 41 components; T-17 relocated to a new `## 5. Margin notes` section; EVID-06 narrowed to the harvested invocation sentences).

**5. Packaging derailment.** The reviewer's attempt to produce a return ZIP failed in its environment. **The review content is unaffected and accepted** — its hash handshake was independently re-verified here: the claimed v10 SHA-256 is exact. Disposition: reviewer-side packaging is abolished (Protocol v2, S-6); returns are plain Markdown only; packaging is an author/executor act using shipped deterministic tools.

## Issued under this adjudication
- **Directive v11** (sealing-only, self-contained, 28 surgical edits, lints CLEAN): SHA-256 `428c609766f08025686580ab88fa25c02e06fb339629c10ec6023ed9c77d7540`
- **Volley Protocol v2**: adds S-6 (Markdown-only returns), S-7 (no narrated execution; fabrication handling), ratchet entries D-15 (late-manifest ordering) and D-16 (derived-governance ownership); ships `tools/validate_return.py`.

**Rob countersign:** ______________
