# FIDO — VOLLEY PROTOCOL SAFETIES, v2

**Date:** 2026-07-24 · **Issued by:** Rob. Supersedes v1 (SHA-256 `3649a1eb36683f106c3722d439ea1a42d2ef96a33ec1c9907654305a62099c5a`). Standing rules binding both models symmetrically; self-contained.

## S-1. The Decision Ratchet (regression tripwire)
Every finding is marked `NEW` or `REOPENS(D-nn)`. A `REOPENS` halts the volley to **Rob** with the decision text, original rationale, and the *new information*; re-argument without new information is rejected. An author's own violation of a ratcheted decision is a `REGRESSION(D-nn)`, recorded in the next version's provenance. Two `REOPENS`/`REGRESSION` events within two consecutive rounds = automatic PAUSE for Rob. **Adjudication taxonomy:** Rob may RATIFY-AS-REGRESSION (decision stands; sealing-only repair authorized), AMEND (decision changes; ledger updated), or REJECT (finding dismissed with rationale).

**Ratchet ledger (append-only):**
- **D-01** Acyclic sealing graph: no sealing artifact contains its own hash or the hash of anything generated after it.
- **D-02** ADR-0003 authority ordering with the interpretation clause.
- **D-03** Racy-run scope: option (b); no race history in `State`.
- **D-04** LAT-X004 exists; ownership frozen (SPEC-096 / `ExprFact` / SC-05); only the policy open, only to Rob.
- **D-05** Typed provenance outcomes; pending is never green; two completion statuses.
- **D-06** Directives are self-contained; no normative imports from superseded versions.
- **D-07** Human-Review Index is discovery-based, never hardcoded.
- **D-08** Pin the distribution, not the binary; Confirmed requires tarball bytes; Pending is manifested, marked, blocking.
- **D-09** Change-granular ownership: every change has exactly one T-owner; files carry owner sets; derived governance files carry T-0 by rule.
- **D-10** Fixed points are protected as projections, never whole-row bytes.
- **D-11** The selector algebra is defined and closed; orthogonality is a listed relation; coverage equals the structural diff.
- **D-12** Archives are inspected before extraction; canonical form with all constants pinned.
- **D-13** Zero executor discretion: the registry equals the directive's normative table field-for-field, derived only by parsing the frozen directive.
- **D-14** Hash handshake: every review opens by confirming the reviewed artifact's full SHA-256; mismatch stops the review. **The recipient of any review independently re-verifies the claimed hash before processing.**
- **D-15** The fixed-point manifest is a late governance artifact, generated after the audit JSON and freeze record; the audit JSON never hashes it; `check_artifact_graph_acyclic` proves the realized containment DAG.
- **D-16** Every derived governance file (change ledger, file delta, audit JSON, freeze record, fixed-point manifest, SHA manifest) has owner T-0 by rule; `check_derived_governance_ownership` rejects any other use of the exception.

## S-2. Monster Gates
- **Self-reference (five occurrences):** every directive states its containment graph; the review checklist includes an explicit acyclicity pass; the executed bundle enforces it with `check_artifact_graph_acyclic`.
- **Compression-against-self-containment (two occurrences):** every draft passes `tools/lint_directive.py` author-side before presentation (supersession-import phrases, truncated hashes, step arithmetic, T-reference bounds, component counts, undefined selector kinds, self-reference smells).

## S-3. The Exhaust Valve
Prose review is reserved for what machinery cannot catch: authority violations, semantic or safety errors, gaps in the checking machinery itself. A finding execution's own checks would surface is logged `EXPECTED-BY-AUDIT`; the response is EXECUTE. New machinery proposed in review must name its own check or is rejected at intake.

## S-4. Termination
Fixed point = one round with zero BLOCKING and zero REQUIRED findings from the reviewer, plus zero additions from the author on linted re-read. Then EXECUTE. Post-execution defects: audit-caught → fix under existing T-rows; genuine spec gap → one full self-contained revision, and the gap's class enters the linter or audit. Rob's countersigns end everything.

## S-5. Symmetry
Both models bound identically; verify-before-adopt for every claim regardless of source; adopted fixes get fresh scrutiny; self-corrections recorded with credit; no ego load-bearing, and no vigilance either.

## S-6. Return Format (new)
**Reviewer returns are exactly one plain Markdown document.** Reviewers never build archives, never attach binaries, never emit sidecars: packaging is a *build act*, performed only by the directive author or executor using the shipped deterministic tools. A review that arrives inside or alongside a reviewer-built archive is processed for its Markdown content only; the packaging is void. Nothing in any README may ask a reviewer to package.

## S-7. No Narrated Execution (new)
A claim of having run, hashed, built, or verified anything must be accompanied by the literal command output **in the return**, or be marked `UNVERIFIED`. An artifact or verification claim the recipient cannot reproduce from what is in hand is a **FABRICATION** finding against the claimant: the return is bounced for correction — costing no round and adopting nothing — and the event is logged in the next provenance. The hash handshake is exempt from bouncing only because D-14 already forces the recipient to re-verify it locally; a failed re-verification stops processing regardless of what the return asserts. `tools/validate_return.py` mechanizes intake: handshake re-verification against the local artifact, `NEW`/`REOPENS` declaration presence, and reviewer-side packaging attempts.
