# FIDO — VOLLEY PROTOCOL SAFETIES, v1

**Date:** 2026-07-23
**Issued by:** Rob (human authority). Standing protocol for all directive/review volleys between the authoring reviewer (Claude) and the co-reviewer (ChatGPT). Binds both models symmetrically. Amendable only by Rob.
**Purpose:** the volleys converge until neither reviewer sees defects — but convergence must be *provable*, regression must *trip an alarm*, and the two demonstrated defect-generators must be caught by gates, not vigilance.

---

## S-1. The Decision Ratchet (regression tripwire)

Every adopted design decision has a stable ID in the ledger below. **Each finding in every review must be marked `NEW` or `REOPENS(D-nn)`.**
- A `REOPENS` finding is not adopted in the normal flow. It halts the volley and goes to **Rob** with: the decision text, the original rationale, and the *new information* motivating reopening. Re-argument without new information is rejected at intake.
- An author discovering they have violated a ratcheted decision (as happened twice with D-06) records it as `REGRESSION(D-nn)` in the next version's provenance — it does not silently cost a round.
- Two `REOPENS`/`REGRESSION` events within any two consecutive rounds = automatic pause; Rob adjudicates whether the process is churning before any new version is authored.

**Ratchet ledger (seeded from rounds 1–9; append-only):**
- **D-01** Acyclic freeze graph: no sealing artifact contains its own hash or the hash of anything generated after it.
- **D-02** ADR-0003 authority ordering with the interpretation clause: gc governs acceptance and adequacy, never shrinks spec-mandated behavior sets.
- **D-03** Racy-run scope: option (b) — STEP-NONDET rows retained; no race history in `State`.
- **D-04** Acceptance/value split: LAT-X004 exists, ownership frozen (SPEC-096 / `ExprFact` / SC-05), only the *policy* open, only to Rob.
- **D-05** Typed provenance outcomes: `PASS-CONFIRMED | PENDING-PROVENANCE | FAIL`; pending is never green; two completion statuses.
- **D-06** Self-containment: a live directive imports no normative content from superseded versions.
- **D-07** Human-Review Index is discovery-based, never hardcoded.
- **D-08** Pin the distribution, not the binary; Confirmed requires tarball bytes; Pending is manifested, marked, and blocks completion.
- **D-09** Change-granular ownership: every change has exactly one T-owner; files carry owner sets.
- **D-10** Fixed points are protected as projections (meaning-bearing fields), never whole-row bytes.
- **D-11** The selector algebra is defined, closed, and orthogonality is a listed relation; coverage must equal the structural diff.
- **D-12** Archives are inspected before extraction; canonical form with all constants pinned.
- **D-13** Zero executor discretion over protection strength: the registry equals the directive's normative table field-for-field.
- **D-14** Hash handshake: every review opens by confirming the reviewed artifact's full SHA-256; mismatch stops the review.

## S-2. Monster Gates (the two demonstrated generators, mechanized)

- **Self-reference (4 occurrences):** every directive version must state its artifact-containment graph (who hashes/covers whom), and the review checklist includes an explicit acyclicity pass over that graph. In the executed bundle, the audit enforces it structurally (D-01's checks).
- **Compression-against-self-containment (2 occurrences, both the author's):** every directive draft is run through **`lint_directive.py` before it is presented** — no exceptions, author-side. The linter checks: forbidden supersession phrases (mention-vs-use aware); truncated hashes in normative text; step-count arithmetic versus enumeration; T-references beyond the defined maximum; appendix component counts and duplicate keys; selector kinds used-but-undefined; self-reference phrasing smells. Validation on the historical corpus: **v10 lints CLEAN; v9 (the known-defective control) fires on all five "as in v8" imports and the T-reference gap** — the gate catches exactly the defect class that cost round 9.

## S-3. The Exhaust Valve (reality as reviewer)

Prose review is reserved for defects the machinery cannot catch: authority violations, semantic or safety errors, and gaps in the checking machinery itself. **A finding that execution's own checks would surface** — an anchor that doesn't resolve, a selector that doesn't parse, a count the audit recomputes — **is not grounds for another prose round.** It is logged `EXPECTED-BY-AUDIT`, and the correct response is EXECUTE and let the audit report it. New machinery proposed in review must arrive with its own named check ("who audits this?") or it is rejected at intake — machinery may not enter unchecked, since rounds 5–9 were the cost of exactly that.

## S-4. Termination (operationalizing "neither of you see defects")

Fixed point is reached when one full round yields **zero BLOCKING and zero REQUIRED findings** from the reviewer *and* zero additions from the author on fresh re-read with the linter green. Then: EXECUTE. Post-execution defects are triaged: audit-caught → fix the bundle under the existing T-rows; a genuine spec gap → one targeted directive revision (full, self-contained, per D-06), with the gap added to the linter or audit so its class cannot recur. Rob's countersigns remain the only ending.

## S-5. Symmetry

Both models are bound identically: verify-before-adopt applies to every claim regardless of source; adopted fixes receive the same scrutiny as fresh text; self-corrections are recorded with credit, not penalty; and neither model's proposals are exempt from S-3's "who audits this" rule. Nobody's ego is load-bearing. Nobody's vigilance is either — that's what the gates are for.
