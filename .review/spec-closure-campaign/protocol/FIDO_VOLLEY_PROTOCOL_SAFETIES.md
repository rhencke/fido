# FIDO — VOLLEY PROTOCOL SAFETIES, v3

**Date:** 2026-07-24 · **Issued by:** Rob. Supersedes the two earlier protocol revisions, which are retired from the working tree and live in Git history. Standing rules bind both models symmetrically and are self-contained.

**Rob's format correction:** a return volley is an amended ZIP in the same package form as the send volley. The v2 Markdown-only rule is withdrawn. A reviewer who finds a defect repairs the live artifact and strengthens the mechanical checks before returning it.

## S-1. The Decision Ratchet

Every substantive finding is marked `NEW`, `REOPENS(D-nn)`, or `REGRESSION(D-nn)`. A `REOPENS` states the prior decision, the original reason, and the new fact. Re-argument without a new fact is rejected. An author's violation of a ratcheted decision is a `REGRESSION(D-nn)` and enters the next directive's provenance.

Rob may `RATIFY-AS-REGRESSION`, `AMEND`, or `REJECT`. Two unresolved `REOPENS` events in two consecutive rounds pause semantic work for Rob, but Rob may directly authorize a sealing repair and amended return package.

**Ratchet ledger, append-only:**

- **D-01** Acyclic sealing graph: no sealing artifact contains its own hash or a hash that creates a cycle.
- **D-02** ADR-0003 authority ordering with its interpretation clause.
- **D-03** Racy-run scope is option (b); no race history in `State`.
- **D-04** LAT-X004 exists; ownership is SPEC-096 / `ExprFact` / SC-05; only policy is open, only to Rob.
- **D-05** Provenance outcomes are typed; pending is never green; completion statuses are distinct.
- **D-06** Directives are self-contained; no normative import from a superseded version.
- **D-07** Human-Review Index is discovered, never hand-listed.
- **D-08** Pin the distribution, not one binary; Confirmed needs tarball bytes; Pending is explicit and blocking.
- **D-09** Every change has one T-owner at change granularity; derived governance artifacts use T-0 only by the closed exception.
- **D-10** Fixed points are projections, not whole-row bytes.
- **D-11** Selector algebra is closed; orthogonality is listed; coverage equals the structural diff.
- **D-12** Inspect archives before extraction; all canonical archive constants are pinned.
- **D-13** Zero executor discretion: the registry is parsed only from the frozen directive's normative table.
- **D-14** Hash handshake: each volley independently verifies the live directive's full SHA-256 before amendment.
- **D-15** The fixed-point manifest is a late governance artifact after audit JSON and freeze record; the audit JSON never hashes it; the realized graph is checked as a DAG.
- **D-16** Change ledger, file delta, audit JSON, freeze record, fixed-point manifest, and SHA manifest have T-0 ownership by rule; no other file may use that rule.
- **D-17** Return volleys are amended canonical ZIPs, not review-only prose. The package itself is the answer.
- **D-18** Live directive identity is one tuple: archive filename, directive filename, title, Version field, leading Supersedes entry, normative self-reference, and recorded SHA must agree.
- **D-19** Late governance output membership has one named authority. Phase-1 inventory, build order, final-set equation, and verifier must use the same exact set.
- **D-20** Check-function inventory is closed. Every named `check_*` function is declared, implemented once, owned by one script, and cited by a gate; no orphan check may appear.
- **D-21** Recurrence counts and provenance facts must be internally consistent and mechanically linted.

## S-2. Monster Gates

The author-side directive linter must run before each volley and must include regression checks for every defect class that has occurred. At minimum it checks:

- self-containment and full hashes;
- build-step arithmetic and T-reference bounds;
- component count and unique keys;
- selector definitions;
- direct self-reference smells;
- live-version tuple agreement;
- one named late-governance set and correct generation order;
- closed check-function inventory;
- provenance recurrence-count agreement.

The package validator independently checks the archive form, internal manifest, directive version increment, supersedes hash handshake, protocol version, linter result, and presence of control-test evidence.

## S-3. The Exhaust Valve

Prose review is for defects the current machinery cannot catch: authority errors, semantic or safety errors, and gaps in the checks. A defect already caught by an existing shipped check is `EXPECTED-BY-AUDIT`; repair proceeds under the owning row. Any newly found repeatable defect must add or strengthen a named check in the same return volley.

## S-4. Termination

A fixed point is one amended volley with zero BLOCKING and zero REQUIRED defects after all shipped validators pass, plus zero additions on the author's linted re-read. Then execution may begin under Rob's authority. A later audit-caught defect is repaired under its existing owner. A genuine semantic gap requires one self-contained revision and a new permanent gate.

## S-5. Symmetry

Both models verify claims regardless of source. Adopted fixes receive fresh adversarial review. Self-corrections are recorded. Neither agreement nor disagreement has authority without evidence.

## S-6. Return Package

A return volley is exactly one canonical ZIP. It contains one root and at least:

1. one live directive whose version is exactly the sent directive version plus one;
2. this protocol or its successor;
3. one return brief with findings, repairs, and literal command outputs;
4. the prior adjudication brief when supplied, byte-identical;
5. `README.md`;
6. `MANIFEST.sha256`, covering every other file exactly once;
7. `tools/lint_directive.py`;
8. `tools/validate_return.py`.

The return ZIP uses the same canonical profile as the send package: one root, no directory entries, sorted ASCII paths, `1980-01-01 00:00:00`, `ZIP_STORED`, Unix creator system, regular-file mode 0644, no comments, and no extra fields. No sidecar accompanies a volley package.

## S-7. Verification Claims

The return brief contains the literal commands and outputs for:

- sent-package manifest verification;
- reviewed-directive hash handshake;
- amended-directive linter result;
- each negative control proving the new regression checks fire;
- provisional and final package validation.

A chat response may summarize and link the ZIP. The package is authoritative. A claim that is not reproducible from the package is marked `UNVERIFIED`.

## S-8. Repair-to-Gate Coupling

A correction is incomplete until its defect class has a regression check. The return brief maps every repair to:

- one ratchet decision or `NEW` class;
- one directive amendment;
- one linter or validator check;
- one negative control that fails when the defect is reintroduced.

`tools/validate_return.py` rejects a package whose return brief lacks that mapping or whose bundled regression controls do not pass.
