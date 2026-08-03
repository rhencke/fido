# FCB Amendment A009 — Complexity Fit

- **ID:** `FCB-A009-COMPLEXITY-FIT`
- **Status:** **ACCEPTED** — human owner Rob, token `FCB-A009-complexity-fit`
- **Author:** Primary ChatGPT Fido review thread
- **Committer:** Claude Code (applied the amendment; authored nothing in it)
- **Date:** `2026-08-03`
- **Reviewed repository ref:** `1fa17b5946a507ae3f350135b7a9ec98b10171ff`

## New information

The Build Observatory reached roughly fifty thousand lines and a self-verifying measurement platform to answer
a question a sixty-line shell script answers. Nothing in the accepted contracts forbade that: every individual
addition was defensible, and no rule asked whether the machinery still fit the job. Rob withdrew the product
outright rather than repair it a sixth time.

## The rule

> **Make each component as exact and rigorous as its real job requires, but no more complicated than that job
> justifies.**

## Consequences

- A design states the component's real job before proposing machinery.
- Implementation keeps only machinery which directly serves that job.
- Review reports `Complexity fit: PASS` or `Complexity fit: BLOCKED — <plain reason>`.
- A new framework, registry, schema, validator hierarchy, compatibility layer or governance surface not
  already required by the accepted contract needs Rob's approval before implementation.
- **No automated gate is created for this judgment.** It is a review duty, and a gate around it would be the
  first thing the rule forbids.

## Disposition

| Field | Disposition |
|---|---|
| Governance decisions added | `D-30` |
| Reopened fixed point | None |
| Contracts affected | Design, implementation and review process only; no semantic contract changes |
| Proof theorem or generated-byte guarantee changed | None |
| OCaml trust boundary changed | None |
| Target/toolchain policy changed | None |
| Human act added | None |
