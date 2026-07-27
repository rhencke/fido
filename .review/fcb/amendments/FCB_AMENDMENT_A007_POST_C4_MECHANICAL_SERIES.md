# FCB Amendment A007 — Post-C4 Mechanical Series

- **ID:** `FCB-A007-POST-C4-MECHANICAL-SERIES`
- **Status:** **ACCEPTED** — human owner Rob, token `FCB-A007-post-C4-mechanical-series`
- **Author:** Primary ChatGPT Fido review thread
- **Committer:** Claude Code (applied the amendment; authored nothing in it)
- **Date:** `2026-07-26`
- **Reviewed repository ref:** `0ffdc5f7019204a868d75ef709a16fb69a9979d5`

The source human direction, in the authoritative primary review thread, was *"Next round let's install the M
series in the repo regardless of review."* Rob then confirmed the resulting sequence and the strict comment
rule. No further human confirmation is required to install A007.

## New information

The repository carries a large amount of source prose, proof text and ad hoc build tooling. Much of the prose
records superseded design history that Git already preserves. Full builds approach two to three minutes, and
the project lacks one measured account of module cost, dependency fan-out, edit frequency, cache behaviour and
duplicated gate work. Auxiliary tools and Make/Buildx duties have accumulated without one owned build
architecture.

This mechanical debt raises review cost, model-token cost, feedback time, and the risk that stale prose hides
the current system. The permanent C5 `Machine` base should not be frozen on top of that avoidable debt.

## Settled sequence

After C4 acceptance, and before checkpoint-definition Step 0 for C5:

```text
C4 acceptance closeout
→ M1 Source Diet
→ M2 Build Observatory
→ M3 Tool and Build Architecture Audit
→ Rob approves the exact M4 plan
→ M4 Mechanical Refactor
→ checkpoint-definition Step 0
→ C5 Machine base
```

While C4 remains unaccepted, M1, M2, M3 and M4 implementation are forbidden. Installing this amendment and the
M-series plan does not authorize their implementation.

## Governance decision added

**D-27 — Mechanical debt is removed before the permanent runtime base.** (Exact text in
`FIDO_FCB_GOVERNANCE.md`.)

## Scope

| Field | Disposition |
|---|---|
| Governance decision | Add `D-27` |
| Roadmap | Insert M1–M4 between C4 closeout and C5 Step 0 |
| Fixed points | None reopened; M1–M4 must preserve all |
| Closure rows | None changed |
| Latitude rows | None changed |
| Acceptance-gate rows | None changed |
| Go meaning | Unchanged |
| Accepted/rejected program sets | Unchanged |
| Diagnostics | Unchanged |
| Public theorem guarantees | Must not weaken |
| Generated Go | Byte-identical through M1–M4 |
| Target/toolchain policy | Unchanged |
| OCaml trust boundary | Unchanged |
| Human act | Add deferred `M4-PLAN-APPROVAL` |
| New live authority | The M-series plan under `.review/` |

C4 remains **NOT accepted**. Only Rob accepts it. C5, checkpoint-definition Step 0, post-C4 features, the
broad source cleanup and proof-module partitioning remain forbidden.
