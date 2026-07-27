# FCB Amendment A008 — Strict Checkpoint Scope and M0 Closeout

- **ID:** `FCB-A008-STRICT-CHECKPOINT-SCOPE-AND-M0-CLOSEOUT`
- **Status:** **ACCEPTED** — human owner Rob, token `FCB-A008-strict-checkpoint-scope-and-M0-closeout`
- **Author:** Primary ChatGPT Fido review thread
- **Committer:** Claude Code (applied the amendment; authored nothing in it)
- **Date:** `2026-07-27`
- **Reviewed repository ref:** `39ea7e3b012ec798c6a756c971c10bb363557ef8`

Rob accepted the substance in the primary review thread on 2026-07-27 by directing that the strict scope rule
enter the next round and that work move to M0 with scope creep limited.

## New information

Requiring all useful repository and FCB infrastructure work to finish before the next checkpoint can enlarge a
semantic checkpoint without changing its accepted result. C4 showed it directly: the semantic capability was
complete for many rounds while governance hardening continued, and each round's findings were real but were
not findings against C4's accepted contract.

## Settled rule

A checkpoint blocks only on defects within its accepted contract or an explicit acceptance dependency. Wider
findings are assigned to the earliest mandatory follow-up and cannot silently disappear. M0 performs the
post-C4 governance closeout before M1.

## Governance decisions added

**D-28 — A checkpoint blocks only on its accepted contract.**
**D-29 — M0 closes governance after C4 without reopening C4.**

Exact text in `FIDO_FCB_GOVERNANCE.md`.

## Settled sequence

```text
C4 acceptance closeout → M0 Governance Closeout → M1 → M2 → M3 → Rob approves the M4 plan → M4
→ checkpoint-definition Step 0 → C5
```

## Scope

| Field | Disposition |
|---|---|
| Reopened fixed point | None |
| Contracts affected | Review and checkpoint-authoring process only; no semantic contract changes |
| Checkpoints affected | C4 is accepted; M0 is inserted before M1; C5 remains after M4 |
| Closure / latitude / standing acceptance-gate rows changed | None |
| Target/toolchain policy changed | None |
| Proof theorem or generated-byte guarantee changed | None |
| OCaml trust boundary changed | None |

C4 is **ACCEPTED** at `39ea7e3b012ec798c6a756c971c10bb363557ef8` under the human disposition
`C4-ACCEPT-39ea7e3`. M1 through M4 and C5 remain forbidden until M0 is separately accepted.
