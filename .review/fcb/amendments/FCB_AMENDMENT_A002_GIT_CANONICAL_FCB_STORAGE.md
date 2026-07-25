# FCB Amendment A002 — Git Is the Sole Canonical FCB Store

- **ID:** `FCB-A002-GIT-CANONICAL-FCB-STORAGE`
- **Status:** ACCEPTED
- **Human owner:** Rob
- **Date:** `2026-07-25`
- **Source repository basis:** `rhencke/fido@ece4c1dd0797eff6e9ebdd5d77a0e59f1c9e76e0`

## New information

Maintaining full editable FCB copies in multiple model project libraries creates unnecessary duplication,
synchronization work, and a material risk that different model conversations consult different bytes.

## Settled rule

Git is the sole canonical home of the live FCB. The live corpus is committed under `.review/fcb/current/`.
Model project libraries contain one small bootstrap shim only. The shim is not authority; it directs the model
to the current Git corpus. Root `CLAUDE.md` gives Claude Code the same bootstrap rules.

Every serious Fido task resolves one exact Git ref, reads `.review/fcb/current/INDEX.md`, verifies the current
manifest, reads `.review/NEXT_STEPS.md`, and consults the documents named by the current FCB Index. When the task
specifies a candidate commit or uploaded repository snapshot, that exact ref owns the documents for that task;
otherwise the latest accessible `main` is used. FCB files from different refs are never mixed.

If Git or the exact repository snapshot is unavailable, or manifest verification fails, the model stops and
reports the documentation-access defect. It does not answer from stale project-library files or memory.

## Effects

- Adds Governance decision `D-23`.
- Changes the distribution and update rules in every live FCB document banner.
- Changes Index, Governance, Model Operations, Checkpoint Authoring Guide, and Human Review Index body text.
- Adds a stable Git bootstrap at `.review/fcb/current/INDEX.md`.
- Adds `.review/fcb/tools/verify_current_fcb.py`.
- Requires a matching FCB bootstrap block in root `CLAUDE.md`.
- Archives the exact former project-library v2 set in Git.

No Go-language meaning, proof contract, fixed-point count, Closure row, Latitude row, Acceptance Gate, roadmap
row assignment, checkpoint order, or target/toolchain policy changes.

## Installed corpus identity

- **Canonical path:** `.review/fcb/current/` (the corpus is no longer version-labelled; see A003)
