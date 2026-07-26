# Source Forest Campaign — Status Ledger

Campaign: **Specification-Shaped Source Forest, Snapshot-Local Occurrence Identity, and Occurrence-Anchored
Compilation.** The full design is `.review/SOURCE_FOREST_MASTER_PLAN.md`.

**This file does not own current state.** One thing owns each:

| Question | Owner |
|---|---|
| Which candidate is current, what is its status, which repair is active, what is the freeze head | `.review/NEXT_STEPS.md` |
| What is still open for Rob | `.review/fcb/current/FIDO_FCB_HUMAN_ACTS.tsv` (generated view: the Human Review Index) |
| Checkpoint order and stable dependencies | `.review/fcb/current/FIDO_FCB_ROADMAP.md` |
| What is proved, and the retained architecture | `PROGRESS.md` and `ARCHITECTURE.md` |
| Settled decisions, ADRs, amendments | `.review/fcb/current/FIDO_FCB_GOVERNANCE.md` |
| Superseded candidate lists, per-repair theorem tables, prior repair narratives | `git log` |

Nothing here restates any of those. A second roster of the same facts is a second authority, and the two drift.

## Completed checkpoints

- **C0–C3 GREEN and accepted by Rob.** C0 preflight + proof spike; C1 spec-shaped file roots + path-keyed
  file map; C2 production `Index` + `NodeRef` navigation; C3 occurrence-anchored diagnostics and the
  fresh-image literal-build closeout, accepted at the original C4 baseline `8c9212a`.
- **C4 is NOT accepted.** Only Rob accepts it. C5 and the post-C4 trim remain forbidden until he does.

## Durable campaign lessons

These are recorded here because they are about how this campaign has gone wrong, not about any one checkpoint.
The design law they feed is in `ARCHITECTURE.md`; the traps are in `PAINFUL_LESSONS.md`.

- **Verification does not inspect topology.** A green proof says the stated theorem holds; it says nothing
  about whether the statement was the right one. Repeatedly, the defect was a true theorem that claimed less
  than the prose around it. Read the retention shape, not the verdict.
- **A checker cannot report what it never parsed.** The naming gate had two must-accept controls passing
  vacuously because its extractor never reached the constructor after `:=`. A control that passes because the
  parser is blind is indistinguishable from one that passes because the rule holds. Every must-fail control
  now pins the REASON it must fail on.
- **A retained object makes identity a `reflexivity`.** Every time a builder disappeared from a proof, the
  proof got smaller. An equality to a rerun is provenance theatre — it is a receipt for an object nobody kept.
