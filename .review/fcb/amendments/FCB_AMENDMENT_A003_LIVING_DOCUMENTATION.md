# FCB Amendment A003 — Living Documentation: Git Is the Version and the Integrity Mechanism

- **ID:** `FCB-A003-LIVING-DOCUMENTATION`
- **Status:** ACCEPTED
- **Author:** Rob
- **Human owner:** Rob
- **Committer:** Claude Code (applied only; authored nothing in this amendment)
- **Date:** `2026-07-25`
- **Source repository basis:** `rhencke/fido@e6acfacc` (post-A002 Git-canonical FCB)
- **Superseded apparatus:** `.review/fcb/current/FIDO_FCB_MANIFEST.sha256`, `.review/fcb/tools/verify_current_fcb.py`

## New information

A002 made Git the sole canonical FCB store. Once that landed, the per-file SHA-256 manifest became redundant
with Git itself: Git content-addresses every blob, and a commit pins the whole tree. The manifest's original
justification — verifying a corpus that travelled out-of-band into model project libraries — was abolished by
A002, which reduced those libraries to bootstrap shims. Documentation now reaches a reviewer as a ZIP of the
repository, where one sidecar over the archive covers the whole set; per-file hashes inside it duplicate that
guarantee while adding a regeneration duty to every documentation edit.

The same reasoning retires version suffixes. A document's version is its blob hash; its history is the commit
log; two states are compared by diffing two refs, or two extracted directories for a distributed ZIP. Encoding
a version in the filename adds rename churn, dangling cross-references, and a second thing to keep in sync with
no information Git does not already hold.

## Settled rule

**Documentation is living.** The FCB corpus carries no version suffixes and no checksum manifest.

- **Version** of a document = its Git blob hash. **History** = the commit log.
- **Identity of the whole live set** = its tree hash, `git rev-parse HEAD:.review/fcb/current`. Terminal reports
  state the Git ref and that tree hash.
- **Integrity** = Git content addressing, within one exact ref. Every FCB document for a task is taken from that
  single ref; files are never mixed across refs.
- **Comparison** = `git diff` between refs, or a directory diff between extracted ZIPs.
- No document is renamed on change, so cross-references stay stable.

## Authority note

Rob authored this amendment and this rule. Claude Code applied it as Committer and did not originate it. In Git
terms: Rob is Author, Claude Code is Committer. Claude Code may run documentation tooling to validate changes;
it may not author, version, or self-accept documentation.

## Effects

- Deletes `FIDO_FCB_MANIFEST.sha256` and `verify_current_fcb.py` (and the now-empty `tools/`).
- Renames all fourteen live FCB documents to unversioned filenames.
- Removes `Supersedes:` banner lines (Git history is the supersession record) and replaces the per-document
  version field with a living-document line.
- Rewrites every live cross-reference, the stable bootstrap, `README.md`, `PROJECT_LIBRARY_BOOTSTRAP.md`,
  Governance D-23, Model Operations, the Checkpoint Authoring Guide's publication duty, and the Index update law.
- Updates the root `CLAUDE.md` bootstrap block to match, and records the Committer-not-Author rule there.
- In `FIDO_FCB_FIXED_POINTS.md`, the ARCH-03 `static-capability-provenance` component's paths become the
  unversioned charter filename on both sides. The selector and protected projection are unchanged; baseline and
  terminal are now distinguished by **ref**, which is precisely the living-document model.

## Deliberately unchanged

- `amendments/A001` and `A002` keep their recorded manifest hashes: those are historical statements of what was
  true when they were accepted, not live pointers.
- `.review/fcb/archive/**` stays byte-exact as frozen provenance, version suffixes included.
- `.review/spec-closure-campaign/**` keeps its manifest: it records the integrity of an actual out-of-band ZIP
  transfer and is provenance, not live documentation.
- Governance D-16's "SHA manifest" refers to the **terminal bundle's** manifest, a different artifact, and is
  untouched.
- No Closure Ledger row, Latitude Ledger row, Acceptance Gate, fixed-point count, roadmap row assignment,
  checkpoint order, Go-language meaning, proof contract, or target/toolchain policy changes.
