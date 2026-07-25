# Fido Conformance Basis in Git

Git is the sole canonical home of the live FCB.

## Layout

- `current/` — the only live FCB corpus. Start at `current/INDEX.md`.
- `amendments/` — accepted living-document amendments.
- `PROJECT_LIBRARY_BOOTSTRAP.md` — exact bootstrap shim to place in ChatGPT or Claude project libraries.

Root `.review/NEXT_STEPS.md` remains the live checkpoint authority. Code and gated theorems remain the sole
implementation authority.

## Identity

These are living documents with no version suffixes and no checksum manifest: Git already content-addresses
every byte. A document's version is its blob hash, its history is the commit log, and the identity of the whole
live set is its tree hash:

```sh
git rev-parse HEAD:.review/fcb/current
```

To compare two states of the corpus, diff the two refs (or, for a distributed ZIP, diff the extracted directories).
