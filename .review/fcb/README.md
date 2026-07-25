# Fido Conformance Basis in Git

Git is the sole canonical home of the live FCB.

## Layout

- `current/` — the only live FCB corpus. Start at `current/INDEX.md`.
- `archive/project-library-v2/` — exact former project-library v2 set; provenance only.
- `amendments/` — accepted living-document amendments.
- `tools/verify_current_fcb.py` — verifies the current manifest and rejects extra live files.
- `PROJECT_LIBRARY_BOOTSTRAP.md` — exact bootstrap shim to place in ChatGPT or Claude project libraries.

Root `.review/NEXT_STEPS.md` remains the live checkpoint authority. Code and gated theorems remain the sole
implementation authority.

## Verify

From the repository root:

```sh
python3 .review/fcb/tools/verify_current_fcb.py
```

The current manifest-file SHA-256 at packaging time is `992ac96a18f86295b1c1a5ce256ab2601a7417da1e52db8b91e7e38674b44a28`.
