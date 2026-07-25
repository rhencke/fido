# Current Fido Conformance Basis — Stable Git Bootstrap

Git is the sole canonical FCB store. This stable file is the entry point for models and tools.

- **Index:** `FIDO_FCB_INDEX.md`
- **Live checkpoint authority:** `../../NEXT_STEPS.md`

Use all files from one exact Git ref. If a task specifies a candidate commit or repository snapshot, use that exact
ref. Otherwise use the latest accessible `main`. Never mix FCB files across refs.

These are living documents. Git is the integrity mechanism: the blob hash is the version, the commit log is the
history, and the identity of the whole live set is its tree hash:

```sh
git rev-parse HEAD:.review/fcb/current
```

Project libraries contain bootstrap shims only. They are not FCB authority.
