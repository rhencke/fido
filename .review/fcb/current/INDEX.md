# Current Fido Conformance Basis — Stable Git Bootstrap

Git is the sole canonical FCB store. This stable file is the entry point for models and tools.

- **Current versioned Index:** `FIDO_FCB_INDEX_v3.md`
- **Current manifest:** `FIDO_FCB_MANIFEST.sha256`
- **Verification tool:** `../tools/verify_current_fcb.py`
- **Live checkpoint authority:** `../../NEXT_STEPS.md`

Use all files from one exact Git ref. If a task specifies a candidate commit or repository snapshot, use that exact
ref. Otherwise use the latest accessible `main`. Never mix FCB files across refs.

From the repository root, verify with:

```sh
python3 .review/fcb/tools/verify_current_fcb.py
```

Project libraries contain bootstrap shims only. They are not FCB authority.
