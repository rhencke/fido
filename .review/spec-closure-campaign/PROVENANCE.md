# Provenance — spec-closure campaign

Per Rob's standing rule (FCB amendment A003 and after): **documentation is not checksummed.** Git
content-addresses every file in this tree, the commit log is its history, and the identity of the whole
directory is its tree hash:

```sh
git rev-parse HEAD:.review/spec-closure-campaign
```

The former per-file SHA-256 table and `MANIFEST.sha256` are retired. They restated, by hand, a guarantee Git
already provides — and imposed a regeneration duty on every edit to a frozen tree that is not supposed to
change anyway.

## What this tree is

The frozen record of the July 2026 Go 1.23 spec-closure campaign: the terminal-correctness directive lineage
(`directives/FIDO_TERMINAL_CORRECTNESS_DIRECTIVE.md` is the executable authority the campaign reached; its
earlier revisions are retired from the working tree and live in Git history), the volley
protocols and adjudications, the founding reviews, the FCB transformation instructions, and the campaign
toolkit.

`directives/`, `protocol/` and `reviews/` are **frozen and append-only** — byte-preserved evidence. Their
version numbers are identity, not staleness: v12's supersedes chain cites each predecessor by full SHA-256
inside the documents themselves, so the lineage remains self-describing without an external manifest.

Nothing here is current authority. The live Fido Conformance Basis is `.review/fcb/current/`; the live
checkpoint authority is `.review/NEXT_STEPS.md`; the code and its gated theorems are the sole implementation
authority.

## External artifacts (not in this repository)

The campaign was carried in ZIP packages (`FIDO_VOLLEY_SEND`, `FIDO_VOLLEY_SEND_2`, `FIDO_VOLLEY_RETURN_2`)
against the `FIDO_GO1_23_SPEC_CLOSURE_REVIEW_BUNDLE_R1` baseline. Those archives are not checksummed here: a
ZIP carries a CRC-32 per entry and validates itself on extraction, and per Rob's mandate nothing
documentation-related is checksummed in this repository.
