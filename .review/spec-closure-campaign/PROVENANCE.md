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

**What is here versus what is in history.** The working tree keeps ONE living representative of the directive
and of the volley protocol, renamed to unversioned filenames and edited to remove name-versioning and
documentation checksums. Those working-tree files are therefore **not** byte-preserved and **not** append-only.
The exact earlier revisions — eleven directives and two protocols, with their original bytes, filenames and
supersedes-by-hash chains intact — are retained in Git history and recoverable from it.

`reviews/` and the dated volley briefs under `protocol/` are unchanged historical records. Their literal command
transcripts are left exactly as written, hashes included: editing a recorded `sha256sum` transcript would
falsify evidence of what actually ran.

Nothing here is current authority. The live Fido Conformance Basis is `.review/fcb/current/`; the live
checkpoint authority is `.review/NEXT_STEPS.md`; the code and its gated theorems are the sole implementation
authority.

## External artifacts (not in this repository)

The campaign was carried in ZIP packages (`FIDO_VOLLEY_SEND`, `FIDO_VOLLEY_SEND_2`, `FIDO_VOLLEY_RETURN_2`)
against the `FIDO_GO1_23_SPEC_CLOSURE_REVIEW_BUNDLE_R1` baseline. Those archives are not checksummed here: a
ZIP carries a CRC-32 per entry and validates itself on extraction, and per Rob's mandate nothing
documentation-related is checksummed in this repository.
