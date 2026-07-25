# Spec-Closure Campaign — July 2026 (historical record + toolkit)

The record of the Go 1.23 spec-closure campaign: the terminal-correctness directive the adversarial review
converged on, the volley protocol and its adjudications, the founding reviews, the FCB transformation
instructions, and the campaign toolkit.

**Authority.** Nothing here is current authority. The live Fido Conformance Basis is `.review/fcb/current/`;
the live checkpoint authority is `.review/NEXT_STEPS.md`; the code and its gated theorems are the sole
implementation authority.

**Living names, no checksums.** Per Rob's mandate, documentation is neither versioned by filename nor
checksummed. `directives/FIDO_TERMINAL_CORRECTNESS_DIRECTIVE.md` is the executable authority the campaign
reached; its eleven earlier revisions, and the two superseded volley protocols, are retired from the working
tree and live in Git history. Git content-addresses everything here, the commit log is the history, and the
identity of this tree is `git rev-parse HEAD:.review/spec-closure-campaign`.

**Toolkit.** `tools/` holds the campaign scripts. The implemented ones run today; the `[BUNDLE]` stubs raise
`SystemExit` with their exact remaining duty quoted from the directive, so nothing pretends to work. They were
last exercised against the R1 baseline on 2026-07-24 — a claim not reproducible from this directory alone,
since that baseline is an external artifact and is not stored here.

**Historical records are not rewritten.** The dated documents under `protocol/` and `reviews/` quote literal
command transcripts. Their contents stand as written: editing a recorded `sha256sum` transcript would falsify
evidence of what actually ran.

See `PROVENANCE.md` and `COLLABORATION.md`.
