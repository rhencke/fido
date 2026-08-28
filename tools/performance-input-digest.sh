#!/bin/sh
# The canonical performance-input digest.
#
# A single deterministic SHA-256 over the EXACT tracked performance-relevant input set: every tracked file —
# by Git mode, blob identity and path, in one stable byte order — EXCEPT the two performance-evidence files
# themselves.  It therefore binds every final non-evidence byte (source, proofs, fixtures, Dune, Dockerfile,
# Makefile, hooks, tools/gates, e2e, generated/golden inputs, governing files, and this digest + the evidence
# validator) so a measurement can reference the exact content it was taken on without the impossible
# self-reference of a tree hash that includes the evidence file recording it.
#
# Excluded (and ONLY these): .review/PERFORMANCE.tsv, .review/PERFORMANCE_OPPORTUNITIES.tsv.  Nothing else is
# excluded to make the digest stable — an omission there would be an unsafe exclusion (contract §20.1, §30.14).
#
# `git ls-files -s` prints "<mode> <blob-sha> <stage>\t<path>"; the blob-sha is Git's content address, so the
# digest changes iff any included file's bytes, mode, or path changes.  It reads the INDEX, which equals the
# working tree and HEAD on the clean, committed state under which the gate and the freeze discipline run.
set -eu
cd "$(git rev-parse --show-toplevel)"
git ls-files -s -- \
    ':(exclude).review/PERFORMANCE.tsv' \
    ':(exclude).review/PERFORMANCE_OPPORTUNITIES.tsv' \
  | LC_ALL=C sort -k4 \
  | sha256sum \
  | cut -d' ' -f1
