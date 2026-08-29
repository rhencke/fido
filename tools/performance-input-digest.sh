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
# Excluded (and ONLY these): .review/PERFORMANCE.tsv, .review/PERFORMANCE_OPPORTUNITIES.tsv, and the
# detailed measurement tables under .review/perf/ — every one a performance-evidence file recording
# measurements OF the digested content (the impossible self-reference).  Nothing else is excluded to make
# the digest stable — an omission there would be an unsafe exclusion.
#
# `git ls-files -s` prints "<mode> <blob-sha> <stage>\t<path>"; the blob-sha is Git's content address, so the
# digest changes iff any included file's bytes, mode, or path changes.  It reads the INDEX, which equals the
# working tree and HEAD on the clean, committed state under which the gate and the freeze discipline run.
# `--head` digests the SAME input set at the committed HEAD instead of the index, through the identical
# byte pipeline (HEAD read into a throwaway index), so an index digest and a HEAD digest are comparable:
# equal iff no included byte differs between the proposed and the committed tree.
set -eu
cd "$(git rev-parse --show-toplevel)"
if [ "${1:-}" = "--head" ]; then
  GIT_INDEX_FILE=$(mktemp); export GIT_INDEX_FILE
  trap 'rm -f "$GIT_INDEX_FILE"' EXIT
  git read-tree HEAD
fi
git ls-files -s -- \
    ':(exclude).review/PERFORMANCE.tsv' \
    ':(exclude).review/PERFORMANCE_OPPORTUNITIES.tsv' \
    ':(exclude).review/perf/*' \
  | LC_ALL=C sort -k4 \
  | sha256sum \
  | cut -d' ' -f1
