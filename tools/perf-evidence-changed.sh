#!/bin/sh
# Prints `yes` iff the STAGED measurement content of .review/PERFORMANCE.tsv differs from HEAD's.
# The measurement projection is (scenario, relation, digest, exit, wall_s, complete) — the columns a
# fabricated or re-measured observation must move — so a pure schema or annotation re-expression stays
# in the honest historical frame while any added, removed, or altered measurement must bind to the
# exact staged basis.  One authority: make perf-evidence and the staged hook both call this.
set -eu
cd "$(git rev-parse --show-toplevel)"
proj() {
  git show "$1" 2>/dev/null \
    | awk -F'\t' '!/^#/ && NF>1 {print $1"\t"$2"\t"$3"\t"$10"\t"$11"\t"$12}' \
    | LC_ALL=C sort
}
a=$(proj ':.review/PERFORMANCE.tsv' || true)
b=$(proj 'HEAD:.review/PERFORMANCE.tsv' || true)
if [ "$a" = "$b" ]; then echo no; else echo yes; fi
