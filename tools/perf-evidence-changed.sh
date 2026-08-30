#!/bin/sh
# Prints `yes` iff the STAGED performance evidence changes a CURRENT-basis measurement or the currency
# itself — the projections a fabricated, promoted, or re-measured CURRENT claim must move:
#   1. which basis is CURRENT (the registry's CURRENT basis_digest);
#   2. the PERFORMANCE.tsv measurement tuples of rows bound to the CURRENT basis
#      (scenario, relation, run_id, exit, wall_s, complete);
#   3. the event-table timing tuples of rows on the CURRENT basis (run_id, event_id, start/end/elapsed);
#   4. the sentence-table rows on the CURRENT basis (file, secs, population).
# Historical re-expression stays `no`: adding schema columns (clock/resolution), reclassifying an already
# measured historical run as the comparison baseline, or deleting a superseded historical graph does not
# touch any CURRENT-basis measurement, so it lives honestly in the historical frame while any new or
# altered CURRENT measurement — or a flip of which basis is CURRENT — must bind to the exact staged basis.
# One authority: make perf-evidence and the staged hook both call this.  Historical bases are anchored by
# verify-performance-bases (digest reproduces from its source commit) and by the event graph's own terminal
# wall (§5.1), so a fabricated historical measurement is caught there, not here.
set -eu
cd "$(git rev-parse --show-toplevel)"
show() { git show "$1" 2>/dev/null || true; }
cur_basis() {
  show "$1:.review/perf/performance-bases.tsv" \
    | awk -F'\t' '!/^#/ && NF>3 && $4=="CURRENT" {print $1}'
}
proj() {
  ref=$1; cb=$2
  printf 'CURRENT=%s\n' "$cb"
  show "$ref:.review/PERFORMANCE.tsv" \
    | awk -F'\t' -v cb="$cb" '!/^#/ && NF>1 && $3==cb {print "P\t"$1"\t"$2"\t"$15"\t"$10"\t"$11"\t"$12}'
  show "$ref:.review/perf/verification-dag-events.tsv" \
    | awk -F'\t' -v cb="$cb" '!/^#/ && NF>1 && $1==cb {print "E\t"$3"\t"$4"\t"$8"\t"$9"\t"$10}'
  show "$ref:.review/perf/witnessreject-sentences.tsv" \
    | awk -F'\t' -v cb="$cb" '!/^#/ && NF>1 && $1==cb {print "S\t"$2"\t"$3"\t"$4}'
}
a=$(proj '' "$(cur_basis '')" | LC_ALL=C sort)
b=$(proj HEAD "$(cur_basis HEAD)" | LC_ALL=C sort)
if [ "$a" = "$b" ]; then echo no; else echo yes; fi
