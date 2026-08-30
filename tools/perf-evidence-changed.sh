#!/bin/sh
# Prints `yes` iff the STAGED performance-evidence CONTENT differs from HEAD's — the projections a
# fabricated, promoted, or re-measured claim must move:
#   1. the PERFORMANCE.tsv measurement projection (scenario, relation, digest, exit, wall_s, complete);
#   2. the registry's (basis_digest, status) set — flipping or adding a CURRENT basis is a publication;
#   3. the event-table data rows;
#   4. the sentence-table data rows.
# Comments, annotations, schema columns outside the projection, and topology relabels of unchanged
# bases stay `no`, so an honest re-expression lives in the historical frame while any measurement or
# currency change must bind to the exact staged basis.  One authority: make perf-evidence and the
# staged hook both call this.
set -eu
cd "$(git rev-parse --show-toplevel)"
show() { git show "$1" 2>/dev/null || true; }
differs() { [ "$1" != "$2" ]; }
p_perf() {
  show "$1:.review/PERFORMANCE.tsv" \
    | awk -F'\t' '!/^#/ && NF>1 {print $1"\t"$2"\t"$3"\t"$10"\t"$11"\t"$12}' | LC_ALL=C sort
}
p_reg() {
  show "$1:.review/perf/performance-bases.tsv" \
    | awk -F'\t' '!/^#/ && NF>3 && $1!="basis_digest" {print $1"\t"$4}' | LC_ALL=C sort
}
p_data() {
  show "$1:$2" | grep -v '^#' || true
}
if differs "$(p_perf '')" "$(p_perf HEAD)" \
   || differs "$(p_reg '')" "$(p_reg HEAD)" \
   || differs "$(p_data '' .review/perf/verification-dag-events.tsv)" \
              "$(p_data HEAD .review/perf/verification-dag-events.tsv)" \
   || differs "$(p_data '' .review/perf/witnessreject-sentences.tsv)" \
              "$(p_data HEAD .review/perf/witnessreject-sentences.tsv)"; then
  echo yes
else
  echo no
fi
