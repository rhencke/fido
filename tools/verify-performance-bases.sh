#!/bin/sh
# Verify the measurement-basis registry against Git: every row's basis_digest must equal
# performance-input-digest --commit source_commit (computed via a throwaway index; the real index and
# working tree are never touched).  The Git object database is the host boundary's authority, so this
# verification runs host-side; the Python engine owns every other registry law.
#
#   tools/verify-performance-bases.sh [registry-file]      verify each row (default .review/perf/performance-bases.tsv)
#   tools/verify-performance-bases.sh --self-test          a forged row and a wrong-commit row must be rejected
#
# The digest algorithm is the CO-LOCATED tools/performance-input-digest.sh (so the staged hook verifies with
# the staged algorithm), while the Git object database is the caller's repository — the staged export has no
# .git, exactly like the digest script itself, which resolves Git from the caller's toplevel.
set -eu
tooldir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$(git rev-parse --show-toplevel)"

verify() {
  reg=$1
  rc=0
  while IFS="$(printf '\t')" read -r d c _rest; do
    case "$d" in \#*|basis_digest|'') continue ;; esac
    got=$(sh "$tooldir/performance-input-digest.sh" --commit "$c" 2>/dev/null) || {
      echo "verify-performance-bases: cannot digest commit $c" >&2; rc=1; continue; }
    [ "$got" = "$d" ] || {
      echo "verify-performance-bases: basis ${d} does not match commit ${c} (actual ${got})" >&2; rc=1; }
  done < "$reg"
  return $rc
}

if [ "${1:-}" = "--self-test" ]; then
  tmp=$(mktemp); trap 'rm -f "$tmp"' EXIT
  head_commit=$(git rev-parse HEAD)
  head_digest=$(sh "$tooldir/performance-input-digest.sh" --commit "$head_commit")
  # (1) a correct row passes
  printf 'basis_digest\tsource_commit\tt\ts\tp\tn\n%s\t%s\tONE_DAG_V1\tCURRENT\tx\ty\n' \
    "$head_digest" "$head_commit" > "$tmp"
  verify "$tmp" || { echo "verify-performance-bases self-test FAILED — a correct row was rejected"; exit 1; }
  # (2) a forged digest must be rejected
  printf 'basis_digest\tsource_commit\tt\ts\tp\tn\n%s\t%s\tONE_DAG_V1\tCURRENT\tx\ty\n' \
    "$(printf 'f%.0s' 1 2 3 4 5 6 7 8)$(echo "$head_digest" | cut -c9-)" "$head_commit" > "$tmp"
  if verify "$tmp" 2>/dev/null; then
    echo "verify-performance-bases self-test FAILED — a forged basis digest was accepted"; exit 1; fi
  # (3) a valid digest paired with the wrong commit must be rejected — walk back to a commit whose
  # performance-input digest actually differs (evidence-only commits share the digest by design)
  parent=''
  for back in 1 2 3 4 5 6 7 8 9 10; do
    cand=$(git rev-parse "HEAD~$back" 2>/dev/null) || break
    [ "$(sh "$tooldir/performance-input-digest.sh" --commit "$cand")" = "$head_digest" ] || { parent=$cand; break; }
  done
  [ -n "$parent" ] || { echo "verify-performance-bases self-test FAILED — no digest-distinct commit within 10 ancestors"; exit 1; }
  printf 'basis_digest\tsource_commit\tt\ts\tp\tn\n%s\t%s\tONE_DAG_V1\tCURRENT\tx\ty\n' \
    "$head_digest" "$parent" > "$tmp"
  if verify "$tmp" 2>/dev/null; then
    echo "verify-performance-bases self-test FAILED — a wrong-commit pairing was accepted"; exit 1; fi
  # (4) the real index is untouched by --commit digesting
  before=$(git ls-files -s | sha256sum)
  sh "$tooldir/performance-input-digest.sh" --commit "$parent" > /dev/null
  after=$(git ls-files -s | sha256sum)
  [ "$before" = "$after" ] || { echo "verify-performance-bases self-test FAILED — the real index moved"; exit 1; }
  echo "fido: verify-performance-bases self-test OK — correct row accepted; forged digest and wrong-commit pairing rejected; the real index untouched"
  exit 0
fi

verify "${1:-.review/perf/performance-bases.tsv}" \
  && echo "fido: performance-bases OK — every registered basis digest reproduces from its exact source commit"
