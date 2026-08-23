#!/bin/sh
# The repository-owned make-check performance budget decision, in one place.
#
# Usage:  check-budget.sh <elapsed_seconds> <budget_seconds>
#   exit 0  — elapsed <= budget (within budget)
#   exit 1  — elapsed >  budget (over budget); prints the required guidance on stderr
#   exit 3  — malformed or missing input (fail closed; never treated as within-budget)
#
# `make check` measures a warmed successful run and calls this with the one budget owner
# (Makefile CHECK_BUDGET_SECONDS).  `.review/PERFORMANCE.tsv` is a diagnostic written by
# `make perf`; it is NOT consulted here and is not the live gate authority.
#
# --self-test runs the decision's own controls and exits nonzero if any misbehaves.
set -eu

is_nat () { case "$1" in ''|*[!0-9]*) return 1 ;; *) return 0 ;; esac; }

decide () {
  el=$1; bud=$2
  if ! is_nat "$el" || ! is_nat "$bud"; then
    echo "check-budget: malformed timing (elapsed='$el' budget='$bud') — failing closed" >&2
    return 3
  fi
  if [ "$el" -le "$bud" ]; then
    return 0
  fi
  # over budget — emit the required guidance verbatim (budget substituted from the one owner)
  cat >&2 <<MSG

PERFORMANCE BUDGET EXCEEDED

make check: ${el}s
budget:     ${bud}s

Do not continue semantic implementation.

Profile the dominant stage / changed Rocq files.
Optimize the existing certified path.
Do not skip, weaken, sample, or move required gates outside make check.

If restoring the budget requires changing a trusted boundary,
semantic architecture, or verification requirement:
STOP_FOR_ROB.
MSG
  return 1
}

self_test () {
  fails=0
  chk () { # description  expected_rc  args...
    d=$1; want=$2; shift 2
    out=$(decide "$@" 2>&1) && rc=0 || rc=$?
    if [ "$rc" != "$want" ]; then echo "check-budget self-test FAIL: $d (rc=$rc want=$want)"; fails=1; fi
    printf '%s\n' "$out" > /dev/null
  }
  chk "within budget"            0 20 120
  chk "exactly at budget"        0 120 120
  chk "one over budget"          1 121 120
  chk "tiny budget fails closed" 1 20 0
  chk "malformed elapsed"        3 abc 120
  chk "malformed budget"         3 20 xx
  chk "empty elapsed"            3 "" 120
  # the over-budget guidance must carry the exact heading and the STOP_FOR_ROB escalation
  msg=$(decide 200 120 2>&1 || true)
  printf '%s\n' "$msg" | grep -q '^PERFORMANCE BUDGET EXCEEDED$' || { echo "check-budget self-test FAIL: missing heading"; fails=1; }
  printf '%s\n' "$msg" | grep -q '^STOP_FOR_ROB\.$' || { echo "check-budget self-test FAIL: missing STOP_FOR_ROB"; fails=1; }
  printf '%s\n' "$msg" | grep -q 'move required gates outside make check' || { echo "check-budget self-test FAIL: missing gate-integrity line"; fails=1; }
  if [ "$fails" = 0 ]; then
    echo "fido: check-budget self-test OK — within/at/over/tiny/malformed/empty decisions + required guidance all correct"
  fi
  return "$fails"
}

case "${1:-}" in
  --self-test) self_test ;;
  *) [ $# -eq 2 ] || { echo "usage: check-budget.sh <elapsed_seconds> <budget_seconds>" >&2; exit 3; }
     decide "$1" "$2" ;;
esac
