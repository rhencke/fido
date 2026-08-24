#!/bin/sh
# The repository-owned make-check performance budget — decision AND the one production constant, in one place.
#
# The budget value lives ONLY here (BUDGET_SECONDS): there is no Make variable and no second constant, so an
# ordinary `make CHECK_BUDGET_SECONDS=… check` cannot raise it.  Both `make check` and the pre-commit hook time
# a warmed successful verification and call `check-budget.sh <elapsed>`; the budget they apply is this one.
# `.review/PERFORMANCE.tsv` is a `make perf` diagnostic and is NOT consulted here.
#
# Usage:
#   check-budget.sh <elapsed_seconds>   exit 0 within budget · exit 1 over (prints guidance) · exit 3 malformed
#   check-budget.sh --budget            print the production budget in seconds
#   check-budget.sh --self-test         run the decision's own adversarial controls
set -eu

BUDGET_SECONDS=120

is_nat () { case "$1" in ''|*[!0-9]*) return 1 ;; *) return 0 ;; esac; }

# decide <elapsed> <budget>: the pure decision, parameterised on the budget so --self-test can drive it with
# synthetic values without a test override ever reaching production (production always passes BUDGET_SECONDS).
decide () {
  el=$1; bud=$2
  if ! is_nat "$el" || ! is_nat "$bud"; then
    echo "check-budget: malformed timing (elapsed='$el' budget='$bud') — failing closed" >&2
    return 3
  fi
  [ "$el" -le "$bud" ] && return 0
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
  chk () { d=$1; want=$2; shift 2; out=$(decide "$@" 2>&1) && rc=0 || rc=$?
    [ "$rc" = "$want" ] || { echo "check-budget self-test FAIL: $d (rc=$rc want=$want)"; fails=1; }; printf '%s' "$out" >/dev/null; }
  chk "within budget"            0 20 120
  chk "exactly at budget"        0 120 120
  chk "one over budget"          1 121 120
  chk "tiny budget fails closed" 1 20 0
  chk "malformed elapsed"        3 abc 120
  chk "malformed budget"         3 20 xx
  chk "empty elapsed"            3 "" 120
  # the production entry point uses the owned budget and no caller override can widen it
  out=$(decide 200 "$BUDGET_SECONDS" 2>&1 || true)
  printf '%s\n' "$out" | grep -q '^PERFORMANCE BUDGET EXCEEDED$' || { echo "check-budget self-test FAIL: missing heading"; fails=1; }
  printf '%s\n' "$out" | grep -q '^STOP_FOR_ROB\.$' || { echo "check-budget self-test FAIL: missing STOP_FOR_ROB"; fails=1; }
  printf '%s\n' "$out" | grep -q 'move required gates outside make check' || { echo "check-budget self-test FAIL: missing gate-integrity line"; fails=1; }
  [ "$BUDGET_SECONDS" = 120 ] || { echo "check-budget self-test FAIL: production budget is not 120"; fails=1; }
  [ "$fails" = 0 ] && echo "fido: check-budget self-test OK — within/at/over/tiny/malformed/empty + guidance + owned 120s budget all correct"
  return "$fails"
}

case "${1:-}" in
  --self-test) self_test ;;
  --budget)    printf '%s\n' "$BUDGET_SECONDS" ;;
  *) [ $# -eq 1 ] || { echo "usage: check-budget.sh <elapsed_seconds> | --budget | --self-test" >&2; exit 3; }
     decide "$1" "$BUDGET_SECONDS" ;;
esac
