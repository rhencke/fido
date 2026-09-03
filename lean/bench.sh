#!/bin/sh
# Per-module timing for the Lean POC: after `lake build` has produced every dependency, compile each module
# listed in Fido.lean ALONE, one `lean` process at a time, in import order — the analogue of the Rocq
# per-file sweep (`make profile FILE=X.v` per module).  Prints a TSV: module, wall seconds, exit status.
set -eu
lake build > /tmp/lake-build.log 2>&1 || { cat /tmp/lake-build.log; echo "fido-lean bench: lake build FAILED"; exit 1; }
L="$(pwd)/.lake/build/lib/lean"; [ -d "$L" ] || L="$(pwd)/.lake/build/lib"
export LEAN_PATH="$L"
printf 'module\twall_s\trc\n'
total=0
for m in $(grep -oE '^import Fido\.[A-Za-z.]+' Fido.lean | sed 's/^import //'); do
  f="$(echo "$m" | tr . /).lean"
  s=$(date +%s.%N)
  if lean -o /tmp/bench.olean -i /tmp/bench.ilean "$f" > /tmp/bench.log 2>&1; then rc=0; else rc=$?; fi
  e=$(date +%s.%N)
  w=$(awk -v a="$s" -v b="$e" 'BEGIN { printf "%.2f", b - a }')
  total=$(awk -v t="$total" -v w="$w" 'BEGIN { printf "%.2f", t + w }')
  printf '%s\t%s\trc=%s\n' "$m" "$w" "$rc"
  [ "$rc" = 0 ] || { cat /tmp/bench.log; }
done
printf 'TOTAL\t%s\n' "$total"
