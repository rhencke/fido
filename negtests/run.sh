#!/bin/sh
# Fail-closed regression harness — the negative-fixture gate.
#
# Each negtests/*.v is a program that hits a fail-CLOSED backend site; its FIRST line declares
# `(* EXPECT: <substring> *)`, the message extraction MUST abort with.  We compile each one and
# assert it ABORTS with that message.  A negtest that SUCCEEDS (emits Go) means a fail-closed
# site REOPENED — emitting plausible-but-wrong Go where rule 2 demands a loud `unsupported`.
# That is exactly the defect class the happy-path golden CANNOT see.
#
# Run from the repo root AFTER `dune build` (needs the built Fido theory + plugin in _build).
# Requires a host `rocq` on PATH (like `make run-local` needs a host Go); the canonical Docker
# build is unaffected.
set -eu
[ -d _build/default ] || { echo "negtest: run 'dune build' first (need _build/default + _build/install)"; exit 1; }
export OCAMLPATH="$PWD/_build/install/default/lib"
fail=0
for v in negtests/*.v; do
  exp="$(sed -n '1s/^(\* EXPECT: \(.*\) \*)$/\1/p' "$v")"
  [ -n "$exp" ] || { echo "  FAIL $(basename "$v")  has no '(* EXPECT: … *)' first line"; fail=1; continue; }
  out="$(rocq compile -R _build/default Fido "$v" 2>&1 || true)"
  if printf '%s' "$out" | grep -qF "$exp"; then
    echo "  ok   $(basename "$v")  ->  aborts: $exp"
  else
    echo "  FAIL $(basename "$v")  did NOT abort with: $exp"
    printf '%s\n' "$out" | tail -3
    fail=1
  fi
done
rm -f negtests/*.vo negtests/*.glob neg_out.go 2>/dev/null || true
[ "$fail" -eq 0 ] || { echo "negtest: a fail-closed site REOPENED (emitting plausible-but-wrong Go) — rule-2 regression"; exit 1; }
echo "negtest: all fail-closed sites still abort (rule 2 holds) OK"
