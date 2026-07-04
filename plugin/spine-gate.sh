#!/bin/sh
# THE ONE spine-gate authority: compile the trust-boundary SOURCE SET standalone and assert
# ZERO axioms (grep '^Axioms:' over the one log every compile writes to).  Called by BOTH the
# Dockerfile prover stage and the Makefile local mirrors — a single definition, no drift path.
#   mode: printer (digits GoAst GoPrint — leaves the extracted printer.ml in CWD)
#         emit    (the printer set + GoTypes GoSafe GoEmit)
set -eu
mode="$1"; log="$2"
case "$mode" in
  printer) files="digits.v GoAst.v GoPrint.v" ;;
  emit)    files="digits.v GoAst.v GoPrint.v GoTypes.v GoSafe.v GoEmit.v" ;;
  *) echo "spine-gate: unknown mode $mode" >&2; exit 2 ;;
esac
: > "$log"
for f in $files; do
  if ! rocq c -Q . Fido "$f" >> "$log" 2>&1; then
    echo "fido: $mode spine ($files) failed to compile:"; cat "$log"; exit 1
  fi
done
if grep -q '^Axioms:' "$log"; then
  echo "fido: SPINE AXIOM/ADMITTED — a gated $mode-spine theorem depends on an axiom (Print Assumptions over $files):"
  cat "$log"; exit 1
fi
