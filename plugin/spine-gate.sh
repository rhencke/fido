#!/bin/sh
# THE ONE spine-gate authority: compile the trust-boundary SOURCE SET standalone and assert
# ZERO axioms (grep '^Axioms:' over the one log every compile writes to).  Called by BOTH the
# Dockerfile prover stage and the Makefile local mirrors — a single definition, no drift path.
# EVERY failure path cleans the generated artifacts (vo/glob/aux + printer.ml), so read-only
# callers stay read-only even on an axiom regression; on SUCCESS the artifacts are left for
# the caller (the printer flow consumes printer.ml, then runs its own CLEAN).
#   mode: printer  (digits GoAst GoPrint — leaves the extracted printer.ml in CWD)
#         emit     (the printer set + GoTypes GoSafe GoEmit)
#         custom F (one explicit file — the selftest's hook)
#         selftest (force the axiom-failure branch; assert the cleanup contract)
set -eu
mode="$1"
case "$mode" in
  printer) files="digits.v GoAst.v GoPrint.v"; log="$2" ;;
  emit)    files="digits.v GoAst.v GoPrint.v GoTypes.v GoSafe.v GoEmit.v"; log="$2" ;;
  custom)  files="$2"; log="$3" ;;
  selftest)
    tmp="spine_gate_selftest"
    printf 'Axiom sg_selftest_ax : True.\nPrint Assumptions sg_selftest_ax.\n' > "$tmp.v"
    if sh "$0" custom "$tmp.v" /tmp/spine-selftest.log >/dev/null 2>&1; then
      echo "fido: spine-gate selftest FAILED — the axiom branch did not fail" >&2
      rm -f "$tmp.v" "$tmp.vo" "$tmp.glob" ".$tmp.aux"; exit 1
    fi
    for a in "$tmp.vo" "$tmp.glob" ".$tmp.aux"; do
      if [ -e "$a" ]; then
        echo "fido: spine-gate selftest FAILED — stale artifact $a survived the failure path" >&2
        rm -f "$tmp.v" "$tmp.vo" "$tmp.glob" ".$tmp.aux"; exit 1
      fi
    done
    rm -f "$tmp.v"
    echo "fido: spine-gate cleanup-on-failure selftest OK ✓"; exit 0 ;;
  *) echo "spine-gate: unknown mode $mode" >&2; exit 2 ;;
esac
clean_artifacts() {
  for f in $files; do b="${f%.v}"; rm -f "$b.vo" "$b.glob" ".$b.aux"; done
  rm -f printer.ml
}
: > "$log"
for f in $files; do
  if ! rocq c -Q . Fido "$f" >> "$log" 2>&1; then
    echo "fido: $mode spine ($files) failed to compile:"; cat "$log"; clean_artifacts; exit 1
  fi
done
if grep -q '^Axioms:' "$log"; then
  echo "fido: SPINE AXIOM/ADMITTED — a gated $mode-spine theorem depends on an axiom (Print Assumptions over $files):"
  cat "$log"; clean_artifacts; exit 1
fi
