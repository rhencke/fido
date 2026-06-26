#!/bin/sh
# Smart-constructor gate (external review #4 directive).
#
# The proof-carrying Printer atom/type constructors — AIdent / AIntLit / ARaw / GTNamed — erase
# their Rocq validity proofs to a bare string / Z in the extracted OCaml.  So a DIRECT call like
# `Printer.ARaw "a+b"` or `Printer.GTNamed "func"` would inject text the verified round-trip
# (print_parse_expr) / type round-trip (parse_print_ty) never proved valid — re-opening exactly the
# hand-written-printer trust hole, through a side door.
#
# The mk_atom / mk_named_ty smart constructors (the SMART-CONSTRUCTORS block of plugin/go.ml) are the
# SOLE sanctioned construction sites: each re-checks the EXACT predicate its sig demands and fail-louds
# otherwise.  This gate asserts nothing else constructs those four directly.  plugin/printer.ml DEFINES
# them (a separate file) so it is naturally out of scope — we only scan plugin/go.ml.
#
# Run from the repo root: locally via `make smart-ctor-gate` and the pre-commit hook, and
# NON-bypassably in the Docker prover stage (so `make check` always enforces it).
set -e
f=plugin/go.ml

if ! grep -q 'SMART-CONSTRUCTORS-BEGIN' "$f" || ! grep -q 'SMART-CONSTRUCTORS-END' "$f"; then
  echo "fido: SMART-CTOR GATE — the SMART-CONSTRUCTORS-BEGIN/END markers are missing from $f"
  echo "fido: (deleting them does not bypass the gate — the smart constructors' own uses would then"
  echo "fido:  read as offenders — but the markers must be present for the scan to be meaningful)."
  exit 1
fi

# Print "<file>:<lineno>: <text>" for any banned constructor use OUTSIDE the marker block, using the
# ORIGINAL line number (NR) so the offender is clickable.
offenders=$(awk '
  /SMART-CONSTRUCTORS-BEGIN/{s=1}
  /SMART-CONSTRUCTORS-END/{s=0; next}
  !s && /Printer\.(AIdent|AIntLit|ARaw|GTNamed)/ {print FILENAME ":" NR ": " $0}
' "$f")

if [ -n "$offenders" ]; then
  echo "fido: SMART-CTOR GATE — direct proof-carrying Printer constructor OUTSIDE the smart-constructor block:"
  echo "$offenders"
  echo "fido: construct via mk_atom / mk_named_ty (which re-check the erased invariant), never the raw constructor."
  exit 1
fi

echo "fido: smart-ctor gate OK — no direct proof-carrying Printer constructor outside the block ✓"
