#!/bin/sh
# Smart-constructor gate (external review #4 directive; review #5 widened it to ALL plugin OCaml).
#
# The proof-carrying Printer atom/type constructors — SIdent / SIntLit / SRaw / SSelector / AScanned /
# AStringLit / GTNamed — erase their Rocq validity proofs to bare strings in the extracted OCaml.  So a
# DIRECT call like `Printer.SRaw "a+b"` or `Printer.GTNamed "func"` would inject text the verified
# round-trip (print_parse_expr) / type round-trip (parse_print_ty) never proved valid — re-opening
# exactly the hand-written-printer trust hole, through a side door.  (The SCANNED atoms are built only by
# the verified Printer.build_atom; mk_atom uses the lone proof-carrying AStringLit directly.)
#
# The mk_atom / mk_named_ty smart constructors (the SMART-CONSTRUCTORS block of plugin/go.ml) are the
# SOLE sanctioned construction sites: each re-checks the EXACT predicate its sig demands and fail-louds
# otherwise.  This gate asserts NOTHING ELSE constructs those directly — scanning EVERY hand-written
# plugin OCaml file (go.ml AND the .mlg vernac glue), not just go.ml, so a future helper file cannot
# reopen the hole (review #5 item 4).  The GENERATED plugin/printer.ml DEFINES the constructors, so it is
# the one file excluded.
#
# Run from the repo root: locally via `make smart-ctor-gate` and the pre-commit hook, and
# NON-bypassably in the Docker prover stage (so `make check` always enforces it).
set -e

# The smart-constructor block lives in go.ml; assert its markers are present (so the in-block uses are
# correctly excluded below — deleting the markers makes the block's own uses read as offenders, which is
# a failure, not a bypass).
if ! grep -q 'SMART-CONSTRUCTORS-BEGIN' plugin/go.ml || ! grep -q 'SMART-CONSTRUCTORS-END' plugin/go.ml; then
  echo "fido: SMART-CTOR GATE — the SMART-CONSTRUCTORS-BEGIN/END markers are missing from plugin/go.ml"
  exit 1
fi

# Every hand-written plugin OCaml file EXCEPT the generated printer.ml.  (go.ml + g_go_extraction.mlg.)
files=""
for f in plugin/*.ml plugin/*.mlg; do
  [ "$f" = plugin/printer.ml ] && continue
  files="$files $f"
done

# Print "<file>:<lineno>: <text>" for any banned constructor use OUTSIDE the marker block (the block
# exists only in go.ml; in every other file there is no block, so [s] stays 0 and EVERY direct use is an
# offender).  FNR==1 resets the per-file skip flag; FNR is the per-file line number (clickable).
offenders=$(awk '
  FNR==1 { s=0 }
  /SMART-CONSTRUCTORS-BEGIN/{s=1}
  /SMART-CONSTRUCTORS-END/{s=0; next}
  !s && /Printer\.(SIdent|SIntLit|SRaw|SSelector|AScanned|AStringLit|GTNamed)/ {print FILENAME ":" FNR ": " $0}
' $files)

if [ -n "$offenders" ]; then
  echo "fido: SMART-CTOR GATE — direct proof-carrying Printer constructor OUTSIDE the smart-constructor block:"
  echo "$offenders"
  echo "fido: construct via mk_atom / mk_named_ty (which re-check the erased invariant), never the raw constructor."
  exit 1
fi

echo "fido: smart-ctor gate OK — no direct proof-carrying Printer constructor outside the block ✓"
