#!/bin/sh
# Smart-constructor gate (external review #4 directive; review #5 widened it to ALL plugin OCaml).
#
# The extracted [Printer] exposes exactly ONE proof-carrying constructor: [GTNamed], which erases its Rocq
# validity proof ([nominal_type_ident s = true]) to a bare string in OCaml.  A DIRECT [Printer.GTNamed s]
# would inject a type name the verified type round-trip ([parse_print_ty]) never proved valid — re-opening
# the hand-written-printer trust hole through a side door.  (The old expression-printer constructors
# SIdent / SIntLit / SRaw / SSelector / AScanned / AStringLit were DELETED with the SRaw overlay teardown —
# see LESSONS.md; they no longer exist in printer.ml, so there is nothing left to guard there.)
#
# The [mk_named_ty] smart constructor (the SMART-CONSTRUCTORS block of plugin/go.ml) is the SOLE sanctioned
# construction site: it re-checks [nominal_type_ident] and fail-louds otherwise.  This gate asserts NOTHING
# ELSE constructs [GTNamed] directly — scanning EVERY hand-written plugin OCaml file (go.ml AND the .mlg
# vernac glue), not just go.ml, so a future helper file cannot reopen the hole (review #5 item 4).  The
# GENERATED plugin/printer.ml DEFINES the constructor, so it is the one file excluded.
#
# Run from the repo root: locally via `make smart-ctor-gate` and the pre-commit hook, and in the Docker
# prover stage (so `make check` always enforces it).
#
# LIMITATION (review #6 item 3): this is a STATIC-DISCIPLINE GATE, not a type-level seal.  It is a grep over
# the source, so it can be defeated by aliasing the constructor, a different module path, or by editing the
# gate itself.  The extracted `printer.ml` exposes [GTNamed] PUBLICLY.  The STRONGER architecture is a
# hand-written wrapper module (`Printer_checked`) with ABSTRACT types + smart constructors, with plugin code
# importing only that — so the raw constructor is simply unavailable.  Until then: do NOT describe this gate
# as "airtight" — it is a practical discipline gate that catches the easy/accidental bypass, not a proof
# boundary.
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
  !s && /Printer\.GTNamed/ {print FILENAME ":" FNR ": " $0}
' $files)

if [ -n "$offenders" ]; then
  echo "fido: SMART-CTOR GATE — direct proof-carrying Printer.GTNamed OUTSIDE the smart-constructor block:"
  echo "$offenders"
  echo "fido: construct via mk_named_ty (which re-checks the erased nominal_type_ident invariant), never the raw constructor."
  exit 1
fi

echo "fido: smart-ctor gate OK — no direct Printer.GTNamed outside the block ✓"
