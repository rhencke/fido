#!/bin/sh
# OCaml-origin gate (checkpoint 64).  Fido has NO handwritten OCaml backend.  The Go output is produced by
# STANDARD Rocq extraction of a proved closed string ([GoEmit.demo_emit], bytes machine-checked by
# [demo_emit_bytes]); a one-line writer, GENERATED at build time and never tracked, prints it to a .go.
# This gate is literal and fail-closed:
#   (1) the set of tracked *.ml / *.mli / *.mlg is EMPTY — no handwritten OCaml, and no committed generated
#       OCaml either (extraction outputs live only under ignored build dirs);
#   (2) no tracked source names a hallmark of the deleted handwritten backend / custom extraction plugin —
#       a reintroduction tripwire (name-based lowering must never come back).
set -eu

tracked_ocaml=$(git ls-files '*.ml' '*.mli' '*.mlg')
if [ -n "$tracked_ocaml" ]; then
  echo "fido: OCAML-ORIGIN GATE — tracked OCaml is forbidden (the backend is deleted; the writer is"
  echo "fido: build-generated, never committed).  Offending files:"
  echo "$tracked_ocaml" | sed 's/^/  /'
  exit 1
fi

banned='MiniML|Smartlocate|mono_environment|pp_struct|Extract_env|Go Main Extraction|Go File Extraction|rocq-go-extraction|rocq_go_extraction'
# This gate names the hallmarks to detect them, so it excludes itself from the scan.
self='tools/ocaml-origin-gate.sh'
hits=$(git ls-files '*.v' Makefile Dockerfile dune dune-project 'tools/*' '.githooks/*' \
         | grep -vxF "$self" \
         | xargs grep -lE "$banned" 2>/dev/null || true)
if [ -n "$hits" ]; then
  echo "fido: OCAML-ORIGIN GATE — a deleted-backend hallmark reappears in tracked sources:"
  echo "$hits" | sed 's/^/  /'
  echo "fido: the handwritten OCaml backend / custom extraction plugin is deleted for good — no name-based"
  echo "fido: lowering, no MiniML/term inspection, no 'Go Main Extraction'.  Emit through certified extraction."
  exit 1
fi

echo "fido: ocaml-origin gate OK — zero tracked OCaml; no handwritten-backend hallmarks ✓"
