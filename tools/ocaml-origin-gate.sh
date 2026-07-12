#!/bin/sh
# OCaml-origin gate.  Fido has NO handwritten OCaml backend.  There is NO emission this round (the false
# compile/emit authority was deleted), so there is no OCaml at all; when a proof-bearing emission returns it
# is standard Rocq extraction of a proved closed value plus one tiny transparent build-generated writer,
# never tracked.  This gate is literal and fail-closed:
#   (1) the set of tracked *.ml / *.mli / *.mlg is EMPTY — no handwritten OCaml, and no committed generated
#       OCaml either (any future extraction output lives only under ignored build dirs);
#   (2) no tracked source contains a hallmark NAME of the deleted backend / custom extraction plugin
#       (MiniML/Smartlocate/pp_struct/Extract_env/Go Main Extraction/…).  This is a TEXTUAL tripwire on those
#       names — it deters reintroduction, it does NOT semantically detect term inspection / name-based lowering.
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
  echo "fido: OCAML-ORIGIN GATE — a deleted-backend hallmark NAME reappears in tracked sources:"
  echo "$hits" | sed 's/^/  /'
  echo "fido: the handwritten OCaml backend / custom extraction plugin is deleted for good.  This gate is a"
  echo "fido: textual tripwire on hallmark names — do not reintroduce a backend, name-based lowering, or a"
  echo "fido: custom extraction command; any future emission goes through standard extraction of proved bytes."
  exit 1
fi

echo "fido: ocaml-origin gate OK — zero tracked OCaml; no handwritten-backend hallmarks ✓"
