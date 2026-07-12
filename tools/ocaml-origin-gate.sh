#!/bin/sh
# OCaml-origin gate.  Fido has NO handwritten OCaml backend, semantics, or renderer — every language
# decision lives in proved Rocq.  The ONE permitted piece of handwritten OCaml is the tiny transparent
# transport glue `plugin/g_fido.mlg` (the `Fido Emit` command: reduce a proved DirectoryImage, decode
# path+bytes, write files — it inspects/decides nothing).  This gate is literal and fail-closed:
#   (1) the set of tracked *.ml / *.mli / *.mlg is AT MOST { plugin/g_fido.mlg } — no other handwritten
#       OCaml, and no committed generated OCaml (extraction/emission output lives only under ignored
#       build dirs; generated *.go is likewise never tracked — see the uncommittable-Go seal);
#   (2) no tracked source (INCLUDING the glue) contains a hallmark NAME of the deleted backend / custom
#       extraction plugin (MiniML/Smartlocate/pp_struct/Extract_env/Go Main Extraction/…).  A TEXTUAL
#       tripwire on those names — it deters reintroduction, it does NOT semantically detect term
#       inspection / name-based lowering.
set -eu

glue='plugin/g_fido.mlg'
extra_ocaml=$(git ls-files '*.ml' '*.mli' '*.mlg' | grep -vxF "$glue" || true)
if [ -n "$extra_ocaml" ]; then
  echo "fido: OCAML-ORIGIN GATE — only the one tiny transport glue ($glue) may be tracked OCaml."
  echo "fido: no other handwritten OCaml, and no committed generated OCaml.  Offending files:"
  echo "$extra_ocaml" | sed 's/^/  /'
  exit 1
fi

banned='MiniML|Smartlocate|mono_environment|pp_struct|Extract_env|Go Main Extraction|Go File Extraction|rocq-go-extraction|rocq_go_extraction'
# This gate names the hallmarks to detect them, so it excludes itself from the scan.
self='tools/ocaml-origin-gate.sh'
hits=$(git ls-files '*.v' '*.mlg' Makefile Dockerfile dune dune-project 'plugin/*' 'e2e/*' 'tools/*' '.githooks/*' \
         | grep -vxF "$self" \
         | xargs grep -lE "$banned" 2>/dev/null || true)
if [ -n "$hits" ]; then
  echo "fido: OCAML-ORIGIN GATE — a deleted-backend hallmark NAME reappears in tracked sources:"
  echo "$hits" | sed 's/^/  /'
  echo "fido: the handwritten OCaml backend / custom extraction plugin is deleted for good.  This gate is a"
  echo "fido: textual tripwire on hallmark names — do not reintroduce a backend, name-based lowering, or a"
  echo "fido: second emission path; emission goes ONLY through the proved chain + the one transport glue."
  exit 1
fi

echo "fido: ocaml-origin gate OK — at most the one transport glue is tracked; no handwritten-backend hallmarks ✓"
