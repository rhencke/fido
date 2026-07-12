#!/bin/sh
# OCaml-origin gate.  Fido has NO handwritten semantic OCaml — every language decision lives in proved
# Rocq, and the final (relative-path, exact-bytes) image is computed in Rocq and produced by standard
# extraction.  The ONE permitted handwritten OCaml is a tiny filesystem exhaust pipe (`e2e/writer.ml`): it
# receives the already-computed image and writes it, decoding/understanding nothing.  This gate is literal
# and fail-closed:
#   (1) the set of tracked *.ml / *.mli / *.mlg is AT MOST { e2e/writer.ml };
#   (2) that writer is TINY and does only file I/O — it must not walk/decode Rocq terms (no EConstr /
#       Constr / Nametab / interp / Typing / Reductionops / VERNAC / DECLARE PLUGIN), and must stay small;
#   (3) no tracked source contains a hallmark NAME of the deleted OCaml backend / custom extraction plugin.
# Architectural invariants that a shell cannot mechanically check (no second program-AST hierarchy, no
# parser/lexer in the certified path) live in PAINFUL_LESSONS.md and the review, not in filename bans
# (a name ban would also forbid a correct future root that happens to reuse the name).
set -eu

glue='e2e/writer.ml'

extra_ocaml=$(git ls-files '*.ml' '*.mli' '*.mlg' | grep -vxF "$glue" || true)
if [ -n "$extra_ocaml" ]; then
  echo "fido: OCAML-ORIGIN GATE — only the one tiny writer ($glue) may be tracked OCaml.  Offending files:"
  echo "$extra_ocaml" | sed 's/^/  /'
  exit 1
fi

if git ls-files --error-unmatch "$glue" >/dev/null 2>&1; then
  lines=$(wc -l < "$glue")
  if [ "$lines" -gt 25 ]; then
    echo "fido: OCAML-ORIGIN GATE — the writer glue is $lines lines; it must stay a tiny (<=25) I/O-only sink."
    exit 1
  fi
  if grep -nE 'EConstr|Constr\.|Nametab|interp_constr|Typing\.|Reductionops|VERNAC|DECLARE PLUGIN|Evd\.' "$glue"; then
    echo "fido: OCAML-ORIGIN GATE — the writer must do ONLY file I/O; it must not walk or decode Rocq terms."
    exit 1
  fi
fi

banned='MiniML|Smartlocate|mono_environment|pp_struct|Extract_env|Go Main Extraction|Go File Extraction|rocq-go-extraction|rocq_go_extraction'
self='tools/ocaml-origin-gate.sh'
hits=$(git ls-files '*.v' '*.ml' Makefile Dockerfile dune dune-project 'e2e/*' 'tools/*' '.githooks/*' \
         | grep -vxF "$self" \
         | xargs grep -lE "$banned" 2>/dev/null || true)
if [ -n "$hits" ]; then
  echo "fido: OCAML-ORIGIN GATE — a deleted-backend hallmark NAME reappears in tracked sources:"
  echo "$hits" | sed 's/^/  /'
  echo "fido: the handwritten OCaml backend / custom extraction plugin is deleted for good.  Emission goes"
  echo "fido: ONLY through the proved chain + standard extraction + the one tiny I/O writer."
  exit 1
fi

echo "fido: ocaml-origin gate OK — at most the one tiny I/O writer; no term-walking; no backend hallmarks ✓"
