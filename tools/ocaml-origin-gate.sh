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

# (3) Anti-regression: the rejected architecture must not reappear as tracked source FILES — a second IR /
#     grammar / token layer, a lexer/parser/tokenizer, a round-trip authority, or the deleted boolean/backend
#     modules.  A code-level filename tripwire (NOT a prose linter): the current modules
#     (GoAST/GoCompile/GoSafe/GoRender/GoEmit/…) do not match; the deleted ones and the generic
#     lexer/parser/tokenizer/round-trip names do.  Case-sensitive on the module list so GoAST ≠ the deleted GoAst.
rejected=$(git ls-files '*.v' '*.mlg' | awk -F/ '{print $NF}' \
  | grep -E '^(GoPrint|GoLex|GoParse|GoParser|GoGrammar|GoToken|GoSyntax|GoStatic|GoAst|Surface|TypedIR|CoreType|CompileEnv|Elaborate|Semantics|CertifiedArtifact|relooper)[.](v|mlg)$' || true)
rejected_kind=$(git ls-files '*.v' '*.mlg' | grep -iE '(lexer|parser|tokeni[sz]er|round[_-]?trip)' || true)
if [ -n "$rejected$rejected_kind" ]; then
  echo "fido: ANTI-REGRESSION GATE — a rejected-architecture module reappeared as a tracked file:"
  printf '%s\n%s\n' "$rejected" "$rejected_kind" | grep -v '^$' | sed 's/^/  /'
  echo "fido: there is no second IR/grammar/token layer, no lexer/parser/tokenizer, no round-trip authority."
  echo "fido: the AST IS the IR; renderer correctness is structural.  See PAINFUL_LESSONS.md."
  exit 1
fi

echo "fido: ocaml-origin gate OK — at most the one transport glue; no backend hallmarks; no rejected modules ✓"
