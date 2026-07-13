#!/bin/sh
# OCaml-origin gate.  Fido has NO handwritten OCaml language semantics, compilation, safety reasoning,
# lowering, or rendering — all of that lives in proved Rocq.  The ONLY handwritten OCaml is the Fido Emit
# transport boundary:
#   - plugin/fido_sink.ml  — the generic dirty-directory filesystem sink (filesystem ONLY);
#   - e2e/sink_test.ml      — a standalone driver that exercises the sink (filesystem ONLY);
#   - plugin/g_fido.mlg     — the transport bridge.  Its boundary is EXACTLY four ordered steps: (1)
#                             typecheck the image type; (2) reject a non-empty assumption closure (a kernel
#                             provenance query that descends Qed proof bodies — NOT program/AST inspection);
#                             (3) decode ONLY the final (path, bytes) transport; (4) call the sink.  It does
#                             no semantic program/AST/behaviour inspection.
# This gate is literal and fail-closed:
#   (1) the set of tracked *.ml / *.mli / *.mlg is AT MOST those three;
#   (2) the two filesystem files must NOT walk Rocq terms (no EConstr / Constr / Nametab / interp / Evd /
#       Reductionops / Global) and stay bounded;
#   (3) the transport bridge must NOT mention any Fido program/AST type (GoProgram / GoFileAST / GoDecl /
#       CompilableProgram / SafeProgram / CompilationFacts / render);
#   (4) no tracked source contains a hallmark NAME of the deleted OCaml backend / lowering / renderer.
# That the two provenance guards stay LIVE is a mutation-sensitive REGRESSION gate (not a proof): the emit
# stage's negative fixtures (WitnessNeg = the type guard; WitnessForge{,Opaque,Var,VarIndirect} = the
# assumption-closure guard) EXECUTE forged inputs, and removing either guard makes the corresponding
# `Fido Emit` succeed and create a target, failing the e2e.  A string grep here would only show a name
# appears (in a comment or dead code), so it is not attempted.
set -eu

fs_files='plugin/fido_sink.ml e2e/sink_test.ml'
bridge='plugin/g_fido.mlg'
allowed='e2e/sink_test.ml plugin/fido_sink.ml plugin/g_fido.mlg'

# (1) only the three transport files may be tracked OCaml.
extra_ocaml=$(git ls-files '*.ml' '*.mli' '*.mlg' | grep -vxF -e e2e/sink_test.ml -e plugin/fido_sink.ml -e plugin/g_fido.mlg || true)
if [ -n "$extra_ocaml" ]; then
  echo "fido: OCAML-ORIGIN GATE — only the transport files ($allowed) may be tracked OCaml.  Offending:"
  echo "$extra_ocaml" | sed 's/^/  /'
  exit 1
fi

# (2) the filesystem files walk no Rocq terms and stay bounded.
for f in $fs_files; do
  if git ls-files --error-unmatch "$f" >/dev/null 2>&1; then
    lines=$(wc -l < "$f")
    if [ "$lines" -gt 300 ]; then
      echo "fido: OCAML-ORIGIN GATE — $f is $lines lines; a filesystem sink must stay bounded (<=300)."; exit 1
    fi
    if grep -nE 'EConstr|Constr\.|Nametab|interp_constr|Reductionops|Evd\.|Global\.env' "$f"; then
      echo "fido: OCAML-ORIGIN GATE — $f is filesystem-only; it must not walk or decode Rocq terms."; exit 1
    fi
    # staging is ONE fixed slot (`.fido/staging/tmp`): the sync renames each staged file out before the
    # next, so there is never more than one temp.  Forbidding Unix.rmdir keeps recursive staging cleanup
    # from returning; forbidding an index allocator / numeric name parsing keeps the counter, cursor, and
    # numeric-name grammar (a state space the sequential loop does not need) from returning.
    if grep -nE 'Unix\.rmdir|int_of_string|string_of_int|max_int|module Alloc' "$f"; then
      echo "fido: OCAML-ORIGIN GATE — $f must use the single fixed staging slot (no directory removal, no index allocator / numeric-name grammar)."; exit 1
    fi
  fi
done

# (3) the transport bridge decodes the transport only — never a Fido program/AST type.  (That the live
#     provenance guards remain is a mutation-sensitive regression gate — the emit fixtures — not a proof
#     and not a spoofable grep.)
if git ls-files --error-unmatch "$bridge" >/dev/null 2>&1; then
  lines=$(wc -l < "$bridge")
  if [ "$lines" -gt 200 ]; then
    echo "fido: OCAML-ORIGIN GATE — $bridge is $lines lines; the transport bridge must stay bounded (<=200)."; exit 1
  fi
  if grep -nE 'GoProgram|GoFileAST|GoDecl|GoStmt|GoExpr|CompilableProgram|SafeProgram|CompilationFacts|render_|eval_|GoCompile' "$bridge"; then
    echo "fido: OCAML-ORIGIN GATE — $bridge must decode ONLY the final transport; it names a program/AST type."; exit 1
  fi
fi

# (4) no deleted-backend hallmark NAME reappears.
banned='MiniML|Smartlocate|mono_environment|pp_struct|Extract_env|rocq-go-extraction|rocq_go_extraction|g_go_extraction|build_goexpr|pp_expr'
self='tools/ocaml-origin-gate.sh'
hits=$(git ls-files '*.v' '*.ml' '*.mlg' Makefile Dockerfile dune dune-project 'plugin/*' 'e2e/*' 'tools/*' '.githooks/*' \
         | grep -vxF "$self" \
         | xargs grep -lE "$banned" 2>/dev/null || true)
if [ -n "$hits" ]; then
  echo "fido: OCAML-ORIGIN GATE — a deleted-backend hallmark NAME reappears in tracked sources:"
  echo "$hits" | sed 's/^/  /'
  exit 1
fi

echo "fido: ocaml-origin gate OK — only the transport boundary (sink + bridge); no semantic OCaml; no backend hallmarks ✓"
