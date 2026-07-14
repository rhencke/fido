#!/bin/sh
# OCaml-origin gate — STAGED-TREE AUTHORITATIVE.  Operate on a ROOT directory (arg 1, default "."); for the
# pre-commit hook and `make check` this is the Git index materialized by `git checkout-index`, so it is the
# proposed commit's bytes and needs no `.git`.  find-based, skipping the opaque dot/underscore/testdata/
# vendor trees.
#
# Fido has NO handwritten OCaml language semantics, compilation, safety reasoning, lowering, or rendering —
# all of that lives in proved Rocq.  The ONLY handwritten OCaml is the Fido Emit transport/apply boundary:
#   - plugin/fido_sink.ml  — the generic dirty-directory filesystem sink (filesystem ONLY);
#   - e2e/sink_test.ml      — a standalone driver that exercises the sink (filesystem ONLY);
#   - e2e/fido_apply.ml     — the `make regenerate` apply CLI (filesystem ONLY — no Rocq term, no AST);
#   - plugin/g_fido.mlg     — the transport bridge (four ordered steps: typecheck the image type; reject a
#                             non-empty assumption closure; decode ONLY the final (go.mod, entries) transport;
#                             call the sink).  It does no program/AST/type/safety inspection.
# Fail-closed: (1) the tracked *.ml/*.mli/*.mlg set is AT MOST those four; (2) the three filesystem-only
# files walk no Rocq terms; (3) the bridge names no program/AST/type/safety structure; (4) no deleted-backend
# hallmark name reappears.  There is deliberately NO source-line-count ceiling — a numeric cap is not a
# correctness invariant; the behavioral emit fixtures exercise the live boundary instead.
set -eu
root=${1:-.}
allowed='e2e/fido_apply.ml e2e/sink_test.ml plugin/fido_sink.ml plugin/g_fido.mlg'
fs_files='plugin/fido_sink.ml e2e/sink_test.ml e2e/fido_apply.ml'
bridge='plugin/g_fido.mlg'

# (1) only the four transport/apply files may be tracked OCaml.
found=$(find "$root" \( -name '.*' -o -name '_*' -o -name testdata -o -name vendor \) -prune -o \
             \( -name '*.ml' -o -name '*.mli' -o -name '*.mlg' \) -print 2>/dev/null \
        | sed "s#^$root/*##" | LC_ALL=C sort)
extra=$(printf '%s\n' "$found" | grep -vxF -e e2e/sink_test.ml -e plugin/fido_sink.ml -e e2e/fido_apply.ml -e plugin/g_fido.mlg || true)
if [ -n "$extra" ]; then
  echo "fido: OCAML-ORIGIN GATE — only the transport/apply files ($allowed) may be tracked OCaml.  Offending:"; printf '%s\n' "$extra" | sed 's/^/  /'; exit 1
fi

# (2) the filesystem-only files walk no Rocq terms (no source-line ceiling — a cap is not a correctness invariant).
for f in $fs_files; do
  if [ -f "$root/$f" ]; then
    if grep -nE 'EConstr|Constr\.|Nametab|interp_constr|Reductionops|Evd\.|Global\.env' "$root/$f"; then
      echo "fido: OCAML-ORIGIN GATE — $f is filesystem-only; it must not walk or decode Rocq terms."; exit 1
    fi
  fi
done

# (3) the transport bridge decodes the final transport only — never a Fido program/AST/type/safety structure.
if [ -f "$root/$bridge" ]; then
  if grep -nE 'GoProgram|GoFileAST|GoDecl|GoStmt|GoExpr|GoType|GoConst|CompilableProgram|SafeProgram|CompilationFacts|ProgramTyped|ResolveExpr|render_|eval_|GoCompile' "$root/$bridge"; then
    echo "fido: OCAML-ORIGIN GATE — $bridge must decode ONLY the final transport; it names a program/AST/type structure."; exit 1
  fi
fi

# (4) no deleted-backend hallmark NAME reappears in tracked sources.
banned='MiniML|Smartlocate|mono_environment|pp_struct|Extract_env|rocq-go-extraction|rocq_go_extraction|g_go_extraction|build_goexpr|pp_expr'
hits=$(find "$root" \( -name '.*' -o -name '_*' -o -name testdata -o -name vendor \) -prune -o \
            \( -name '*.v' -o -name '*.ml' -o -name '*.mlg' -o -name 'Makefile' -o -name 'Dockerfile' -o -name 'dune' -o -name 'dune-project' \) -type f -print 2>/dev/null \
       | grep -v "/tools/ocaml-origin-gate.sh$" \
       | xargs grep -lE "$banned" 2>/dev/null || true)
if [ -n "$hits" ]; then
  echo "fido: OCAML-ORIGIN GATE — a deleted-backend hallmark NAME reappears in tracked sources:"; printf '%s\n' "$hits" | sed "s#^$root/*##; s/^/  /"; exit 1
fi

echo "fido: ocaml-origin gate OK — only the transport/apply boundary (sink + driver + apply + bridge) under $root; no semantic OCaml; no backend hallmarks; no line cap ✓"
