#!/bin/sh
# OCaml-origin gate.  Operates on a ROOT directory (arg 1, default ".") — the WORKING TREE for `make check`,
# or the Git index materialized by `git checkout-index` for the pre-commit hook (the proposed commit's bytes,
# needing no `.git`).  find-based, inspecting EVERY file at EVERY depth — this is a REPOSITORY-CONTENT gate,
# NOT the runtime sink: it must NOT adopt the sink's Go-discovery directory skipping (a rogue `.hidden/x.ml` /
# `_priv/x.ml` / `testdata/x.ml` / `vendor/x.ml` would escape the OCaml allowlist, and `.dockerignore` hides
# tracked `.go` from Buildx, so only this host gate can catch them).  Only VCS metadata (`.git`) is pruned.
#
# Fido has NO handwritten OCaml language semantics, compilation, safety reasoning, lowering, or rendering —
# all of that lives in proved Rocq.  The ONLY handwritten OCaml is the Fido transport / apply boundary:
#   - plugin/sink.ml  — the generic dirty-directory filesystem sink (filesystem ONLY);
#   - e2e/sink_test.ml      — a standalone driver that exercises the sink (filesystem ONLY);
#   - e2e/apply.ml     — the `make regenerate` apply CLI (filesystem ONLY — no Rocq term, no AST);
#   - plugin/materialize.mlg     — the transport bridge (four ordered steps: typecheck the image type; reject a
#                             non-empty assumption closure; decode ONLY the final (go.mod, entries) transport;
#                             materialize a pristine export via `Fido Materialize`).  It does NOT call the
#                             dirty-directory sink (that is reached only from sink_test + the apply CLI), and
#                             does no program/AST/type/safety inspection.
# Fail-closed: (1) the tracked *.ml/*.mli/*.mlg set is AT MOST those four; (2) the three filesystem-only
# files walk no Rocq terms; (3) the bridge names no program/AST/type/safety structure.  There is deliberately
# NO source-line-count ceiling — a numeric cap is not a correctness invariant; the behavioral emit fixtures
# exercise the live boundary instead.  There is also NO whole-repository historical-name scanner: the real
# boundary is this OCaml allowlist + the responsibility checks.
set -eu
root=${1:-.}
allowed='e2e/apply.ml e2e/sink_test.ml plugin/sink.ml plugin/materialize.mlg'
fs_files='plugin/sink.ml e2e/sink_test.ml e2e/apply.ml'
bridge='plugin/materialize.mlg'

# (1) only the four transport/apply files may be tracked OCaml (every depth; only .git metadata pruned).
#     PATHNAME-SAFE: the four allowed paths are PRUNED, so `find -print` emits exactly the OCaml files that
#     are NOT allowed — no shell word-splitting of paths (a rogue name with spaces/newlines is still
#     surfaced).  No -type f, so a tracked symlink or directory named *.ml/*.mli/*.mlg is surfaced too.
extra=$(find "$root" -name .git -prune -o \
             -path "$root/e2e/apply.ml"  -prune -o \
             -path "$root/e2e/sink_test.ml"   -prune -o \
             -path "$root/plugin/sink.ml" -prune -o \
             -path "$root/plugin/materialize.mlg"  -prune -o \
             \( -name '*.ml' -o -name '*.mli' -o -name '*.mlg' \) -print 2>/dev/null)
if [ -n "$extra" ]; then
  echo "fido: OCAML-ORIGIN GATE — only the transport/apply files ($allowed) may be tracked OCaml.  Offending:"; printf '%s\n' "$extra" | sed "s#^$root/*##; s/^/  /"; exit 1
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
  if grep -nE 'Syntax.Program|Syntax.Files|Syntax.File|Syntax.FileNode|Syntax.Decl|Syntax.Stmt|Syntax.Expr|Typing.SemanticType|Typing.Constant|Compilable.Program|Safe.Program|Typing.Program|Typing.Resolve|render_|eval_|Compilable' "$root/$bridge"; then
    echo "fido: OCAML-ORIGIN GATE — $bridge must decode ONLY the final transport; it names a program/AST/type structure."; exit 1
  fi
fi

echo "fido: ocaml-origin gate OK — only the transport/apply boundary (sink + driver + apply + bridge) under $root (every depth inspected, only .git pruned); no semantic OCaml; no line cap; no whole-repo historical-name scanner ✓"
