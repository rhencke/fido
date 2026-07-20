#!/bin/sh
# Compare a canonical generated module tree against a pristine `generated-module` tree, EXACT relative path
# set AND exact bytes, both directions.  SHARED (contract) by two callers over different ROOT trees (arg
# 1): `make check` passes a temp tree materialized from the working-tree content (tracked PLUS
# untracked-non-gitignored, via `git ls-files --cached --others --exclude-standard | tar`); the pre-commit
# hook passes the Git index materialized by `git checkout-index` (the PROPOSED COMMIT).  The tree is read
# find-based so every
# go.mod + recursive .go at EVERY depth is compared, immune to .dockerignore / file-type filtering.  Only
# `.git` metadata is pruned — this is a REPOSITORY-CONTENT comparison, NOT the runtime sink, so it must NOT
# skip the sink's opaque directories: a rogue `.go` under `.hidden`/`_priv`/`testdata`/`vendor` (absent from
# the pristine build) must surface as a path-set mismatch here.  No -type f, so a symlink/special named *.go
# is surfaced too.  Args: $1 = the tree to check (working tree or exported index), $2 = pristine dir.
#
# Fails on: modified bytes, a generated file in the checked tree absent from the pristine build (stale/extra),
# a pristine file absent from the checked tree (a newly-generated path not present), and any nested mismatch.
# PATHNAME-SAFE: paths are processed via `find -exec sh -c` (real paths as "$@"), NEVER serialized into
# newline-delimited shell variables (a single file named `go.mod<newline>main.go` would otherwise
# serialize to the same two apparent paths as a pristine `go.mod` + `main.go`).  Exact equality is two
# directions: EVERY pristine file must be present in the checked tree AND byte-identical (a missing one is a
# FAILURE, never a silent skip), and NO generated file in the checked tree may be absent from the pristine build.
set -eu
root=$1; pristine=$2
[ -d "$root" ]     || { echo "fido: GENERATED-COMPARE — the tree to check ($root) is missing"; exit 1; }
[ -d "$pristine" ] || { echo "fido: GENERATED-COMPARE — pristine tree $pristine is missing"; exit 1; }
rc=0

# (1) every pristine file is present in the checked tree AND byte-identical (absent ⇒ FAIL, not skip).
if ! find "$pristine" -name .git -prune -o -type f -exec sh -c '
  root=$1; pristine=$2; shift 2; irc=0
  for f do
    rel=${f#"$pristine"/}
    if   [ ! -f "$root/$rel" ]; then echo "  MISSING: $rel (the pristine certified build has it)"; irc=1
    elif ! cmp -s "$f" "$root/$rel"; then echo "  BYTES differ: $rel"; irc=1
    fi
  done
  exit $irc
' _ "$root" "$pristine" {} +; then rc=1; fi

# (2) no EXTRA generated file: every .go / root go.mod in the checked tree exists in the pristine build.
if ! find "$root" -name .git -prune -o \( -name '*.go' -o -path "$root/go.mod" \) -exec sh -c '
  root=$1; pristine=$2; shift 2; irc=0
  for f do
    rel=${f#"$root"/}
    if [ ! -e "$pristine/$rel" ]; then echo "  EXTRA generated file (absent from the pristine build): $rel"; irc=1; fi
  done
  exit $irc
' _ "$root" "$pristine" {} +; then rc=1; fi

if [ "$rc" -ne 0 ]; then
  echo "fido: the generated module does not match the pristine certified build (exact path set + bytes)."
  echo "      Run:  make regenerate && git add -A -- go.mod ':(top,glob)**/*.go' && git commit"
  exit 1
fi
echo "fido: generated-compare OK — the root go.mod + recursive .go byte-match the pristine build (exact path set + bytes)"
