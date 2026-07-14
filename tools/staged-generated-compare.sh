#!/bin/sh
# Compare the STAGED canonical generated module against a pristine `generated-module` tree, EXACT relative
# path set AND exact bytes, both directions.  The staged side is the exported staged tree ROOT (arg 1; the
# Git index materialized by `git checkout-index`, so it is the PROPOSED COMMIT — never the unstaged working
# tree — and is read find-based so every generated go.mod + recursive .go at every depth is compared, immune
# to .dockerignore / file-type filtering).  Opaque dot/underscore/testdata/vendor trees hold no generated
# output and are skipped.  Args: $1 = exported staged tree, $2 = pristine dir.
#
# Fails on: modified staged bytes, a staged generated file absent from the pristine build (stale/extra), a
# pristine file absent from the staged tree (a newly-generated path not staged), and any nested mismatch.
set -eu
root=$1; pristine=$2
[ -d "$root" ]     || { echo "fido: STAGED-GENERATED — exported staged tree $root is missing"; exit 1; }
[ -d "$pristine" ] || { echo "fido: STAGED-GENERATED — pristine tree $pristine is missing"; exit 1; }
rc=0

staged_rel=$(find "$root" \( -name '.*' -o -name '_*' -o -name testdata -o -name vendor \) -prune -o \
                  \( -name '*.go' -o -path "$root/go.mod" \) -type f -print 2>/dev/null \
             | sed "s#^$root/*##" | LC_ALL=C sort)
pristine_rel=$( cd "$pristine" && find . -type f | sed 's#^\./##' | LC_ALL=C sort )

# (1) exact relative path set, both directions
if [ "$staged_rel" != "$pristine_rel" ]; then
  echo "fido: STAGED-GENERATED MISMATCH — the generated path set differs from the pristine certified build:"
  echo "  staged:   $(echo $staged_rel)"
  echo "  pristine: $(echo $pristine_rel)"
  rc=1
fi
# (2) exact bytes for every pristine path present in the staged tree
for rel in $pristine_rel; do
  if [ -f "$root/$rel" ]; then
    cmp -s "$root/$rel" "$pristine/$rel" || { echo "fido: STAGED-GENERATED MISMATCH — $rel bytes differ from the pristine certified build"; rc=1; }
  fi
done

if [ "$rc" -ne 0 ]; then
  echo "fido: the staged generated module does not byte-match the pristine certified build."
  echo "      Run:  make regenerate && git add -A -- go.mod ':(top,glob)**/*.go' && git commit"
  exit 1
fi
echo "fido: staged-generated verify OK — the staged root go.mod + recursive .go byte-match /generated (exact path set + bytes)"
