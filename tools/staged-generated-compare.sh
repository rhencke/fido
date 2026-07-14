#!/bin/sh
# Compare the STAGED canonical generated module against a pristine `generated-module` tree, EXACT relative
# path set AND exact bytes, both directions.  The staged side is read from the Git INDEX via `git cat-file`
# (so it is the PROPOSED COMMIT — never the unstaged working tree — and is immune to .dockerignore/file-type
# filtering: every indexed go.mod + recursive .go is compared, at every depth).  Args: $1 = pristine dir.
#
# Fails on: modified staged bytes, a staged generated file absent from the pristine build (stale/extra), a
# pristine file absent from the index (a newly-generated path not staged), and any nested mismatch.
set -eu
pristine=$1
[ -d "$pristine" ] || { echo "fido: STAGED-GENERATED — pristine tree $pristine is missing"; exit 1; }
work=$(mktemp -d); trap 'rm -rf "$work"' EXIT
rc=0

# (1) every STAGED go.mod/.go must be present + byte-identical in the pristine tree.
staged_list=$(git ls-files -- 'go.mod' '*.go')
for f in $staged_list; do
  git cat-file blob ":$f" > "$work/blob"
  if [ ! -f "$pristine/$f" ]; then
    echo "fido: STAGED-GENERATED MISMATCH — $f is staged but not produced by certified generation (stale/extra)"; rc=1
  elif ! cmp -s "$work/blob" "$pristine/$f"; then
    echo "fido: STAGED-GENERATED MISMATCH — $f bytes differ from the pristine certified build"; rc=1
  fi
done

# (2) every pristine file must be present in the staged index (no missing / newly-generated-but-unstaged).
for f in $( cd "$pristine" && find . -type f | sed 's#^\./##' ); do
  git ls-files --error-unmatch -- "$f" >/dev/null 2>&1 || {
    echo "fido: STAGED-GENERATED MISMATCH — $f is produced by generation but absent from the index (run make regenerate + git add)"; rc=1; }
done

if [ "$rc" -ne 0 ]; then
  echo "fido: the staged generated module does not byte-match the pristine certified build."
  echo "      Run:  make regenerate && git add -A -- go.mod ':(top,glob)**/*.go' && git commit"
  exit 1
fi
echo "fido: staged-generated verify OK — the staged root go.mod + recursive .go byte-match /generated (exact path set + bytes, index-authoritative)"
