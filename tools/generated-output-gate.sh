#!/bin/sh
# Generated-output policy gate — STAGED-TREE AUTHORITATIVE.  Operate on a ROOT directory (arg 1, default
# ".") that is a PLAIN tree — for the pre-commit hook and `make check` this is the Git index materialized by
# `git checkout-index`, so it contains exactly the tracked files and NO `.git`.  find-based (needs no `.git`
# to inspect source contents), scanning the Go-discovered namespace and skipping the opaque
# dot/underscore/testdata/vendor trees.  Generated Go is a TRACKED, reviewed derived artifact; this enforces
# the standing policy over its bytes and Git mode (the byte/path equality vs the pristine layer is the hook's
# separate job):
#   - every generated .go and the root go.mod is a REGULAR, non-symlink, non-executable file (Git mode
#     100644) whose first line is the exact Fido header;
#   - no NESTED go.mod (only the root go.mod is generated);
#   - no .fido control entry or *.fido-tmp-v1 temp anywhere in the tracked tree.
set -eu
root=${1:-.}
header='// fido generated.  do not edit.'
fail=0

# tracked control/temp residue anywhere in the tracked-only tree (never source artifacts)
ctl=$(find "$root" \( -name '.fido' -o -name '*.fido-tmp-v1' \) -print 2>/dev/null || true)
if [ -n "$ctl" ]; then
  echo "fido: GENERATED-OUTPUT GATE — tracked control/temp residue must never be committed:"; printf '%s\n' "$ctl" | sed "s#^$root/*##; s/^/  /"; fail=1
fi

# a NESTED go.mod (depth >= 2) is never generated
nested=$(find "$root" -mindepth 2 -name go.mod -print 2>/dev/null || true)
if [ -n "$nested" ]; then
  echo "fido: GENERATED-OUTPUT GATE — a nested go.mod is never generated (only the root go.mod is tracked):"; printf '%s\n' "$nested" | sed "s#^$root/*##; s/^/  /"; fail=1
fi

# every generated .go + the root go.mod (in the Go-discovered namespace): a regular non-symlink non-exec file
# (Git mode 100644) with the exact Fido header.  Skip opaque dot/underscore/testdata/vendor trees.
gofiles=$(find "$root" \( -name '.*' -o -name '_*' -o -name testdata -o -name vendor \) -prune -o \
              \( -name '*.go' -o -path "$root/go.mod" \) -print 2>/dev/null || true)
for f in $gofiles; do
  rel=$(printf '%s' "$f" | sed "s#^$root/*##")
  if [ -L "$f" ]; then echo "fido: GENERATED-OUTPUT GATE — tracked $rel is a symlink — generated Go/go.mod must be a regular file (Git mode 100644)"; fail=1; continue; fi
  if [ ! -f "$f" ]; then echo "fido: GENERATED-OUTPUT GATE — tracked $rel is not a regular file (gitlink/special?) — must be Git mode 100644"; fail=1; continue; fi
  if [ -x "$f" ]; then echo "fido: GENERATED-OUTPUT GATE — tracked $rel is executable — generated Go/go.mod must be Git mode 100644, not 100755"; fail=1; continue; fi
  if [ "$(head -n 1 "$f")" != "$header" ]; then
    echo "fido: GENERATED-OUTPUT GATE — tracked $rel lacks the exact Fido header first line — handwritten/unowned Go is forbidden in the canonical module"; fail=1
  fi
done

[ "$fail" -eq 0 ] || exit 1
echo "fido: generated-output gate OK — tracked Go/go.mod under $root are Fido-headed regular (mode 100644) generated artifacts; no nested go.mod; no .fido/temp ✓"
