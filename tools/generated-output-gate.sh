#!/bin/sh
# Generated-output policy gate — STAGED-TREE AUTHORITATIVE.  Operate on a ROOT directory (arg 1, default
# ".") that is a PLAIN tree — for the pre-commit hook and `make check` this is the Git index materialized by
# `git checkout-index`, so it contains exactly the tracked files and NO `.git`.  find-based, inspecting
# EVERY tracked `.go` at EVERY depth (only `.git` metadata is pruned).  This is a REPOSITORY-CONTENT gate,
# NOT the runtime sink: it must NOT adopt the sink's Go-discovery directory skipping — a rogue unheaded /
# executable / symlinked `.go` under `.hidden`/`_priv`/`testdata`/`vendor` would otherwise escape, and
# `.dockerignore` hides tracked `.go` from Buildx, so only this host gate can catch it.  Generated Go is a
# TRACKED, reviewed derived artifact; this enforces the standing policy over its header and shape (the
# byte/path equality vs the pristine layer is the separate `verify-generated` compare's job; the
# AUTHORITATIVE exact-Git-mode-100644 check is the separate index-reading `generated-mode-gate` — the
# exported-object `-L`/`-f`/`-x` tests below are a best-effort complement that a `core.symlinks=false` export
# can defeat, so they are not relied on for the mode decision — all run by BOTH `make check` and the hook):
#   - every generated .go and the root go.mod is a REGULAR, non-symlink, non-executable file (mode 100644 —
#     authoritatively via generated-mode-gate) whose first line is the exact Fido header;
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

# every tracked .go + the root go.mod (EVERY depth, only .git pruned): a regular non-symlink non-exec file
# (Git mode 100644) with the exact Fido header.  PATHNAME-SAFE: `find -exec sh -c` passes real paths as "$@"
# to the inner shell — never through `for f in $var` word-splitting (a `main.go main.go` would otherwise
# split into two valid-looking paths and the rogue itself go uninspected).  No -type f — a symlink/special
# named *.go is still surfaced and rejected below (fail-closed).
if ! find "$root" -name .git -prune -o \( -name '*.go' -o -path "$root/go.mod" \) -exec sh -c '
  header=$1; root=$2; shift 2; rc=0
  for f do
    rel=${f#"$root"/}
    if   [ -L "$f" ]; then echo "  $rel — symlink (generated Go/go.mod must be a regular Git-mode-100644 file)"; rc=1
    elif [ ! -f "$f" ]; then echo "  $rel — not a regular file (gitlink/special?); must be Git mode 100644"; rc=1
    elif [ -x "$f" ]; then echo "  $rel — executable; generated Go/go.mod must be Git mode 100644, not 100755"; rc=1
    elif [ "$(head -n 1 "$f")" != "$header" ]; then echo "  $rel — lacks the exact Fido header first line (handwritten/unowned Go is forbidden)"; rc=1
    fi
  done
  exit $rc
' _ "$header" "$root" {} + 2>/dev/null; then
  echo "fido: GENERATED-OUTPUT GATE — a tracked .go / root go.mod is not a Fido-headed regular (mode 100644) file (offenders above)"; fail=1
fi

[ "$fail" -eq 0 ] || exit 1
echo "fido: generated-output gate OK — tracked Go/go.mod under $root are Fido-headed regular (mode 100644) generated artifacts; no nested go.mod; no .fido/temp ✓"
