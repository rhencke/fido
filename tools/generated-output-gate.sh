#!/bin/sh
# Generated-output policy gate (replaces the deleted no-tracked-Go seal — the two models are NOT both kept).
# Generated Go is now a TRACKED, REVIEWED derived artifact of ONE certified generation; the pre-commit
# staged-index check verifies it is byte-exact against the pristine `generated-module` layer.  This is the
# fast, offline STANDING policy over tracked Go/module/control bytes — and it is INDEX-AUTHORITATIVE: it
# reads the staged blob (content + mode) via git, never the unstaged working tree, so a staged/worktree
# divergence cannot make it inspect different bytes from the proposed commit.  It enforces:
#   - every tracked .go and the tracked root go.mod is a REGULAR blob (no symlink/gitlink) whose staged
#     first line is the exact Fido header;
#   - no tracked NESTED go.mod (only the root go.mod is a generated artifact);
#   - no tracked .fido control entry or *.fido-tmp-v1 temp (crash/control residue is never source);
#   - therefore no handwritten/unowned tracked Go in the canonical module.
# (The byte/path equality of the whole module vs the pristine build is the pre-commit hook's job.)
set -eu
header='// fido generated.  do not edit.'
fail=0

# tracked control/temp residue (any depth)
ctl=$(git ls-files | grep -E '(^|/)\.fido($|/)|\.fido-tmp-v1$' || true)
if [ -n "$ctl" ]; then
  echo "fido: GENERATED-OUTPUT GATE — tracked control/temp residue must never be committed:"; printf '%s\n' "$ctl" | sed 's/^/  /'; fail=1
fi

# nested go.mod (only the root go.mod is tracked)
nested=$(git ls-files | grep -E '.+/go\.mod$' || true)
if [ -n "$nested" ]; then
  echo "fido: GENERATED-OUTPUT GATE — a nested go.mod is never generated (only the root go.mod is tracked):"; printf '%s\n' "$nested" | sed 's/^/  /'; fail=1
fi

# every tracked .go + root go.mod: a REGULAR staged blob (mode 100644/100755) whose STAGED first line is the
# exact Fido header.  `git ls-files -s` emits `<mode> <sha> <stage>\t<path>` (path after a TAB); a symlink is
# mode 120000, a gitlink 160000 — both rejected.
git ls-files -s -- '*.go' go.mod | while read -r line; do
  mode=${line%% *}          # first space-delimited field
  path=${line#*	}          # everything after the first TAB
  case "$mode" in
    100644|100755) : ;;
    *) echo "fido: GENERATED-OUTPUT GATE — tracked $path is a non-regular blob (mode $mode) — tracked Go/go.mod must be a regular file"; exit 7 ;;
  esac
  if [ "$(git cat-file blob ":$path" | head -n 1)" != "$header" ]; then
    echo "fido: GENERATED-OUTPUT GATE — tracked $path lacks the exact Fido header first line (staged) — handwritten/unowned Go is forbidden in the canonical module"; exit 7
  fi
done || fail=1

[ "$fail" -eq 0 ] || exit 1
echo "fido: generated-output gate OK — tracked Go/go.mod are Fido-headed regular generated artifacts (index-authoritative); no nested go.mod; no tracked .fido/temp ✓"
