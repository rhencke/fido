#!/bin/sh
# Generated-output policy gate (replaces the deleted no-tracked-Go seal — the two models are NOT both kept).
# Generated Go is now a TRACKED, REVIEWED derived artifact of ONE certified generation; the pre-commit
# staged-index Buildx check verifies it is byte-exact against the pristine `generated-module` layer.  This is
# the fast, offline STANDING policy over tracked Go/module/control bytes (the byte/path equality is the hook's
# job, not this gate's):
#   - every tracked .go and the tracked root go.mod begins with the exact Fido header first line;
#   - no tracked NESTED go.mod (only the root go.mod is a generated artifact);
#   - no tracked .fido control entry or *.fido-tmp-v1 temp (crash/control residue is never source);
#   - therefore no handwritten/unowned tracked Go in the canonical module.
set -eu
header='// fido generated.  do not edit.'
tracked=$(git ls-files)
fail=0

ctl=$(printf '%s\n' "$tracked" | grep -E '(^|/)\.fido($|/)|\.fido-tmp-v1$' || true)
if [ -n "$ctl" ]; then
  echo "fido: GENERATED-OUTPUT GATE — tracked control/temp residue must never be committed:"; printf '%s\n' "$ctl" | sed 's/^/  /'; fail=1
fi

nested=$(printf '%s\n' "$tracked" | grep -E '.+/go\.mod$' || true)
if [ -n "$nested" ]; then
  echo "fido: GENERATED-OUTPUT GATE — a nested go.mod is never generated (only the root go.mod is tracked):"; printf '%s\n' "$nested" | sed 's/^/  /'; fail=1
fi

for f in $(printf '%s\n' "$tracked" | grep -E '\.go$|^go\.mod$' || true); do
  if [ ! -f "$f" ]; then echo "fido: GENERATED-OUTPUT GATE — tracked $f is absent from the working tree"; fail=1; continue; fi
  if [ "$(head -n 1 "$f")" != "$header" ]; then
    echo "fido: GENERATED-OUTPUT GATE — tracked $f lacks the exact Fido header first line — handwritten/unowned Go is forbidden in the canonical module"; fail=1
  fi
done

[ "$fail" -eq 0 ] || exit 1
echo "fido: generated-output gate OK — tracked Go/go.mod are Fido-headed generated artifacts; no nested go.mod; no tracked .fido/temp ✓"
