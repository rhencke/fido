#!/bin/sh
# GENERATED-MODE GATE — INDEX-authoritative.  Every tracked generated file (the root go.mod + every tracked
# `*.go`) must have EXACT stage-0 Git index mode 100644 — no symlink (120000), executable (100755), or
# gitlink (160000).
#
# The mode is read from the INDEX itself (`git ls-files -s`), NOT inferred from an exported filesystem
# object: `git checkout-index` under `core.symlinks=false` materializes a mode-120000 (symlink) index entry
# as a PLAIN FILE holding the link blob, so the exported-object `-L`/`-f`/`-x` checks in generated-output-gate
# cannot see the recorded symlink mode — a mode-120000 `main.go` whose blob equals the canonical bytes would
# export as a regular file with the correct header and pass every export-based check while the proposed commit
# still records mode 120000.  Reading the index closes that hole regardless of core.symlinks.
#
# Runs in the repository (cwd = repo root), so `git ls-files` reads the PROPOSED COMMIT's index (stage 0) —
# never the working tree.  `git ls-files -s` prints "<mode> <object> <stage>\t<path>"; generated paths are
# canonical FilePaths (no spaces), so the first field is the mode.
set -eu
# Read the index FIRST and check git's OWN exit status — a pipeline's status is the LAST stage's (awk), so
# `git ls-files | awk` would mask a git failure (not a repo / unreadable index) and certify everything as
# 100644.  FAIL-CLOSED: if the index cannot be read, refuse.
if ! entries=$(git ls-files -s -- '*.go' 'go.mod'); then
  echo "fido: GENERATED-MODE GATE — cannot read the Git index (git ls-files failed) — refusing (fail-closed)"
  exit 1
fi
bad=$(printf '%s\n' "$entries" | awk 'NF && $1 != "100644" { print }')
if [ -n "$bad" ]; then
  echo "fido: GENERATED-MODE GATE — a tracked generated file has a non-100644 Git index mode (must be EXACTLY 100644 — reject symlink 120000 / exec 100755 / gitlink 160000):"
  printf '%s\n' "$bad" | sed 's/^/  /'
  exit 1
fi
echo "fido: generated-mode gate OK — every tracked go.mod + .go has exact Git index mode 100644 (read from the index, not an exported object) ✓"
