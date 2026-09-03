#!/bin/sh
# Compile ONE module alone and audit its axioms, without touching the shared .lake/ tree — so several ports can
# be checked concurrently.  Dependencies come from the last `lake build` (single-writer), copied into a private
# overlay root: Lean binds a module to the FIRST search root holding its top-level directory, so the fresh olean
# and its dependencies must live under one root.
# usage: check.sh Fido.Decimal
set -eu
MOD=${1:?module name, e.g. Fido.Decimal}
SRC="$(echo "$MOD" | tr . /).lean"
[ -f "$SRC" ] || { echo "fido-lean check: no such module file $SRC"; exit 2; }
D=$(mktemp -d); trap 'rm -rf "$D"' EXIT
L="$(pwd)/.lake/build/lib/lean"; [ -d "$L" ] || L="$(pwd)/.lake/build/lib"
mkdir -p "$D/root"; [ -d "$L" ] && cp -r "$L/." "$D/root/"
mkdir -p "$D/root/$(dirname "$SRC")"
export LEAN_PATH="$D/root"
s=$(date +%s.%N)
lean -o "$D/root/${SRC%.lean}.olean" -i "$D/root/${SRC%.lean}.ilean" "$SRC" || { echo "fido-lean check: $MOD FAILED to compile"; exit 1; }
e=$(date +%s.%N)
echo "fido-lean check: $MOD compiled alone in $(awk -v a="$s" -v b="$e" 'BEGIN { printf "%.2f", b - a }') s"
{ echo "import $MOD"; sed '/^import Fido$/d' Audit.lean; } > "$D/audit.lean"
FIDO_AUDIT_PREFIX="$MOD" lean "$D/audit.lean"
