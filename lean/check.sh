#!/bin/sh
# Compile one or more modules alone and audit their axioms, without touching the shared .lake/ tree — so several
# ports can be checked concurrently.  Dependencies come from the last `lake build` (single-writer), copied into
# a private overlay root: Lean binds a module to the FIRST search root holding its top-level directory, so the
# fresh oleans and their dependencies must live under one root.  Several modules, in dependency order, let a
# module be checked together with a new module it imports before either is in .lake/build.
# usage: check.sh Fido.Decimal            check.sh "Fido.SpecFloat Fido.Float"
set -eu
MODS=${1:?module name(s) in dependency order, e.g. Fido.Decimal or "Fido.SpecFloat Fido.Float"}
D=$(mktemp -d); trap 'rm -rf "$D"' EXIT
L="$(pwd)/.lake/build/lib/lean"; [ -d "$L" ] || L="$(pwd)/.lake/build/lib"
mkdir -p "$D/root"; [ -d "$L" ] && cp -r "$L/." "$D/root/"
export LEAN_PATH="$D/root"
for MOD in $MODS; do
  SRC="$(echo "$MOD" | tr . /).lean"
  [ -f "$SRC" ] || { echo "fido-lean check: no such module file $SRC"; exit 2; }
  mkdir -p "$D/root/$(dirname "$SRC")"
  s=$(date +%s.%N)
  lean -o "$D/root/${SRC%.lean}.olean" -i "$D/root/${SRC%.lean}.ilean" "$SRC" || { echo "fido-lean check: $MOD FAILED to compile"; exit 1; }
  e=$(date +%s.%N)
  echo "fido-lean check: $MOD compiled alone in $(awk -v a="$s" -v b="$e" 'BEGIN { printf "%.2f", b - a }') s"
done
for MOD in $MODS; do
  { echo "import $MOD"; sed '/^import Fido$/d' Audit.lean; } > "$D/audit.lean"
  FIDO_AUDIT_PREFIX="$MOD" lean "$D/audit.lean"
done
