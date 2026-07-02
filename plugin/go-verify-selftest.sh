#!/bin/sh
# fido go-verify-selftest — FAIL-CLOSED harness for the gc ground-truthing helper: every
# negative case (empty GO / missing dir / sibling .go file) must fail BEFORE docker with its
# EXACT first fido: diagnostic; a PATH-shadowed docker sentinel proves docker is never reached.
#   usage: go-verify-selftest.sh <make>
set -eu
MK="$1"
sd=$(mktemp -d); trap 'rm -rf "$sd"' EXIT
printf '#!/bin/sh\necho FIDO-DOCKER-INVOKED >&2; exit 97\n' > "$sd/docker"
chmod +x "$sd/docker"
fx="$sd/fx"; mkdir "$fx"
printf 'package main\nfunc main() {}\n' > "$fx/main.go"
: > "$fx/helper.go"
test -s "$fx/main.go"; test -f "$fx/helper.go"
chk() {
  if out=$(PATH="$sd:$PATH" $MK -s go-verify GO="$1" 2>&1); then
    echo "fido: go-verify ACCEPTED GO='$1'"; exit 1
  fi
  line=$(echo "$out" | grep '^fido:' | head -1)
  test "$line" = "$2" || { echo "fido: unexpected diagnostic for GO='$1':"; echo "$out"; exit 1; }
  if echo "$out" | grep -q FIDO-DOCKER-INVOKED; then
    echo "fido: go-verify reached docker for GO='$1' (a fail-before-docker case)"; exit 1
  fi
}
chk "" "fido: go-verify needs GO=<dir containing ONLY main.go>"
chk "/nonexistent-fido-selftest" "fido: go-verify — no main.go in '/nonexistent-fido-selftest' (missing/typo'd dir; nothing created)"
test ! -e /nonexistent-fido-selftest || { echo "fido: go-verify CREATED the missing dir"; exit 1; }
chk "$fx" "fido: go-verify — main.go must be the ONLY .go file (file-mode run would silently IGNORE siblings):"
echo "fido: go-verify-selftest OK — every negative case fails with its exact diagnostic, docker never reached ✓"
