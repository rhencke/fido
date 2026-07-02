#!/bin/sh
# fido toolchain-selftest — proves the GOIMAGE one-authority setup is FAIL-CLOSED:
#   (1) CLI / env / pinned-but-different GOIMAGE overrides are INERT (the `override` directive);
#   (2) every synthesized Makefile-side GOIMAGE mutation class (global, target-/pattern-specific,
#       private, CONTINUED lines, sinclude/-include, recipe-position and brace eval, computed LHS,
#       .RECIPEPREFIX re-typing) is REJECTED by the gate on a mutated COPY (make -f);
#   (3) Dockerfile drift (defaulted/lowercase ARG, rogue/indented FROM, an ACTIVE
#       leading-whitespace escape directive + backtick-split rogue FROM, a builder-FROM bypass)
#       is REJECTED, and the Go-image detector's own coverage (tag + digest-only spellings) is
#       probed with runtime-constructed fixtures (this file never spells a Go image itself).
#   usage: toolchain-selftest.sh <make> <makefile> <effective-goimage>
set -eu
MK="$1"; mk="$2"; eff="$3"

# (1) override inertness
auth=$($MK -s print-goimage)
got=$($MK -s GOIMAGE=unpinned-override print-goimage)
test "$got" = "$auth" || { echo "fido: an UNPINNED GOIMAGE override changed the effective toolchain to '$got'"; exit 1; }
got=$($MK -s GOIMAGE=other-image@sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa print-goimage)
test "$got" = "$auth" || { echo "fido: a PINNED-BUT-DIFFERENT GOIMAGE override changed the effective toolchain to '$got'"; exit 1; }
GOIMAGE=env-override; export GOIMAGE
got=$($MK -s print-goimage)
test "$got" = "$auth" || { echo "fido: an ENVIRONMENT GOIMAGE override changed the effective toolchain to '$got'"; exit 1; }

# (2) Makefile-side mutation classes (fixtures placeholder-encoded so this file cannot satisfy
#     the gate's own bans; each is synthesized onto a COPY at runtime)
tmp=$(mktemp); trap 'rm -f "$tmp"' EXIT
for evil in \
  'override GOIMAGE = evil-image@sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa' \
  'override GOIMAGE += -tainted' \
  'print-goimage: GOIMAGE := evil' \
  'extract: private GOIMAGE := evil' \
  '%.go: GOIMAGE += -tainted' \
  'extract: GOIMAGE \\@@NL@@ := evil' \
  '%.go: GOIMAGE \\@@NL@@ += -tainted' \
  'sinclude evil.mk' \
  '-include evil.mk' \
  'evil-target:@@NL@@	@$@@LP@@eval extract: GOIMAGE := evil)' \
  'evil-target:@@NL@@	@$@@LB@@eval extract: GOIMAGE := evil}' \
  'INDIR = GOIMAGE@@NL@@$@@LP@@INDIR) := evil' \
  '@@RP@@ := >@@NL@@@@TAB@@extract: GOIMAGE := evil'; do
  rp=$(printf '.%s' 'RECIPEPREFIX')
  cp "$mk" "$tmp"
  printf '%s\n' "$evil" | sed -e 's/@@NL@@/\n/g' -e 's/@@LP@@/(/g' -e 's/@@LB@@/{/g' -e 's/@@TAB@@/\t/g' -e "s/@@RP@@/$rp/g" >> "$tmp"
  if $MK -f "$tmp" -s toolchain-gate >/dev/null 2>&1; then
    echo "fido: toolchain-gate ACCEPTED a Makefile-side GOIMAGE mutation: $evil"; exit 1
  fi
done

# (3) Dockerfile drift + the detector's own coverage
for dfevil in \
  'ARG GOIMAGE=evil-default' \
  'arg GOIMAGE=evil-default' \
  'from @@GOIMG@@@sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa AS rogue' \
  '  FROM @@GOIMG@@@sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa AS rogue' \
  ; do
  cp Dockerfile "$tmp"
  printf '%s\n' "$dfevil" | sed -e 's/@@NL@@/\n/g' -e 's/@@GOIMG@@/golang/g' >> "$tmp"
  if sh plugin/toolchain-gate.sh "$mk" "$eff" "$tmp" >/dev/null 2>&1; then
    echo "fido: toolchain-gate ACCEPTED a Dockerfile mutation: $dfevil"; exit 1
  fi
done
{ head -1 Dockerfile; printf '  # escape=`\n'; tail -n +2 Dockerfile; \
  printf 'FROM `\n  gola%s@sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa AS rogue\n' ng; } > "$tmp"
if sh plugin/toolchain-gate.sh "$mk" "$eff" "$tmp" >/dev/null 2>&1; then
  echo "fido: toolchain-gate ACCEPTED an ACTIVE leading-whitespace escape directive + backtick-split rogue FROM"; exit 1
fi
re=$(sed -n "s/^GO_IMAGE_RE='\(.*\)'$/\1/p" plugin/toolchain-gate.sh)
test -n "$re" || { echo "fido: could not extract GO_IMAGE_RE from the gate script"; exit 1; }
printf 'x gola%s@sha256:aa\n' ng | grep -qE "$re" || { echo "fido: the Go-image detector misses DIGEST-ONLY spellings"; exit 1; }
printf 'x gola%s:1.99-alpine\n' ng | grep -qE "$re" || { echo "fido: the Go-image detector misses TAG spellings"; exit 1; }
sed 's/^FROM ${GOIMAGE} AS builder$/FROM alpine AS builder/' Dockerfile > "$tmp"
if sh plugin/toolchain-gate.sh "$mk" "$eff" "$tmp" >/dev/null 2>&1; then
  echo "fido: toolchain-gate ACCEPTED a builder FROM that bypasses \${GOIMAGE}"; exit 1
fi
echo "fido: toolchain-selftest OK — CLI/env overrides INERT; every tested Makefile-side mutation class + Dockerfile drift REJECTED ✓"
