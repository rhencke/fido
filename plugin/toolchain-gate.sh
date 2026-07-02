#!/bin/sh
# fido toolchain-gate — the GOIMAGE ONE-AUTHORITY checker (Make-aware, fail-closed).
#   usage: toolchain-gate.sh <makefile> <effective-goimage-value>
# What it mechanically enforces, in order:
#   1. NO dynamic-parse constructs: $(eval ...) / ${eval ...} are banned ANYWHERE in the makefile —
#      including recipe lines, where make expands them before the shell runs (a recipe-prefixed
#      eval is a make-side mutation, not shell).
#   2. Logical lines are NORMALIZED (GNU make joins a trailing-backslash line with the next) before
#      any assignment scanning, so a continued target-specific assignment cannot hide.
#   3. NO include of any spelling (include / -include / sinclude): this file is the WHOLE parse.
#   4. Exactly ONE logical line assigns GOIMAGE, in ANY form (global, target-/pattern-specific,
#      private/override/export-prefixed, define), and it is the strict digest-pinned authority.
#   5. NO computed assignment LHS ($(...) or ${...} before the first operator) — an expanded LHS
#      could name GOIMAGE indirectly.
#   6. The EFFECTIVE value equals the authority line's RHS exactly.
#   7. The only repo-wide Go-image spelling is the authority line; the Dockerfile ARG is
#      default-less (the makefile is the only source of the image).
set -eu
mk="$1"; eff="$2"

# (1) eval ban — every physical line, recipes included.
if grep -nE '\$[({][[:space:]]*eval' "$mk"; then
  echo "fido: TOOLCHAIN DRIFT — \$(eval)/\${eval} is BANNED (dynamic make-side mutation, even in recipes)"; exit 1
fi

# (2) logical-line normalization (join trailing-backslash continuations).
norm=$(awk '{ if (sub(/\\$/, "")) { buf = buf $0 " "; next } print buf $0; buf = "" } END { if (buf != "") print buf }' "$mk")

# (3) include ban — logical-line level.
if printf '%s\n' "$norm" | grep -nE '^[ \t]*-?s?include([ \t]|$)'; then
  echo "fido: TOOLCHAIN DRIFT — include/-include/sinclude is BANNED (the scan covers only this file)"; exit 1
fi

# (4) exactly one GOIMAGE-assigning logical line, and it is the strict authority.
assigns=$(printf '%s\n' "$norm" | awk '!/^\t/ && !/^[ \t]*#/ && (/GOIMAGE[ \t]*(:=|::=|:::=|\+=|\?=|!=|=)/ || /define[ \t]+GOIMAGE/) { print $0 }')
n=$(printf '%s' "$assigns" | grep -c . || true)
if [ "$n" != "1" ]; then
  echo "fido: TOOLCHAIN DRIFT — expected exactly ONE logical line assigning GOIMAGE (any form), found $n:"
  printf '%s\n' "$assigns"; exit 1
fi
printf '%s\n' "$assigns" | grep -qE '^override GOIMAGE := golang[:][0-9A-Za-z._-]+@sha256:[0-9a-f]{64} ?$' || {
  echo "fido: TOOLCHAIN DRIFT — the single GOIMAGE assignment is not the strict authority form:"
  printf '%s\n' "$assigns"; exit 1
}

# (5) computed-LHS ban (a $(...) / ${...} before the first assignment operator, non-recipe lines).
if printf '%s\n' "$norm" | awk '!/^\t/ && !/^[ \t]*#/' | grep -nE '^[^=]*\$[({][^=]*(:=|::=|:::=|\+=|\?=|!=|=)'; then
  echo "fido: TOOLCHAIN DRIFT — a computed assignment LHS is BANNED (\$(X) := ... can name GOIMAGE indirectly)"; exit 1
fi

# (6) effective == authority RHS.
rhs=$(printf '%s\n' "$norm" | sed -n 's/^override GOIMAGE := //p' | sed 's/ *$//')
[ "$eff" = "$rhs" ] || {
  echo "fido: TOOLCHAIN DRIFT — effective GOIMAGE '$eff' != the authority value '$rhs'"; exit 1
}

# (7) repo-wide: no other Go-image spelling; Dockerfile ARG default-less.
bad=$(git grep -nI "golang[:]" -- . 2>/dev/null | grep -v "^Makefile:[0-9]*:override GOIMAGE := golang[:]" || true)
if [ -n "$bad" ]; then
  echo "fido: TOOLCHAIN DRIFT — a Go-image spelling outside the single GOIMAGE authority line:"
  echo "$bad"; exit 1
fi
grep -q '^ARG GOIMAGE$' Dockerfile || {
  echo "fido: TOOLCHAIN DRIFT — the Dockerfile GOIMAGE ARG must be DEFAULT-LESS"; exit 1
}

echo "fido: toolchain-gate OK — one strict GOIMAGE authority (logical-line scan; eval/include/computed-LHS banned; effective == authority) ✓"
