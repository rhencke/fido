#!/bin/sh
# fido toolchain-gate — the GOIMAGE ONE-AUTHORITY checker (Make-aware, fail-closed).
#   usage: toolchain-gate.sh <makefile> <effective-goimage-value> [dockerfile]
# What it mechanically enforces, in order:
#   1. NO dynamic-parse constructs: $(eval ...) / ${eval ...} are banned ANYWHERE in the makefile —
#      including recipe lines, where make expands them before the shell runs — and .RECIPEPREFIX is
#      banned (it would re-type tab lines from recipe-shell into make syntax, breaking the
#      recipe-line classification below).
#   2. Logical lines are NORMALIZED (GNU make joins a trailing-backslash line with the next) before
#      any assignment scanning, so a continued target-specific assignment cannot hide.
#   3. NO include of any spelling (include / -include / sinclude): this file is the WHOLE parse.
#   4. Exactly ONE logical line assigns GOIMAGE, in ANY form (global, target-/pattern-specific,
#      private/override/export-prefixed, define), and it is the strict digest-pinned authority.
#   5. NO computed assignment LHS ($(...) or ${...} before the first operator) — an expanded LHS
#      could name GOIMAGE indirectly.
#   6. The EFFECTIVE value equals the authority line's RHS exactly.
#   7. The only repo-wide Go-image reference (TAG or DIGEST-ONLY spelling) is the authority line;
#      the Dockerfile bans ALL escape parser directives in any position or spelling, Docker's
#      leading-whitespace comment rule included (a directive would re-type the continuation
#      character the normalizer assumes), has EXACTLY ONE default-less ARG GOIMAGE, and the builder
#      stage consumes it verbatim (FROM ${GOIMAGE} AS builder) with no other FROM referencing a Go
#      image.
set -eu
mk="$1"; eff="$2"; df="${3:-Dockerfile}"
# THE Go-image reference detector — tag OR digest-only spellings (single-sourced; the selftest
# asserts its coverage directly).
GO_IMAGE_RE='golang[:@]'

# (1) eval + .RECIPEPREFIX bans — every physical line, recipes included.
if grep -nE '\$[({][[:space:]]*eval' "$mk"; then
  echo "fido: TOOLCHAIN DRIFT — \$(eval)/\${eval} is BANNED (dynamic make-side mutation, even in recipes)"; exit 1
fi
if grep -n '\.RECIPEPREFIX' "$mk"; then
  echo "fido: TOOLCHAIN DRIFT — .RECIPEPREFIX is BANNED (it re-types tab lines from recipe-shell into make syntax)"; exit 1
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

# (7) repo-wide: no other Go-image spelling; the Dockerfile's ARG is UNIQUE and default-less and
#     the builder stage consumes it verbatim.  Dockerfile instructions are CASE-INSENSITIVE and may
#     be indented or backslash-continued, so the file is NORMALIZED first (continuations joined,
#     leading whitespace stripped, the opcode uppercased) and every check runs on normalized lines.
bad=$(git grep -nIE "$GO_IMAGE_RE" -- . 2>/dev/null | grep -v "^Makefile:[0-9]*:override GOIMAGE := golang[:]" || true)
if [ -n "$bad" ]; then
  echo "fido: TOOLCHAIN DRIFT — a Go-image spelling (tag or digest form) outside the single GOIMAGE authority line:"
  echo "$bad"; exit 1
fi
if grep -niE '^[[:space:]]*#[[:space:]]*escape[[:space:]]*=' "$df"; then
  echo "fido: TOOLCHAIN DRIFT — an escape parser directive is BANNED in any position/spelling (Docker ignores leading whitespace before comments; a directive would re-type the continuation character the normalizer assumes)"; exit 1
fi
dfnorm=$(awk '{ if (sub(/\\$/, "")) { buf = buf $0 " "; next } print buf $0; buf = "" } END { if (buf != "") print buf }' "$df" \
  | awk '{ sub(/^[ \t]+/, "");
           if (match($0, /^[A-Za-z]+/)) { $0 = toupper(substr($0, RSTART, RLENGTH)) substr($0, RLENGTH + 1) }
           print }')
n_arg=$(printf '%s\n' "$dfnorm" | grep -cE '^ARG[ \t]+GOIMAGE([ \t]*$|=)' || true)
if [ "$n_arg" != "1" ]; then
  echo "fido: TOOLCHAIN DRIFT — expected exactly ONE normalized 'ARG GOIMAGE' in $df, found $n_arg (a duplicate/defaulted ARG is a second authority)"; exit 1
fi
printf '%s\n' "$dfnorm" | grep -qE '^ARG[ \t]+GOIMAGE[ \t]*$' || {
  echo "fido: TOOLCHAIN DRIFT — the single ARG must be default-less ('ARG GOIMAGE')"; exit 1
}
n_from=$(printf '%s\n' "$dfnorm" | grep -cE '^FROM[ \t]+\$\{GOIMAGE\}[ \t]+AS[ \t]+builder[ \t]*$' || true)
if [ "$n_from" != "1" ]; then
  echo "fido: TOOLCHAIN DRIFT — the builder stage must consume the ARG verbatim: exactly one normalized 'FROM \${GOIMAGE} AS builder' in $df (found $n_from)"; exit 1
fi
if printf '%s\n' "$dfnorm" | grep -E '^FROM[ \t]' | grep -v -E '\$\{GOIMAGE\}[ \t]+AS[ \t]+builder[ \t]*$' | grep -iE 'golang'; then
  echo "fido: TOOLCHAIN DRIFT — another FROM references a Go image"; exit 1
fi

echo "fido: toolchain-gate OK — one strict GOIMAGE authority: Makefile logical-line scan (eval/include/.RECIPEPREFIX/computed-LHS banned), effective == authority, repo-wide single Go-image reference (tag+digest forms), normalized Dockerfile (escape-directive ban, one default-less ARG, verbatim builder FROM, no rogue Go FROM) ✓"
