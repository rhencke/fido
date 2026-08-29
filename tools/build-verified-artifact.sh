#!/bin/sh
# The ONE project-verification Buildx solve.
#
# It builds the final `generated-artifact` target, whose BuildKit graph IS the complete verification DAG:
# one shared theory-built parent (the single `dune build @install @all`), the proof/audit branch (whole-theory
# audit + every control, ending in /workspace/proof-ok), the emit branch (materialization + fixtures + e2e
# audit + sink controls) feeding go-e2e (pinned `go build ./...` + goldens + differentials, ending in
# /fresh-build-ok), and the verified join that requires BOTH markers and carries the exact pristine generated
# module.  The export contains exactly go.mod + the recursive generated .go — nothing else.
#
# Both `make check` and the staged pre-commit hook call THIS script (the hook calls the staged copy against
# the staged context), so the complete path issues exactly one project solve; the Buildx exit status is
# propagated exactly, and a failed branch fails the solve — no sibling can mask it.
#
# --project-cold invalidates every project-derived stage (theory-built, prover, emit, go-e2e, verified-join,
# generated-artifact) via --no-cache-filter while base/toolchain layers stay primed.  The Dune `_build` cache
# mount may still warm the theory build's internal cost; the scenario evidence records cache state exactly.
set -eu
BUILDER=fido-builder PLATFORM=linux/amd64 CONTEXT=. OUTPUT= COLD= PLAIN=
while [ $# -gt 0 ]; do
  case "$1" in
    --builder)      BUILDER=$2;  shift 2 ;;
    --platform)     PLATFORM=$2; shift 2 ;;
    --context)      CONTEXT=$2;  shift 2 ;;
    --output)       OUTPUT=$2;   shift 2 ;;
    --project-cold) COLD=1;      shift ;;
    --plain-log)    PLAIN=$2;    shift 2 ;;
    *) echo "build-verified-artifact: unknown argument $1" >&2; exit 2 ;;
  esac
done
[ -n "$OUTPUT" ] || { echo "build-verified-artifact: --output <dir> is required" >&2; exit 2; }
set -- docker buildx build --builder "$BUILDER" --platform "$PLATFORM" \
  --target generated-artifact --output "type=local,dest=$OUTPUT"
if [ -n "$COLD" ]; then
  for st in theory-built prover emit go-e2e verified-join generated-artifact; do
    set -- "$@" --no-cache-filter "$st"
  done
fi
if [ -n "$PLAIN" ]; then
  "$@" --progress=plain "$CONTEXT" > "$PLAIN" 2>&1
else
  "$@" "$CONTEXT"
fi
