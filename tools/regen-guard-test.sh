#!/bin/sh
# Structural regression for VALIDATE-BEFORE-PUBLISH — the ONE supported publication ordering.
#
# `make regenerate` builds the `sync` stage, which `COPY --from=go-e2e /fresh-build-ok`.  That Docker-DAG edge
# is the whole guarantee: the marker exists only if the go-e2e stage (the pinned one-shot `go build ./...` over
# the materialized pristine) completed successfully, so a FAILED fresh build must make `--target sync`
# unbuildable — no sink effect can occur.  This proves that edge is load-bearing.  (It is NOT resistance to a
# deliberate local bypass — that is explicitly out of scope; it guards against a broken or removed validation
# step for the cooperating workflow.)
#
#   (1) go-e2e FORCED TO FAIL (a temp Dockerfile copy) -> `--target sync` MUST fail to build.
#   (2) the unmodified Dockerfile                      -> `--target sync` MUST build.
#
# The go-e2e RUN uses `set -u` (not `set -e`), so a bare `false` would NOT abort it; the injection is `exit 1`
# placed exactly where the success marker would be written.
set -eu

BUILDER=${BUILDER:-fido-builder}
PLATFORM=${PLATFORM:-linux/amd64}
cd "$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)"

[ -f Dockerfile ] || { echo "regen-guard: no Dockerfile in $(pwd)"; exit 2; }
grep -q '^: > /fresh-build-ok$' Dockerfile \
  || { echo "regen-guard: the go-e2e success marker line ': > /fresh-build-ok' was not found — the DAG edge changed; update this test"; exit 2; }

tmp=$(mktemp "${TMPDIR:-/tmp}/Dockerfile.regen-guard.XXXXXX")
trap 'rm -f "$tmp"' EXIT INT TERM

# Replace the go-e2e success marker write with an unconditional failure, so the go-e2e stage exits nonzero and
# never records validation.  Everything before this line is byte-identical, so prover/emit stay cache-shared.
sed 's|^: > /fresh-build-ok$|exit 1  # regen-guard: forced go-e2e failure|' Dockerfile > "$tmp"
grep -q 'forced go-e2e failure' "$tmp" || { echo "regen-guard: failed to inject the go-e2e failure"; exit 2; }

echo "regen-guard: (1) building --target sync with go-e2e FORCED TO FAIL (must NOT build)..."
if docker buildx build --builder "$BUILDER" --platform "$PLATFORM" --target sync -f "$tmp" . >/dev/null 2>&1; then
  echo "regen-guard FAIL: --target sync BUILT despite a failing go-e2e — validate-before-publish is NOT load-bearing"
  exit 1
fi
echo "regen-guard: (1) OK — --target sync is UNBUILDABLE when go-e2e fails (the DAG edge blocks publication)"

echo "regen-guard: (2) building --target sync on the unmodified (passing) Dockerfile (must build)..."
if ! docker buildx build --builder "$BUILDER" --platform "$PLATFORM" --target sync -f Dockerfile . >/dev/null 2>&1; then
  echo "regen-guard FAIL: --target sync did not build on the passing tree"
  exit 1
fi
echo "regen-guard: (2) OK — --target sync builds when go-e2e passes"

echo "regen-guard OK — validate-before-publish DAG edge confirmed load-bearing (go-e2e fail => sync unbuildable; pass => buildable)"
