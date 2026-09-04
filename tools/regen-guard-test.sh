#!/bin/sh
# Structural regression for VALIDATE-BEFORE-PUBLISH — the ONE supported publication ordering.
#
# `make regenerate` builds the `sync` stage, which `COPY --from=go-e2e /fresh-build-ok` and
# `COPY --from=emit-controls /workspace/emit-controls-ok`.  Those Docker-DAG edges are the whole guarantee: each
# marker exists only if its stage (the pinned one-shot `go build ./...` over the materialized pristine; the
# emit-side proof matrix, audits, adversaries and sink exercise) completed successfully, so a FAILED validation
# must make `--target sync` unbuildable — no sink effect can occur.  This proves both edges are load-bearing.
# (It is NOT resistance to a deliberate local bypass — that is explicitly out of scope; it guards against a
# broken or removed validation step for the cooperating workflow.)
#
#   (1)  go-e2e FORCED TO FAIL (a temp Dockerfile copy)        -> `--target sync` MUST fail to build.
#   (1b) emit-controls FORCED TO FAIL (a temp Dockerfile copy) -> `--target sync` MUST fail to build.
#   (2)  the unmodified Dockerfile                             -> `--target sync` MUST build.
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
grep -q '^touch /workspace/emit-controls-ok$' Dockerfile \
  || { echo "regen-guard: the emit-controls marker line 'touch /workspace/emit-controls-ok' was not found — the DAG edge changed; update this test"; exit 2; }

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

sed 's|^touch /workspace/emit-controls-ok$|exit 1  # regen-guard: forced emit-controls failure|' Dockerfile > "$tmp"
grep -q 'forced emit-controls failure' "$tmp" || { echo "regen-guard: failed to inject the emit-controls failure"; exit 2; }
echo "regen-guard: (1b) building --target sync with emit-controls FORCED TO FAIL (must NOT build)..."
if docker buildx build --builder "$BUILDER" --platform "$PLATFORM" --target sync -f "$tmp" . >/dev/null 2>&1; then
  echo "regen-guard FAIL: --target sync BUILT despite failing emit-controls — validate-before-publish is NOT load-bearing"
  exit 1
fi
echo "regen-guard: (1b) OK — --target sync is UNBUILDABLE when emit-controls fails (the DAG edge blocks publication)"

echo "regen-guard: (2) building --target sync on the unmodified (passing) Dockerfile (must build)..."
if ! docker buildx build --builder "$BUILDER" --platform "$PLATFORM" --target sync -f Dockerfile . >/dev/null 2>&1; then
  echo "regen-guard FAIL: --target sync did not build on the passing tree"
  exit 1
fi
echo "regen-guard: (2) OK — --target sync builds when go-e2e and emit-controls pass"

echo "regen-guard OK — validate-before-publish DAG edges confirmed load-bearing (go-e2e fail or emit-controls fail => sync unbuildable; pass => buildable)"
