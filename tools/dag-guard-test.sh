#!/bin/sh
# Structural regression for the ONE-BUILD VERIFICATION DAG — the final `generated-artifact` target must be
# UNBUILDABLE when any verification branch fails or any marker dependency is broken, and buildable on
# the unmodified passing tree.  Each mutation is a valid Dockerfile whose graph fails for the intended
# invariant (never a syntax typo):
#
#   (1) proof branch FORCED TO FAIL (exit where /workspace/proof-ok would be written)
#         -> `--target generated-artifact` MUST fail (the join requires the proof marker).
#   (2) go-e2e FORCED TO FAIL (exit where /fresh-build-ok would be written)
#         -> `--target generated-artifact` MUST fail (the join requires the fresh-build marker).
#   (2b) emit-controls FORCED TO FAIL (exit where /workspace/emit-controls-ok would be written)
#         -> `--target generated-artifact` MUST fail (the join requires the emit-controls marker; go-e2e
#            alone, which consumes only the materialization, cannot satisfy it).
#   (3) the proof marker write REMOVED (branch succeeds, marker absent)
#         -> the join's COPY --from=prover /workspace/proof-ok MUST fail: a green-but-markerless branch
#            cannot satisfy the join, even with every generated-module layer cached.
#   (4) the unmodified Dockerfile -> `--target generated-artifact` MUST build.
#
# Like regen-guard, this proves the DAG edges are load-bearing for the cooperating workflow; it is not
# resistance to a deliberate local bypass.
set -eu

BUILDER=${BUILDER:-fido-builder}
PLATFORM=${PLATFORM:-linux/amd64}
cd "$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)"

[ -f Dockerfile ] || { echo "dag-guard: no Dockerfile in $(pwd)"; exit 2; }
grep -q '^touch /workspace/proof-ok$' Dockerfile \
  || { echo "dag-guard: the proof marker line 'touch /workspace/proof-ok' was not found — the DAG changed; update this test"; exit 2; }
grep -q '^: > /fresh-build-ok$' Dockerfile \
  || { echo "dag-guard: the go-e2e marker line ': > /fresh-build-ok' was not found — the DAG changed; update this test"; exit 2; }
grep -q '^touch /workspace/emit-controls-ok$' Dockerfile \
  || { echo "dag-guard: the emit-controls marker line 'touch /workspace/emit-controls-ok' was not found — the DAG changed; update this test"; exit 2; }

tmp=$(mktemp "${TMPDIR:-/tmp}/Dockerfile.dag-guard.XXXXXX")
trap 'rm -f "$tmp"' EXIT INT TERM

build() { docker buildx build --builder "$BUILDER" --platform "$PLATFORM" --target generated-artifact -f "$1" . >/dev/null 2>&1; }

echo "dag-guard: (1) proof branch FORCED TO FAIL (must NOT build the final artifact)..."
sed 's|^touch /workspace/proof-ok$|exit 1  # dag-guard: forced proof-branch failure|' Dockerfile > "$tmp"
grep -q 'forced proof-branch failure' "$tmp" || { echo "dag-guard: injection (1) failed"; exit 2; }
if build "$tmp"; then
  echo "dag-guard FAIL: the final artifact BUILT despite a failing proof branch"; exit 1
fi
echo "dag-guard: (1) OK — a failing proof/audit branch makes the final artifact unbuildable"

echo "dag-guard: (2) go-e2e FORCED TO FAIL (must NOT build the final artifact)..."
sed 's|^: > /fresh-build-ok$|exit 1  # dag-guard: forced go-e2e failure|' Dockerfile > "$tmp"
grep -q 'forced go-e2e failure' "$tmp" || { echo "dag-guard: injection (2) failed"; exit 2; }
if build "$tmp"; then
  echo "dag-guard FAIL: the final artifact BUILT despite a failing Go validation"; exit 1
fi
echo "dag-guard: (2) OK — a failing Go branch makes the final artifact unbuildable"

echo "dag-guard: (2b) emit-controls FORCED TO FAIL (must NOT build the final artifact)..."
sed 's|^touch /workspace/emit-controls-ok$|exit 1  # dag-guard: forced emit-controls failure|' Dockerfile > "$tmp"
grep -q 'forced emit-controls failure' "$tmp" || { echo "dag-guard: injection (2b) failed"; exit 2; }
if build "$tmp"; then
  echo "dag-guard FAIL: the final artifact BUILT despite a failing emit-controls branch"; exit 1
fi
echo "dag-guard: (2b) OK — a failing emit-controls branch makes the final artifact unbuildable"

echo "dag-guard: (3) proof marker OMITTED from a green branch (must NOT build the final artifact)..."
sed 's|^touch /workspace/proof-ok$|true  # dag-guard: marker write removed, branch still green|' Dockerfile > "$tmp"
grep -q 'marker write removed' "$tmp" || { echo "dag-guard: injection (3) failed"; exit 2; }
if build "$tmp"; then
  echo "dag-guard FAIL: the final artifact BUILT although the proof marker was never written"; exit 1
fi
echo "dag-guard: (3) OK — a green-but-markerless proof branch cannot satisfy the verified join"

echo "dag-guard: (4) the unmodified Dockerfile (must build)..."
if ! build Dockerfile; then
  echo "dag-guard FAIL: the final artifact did not build on the passing tree"; exit 1
fi
echo "dag-guard: (4) OK — the final artifact builds when every branch passes"

echo "dag-guard OK — the verified join is load-bearing (proof fail / Go fail / emit-controls fail / missing marker => final artifact unbuildable; passing tree => buildable)"
