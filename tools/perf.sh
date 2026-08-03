#!/bin/sh
# One diagnostic timing aid: run the real `make -j1 check` path once project-cold and once hot on a
# dedicated serial builder, record cumulative elapsed milliseconds at a few real target completions, and
# replace .review/PERFORMANCE.tsv.  `git diff` is the comparison.
#
# This is evidence, not a benchmark framework and not a gate.  Its complete behaviour should be obvious from
# reading it once.  Do not grow it to anticipate hypothetical future needs.
set -eu

root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"

BUILDER=fido-perf-v1
OUT=.review/PERFORMANCE.tsv

# ── Outside the measured interval: the builder and the stable toolchain layers ────────────────────────────
# A serial builder, because a timing that depends on how many stages happened to run in parallel is not a
# timing anyone can compare across runs.
if ! docker buildx inspect "$BUILDER" >/dev/null 2>&1; then
    cfg=$(mktemp -d)
    printf '[worker.oci]\n  max-parallelism = 1\n' > "$cfg/buildkitd.toml"
    docker buildx create --name "$BUILDER" --driver docker-container --buildkitd-config "$cfg/buildkitd.toml" \
        >/dev/null
    rm -rf "$cfg"
fi
docker buildx inspect --bootstrap "$BUILDER" >/dev/null

# Base images and pinned toolchain layers are acquired here, so no registry pull and no builder bootstrap
# lands inside a measured interval.  Cold means cold for the PROJECT, not an empty machine.
echo "fido: perf — priming stable toolchain layers (outside every measured interval)"
BUILDER="$BUILDER" make -j1 pytools >/dev/null

log=$(mktemp)
trap 'rm -f "$log"' EXIT INT TERM

now_ms() { IFS='. ' read -r s c _ < /proc/uptime; c=${c#0}; echo $(( s * 1000 + ${c:-0} / 10 )); }

run() {
    mode=$1
    echo "fido: perf — $mode: make -j1 check"
    t0=$(now_ms)
    printf '%s\t%s\t%s\n' "$mode" start 0 >> "$log"
    if [ "$mode" = cold ]; then FIDO_PERF_COLD=1; else FIDO_PERF_COLD=; fi
    FIDO_PERF_LOG="$log" FIDO_PERF_MODE="$mode" FIDO_PERF_T0="$t0" FIDO_PERF_COLD="$FIDO_PERF_COLD" \
        BUILDER="$BUILDER" make -j1 check
}

run cold
run hot

# ── Publication: only after BOTH runs succeeded ───────────────────────────────────────────────────────────
# A failed run leaves the tracked record exactly as it was, so the file always describes a pair of real
# successful invocations rather than the last thing that happened to finish.
tmp=$(mktemp)
{
    echo '# command: make -j1 check'
    echo "# builder: $BUILDER; BuildKit max-parallelism=1"
    echo '# cold: project stages forced (prover, emit); stable image/toolchain layers retained'
    echo '# hot: immediate repeat, same source and builder'
    echo '# clock: /proc/uptime, 10ms resolution; elapsed_ms is cumulative from that run start'
    printf 'mode\tcheckpoint\telapsed_ms\n'
    cat "$log"
} > "$tmp"
mv "$tmp" "$OUT"
chmod 644 "$OUT"

echo "fido: perf OK — $OUT replaced after two successful runs; the diff is the comparison:"
git diff -- "$OUT"
