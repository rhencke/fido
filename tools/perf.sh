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
PLATFORM=linux/amd64
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

# Every stable toolchain authority, built ON THE MEASURED BUILDER, so no registry pull and no toolchain
# construction can land inside a timed interval.  A fresh builder shares nothing with the developer's, so
# priming only Python left Rocq, OCaml and Go to be acquired inside the cold run the file called excluded.
# Cold means cold for the PROJECT, not an empty machine.
echo "fido: perf — priming stable toolchain layers on $BUILDER (outside every measured interval)"
for stage in python-tools rocq-builder rocq-base go-base; do
    docker buildx build --builder "$BUILDER" --platform "$PLATFORM" --target "$stage" . >/dev/null 2>&1
done

log=$(mktemp)
tmp=
trap 'rm -f "$log" ${tmp:+"$tmp"}' EXIT INT TERM

# /proc/uptime's fraction is HUNDREDTHS of a second, so a hundredth is ten milliseconds.  The leading zero is
# stripped because 08 and 09 are octal to the shell.
now_ms() { IFS='. ' read -r s c _ < /proc/uptime; c=${c#0}; echo $(( s * 1000 + ${c:-0} * 10 )); }

# BUILDER must be a COMMAND-LINE variable: the Makefile assigns it with `:=`, which overrides the
# environment, so an exported value would have been silently ignored and every measurement taken on the
# developer's ordinary builder while this file claimed otherwise.
run() {
    mode=$1
    cold=$2
    echo "fido: perf — $mode: make -j1 check"
    t0=$(now_ms)
    printf '%s\t%s\t%s\n' "$mode" start 0 >> "$log"
    FIDO_PERF_LOG="$log" FIDO_PERF_MODE="$mode" FIDO_PERF_T0="$t0" \
        make -j1 BUILDER="$BUILDER" FIDO_PERF_COLD="$cold" check
}

run cold 1
run hot ''

# ── Publication: only after BOTH runs succeeded ───────────────────────────────────────────────────────────
# The temporary file lives beside its destination so `mv` is a same-filesystem RENAME rather than a
# copy-and-remove, and its mode is set BEFORE publication so a chmod failure cannot report failure after the
# tracked record has already changed.  A failed run leaves the previous record exactly as it was.
tmp=$(mktemp "$root/.review/.PERFORMANCE.tsv.XXXXXX")
{
    echo '# command: make -j1 check'
    echo "# builder: $BUILDER; BuildKit max-parallelism=1"
    echo '# cold: project stages forced (prover, emit); stable image/toolchain layers primed on this builder'
    echo '# hot: immediate repeat, same source and builder'
    echo '# clock: /proc/uptime, 10ms resolution; elapsed_ms is cumulative from that run start'
    printf 'mode\tcheckpoint\telapsed_ms\n'
    cat "$log"
} > "$tmp"
chmod 644 "$tmp"
mv "$tmp" "$OUT"
tmp=

echo "fido: perf OK — $OUT replaced after two successful runs; the diff is the comparison:"
git diff -- "$OUT"
