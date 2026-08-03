# M2 — Performance Snapshot

> **Live checkpoint contract.** Installed by Rob's human disposition
> `.review/M2_GREAT_MEASUREMENT_CULLING.md`. <!-- FIDO-FCB-REF:REVIEW-M2-GREAT-MEASUREMENT-CULLING-MD -->
> The withdrawn experiment survives only in Git history.
> **Obligations:** `.review/M2_OBLIGATION_MATRIX.tsv`. **Review basis:** `.review/REVIEW_BASIS.md`.

Only Rob accepts M2.

---

# 1. Purpose

Answer one question, cheaply: **where does `make check` spend its time, cold and hot, and did that change?**

Performance timing is diagnostic evidence. It is **not** certified correctness, not a semantic authority, not
a benchmark framework, and not an acceptance gate. Nothing in the proof, transport, generated-byte or
publication path depends on it, and no gate consults it.

The implementation must stay understandable in one sitting.

---

# 2. Interface

```text
make perf
```

It invokes `sh tools/perf.sh` <!-- FIDO-FCB-REF:TOOLS-PERF-SH --> and nothing else. It replaces `.review/PERFORMANCE.tsv`; inspect `git diff`.

`make perf` is a dependency of nothing — not `make check`, not `make fcb`, not the pre-commit hook, not any
correctness or publication gate.

---

# 3. The canonical subject

```text
make -j1 check
```

Both measurements run that exact public path. There is no parallel `perf-check` target, no duplicated recipe
and no reconstruction of the dependency graph inside the script.

The script uses a dedicated serial Buildx builder, `fido-perf-v1`, with BuildKit max-parallelism 1 and Make
jobs 1. Ordinary development, ordinary `make check` and the real pre-commit hook keep their existing
parallelism and behaviour.

---

# 4. Cold and hot

**Project-stage cold, not empty-cache cold.** Before the timed interval the builder exists, base images are
local, and the pinned Python, Rocq, Dune, OCaml and Go toolchain layers are available. Builder bootstrap and
registry pulls are outside the interval. The cold invocation runs the real path while forcing the
project-dependent roots — `prover` and `emit` and the descendants `make check` requires — through the
existing Buildx `--no-cache-filter` mechanism. The tracked file states this honestly.

**Hot** is the same `make -j1 check` immediately afterwards, same builder, same source tree, no project
invalidation. No file changes between the two.

**Publication.** Results are written to a temporary file beside `.review/PERFORMANCE.tsv`, its final mode is
set before publication, and it is renamed over the destination only after both runs succeed. A failed run
leaves the tracked record untouched. The temporary shares the destination's directory because a rename is
atomic only within one filesystem; a temporary elsewhere would degrade to copy-and-remove.

---

# 5. Completion checkpoints

Cumulative elapsed milliseconds at these real target boundaries:

```text
pytools  hostpython  names  fcb  claims  diet  prove  e2e  check
```

A marker is a completion timestamp — not a nested span, trace, parent, partition, or proof of attribution.
The clock is the monotonic host clock the shell already has (`/proc/uptime`); there is no clock abstraction.

The Makefile carries one tiny macro that is inert unless `tools/perf.sh` supplies a metrics log and a run
start. It never parses, validates, compares or retains timing data. With timing disabled the markers produce
no output and alter no order, bytes, exit status or side effect. There are no pre-commit timing markers: the
canonical subject is `make check`, not the hook.

---

# 6. The tracked record

`.review/PERFORMANCE.tsv` <!-- FIDO-FCB-REF:REVIEW-PERFORMANCE-TSV --> is the sole retained performance record, in a plain diffable form. It stores no raw
logs, medians, percentages, verdicts, environment fingerprints, cache-stage maps, history analysis, module
graphs, source inventories, trace or sample identities, log hashes or validation metadata.

Git owns the historical sequence. **`git diff` is the comparison mechanism**; the project ships no comparison
implementation.

It is listed in `.dockerignore` so updating the record cannot invalidate project Buildx layers, and it stays
tracked by Git.

---

# 7. Scope

M2 delivers exactly: one `make perf` target, one small POSIX shell script, one tracked TSV, and a handful of
inert completion markers in the existing `make check` path.

**Unsupported by design — no mutation-test obligation.** This facility has no mutation-test coverage
obligation and no performance-specific permanent gate, because it makes no correctness claim to protect. The
existing correctness gates test the path being timed; a diagnostic timer does not need a second correctness
system built around it. Matrix cells state that boundary explicitly rather than inventing a control.

Do not recreate any deleted abstraction under a new name: no registry, configuration language, resume,
partial selector, statistical analysis, self-test framework, bundle hierarchy, schema or comparison
implementation.

---

# 8. Exit condition

M2 is complete when `make perf` runs the exact serial `make check` path project-cold and then hot; the tracked TSV
holds that result and changes only after both runs succeed; every correctness, proof, artifact and runtime
check remains green; and one exact replacement candidate is frozen for Rob's review.
