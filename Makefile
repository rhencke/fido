BUILDER := fido-builder
# The 64-bit target the theory assumes; `override` makes a command-line or environment change inert.
override PLATFORM := linux/amd64
# Project-stage cold, for `make perf` alone: unset, this expands to nothing and every recipe below is
# exactly the one that has always run.  Set, it forces the project roots `make check` depends on to rebuild
# while their stable toolchain ancestors stay cache hits — cold for the project, not an empty machine.
NOCACHE := $(if $(FIDO_PERF_COLD),prover emit,)
NC := $(foreach root,$(NOCACHE),--no-cache-filter $(root))

# ── The Python boundary ───────────────────────────────────────────────────────
# Project Python never runs on the host.  This block is the whole boundary: every Python-consuming recipe
# below goes through PYRUN or PYWRITE, and none of them names an interpreter itself.  The host needs only
# shell, Make, Git, Docker and Buildx.
#
# The tag is content-addressed over the two files that define the image, so changing the pin or the lock
# builds a new tag and a stale image cannot be reused; an unchanged pin costs one `docker image inspect`.
# Sources are MOUNTED rather than copied in, so a gate inspects exactly the source view named at the mount
# — the working tree here, the exported index in the hook — and no COPY set can silently go stale.
# The mount is read-only for every gate; PYWRITE exists only for the writers, which publish under §7.
PYTAG   := fido-python-tools:$(shell cat Dockerfile tools/python-requirements.lock | sha256sum | cut -c1-16)
PYARGS  := --rm -u $(shell id -u):$(shell id -g) -e PYTHONDONTWRITEBYTECODE=1 -e HOME=/tmp \
           -e GIT_CONFIG_COUNT=1 -e GIT_CONFIG_KEY_0=safe.directory -e GIT_CONFIG_VALUE_0=/repo -w /repo
PYRUN    = docker run $(PYARGS) -v "$(CURDIR)":/repo:ro $(PYTAG) python3
PYWRITE  = docker run $(PYARGS) -v "$(CURDIR)":/repo    $(PYTAG) python3

# ── Completion markers.  INERT unless FIDO_PERF_LOG names a file: with the variable absent the `if` is
# false and nothing is written, so command order, bytes, output, exit status, side effects and normal
# parallelism are exactly what they were.  A measurement that alters what it measures is not a measurement.
#
# A marker is a COMPLETION TIMESTAMP and nothing else — not a nested span, not a trace, not a parent, not a
# partition, and not a proof of attribution.  Cumulative milliseconds since the run start `tools/perf.sh`
# supplies; a reader subtracts adjacent rows.  CLOCK_MONOTONIC from /proc/uptime, because a wall clock can
# step under NTP and a duration that can go backwards is not a duration.  The centiseconds field is two
# digits, so 08 and 09 read as OCTAL and silently drop a marker — stripping the leading zero is the POSIX
# fix, and `10#` would be a bashism.
#
# The Makefile never parses, validates, compares or retains timing data.
define fido_mark
@if [ -n "$$FIDO_PERF_LOG" ]; then IFS='. ' read -r _s _c _r < /proc/uptime; _c=$${_c#0}; \
  printf '%s\t%s\t%s\n' "$$FIDO_PERF_MODE" '$(1)' \
    $$(( _s * 1000 + $${_c:-0} / 10 - $${FIDO_PERF_T0:-0} )) >> "$$FIDO_PERF_LOG"; fi
endef

# Build the pinned tooling images if this exact tag is not already present.  Never a rebuild of an existing
# tag: the tag changed if and only if its inputs did.
pytools: builder
	@docker image inspect $(PYTAG) > /dev/null 2>&1 || \
	  docker buildx build --builder $(BUILDER) --platform $(PLATFORM) --target python-tools \
	    --load -t $(PYTAG) . > /dev/null
	$(call fido_mark,pytools)

.PHONY: check prove emit e2e regenerate regen-guard builder install-hooks prover-log prove-errors fmt names \
        fcb fcb-write claims diet audit-fresh profile perf pytools hostpython
.DEFAULT_GOAL := check

# All Rocq and Go work runs in the pinned container through buildx; host Rocq is not supported.

# `make check` verifies the WORKING TREE.  Two choices in the recipe below are load-bearing:
#   `tools/worktree-list.py` owns the inventory — which paths Git considers part of the tree, and which of
#     them are actually present on disk — and its own controls run first, so a green here is one it earned;
#   plain `tar` (no --ignore-failed-read) makes an existing-but-unreadable file fail loudly.
# `.dockerignore` hides the committed go.mod and .go from Buildx, so the pristine is independent of the
# tracked bytes — which is what catches a header-preserving edit to a tracked `.go`.  The staged snapshot,
# and the exact-Git-mode gate over it, are the pre-commit hook's job rather than this one's.
# `check` is the canonical performance subject: its own wall time is the whole process, which `make perf`
# invocation rather than from inside it — its prerequisites have already run by the time this recipe starts,
# so an anchor here would begin after most of the work.  What this recipe body IS, is the working-tree
# archive and generated compare, and §7 requires that unowned segment to carry its own stable ID so the
# parent partitions into children plus explicit overhead instead of hiding the difference.
check: pytools hostpython names fcb claims diet prove e2e builder
	@tmp=$$(mktemp -d); tree="$$tmp/tree"; mkdir -p "$$tree"; \
	  $(PYRUN) tools/worktree-list.py --self-test && \
	  $(PYRUN) tools/worktree-list.py > "$$tmp/list.nul" && \
	  tar --null -T "$$tmp/list.nul" -cf "$$tmp/tree.tar" && \
	  tar -xf "$$tmp/tree.tar" -C "$$tree" && \
	  sh tools/ocaml-origin-gate.sh    "$$tree" && \
	  sh tools/generated-output-gate.sh "$$tree" && \
	  docker buildx build --builder $(BUILDER) --platform $(PLATFORM) $(NC) --target generated-artifact \
	    --output "type=local,dest=$$tmp/pristine" . && \
	  sh tools/staged-generated-compare.sh "$$tree" "$$tmp/pristine"; \
	  rc=$$?; rm -rf "$$tmp"; \
	  if [ $$rc -eq 0 ]; then echo "fido: check OK (working tree) — proved the core axiom-free (whole-theory audit run in prove) AND materialized the pristine generated-module (Fido Materialize) + validated it through go build ./... vs goldens (the internal sibling-temp sink exercised separately); the working-tree generated go.mod + recursive .go byte-match the pristine artifact (exact path set + bytes); transport-only OCaml, tracked Go is Fido-headed generated output ✓"; fi; \
	  exit $$rc
	$(call fido_mark,check)

# The reproducible container proof: dune compiles the modules + the always-run assumptions gate.
prove: builder
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) $(NC) --target prover .
	$(call fido_mark,prove)

prover-log: builder
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) $(NC) --progress=plain --target prover .

# Diagnostic only, never a gate.  Recompiles ONE module with `-time` and ranks its sentences by cost, so a
# slow build can be attributed instead of guessed at.  `make profile FILE=Typing.v TOP=25`.
FILE ?= Compilable.v
TOP  ?= 40
profile: pytools builder
	@out=$${TMPDIR:-/tmp}/fido-profile; rm -rf "$$out"; mkdir -p "$$out"; \
	  docker buildx build --builder $(BUILDER) --platform $(PLATFORM) --progress=plain \
	    --target profile-log --build-arg PROFILE_FILE=$(FILE) --no-cache-filter profile \
	    --output "type=local,dest=$$out" . && \
	  docker run $(PYARGS) -v "$(CURDIR)":/repo:ro -v "$$out":/out:ro $(PYTAG) \
	    python3 tools/rocq-profile.py $(FILE) /out/time.log $(TOP) > "$$out/ranked.txt"; \
	  rc=$$?; cat "$$out/ranked.txt" 2>/dev/null; \
	  echo "fido: raw -time log kept at $$out/time.log, ranked report at $$out/ranked.txt"; exit $$rc

# The emit stage alone: theory and plugin, then each witness materializes its pristine image through an
# explicit `rocq c`, not a .vo side effect.  The internal sink is exercised separately, against dirty and
# adversarial trees.  The fresh-build validation that gates real publication is in `e2e`.
emit: builder
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) $(NC) --progress=plain --target emit .

# Emit the whole tree, then the pinned Go toolchain builds it and runs the witness against the goldens.
e2e: builder
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) $(NC) --progress=plain --target go-e2e .
	$(call fido_mark,e2e)

# Regenerate the tracked module through the one validate-before-publish workflow.  Building `sync` FORCES
# the pinned `go build ./...` through the Docker DAG (`sync` COPYs go-e2e's /fresh-build-ok), so a failed
# fresh build makes `sync` unbuildable and no sink effect occurs.  It publishes the original pristine bytes,
# never a post-build one.
regenerate: builder
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) $(NC) --target sync --load -t fido-sync .
	docker run --rm -u $$(id -u):$$(id -g) -v "$(CURDIR)":/dest fido-sync
	@echo "fido: regenerate OK — building 'sync' forced the pinned go build ./... (Docker DAG), then the SAME pristine bytes were synced into the repo root via Sink."
	@echo "      Stage + commit:  git add -A -- go.mod ':(top,glob)**/*.go' && git commit"

# Force the proof gate and the whole-tree e2e to RUN rather than report a Buildx cache hit.  A cached
# verdict is valid, but an audit should observe its assertions rather than infer them from a cache key.
audit-fresh: builder
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) --progress=plain \
	  --no-cache-filter prover --target prover .
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) --progress=plain \
	  --no-cache-filter go-e2e --target go-e2e .

# With go-e2e forced to FAIL on a temp Dockerfile copy, `--target sync` must be unbuildable, and on the
# unmodified tree it must build — so `make regenerate` cannot publish without a validated fresh build.
regen-guard: builder
	BUILDER=$(BUILDER) PLATFORM=$(PLATFORM) sh tools/regen-guard-test.sh

# Whitespace check against `.editorconfig`, with property resolution delegated to the EditorConfig reference
# implementation.  It reports and never rewrites, because this tree is full of byte-exact artifacts.
# Deliberately not a gate: every whitespace case that can break something is caught by a stronger check.
# The PERMANENT no-host-Python boundary: project Python runs only in the pinned image, and the host needs
# only shell, Make, Git, Docker and Buildx.  Its adversarial controls run first, so a green here is one the
# checker can still earn.
hostpython: pytools
	@$(PYRUN) tools/host-python-gate.py --self-test
	@$(PYRUN) tools/host-python-gate.py
	$(call fido_mark,hostpython)

fmt: pytools
	@$(PYRUN) tools/fmt-check.py

# The scoped-name policy gate.  The compiler verifies Rocq names for free; prose has no verifier at all,
# so this is the only one it gets.
names: pytools
	@$(PYRUN) tools/naming-gate.py
	$(call fido_mark,names)

# The claim-to-theorem matrix.  Freeze prose is gated by nothing else, so it can drift past what the public
# statements carry.  Each completion claim names the exact surface, fixture and gate that establish it, and
# this verifies they exist under those exact names.  It does not judge theorem strength; a human does that.
claims: pytools
	@$(PYRUN) tools/claim-matrix-gate.py --self-test
	@$(PYRUN) tools/claim-matrix-gate.py
	$(call fido_mark,claims)

# The PERMANENT source-comment policy, and only that: the .v comment law and the exception relation both
# ways.  The M1 baseline, metric direction, file disposition and code identity are one checkpoint's exit
# evidence, proved by `--verify-m1-evidence` at M1 review and never here — a permanent gate that enforced
# them would reject every later file, every later declaration and every larger tree forever.  Its
# adversarial controls run first, so a green here is one the checker can still earn.
diet: pytools
	@$(PYRUN) tools/source-diet.py --self-test
	@$(PYRUN) tools/source-diet.py --check
	@$(PYRUN) tools/source-diet.py --wiring
	$(call fido_mark,diet)

# The one diagnostic timing aid.  It runs the exact `make -j1 check` path once project-cold and once hot on
# a dedicated serial builder, records cumulative elapsed milliseconds at a few real target completions, and
# replaces `.review/PERFORMANCE.tsv`.  `git diff` is the comparison.
#
# It is diagnostic evidence, not certified correctness: no gate consults it, nothing depends on it, and it
# is a prerequisite of nothing.  See `.review/M2_PERFORMANCE_SNAPSHOT.md`.
perf:
	@sh tools/perf.sh

# The live-FCB document gates.  Each has ONE implementation shared by its writer and its checker, and each
# runs its adversarial controls FIRST — a gate that has never been shown to fail is not evidence.
fcb: pytools
	@$(PYRUN) tools/human-review-index.py --self-test
	@$(PYRUN) tools/human-review-index.py --check
	@$(PYRUN) tools/fcb-reference-gate.py --self-test
	@$(PYRUN) tools/fcb-reference-gate.py
	@$(PYRUN) tools/closure-ledger-view.py --check
	@$(PYRUN) tools/gate-mutation-test.py
	$(call fido_mark,fcb)

# Regenerate every generated FCB view from its canonical source.  The gate mount is read-only, so each
# writer produces its view into an isolated directory; the complete output set is validated there; and only
# then is any byte published.  Both writers therefore run to completion before publication, so a failure in
# the second can no longer leave the first one's view published on its own — which the old in-place pair
# did.  Publication is `cat >` rather than `mv` because it writes through the existing inode and so
# preserves the tracked file's ownership and mode exactly.
fcb-write: pytools
	@out=$$(mktemp -d); \
	  if ! docker run $(PYARGS) -v "$(CURDIR)":/repo:ro -v "$$out":/out $(PYTAG) \
	         python3 tools/human-review-index.py --write --out /out || \
	     ! docker run $(PYARGS) -v "$(CURDIR)":/repo:ro -v "$$out":/out $(PYTAG) \
	         python3 tools/closure-ledger-view.py --write --out /out; then \
	    rm -rf "$$out"; echo "fido: FCB-WRITE FAILED — a writer failed; nothing published" >&2; exit 1; fi; \
	  n=0; \
	  for rel in $$(cd "$$out" && find . -type f -printf '%P\n' | sort); do \
	    if ! git ls-files --error-unmatch "$$rel" > /dev/null 2>&1; then \
	      rm -rf "$$out"; echo "fido: FCB-WRITE FAILED — writer produced untracked path $$rel; nothing published" >&2; exit 1; fi; \
	    if [ ! -s "$$out/$$rel" ]; then \
	      rm -rf "$$out"; echo "fido: FCB-WRITE FAILED — writer produced empty $$rel; nothing published" >&2; exit 1; fi; \
	    n=$$((n+1)); \
	  done; \
	  if [ $$n -eq 0 ]; then \
	    rm -rf "$$out"; echo "fido: FCB-WRITE FAILED — writers produced no view; nothing published" >&2; exit 1; fi; \
	  for rel in $$(cd "$$out" && find . -type f -printf '%P\n' | sort); do \
	    cat "$$out/$$rel" > "$(CURDIR)/$$rel"; \
	  done; \
	  rm -rf "$$out"; echo "fido: fcb-write OK — published $$n validated view(s) ✓"

# Just the Rocq File/Error lines.  On failure Buildx echoes the entire recipe back as its error trailer,
# hundreds of lines, which buries the two that say what broke.  It reports; it does not verify.
# A DIAGNOSTIC WRAPPER, not a second measurement: this runs `prover-log` — which is itself `prove` with plain
# progress against the same Docker target — and greps its output, swallowing failure on purpose.  With
# observation on, the inner Make emits its own `make.prover-log` interval into the same log, so this trace
# CONTAINS that one.  Both are cataloged rather than measured, because a canonical run that took either as a
# root would pay a second full theory build for a number it already has, and two traces would claim one
# checkpoint interval — which §8 requires recording to refuse.
prove-errors:
	@$(MAKE) --no-print-directory prover-log > /tmp/fido-prover.log 2>&1 || true
	@grep -E '(^|[0-9.# ]+)(File "|Error:)' /tmp/fido-prover.log | sed 's/^[0-9.# ]*//' | sort -u | head -40 \
	  || echo "fido: no File/Error lines — see /tmp/fido-prover.log"

builder:
	@docker buildx inspect $(BUILDER) > /dev/null 2>&1 || \
	  docker buildx create --name $(BUILDER) --driver docker-container --bootstrap
	@docker buildx use $(BUILDER)

install-hooks:
	git config core.hooksPath .githooks
