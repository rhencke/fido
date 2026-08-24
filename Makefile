BUILDER := fido-builder
# The 64-bit target the theory assumes; `override` makes a command-line or environment change inert.
override PLATFORM := linux/amd64
# Project-stage cold, for `make perf` alone: unset, both expand to nothing and every recipe below is exactly
# the one that has always run.  Set, ONE cold pass forces ONE prover root in `prove` and ONE emit root in
# `e2e`, while their stable toolchain ancestors stay cache hits — cold for the project, not an empty machine.
#
# The final generated-artifact comparison in `check` deliberately carries NO filter: it must REUSE the
# generated module the forced-cold `e2e` already produced.  A single filter list applied to every Buildx
# invocation forced `emit` a second time there, after e2e had already built and consumed it, and the total
# was still called one cold pass.  Each root is forced exactly where it is intentionally forced, and nowhere
# else.
PERF_PROVER_NC := $(if $(FIDO_PERF_COLD),--no-cache-filter prover,)
PERF_EMIT_NC   := $(if $(FIDO_PERF_COLD),--no-cache-filter emit,)

# ── The Python boundary ───────────────────────────────────────────────────────
# Project Python never runs on the host.  This block is the whole boundary: every Python-consuming recipe
# below goes through PYRUN, and none of them names an interpreter itself.  The host needs only
# shell, Make, Git, Docker and Buildx.
#
# The tag is content-addressed over the two files that define the image, so changing the pin or the lock
# builds a new tag and a stale image cannot be reused; an unchanged pin costs one `docker image inspect`.
# Sources are MOUNTED rather than copied in, so a gate inspects exactly the source view named at the mount
# — the working tree here, the exported index in the hook — and no COPY set can silently go stale.
# The mount is read-only, because every surviving Python tool reports and none of them writes.
PYTAG   := fido-python-tools:$(shell cat Dockerfile tools/python-requirements.lock | sha256sum | cut -c1-16)
PYARGS  := --rm -u $(shell id -u):$(shell id -g) -e PYTHONDONTWRITEBYTECODE=1 -e HOME=/tmp \
           -e GIT_CONFIG_COUNT=1 -e GIT_CONFIG_KEY_0=safe.directory -e GIT_CONFIG_VALUE_0=/repo -w /repo
PYRUN    = docker run $(PYARGS) -v "$(CURDIR)":/repo:ro $(PYTAG) python3

# ── Completion markers.  INERT unless FIDO_PERF_LOG names a file: with the variable absent the `if` is
# false and nothing is written, so command order, bytes, output, exit status, side effects and normal
# parallelism are exactly what they were.  A measurement that alters what it measures is not a measurement.
#
# A marker is a COMPLETION TIMESTAMP and nothing else — not a nested span, not a trace, not a parent, not a
# partition, and not a proof of attribution.  Cumulative milliseconds since the run start `tools/perf.sh`
# supplies; a reader subtracts adjacent rows.  CLOCK_MONOTONIC from /proc/uptime, because a wall clock can
# step under NTP and a duration that can go backwards is not a duration.  The centiseconds field is two
# digits, so 08 and 09 read as OCTAL and silently drop a marker — stripping the leading zero is the POSIX
# fix, and `10#` would be a bashism.  The fraction is HUNDREDTHS, so a hundredth is ten milliseconds.
#
# The Makefile never parses, validates, compares or retains timing data.
define fido_mark
@if [ -n "$$FIDO_PERF_LOG" ]; then IFS='. ' read -r _s _c _r < /proc/uptime; _c=$${_c#0}; \
  printf '%s\t%s\t%s\n' "$$FIDO_PERF_MODE" '$(1)' \
    $$(( _s * 1000 + $${_c:-0} * 10 - $${FIDO_PERF_T0:-0} )) >> "$$FIDO_PERF_LOG"; fi
endef

# Build the pinned tooling images if this exact tag is not already present.  Never a rebuild of an existing
# tag: the tag changed if and only if its inputs did.
pytools: builder
	@docker image inspect $(PYTAG) > /dev/null 2>&1 || \
	  docker buildx build --builder $(BUILDER) --platform $(PLATFORM) --target python-tools \
	    --load -t $(PYTAG) . > /dev/null
	$(call fido_mark,pytools)

.PHONY: check check-core prove emit e2e regenerate regen-guard builder install-hooks prover-log prove-errors fmt \
        diet mutants ledger profile perf pytools hostpython go-probe toolchain
.DEFAULT_GOAL := check

# All Rocq and Go work runs in the pinned container through buildx; host Rocq is not supported.

# `make check` verifies the WORKING TREE.  Two choices in the recipe below are load-bearing:
#   `tools/worktree-list.py` owns the inventory — which paths Git considers part of the tree, and which of
#     them are actually present on disk — and its own controls run first, so a green here is one it earned;
#   plain `tar` (no --ignore-failed-read) makes an existing-but-unreadable file fail loudly.
# `.dockerignore` hides the committed go.mod and .go from Buildx, so the pristine is independent of the
# tracked bytes — which is what catches a header-preserving edit to a tracked `.go`.  The staged snapshot,
# and the exact-Git-mode gate over it, are the pre-commit hook's job rather than this one's.
# `make perf` times the complete `make -j1 check` invocation externally.
# The `check` marker records only completion of this recipe body.
# `make check` is the SOLE supported full verification.  It runs the whole DAG inline as `run_core`
# (prove + e2e + working-tree pristine byte-compare), times a warmed successful run, and applies the budget;
# a first pass over budget earns ONE warmed confirmation (the cold/setup allowance) and only a confirmed
# warmed overage fails with the STOP_FOR_ROB guidance.  A producer failure in run_core is returned as itself,
# checked before the budget.  There is no separate full-DAG target: `make check-core` is a guidance stub.
check:
	@t0=$$(date +%s); \
	  bud=$$(sh tools/check-budget.sh --budget); \
	  run_all() { \
	    sh tools/check-budget.sh --self-test || return $$?; \
	    [ -z "$$FIDO_CHECK_TEST_SLEEP" ] || sleep "$$FIDO_CHECK_TEST_SLEEP"; \
	    s=$$(date +%s); $(MAKE) --no-print-directory builder pytools || return $$?; \
	    echo "fido: [check stage] builder+tools = $$(( $$(date +%s) - s ))s"; \
	    s=$$(date +%s); $(MAKE) --no-print-directory hostpython diet mutants ledger || return $$?; \
	    echo "fido: [check stage] policy gates = $$(( $$(date +%s) - s ))s"; \
	    s=$$(date +%s); $(MAKE) --no-print-directory prove || return $$?; \
	    echo "fido: [check stage] prove = $$(( $$(date +%s) - s ))s"; \
	    s=$$(date +%s); $(MAKE) --no-print-directory e2e || return $$?; \
	    echo "fido: [check stage] e2e = $$(( $$(date +%s) - s ))s"; \
	    s=$$(date +%s); tmp=$$(mktemp -d); tree="$$tmp/tree"; mkdir -p "$$tree"; \
	    { $(PYRUN) tools/worktree-list.py --self-test && \
	      $(PYRUN) tools/worktree-list.py > "$$tmp/list.nul" && \
	      tar --null -T "$$tmp/list.nul" -cf "$$tmp/tree.tar" && \
	      tar -xf "$$tmp/tree.tar" -C "$$tree" && \
	      sh tools/ocaml-origin-gate.sh    "$$tree" && \
	      sh tools/generated-output-gate.sh "$$tree" && \
	      docker buildx build --builder $(BUILDER) --platform $(PLATFORM) --target generated-artifact \
	        --output "type=local,dest=$$tmp/pristine" . && \
	      sh tools/staged-generated-compare.sh "$$tree" "$$tmp/pristine"; }; \
	    rc=$$?; rm -rf "$$tmp"; \
	    echo "fido: [check stage] artifact-compare = $$(( $$(date +%s) - s ))s"; \
	    if [ $$rc -eq 0 ]; then echo "fido: check OK (working tree) — proved the core axiom-free (the coverage + layer-dependency gate + whole-theory audit + controls chain runs in prove) AND materialized the pristine generated-module (Fido Materialize) + validated it through go build ./... vs goldens (the internal sibling-temp sink exercised separately); the working-tree generated go.mod + recursive .go byte-match the pristine artifact (exact path set + bytes); transport-only OCaml, tracked Go is Fido-headed generated output ✓"; fi; \
	    return $$rc; \
	  }; \
	  run_all; rc=$$?; dt=$$(( $$(date +%s) - t0 )); \
	  [ $$rc -eq 0 ] || exit $$rc; \
	  echo "fido: make check — warmed total $${dt}s (budget $${bud}s, complete path)"; \
	  if sh tools/check-budget.sh $$dt; then exit 0; fi; \
	  echo "fido: make check — first pass $${dt}s over budget; ONE warmed confirmation follows (reuses acquired images/builders)"; \
	  t1=$$(date +%s); run_all; rc=$$?; dt2=$$(( $$(date +%s) - t1 )); \
	  [ $$rc -eq 0 ] || exit $$rc; \
	  echo "fido: make check — warmed confirmation $${dt2}s (budget $${bud}s, complete path)"; \
	  sh tools/check-budget.sh $$dt2
	$(call fido_mark,check)

# check-core is NOT a supported entry point: the only budget-enforced full verification is `make check`.
# This stub exists so a direct invocation fails with clear guidance rather than silently running unbudgeted.
check-core:
	@echo "fido: 'make check-core' is not a supported target — run 'make check' (the budget-enforced full verification)"; exit 2

# The reproducible container proof: dune compiles the modules, the always-run layer-dependency gate (rocq dep
# direct edges == the sole ARCHITECTURE policy), + the whole-theory assumption audit.
prove: builder
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) $(PERF_PROVER_NC) --target prover .
	$(call fido_mark,prove)

prover-log: builder
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) $(PERF_PROVER_NC) --progress=plain --target prover .

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
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) $(PERF_EMIT_NC) --progress=plain --target emit .

# Emit the whole tree, then the pinned Go toolchain builds it and runs the witness against the goldens.
e2e: builder
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) $(PERF_EMIT_NC) --progress=plain --target go-e2e .
	$(call fido_mark,e2e)

# Regenerate the tracked module through the one validate-before-publish workflow.  Building `sync` requires
# the pinned `go build ./...` through the Docker DAG (`sync` COPYs go-e2e's success marker), so a failed
# validation makes `sync` unbuildable and no sink effect occurs — a cache hit on a passing go-e2e is equally
# valid.  It publishes the original pristine bytes, never a post-build one.
regenerate: builder
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) --target sync --load -t fido-sync .
	docker run --rm -u $$(id -u):$$(id -g) -v "$(CURDIR)":/dest fido-sync
	@echo "fido: regenerate OK — building 'sync' forced the pinned go build ./... (Docker DAG), then the SAME pristine bytes were synced into the repo root via Sink."
	@echo "      Stage + commit:  git add -A -- go.mod ':(top,glob)**/*.go' && git commit"

# With go-e2e forced to FAIL on a temp Dockerfile copy, `--target sync` must be unbuildable, and on the
# unmodified tree it must build — so `make regenerate` cannot publish without a passing go-e2e validation.
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

# The PERMANENT source-comment policy, and only that: the .v comment law and the exception relation both
# ways.  Its adversarial controls run first, so a green here is one the checker can still earn.
diet: pytools
	@$(PYRUN) tools/source-diet.py --self-test
	@$(PYRUN) tools/source-diet.py --check
	$(call fido_mark,diet)

# The raw structured-data gate: the .review ledgers are well-formed BEFORE any derived count or cross-ledger
# claim.  Its adversarial controls run first, so a green here is one the checker can still earn.  It owns no
# derived count and no semantic decision; the code and its gated theorems remain the sole authority.
ledger: pytools
	@$(PYRUN) tools/ledger-validate.py --self-test
	@$(PYRUN) tools/ledger-validate.py
	$(call fido_mark,ledger)

# The one diagnostic timing aid.  It runs the exact `make -j1 check` path once project-cold and once hot on
# a dedicated serial builder, records cumulative elapsed milliseconds at a few real target completions, and
# replaces `.review/PERFORMANCE.tsv`.  `git diff` is the comparison.
#
# It is diagnostic evidence, not certified correctness: no gate consults it, nothing depends on it, and it
# is a prerequisite of nothing.
perf:
	@sh tools/perf.sh

# Every root helper in the surviving policy gates must be LOAD-BEARING: delete its effect in a copy of the
# tree and that gate's own named controls must fail.  A control that survives the deletion of the rule it
# protects is decoration, not evidence.
mutants: pytools
	@$(PYRUN) tools/gate-mutation-test.py
	$(call fido_mark,mutants)

# A diagnostic wrapper which reports the File/Error lines from `prover-log`; it deliberately swallows the
# build failure so the useful diagnostics remain visible.  On failure Buildx echoes the entire recipe back as
# its error trailer, hundreds of lines, which buries the two that say what broke.
prove-errors:
	@$(MAKE) --no-print-directory prover-log > /tmp/fido-prover.log 2>&1 || true
	@grep -E '(^|[0-9.# ]+)(File "|Error:)' /tmp/fido-prover.log | sed 's/^[0-9.# ]*//' | sort -u | head -40 \
	  || echo "fido: no File/Error lines — see /tmp/fido-prover.log"

# Differential ALARM against the pinned Go toolchain, never a proof authority.  Each immediate subdirectory
# of $(GOPROBE) is one self-contained module; the target reports whether pinned `go build` accepts it.  This
# is how a proposed static rule is checked against `gc` before the rule is written down — the same role the
# e2e differentials play for emitted programs, applied to hand-written probes during contract work.
#
# Sources are MOUNTED read-only and copied to a writable scratch inside, because the Go build cache and
# module bookkeeping write beside the source.  Nothing here enters the repository or the build context.
GOPROBE ?= /tmp/fido-go-probe
GOTAG   := fido-go:$(shell sha256sum Dockerfile | cut -c1-16)
go-probe: builder
	@test -d "$(GOPROBE)" || { echo "fido: no $(GOPROBE) — write probe modules there first"; exit 1; }
	@docker image inspect $(GOTAG) > /dev/null 2>&1 || \
	  docker buildx build --builder $(BUILDER) --platform $(PLATFORM) --target go-base \
	    --load -t $(GOTAG) . > /dev/null
	@docker run --rm -e HOME=/tmp -e GOCACHE=/tmp/gocache -e GOFLAGS=-mod=mod \
	  -v "$(GOPROBE)":/probe:ro $(GOTAG) sh -c ' \
	    cp -r /probe /tmp/p; cd /tmp/p; \
	    for d in */; do d=$${d%/}; \
	      out=$$(cd "$$d" && go build ./... 2>&1); \
	      if [ -z "$$out" ]; then printf "ACCEPT  %s\n" "$$d"; \
	      else printf "REJECT  %s  %s\n" "$$d" "$$(echo "$$out" | head -1)"; fi; \
	    done'

builder:
	@docker buildx inspect $(BUILDER) > /dev/null 2>&1 || \
	  docker buildx create --name $(BUILDER) --driver docker-container --bootstrap
	@docker buildx use $(BUILDER)

install-hooks:
	git config core.hooksPath .githooks

# Build the full Rocq/OCaml/Dune closure ONCE from toolchain.Dockerfile and push it to
# GHCR, so the main Dockerfile consumes it only by immutable @sha256 digest (no live apt/opam at build time).
# One-time operator setup first (not a build dependency, keeps the host boundary at shell/Make/Git/Docker/Buildx):
#   gh auth token | docker login ghcr.io -u fidocancode --password-stdin
# Then `make toolchain`, and pin the printed reference in Dockerfile + TOOLCHAIN.md.
TOOLCHAIN_IMAGE := ghcr.io/fidocancode/fido-toolchain
TOOLCHAIN_TAG   := rocq-9.2.0-ocaml-5.3-$(shell sha256sum toolchain.Dockerfile | cut -c1-12)
toolchain: builder
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) -f toolchain.Dockerfile \
	  --target rocq-base --push -t $(TOOLCHAIN_IMAGE):$(TOOLCHAIN_TAG) .
	@echo "fido: toolchain pushed — pin this immutable reference in Dockerfile + TOOLCHAIN.md:"
	@echo "$(TOOLCHAIN_IMAGE)@$$(docker buildx imagetools inspect $(TOOLCHAIN_IMAGE):$(TOOLCHAIN_TAG) | awk '/^Digest:/{print $$2; exit}')"
