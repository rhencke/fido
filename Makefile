BUILDER := fido-builder
# The 64-bit target the theory assumes; `override` makes a command-line or environment change inert.
override PLATFORM := linux/amd64
# Inert observatory hook: unset, this expands to nothing and every recipe below is exactly the one
# that has always run.  The Build Observatory sets NOCACHE to the SET of declared invalidation roots,
# space-separated, so each is forced to rebuild while their stable ancestors stay cache hits — a
# project-cold measurement, not an empty machine.  A set rather than one name because a compound command
# can force two independent roots, and one name could only ever describe half of that.  Never set by an
# ordinary build.
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

# The observatory runner is the ONE image carrying a Docker client.  It drives the host daemon through the
# mounted socket and the developer's own Buildx config, so it addresses exactly the builder and cache
# authorities the real project commands use — not an independent daemon whose timings would mean nothing.
OBSTAG     := fido-observatory-runner:$(shell cat Dockerfile tools/python-requirements.lock | sha256sum | cut -c1-16)
DOCKER_GID := $(shell getent group docker 2>/dev/null | cut -d: -f3)

# Build the pinned tooling images if this exact tag is not already present.  Never a rebuild of an existing
# tag: the tag changed if and only if its inputs did.
pytools: builder
	@docker image inspect $(PYTAG) > /dev/null 2>&1 || \
	  docker buildx build --builder $(BUILDER) --platform $(PLATFORM) --target python-tools \
	    --load -t $(PYTAG) . > /dev/null

observatory-runner: builder
	@docker image inspect $(OBSTAG) > /dev/null 2>&1 || \
	  docker buildx build --builder $(BUILDER) --platform $(PLATFORM) --target observatory-runner \
	    --load -t $(OBSTAG) . > /dev/null

.PHONY: check prove emit e2e regenerate regen-guard builder install-hooks prover-log prove-errors fmt names \
        fcb fcb-write claims diet audit-fresh profile observatory observe pytools hostpython \
        observatory-runner
.DEFAULT_GOAL := check

# All Rocq and Go work runs in the pinned container through buildx; host Rocq is not supported.

# `make check` verifies the WORKING TREE.  Two choices in the recipe below are load-bearing:
#   `tools/worktree-list.py` owns the inventory — which paths Git considers part of the tree, and which of
#     them are actually present on disk — and its own controls run first, so a green here is one it earned;
#   plain `tar` (no --ignore-failed-read) makes an existing-but-unreadable file fail loudly.
# `.dockerignore` hides the committed go.mod and .go from Buildx, so the pristine is independent of the
# tracked bytes — which is what catches a header-preserving edit to a tracked `.go`.  The staged snapshot,
# and the exact-Git-mode gate over it, are the pre-commit hook's job rather than this one's.
check: pytools hostpython names fcb claims diet observatory prove e2e builder
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

# The reproducible container proof: dune compiles the modules + the always-run assumptions gate.
prove: builder
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) $(NC) --target prover .

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

fmt: pytools
	@$(PYRUN) tools/fmt-check.py

# The scoped-name policy gate.  The compiler verifies Rocq names for free; prose has no verifier at all,
# so this is the only one it gets.
names: pytools
	@$(PYRUN) tools/naming-gate.py

# The claim-to-theorem matrix.  Freeze prose is gated by nothing else, so it can drift past what the public
# statements carry.  Each completion claim names the exact surface, fixture and gate that establish it, and
# this verifies they exist under those exact names.  It does not judge theorem strength; a human does that.
claims: pytools
	@$(PYRUN) tools/claim-matrix-gate.py --self-test
	@$(PYRUN) tools/claim-matrix-gate.py

# The PERMANENT source-comment policy, and only that: the .v comment law and the exception relation both
# ways.  The M1 baseline, metric direction, file disposition and code identity are one checkpoint's exit
# evidence, proved by `--verify-m1-evidence` at M1 review and never here — a permanent gate that enforced
# them would reject every later file, every later declaration and every larger tree forever.  Its
# adversarial controls run first, so a green here is one the checker can still earn.
diet: pytools
	@$(PYRUN) tools/source-diet.py --self-test
	@$(PYRUN) tools/source-diet.py --check
	@$(PYRUN) tools/source-diet.py --wiring

# The PERMANENT command-surface coverage validator, and only that: every public Make target, paired
# pre-commit anchor and Docker stage has exactly one registry entry, in both directions.  It reads three
# files and runs nothing, so it belongs beside the other cheap policy gates and ahead of the expensive
# ones.  It is NOT an observe mode — it never runs, lists, compares, records or subsets a suite, which is
# why `observe` remains the single public entry point for measurement.
observatory: pytools
	@$(PYRUN) tools/build-observatory.py --self-test
	@$(PYRUN) tools/build-observatory.py --check

# The Build Observatory's ONE public entry point.  Every mode is a variable on this target rather than a
# target of its own, so the interface cannot drift into a second build graph:
#   make observe                       the complete canonical suite, compared with the tracked observation
#   make observe ONLY=make.prove       one command or group, plus its required setup
#   make observe SCENARIO=project.warm.noop   one cache scenario, by its registry ID
#   make observe BASE=<ref-or-path>    compare against an observation from a Git ref or a local bundle
#   make observe COMPARE=<ref-or-path> compare two existing observations without running anything
#   make observe RECORD=1              replace the tracked observation, only from a clean complete run
#   make observe LIST=1                every stable command ID and how it is measured
#   make observe HELP=1                usage, cache definitions, recording and comparison rules
# Every path is mounted AT ITS HOST PATH, and that is load-bearing rather than tidy.  The runner drives the
# host daemon through the socket, so any `-v` a measured command issues is resolved by the HOST — a repo
# mounted at /repo inside the runner made `make check` ask the host for /repo, which does not exist, and
# Docker silently supplied an empty directory instead of failing.  Identical paths on both sides means a
# nested mount names the same bytes either way.
observe: observatory-runner
	@bundles=$${FIDO_OBSERVATORY_HOME:-$${TMPDIR:-/tmp}/fido-observatory}; mkdir -p "$$bundles"; \
	  docker run --rm -u $(shell id -u):$(shell id -g) $(if $(DOCKER_GID),--group-add $(DOCKER_GID)) \
	    -e PYTHONDONTWRITEBYTECODE=1 -e HOME=/tmp -e DOCKER_CONFIG=/tmp/.docker \
	    -e GIT_CONFIG_COUNT=1 -e GIT_CONFIG_KEY_0=safe.directory -e GIT_CONFIG_VALUE_0=/repo \
	    -v "$(CURDIR)":"$(CURDIR)" -v "$$bundles":"$$bundles" -v "$$HOME/.docker":/tmp/.docker \
	    -v /var/run/docker.sock:/var/run/docker.sock -w "$(CURDIR)" $(OBSTAG) \
	    python3 tools/build-observatory.py --observe --bundle-root "$$bundles" \
	      $(if $(ONLY),--only "$(ONLY)") $(if $(SCENARIO),--scenario "$(SCENARIO)") \
	      $(if $(BASE),--base "$(BASE)") $(if $(COMPARE),--compare "$(COMPARE)") \
	      $(if $(RECORD),--record) $(if $(LIST),--list) $(if $(HELP),--usage)

# The live-FCB document gates.  Each has ONE implementation shared by its writer and its checker, and each
# runs its adversarial controls FIRST — a gate that has never been shown to fail is not evidence.
fcb: pytools
	@$(PYRUN) tools/human-review-index.py --self-test
	@$(PYRUN) tools/human-review-index.py --check
	@$(PYRUN) tools/fcb-reference-gate.py --self-test
	@$(PYRUN) tools/fcb-reference-gate.py
	@$(PYRUN) tools/closure-ledger-view.py --check
	@$(PYRUN) tools/gate-mutation-test.py

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
