BUILDER  := fido-builder
IMAGE    := fido
TAG      ?= latest
PLATFORM ?= linux/$(shell uname -m | sed 's/x86_64/amd64/;s/aarch64/arm64/')

.PHONY: builder build bake push run run-extracted extract go-run install-hooks check golden
.DEFAULT_GOAL := build

# Run the extracted program (Go's println writes to stderr → capture 2>&1).
GORUN := docker run --rm -v "$(PWD)":/w -w /w golang:1.23-alpine go run .
# `go vet` gate (review #4 R10): `go run` already BUILDS the emitted Go (so a type error
# anywhere fails), but vet catches suspicious-but-COMPILING constructs (bad printf verbs,
# unreachable code, lost cancels, self-assignment, …) that a plugin bug could emit silently.
# The no-import `package main` vets offline.  Wired into [check] and [golden] below.
GOVET := docker run --rm -v "$(PWD)":/w -w /w golang:1.23-alpine go vet .

# One-time setup: activate git hooks from .githooks/.
install-hooks:
	git config core.hooksPath .githooks

# One-time setup: create a docker-container buildx builder capable of multi-platform builds.
builder:
	docker buildx inspect $(BUILDER) > /dev/null 2>&1 || \
	  docker buildx create --name $(BUILDER) --driver docker-container --bootstrap
	docker buildx use $(BUILDER)

# Fast local build (native platform only, loads into local docker daemon).
build:
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) --load -t $(IMAGE):$(TAG) .

# Extract generated Go sources from the prover stage into the repo.
# Wipes all *.go files first so renamed/deleted theories don't leave strays.
extract:
	rm -f *.go
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) \
	  --output type=local,dest=. --target go-src .
	# Canonicalise with gofmt: the plugin emits valid Go, but gofmt's operator-
	# spacing heuristic (e.g. tightening `1.5 + 2.25` to `1.5+2.25`) is depth/
	# operand-dependent and not worth replicating in the plugin.  This guarantees
	# the committed Go is gofmt-clean regardless.
	docker run --rm -v "$(PWD)":/w -w /w golang:1.23-alpine gofmt -w *.go

# Run the extracted Go sources directly without Docker.
run-local: extract
	go run .

# Run the freshly-extracted program (Dockerised; the env may lack a host Go).  DEPENDS
# ON [extract] exactly like [check]/[golden], so an ad-hoc "what does it print?" run can
# NEVER use stale Go.  This (or [check]) is the ONLY sanctioned way to run the program —
# a bare `go run` / `docker run … go run` bypasses extraction and is forbidden.  For
# VERIFYING a change, prefer [check] (runs AND diffs against the golden); use this only
# when you want the raw output with no diff.
run-extracted: extract
	@$(GORUN)

# Run the image built for the native platform.
run: build
	docker run --rm --platform $(PLATFORM) $(IMAGE):$(TAG)

# Golden-file regression check: run the extracted program and diff its output
# against expected_output.txt.  Cheap end-to-end check that a Rocq/plugin change
# did not alter observable behaviour anywhere (not just the demo in focus).
# DEPENDS ON [extract]: a stale main.go must be IMPOSSIBLE here — checking
# against Go that does not reflect current *.v/plugin source would be a false
# green.  [extract] re-runs the prover (Docker layers cached if unchanged), so
# this always validates freshly-extracted Go (and fails loud if a proof broke).
check: extract
	@echo "fido: go vet (suspicious-but-compiling constructs)..."; \
	if ! $(GOVET); then \
	  echo "fido: GO VET FAILED — the emitted Go has a vet diagnostic (a real defect even though it compiles); fix the plugin/.v, not the Go."; \
	  exit 1; \
	fi
	@set +e; $(GORUN) > /tmp/fido_out.txt 2>&1; rc=$$?; set -e; \
	if [ $$rc -ne 0 ]; then \
	  echo "fido: PROGRAM EXITED NON-ZERO (status $$rc) — an uncaught panic / crash, NOT a benign diff:"; \
	  echo ""; cat /tmp/fido_out.txt; \
	  echo ""; echo "fido: a faithful Fido program runs to completion (exit 0)."; \
	  exit 1; \
	fi; \
	if diff -u expected_output.txt /tmp/fido_out.txt; then \
	  echo "fido: output matches golden ✓"; \
	else \
	  echo ""; echo "fido: OUTPUT DIFFERS from golden (above)."; \
	  echo "fido: if the change is intended, run 'make golden' to update."; \
	  exit 1; \
	fi

# Regenerate the golden baseline after an intended behaviour change.  Depends on
# [extract] so the baseline is captured from freshly-extracted Go, never stale, AND
# SHOWS THE DELTA it is about to bless (old golden → new output) before overwriting —
# so blessing can never happen blind: the diff check is part of the bless, not a manual
# step done beside it.  Review the printed delta; if it is more than you intended, your
# change had an unexpected effect somewhere.
golden: extract
	@echo "fido: go vet (gate before bless)..."; \
	if ! $(GOVET); then \
	  echo "fido: REFUSING TO BLESS — go vet reports a diagnostic on the emitted Go; fix it first."; \
	  exit 1; \
	fi
	@set +e; $(GORUN) > /tmp/fido_new.txt 2>&1; rc=$$?; set -e; \
	if [ $$rc -ne 0 ]; then \
	  echo "fido: REFUSING TO BLESS — program EXITED NON-ZERO (status $$rc), an uncaught panic / crash:"; \
	  echo ""; cat /tmp/fido_new.txt; \
	  echo ""; echo "fido: fix the crash before re-blessing (a faithful Fido program exits 0)."; \
	  exit 1; \
	fi; \
	echo "fido: golden delta (committed → new), review before blessing:"; \
	diff -u expected_output.txt /tmp/fido_new.txt || true; \
	cp /tmp/fido_new.txt expected_output.txt; \
	echo "fido: updated expected_output.txt"

# Multi-platform build (does not load locally — use push to ship).
bake:
	docker buildx bake --builder $(BUILDER)

# Multi-platform build + push to registry.
push:
	docker buildx bake --builder $(BUILDER) --push
