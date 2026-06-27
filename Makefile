BUILDER  := fido-builder
IMAGE    := fido
TAG      ?= latest
PLATFORM ?= linux/$(shell uname -m | sed 's/x86_64/amd64/;s/aarch64/arm64/')

.PHONY: builder build bake push run run-extracted extract go-run install-hooks check golden negtest printer printer-verify smart-ctor-gate
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
	rm -f *.go *.go.raw
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) \
	  --output type=local,dest=. --target go-src .
	# Canonicalise with gofmt: the plugin emits valid Go, but gofmt's operator-
	# spacing heuristic (e.g. tightening `1.5 + 2.25` to `1.5+2.25`) is depth/
	# operand-dependent and not worth replicating in the plugin.  This guarantees
	# the committed Go is gofmt-clean regardless.
	#
	# gofmt is a TRUSTED post-step — but review #8 asks it not silently rewrite the verified output.  So
	# MECHANICALLY BOUND it to WHITESPACE-ONLY: snapshot the plugin's raw output, gofmt, then assert the
	# non-whitespace TOKEN STREAM is byte-identical.  gofmt thus provably cannot alter a token / the
	# program's meaning — it only REFORMATS.  The verified printer's TOKENS reach the committed file; gofmt
	# is a CHECKED normaliser, not a trusted byte-rewriter.  (String-literal contents are unchanged by
	# gofmt, so stripping all whitespace cancels on both sides; the plugin emits no comments.)
	for f in *.go; do cp "$$f" "$$f.raw"; done
	docker run --rm -v "$(PWD)":/w -w /w golang:1.23-alpine gofmt -w *.go
	for f in *.go; do \
	  if [ "`tr -d '[:space:]' < "$$f.raw"`" != "`tr -d '[:space:]' < "$$f"`" ]; then \
	    echo "fido: GOFMT ALTERED A TOKEN (not just whitespace) in $$f — gofmt is not semantics-preserving here; refusing."; \
	    rm -f *.go.raw; exit 1; \
	  fi; \
	done
	rm -f *.go.raw
	@echo "fido: gofmt is whitespace-only (token stream preserved) — verified printer's tokens reach the file ✓"

# Run the extracted Go sources directly without Docker.
run-local: extract
	go run .

# Fail-closed regression harness (review #4 R10 — the negative-fixture gate). Compiles each
# negative fixture in negtests/ and asserts it ABORTS extraction with its declared
# `(* EXPECT: … *)` message. A reopened fail-closed site (the plugin emitting plausible-but-
# wrong Go where rule 2 demands a loud `unsupported`) is exactly the defect class the
# happy-path golden CANNOT see — run this after any plugin change. Local (host rocq, like
# run-local); the canonical Docker build is unaffected (negtests/ is outside the Fido theory).
negtest:
	dune build
	@sh negtests/run.sh

# Smart-constructor gate (review #4): ban DIRECT proof-carrying Printer constructors
# (AIdent/AIntLit/ARaw/GTNamed) outside the smart-constructor block in plugin/go.ml — the erased
# Rocq proofs make a direct call a trust hole.  Pure static check (no build); runs here, in the
# pre-commit hook, and NON-bypassably in the Docker prover stage (so `make check` enforces it).
smart-ctor-gate:
	@sh plugin/smart-ctor-gate.sh

# Shared gate for the VERIFIED printer: compile goprint.v STANDALONE (Stdlib only, no plugin — sidesteps
# the build circularity, since the plugin LINKS printer.ml which is extracted FROM a Rocq file) and assert
# its Print-Assumptions show ZERO axioms (goprint.v is part of the trust base, not just main_effect).  On
# success it leaves the freshly-extracted printer.ml + build artifacts in the CWD for the caller to use.
# Recursively-expanded (=) so each user inlines it into a SINGLE recipe line (one shell, `set -e` honoured).
GOPRINT_GATE = rocq c goprint.v > /tmp/goprint.log 2>&1 || { echo "fido: goprint.v failed to compile:"; cat /tmp/goprint.log; exit 1; }; \
	if grep -q '^Axioms:' /tmp/goprint.log; then \
	  echo "fido: VERIFIED-PRINTER AXIOM/ADMITTED — a goprint.v theorem depends on an axiom (Print Assumptions):"; \
	  cat /tmp/goprint.log; rm -f goprint.vo goprint.glob .goprint.aux printer.ml; exit 1; \
	fi
GOPRINT_CLEAN = rm -f goprint.vo goprint.glob .goprint.aux printer.ml

# Regenerate the VERIFIED printer's OCaml (plugin/printer.ml) from goprint.v.  A PROPER file dependency:
# remade only when goprint.v is newer.  The recipe runs the shared gate (compile + zero-axiom) then moves
# the fresh extraction into place.  Commit plugin/printer.ml afterwards (a GENERATED file, like the *.go);
# `make check` (Docker) re-derives it and FAILS on drift.
plugin/printer.ml: goprint.v
	@set -e; $(GOPRINT_GATE); \
	  mv -f printer.ml plugin/printer.ml; rm -f goprint.vo goprint.glob .goprint.aux; \
	  echo "fido: regenerated plugin/printer.ml from goprint.v — zero axioms ✓ (commit it, like *.go)"
printer: plugin/printer.ml

# Read-only LOCAL mirror of the Docker prover-stage printer gate: compile goprint.v, assert ZERO axioms,
# and assert the committed plugin/printer.ml is EXACTLY goprint.v's extraction (drift = the PROVED printer
# differs from the EXECUTED one).  Modifies nothing — run it after editing goprint.v / before committing
# for a fast check without the full Docker `make check`.
printer-verify:
	@set -e; $(GOPRINT_GATE); \
	  if ! diff plugin/printer.ml printer.ml > /dev/null; then \
	    echo "fido: PRINTER DRIFT — committed plugin/printer.ml != goprint.v's extraction; run 'make printer' and commit it."; \
	    $(GOPRINT_CLEAN); exit 1; \
	  fi; \
	  $(GOPRINT_CLEAN); echo "fido: goprint.v OK — zero axioms, plugin/printer.ml in sync ✓"

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
