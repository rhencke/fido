BUILDER  := fido-builder
PLATFORM ?= linux/$(shell uname -m | sed 's/x86_64/amd64/;s/aarch64/arm64/')

# THE one Go-toolchain image authority, DIGEST-PINNED, used ONLY by the e2e smoke test.  `override` makes
# command-line/environment assignments INERT.  Passed to the Dockerfile via --build-arg (its ARG has no
# default — a build bypassing make fails loudly).
override GOIMAGE := golang:1.23-alpine@sha256:383395b794dffa5b53012a212365d40c8e37109a626ca30d6151c8348d380b5f

.PHONY: check ocaml-origin-gate go-uncommittable-seal build builder install-hooks prover-log print-goimage
.DEFAULT_GOAL := check

# Fido is a PROOF repository under a FOUNDATION RESET (checkpoint 65).  The false compile/emit AUTHORITY
# (GoCompile accepted an unresolved named type — see git history) and the disconnected runtime island were
# deleted.  The surviving syntax layer (digits, GoAst, GoPrint) is scheduled for the syntax-root reset — it
# is NOT a certified emission authority and NOTHING here claims Go compiler adequacy.
#
# ALL Rocq/Go work runs in the PINNED container via buildx.  Local host Rocq is NOT supported — a different
# host Rocq version could judge proofs differently, so the proof is only ever what the pinned toolchain says.
# `check` and the pre-commit hook go through buildx, never host rocq/go.

print-goimage:
	@echo $(GOIMAGE)

# check: the git/shell gates (no Rocq/Go) + the reproducible container proof AND the e2e smoke test.  buildx
# runs: dune compiles digits/GoAst/GoPrint (axiom-free surfaces) THEN the e2e prints one known program and
# the pinned Go toolchain accepts it.
check: ocaml-origin-gate go-uncommittable-seal build
	@echo "fido: check OK — pinned container: theory compiles (assumptions gate: all declared surfaces closed) + e2e printed program accepted by the Go toolchain; zero tracked OCaml, no tracked *.go ✓"

ocaml-origin-gate:
	@sh tools/ocaml-origin-gate.sh

# SEAL: no generated Go is tracked (the e2e .go is generated in the container / gitignored locally).
go-uncommittable-seal:
	@tracked=$$(git ls-files -- '*.go' 2>/dev/null); \
	if [ -n "$$tracked" ]; then echo "fido: SEAL FAILED — a tracked *.go exists but generated Go is never committed:"; echo "$$tracked" | sed 's/^/  /'; exit 1; fi; \
	echo "fido: uncommittable-Go seal OK — no *.go is tracked ✓"

# build: the reproducible container.  Targets e2e-check, which depends on the prover — so buildx runs the
# proof (dune, axiom check) AND the e2e (print -> extract -> pinned Go toolchain accepts).  A proof failure,
# an axiom, or Go rejecting the printed program fails the build, hence `check`.
build: builder
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) --build-arg GOIMAGE=$(GOIMAGE) --target e2e-check .

builder:
	@docker buildx inspect $(BUILDER) > /dev/null 2>&1 || \
	  docker buildx create --name $(BUILDER) --driver docker-container --bootstrap
	@docker buildx use $(BUILDER)

install-hooks:
	git config core.hooksPath .githooks

# Diagnose a failure: rebuild streaming the full plain log (the Rocq error / idtac, or the Go toolchain output).
prover-log: builder
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) --build-arg GOIMAGE=$(GOIMAGE) --progress=plain --target e2e-check .
