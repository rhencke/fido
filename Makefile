BUILDER  := fido-builder
PLATFORM ?= linux/$(shell uname -m | sed 's/x86_64/amd64/;s/aarch64/arm64/')

.PHONY: check spine-verify ocaml-origin-gate go-uncommittable-seal build builder install-hooks prover-log
.DEFAULT_GOAL := check

# Fido is a PROOF repository under a FOUNDATION RESET (checkpoint 65).  The false compile/emit authority
# (GoCompile accepted an unresolved named type — see git history) and the disconnected runtime island were
# deleted.  There is NO emitted Go this round: a smaller root-only repository beats a green extraction demo
# resting on a false compile certificate.  The surviving syntax layer (digits, GoAst, GoPrint) is scheduled
# for the syntax-root reset (independent Go grammar + typed elaboration) — it is NOT a certified emission
# authority, and NOTHING here claims Go compiler adequacy.

# check: the one verify — zero tracked OCaml, no tracked generated Go, and the surviving Rocq compiles with
# zero axioms (Rocq's own Print Assumptions).  No Go toolchain is involved (there is no emission).
check: ocaml-origin-gate go-uncommittable-seal spine-verify
	@echo "fido: check OK — surviving Rocq compiles, zero axioms, zero tracked OCaml ✓"

spine-verify:
	@sh tools/spine-gate.sh printer /tmp/fido-verify.log
	@rm -f digits.vo digits.glob .digits.aux GoAst.vo GoAst.glob .GoAst.aux GoPrint.vo GoPrint.glob .GoPrint.aux
	@echo "fido: spine-verify OK — digits/GoAst/GoPrint compile standalone, zero axioms ✓"

ocaml-origin-gate:
	@sh tools/ocaml-origin-gate.sh

# SEAL: no generated Go is tracked (there is no emission this round; when it returns it stays gitignored).
go-uncommittable-seal:
	@tracked=$$(git ls-files -- '*.go' 2>/dev/null); \
	if [ -n "$$tracked" ]; then echo "fido: SEAL FAILED — a tracked *.go exists but generated Go is never committed:"; echo "$$tracked" | sed 's/^/  /'; exit 1; fi; \
	echo "fido: uncommittable-Go seal OK — no *.go is tracked ✓"

# Reproducible container build: the pinned Rocq toolchain compiles the surviving modules + asserts zero axioms.
build:
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) --target prover .

builder:
	docker buildx inspect $(BUILDER) > /dev/null 2>&1 || \
	  docker buildx create --name $(BUILDER) --driver docker-container --bootstrap
	docker buildx use $(BUILDER)
install-hooks:
	git config core.hooksPath .githooks
prover-log:
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) --progress=plain --target prover .
