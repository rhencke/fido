BUILDER := fido-builder
# The pinned target is linux/amd64 (TargetConfig.tc_goos/tc_goarch).  SEALED — the build architecture and
# the proof's target authority are mechanically identical; `override` makes any command-line/env change inert.
override PLATFORM := linux/amd64

.PHONY: check prove ocaml-origin-gate go-uncommittable-seal builder install-hooks prover-log
.DEFAULT_GOAL := check

# Fido — the collapsed architecture (ARCHITECTURE.md): an LLM proposes a GoAST; emission is available only
# after Rocq proves GoCompile (exact static admissibility) and GoSafe.  Chain:
#   GoAST -> GoCompile -> GoSafe/SafeProgram -> direct GoRender -> GoEmit/DirectoryImage -> (tiny plugin).
# ALL Rocq work runs in the PINNED container via buildx — host Rocq is NOT supported.  The `Fido Emit`
# plugin + pinned-Go e2e are the next milestone; today `check` proves the core.

check: ocaml-origin-gate go-uncommittable-seal prove
	@echo "fido: check OK — pinned container proved the core (GoAST/GoCompile/GoSafe/GoRender/GoEmit), assumptions gate closed; zero tracked OCaml, no tracked *.go ✓"

# The reproducible container proof: dune compiles the modules + the always-run assumptions gate.
prove: builder
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) --target prover .

prover-log: builder
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) --progress=plain --target prover .

ocaml-origin-gate:
	@sh tools/ocaml-origin-gate.sh

# SEAL: no generated Go is tracked (emission output lives under _build / is gitignored when it returns).
go-uncommittable-seal:
	@tracked=$$(git ls-files -- '*.go' 2>/dev/null); \
	if [ -n "$$tracked" ]; then echo "fido: SEAL FAILED — a tracked *.go exists but generated Go is never committed:"; echo "$$tracked" | sed 's/^/  /'; exit 1; fi; \
	echo "fido: uncommittable-Go seal OK — no *.go is tracked ✓"

builder:
	@docker buildx inspect $(BUILDER) > /dev/null 2>&1 || \
	  docker buildx create --name $(BUILDER) --driver docker-container --bootstrap
	@docker buildx use $(BUILDER)

install-hooks:
	git config core.hooksPath .githooks
