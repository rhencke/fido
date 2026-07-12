BUILDER := fido-builder
# The pinned target is linux/amd64 (TargetConfig.tc_goos/tc_goarch).  SEALED — the build architecture and
# the proof's target authority are mechanically identical; `override` makes any command-line/env change inert.
override PLATFORM := linux/amd64

.PHONY: check prove emit e2e ocaml-origin-gate go-uncommittable-seal builder install-hooks prover-log
.DEFAULT_GOAL := check

# Fido — ONE AST (ARCHITECTURE.md): an LLM proposes a GoAST; emission is available only after Rocq proves
# GoCompile (exact static admissibility) and GoSafe.  Chain:
#   GoAST -> GoCompile -> GoSafe -> direct GoRender -> GoEmit pairs -> extraction -> tiny I/O writer.
# ALL Rocq/Go work runs in the PINNED container via buildx — host Rocq is NOT supported.

check: ocaml-origin-gate go-uncommittable-seal prove e2e
	@echo "fido: check OK — proved the core (GoAST/GoCompile/GoSafe/GoRender/GoEmit) axiom-free AND emitted+ran the e2e witness through the pinned Go toolchain; one tiny I/O writer, no tracked *.go ✓"

# The reproducible container proof: dune compiles the modules + the always-run assumptions gate.
prove: builder
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) --target prover .

prover-log: builder
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) --progress=plain --target prover .

# The emit stage alone (intermediate): Dune-cached theory build, then extract the image + run the writer
# from proved bytes; checks the witness assumption closure.  Wired into `check` via `e2e`.
emit: builder
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) --progress=plain --target emit .

# The full last-mile e2e (part of `check`): emit the witness, then the pinned Go toolchain builds/runs it
# and compares stdout/stderr/exit to the reviewed goldens.
e2e: builder
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) --progress=plain --target go-e2e .

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
