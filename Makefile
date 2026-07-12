BUILDER := fido-builder
# The build platform is pinned to linux/amd64 — the 64-bit target the theory assumes (Ints: int/uint are
# 64-bit).  SEALED: `override` makes any command-line/env change inert (the e2e also asserts the running
# toolchain's GOOS/GOARCH/word size).  This is an operational pin, not a certified TargetConfig.
override PLATFORM := linux/amd64

.PHONY: check prove emit e2e ocaml-origin-gate go-uncommittable-seal builder install-hooks prover-log
.DEFAULT_GOAL := check

# Fido (ARCHITECTURE.md): an LLM proposes a GoProgram (a nonempty finite map of intrinsic FilePath keys
# to raw file ASTs); emission is available only after Rocq proves GoCompile (exact whole-program
# admissibility, matching `go build ./...`) and GoSafe.  Chain:
#   GoProgram -> GoCompile (+CompilationFacts) -> GoSafe -> direct GoRender -> abstract DirectoryImage
#     -> the general `Fido Emit` transport command -> one dirty-directory filesystem sink -> go build ./...
# ALL Rocq/Go work runs in the PINNED container via buildx — host Rocq is NOT supported.

check: ocaml-origin-gate go-uncommittable-seal prove e2e
	@echo "fido: check OK — proved the core (FilePath/FMap/Ints/GoAST/GoCompile/GoSafe/GoRender/GoEmit) axiom-free AND emitted the whole tree via the Fido Emit transport + dirty-directory sink through go build ./... vs goldens; transport-only OCaml, no tracked *.go ✓"

# The reproducible container proof: dune compiles the modules + the always-run assumptions gate.
prove: builder
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) --target prover .

prover-log: builder
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) --progress=plain --target prover .

# The emit stage alone (intermediate): Dune-cached theory + plugin build, then the general `Fido Emit`
# command (explicit rocq c on the witness, not a .vo side effect) synchronizes the whole tree; the sink
# is exercised against dirty + adversarial trees.  Wired into `check` via `e2e`.
emit: builder
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) --progress=plain --target emit .

# The full last-mile e2e (part of `check`): emit the whole tree, then the pinned Go toolchain runs
# `go build ./...` over it and runs the witness, comparing stdout/stderr/exit to the reviewed goldens.
e2e: builder
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) --progress=plain --target go-e2e .

ocaml-origin-gate:
	@sh tools/ocaml-origin-gate.sh

# Zero project axioms are enforced two ways in the pinned build: gate/axiom_gate.v (Print Assumptions on
# the public surfaces, in `prove`) + the Rocq-native `Fido Audit Assumptions` global-environment audit
# (gate/assumptions_audit.v, in `emit`, with a planted-axiom self-test).  No source-text scanner.

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
