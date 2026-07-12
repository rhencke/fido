BUILDER := fido-builder
# The build platform is pinned to linux/amd64 — the 64-bit target the theory assumes (Ints: int/uint are
# 64-bit).  SEALED: `override` makes any command-line/env change inert (the e2e also asserts the running
# toolchain's GOOS/GOARCH/word size).  This is an operational pin, not a certified TargetConfig.
override PLATFORM := linux/amd64

.PHONY: check prove emit e2e ocaml-origin-gate go-uncommittable-seal axiom-scan builder install-hooks prover-log
.DEFAULT_GOAL := check

# Fido — ONE AST (ARCHITECTURE.md): an LLM proposes a GoProgram (a finite map of relative paths to raw
# file ASTs); emission is available only after Rocq proves GoCompile (exact whole-program admissibility)
# and GoSafe.  Chain:
#   GoProgram -> GoCompile -> GoSafe -> direct GoRender -> GoEmit (finite-map DirectoryImage)
#     -> extraction -> one dirty-directory filesystem sink.
# ALL Rocq/Go work runs in the PINNED container via buildx — host Rocq is NOT supported.

check: ocaml-origin-gate go-uncommittable-seal axiom-scan prove e2e
	@echo "fido: check OK — proved the core (FMap/Ints/GoAST/GoCompile/GoSafe/GoRender/GoEmit) axiom-free AND emitted+synced the e2e witness through the pinned Go toolchain; one filesystem sink, no tracked *.go ✓"

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

# Anti-axiom DECLARATION scan (defense-in-depth; the AUTHORITY is gate/axiom_gate.v's Print Assumptions).
# Rejects Axiom/Parameter/Conjecture/Admitted/admit anywhere and top-level Variable/Hypothesis/Context;
# Sections are permitted.  Has positive+negative self-tests.
axiom-scan:
	@sh tools/axiom-scan.sh

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
