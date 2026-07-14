BUILDER := fido-builder
# The build platform is pinned to linux/amd64 — the 64-bit target the theory assumes (Ints: int/uint are
# 64-bit).  SEALED: `override` makes any command-line/env change inert (the e2e also asserts the running
# toolchain's GOOS/GOARCH/word size).  This is an operational pin, not a certified TargetConfig.
override PLATFORM := linux/amd64

.PHONY: check prove emit e2e regenerate ocaml-origin-gate generated-output-gate builder install-hooks prover-log
.DEFAULT_GOAL := check

# Fido (ARCHITECTURE.md): an LLM proposes a GoProgram (a ModuleSpec + a possibly-empty finite map of
# intrinsic FilePath keys to raw file ASTs); emission is available only after Rocq proves GoCompile (exact
# whole-program admissibility, matching `go build ./...`) and GoSafe.  Chain:
#   GoProgram -> GoCompile (+CompilationFacts) -> GoSafe -> direct GoRender (incl. go.mod) -> complete
#     DirectoryImage -> the general `Fido Emit` transport command -> foreign-Go-rejecting local-staging
#     sink -> go build ./...
# ALL Rocq/Go work runs in the PINNED container via buildx — host Rocq is NOT supported.

check: ocaml-origin-gate generated-output-gate prove e2e
	@echo "fido: check OK — proved the core axiom-free (whole-theory audit: constants+inductives+named, run in prove) AND emitted the pristine generated-module (rendered go.mod + witness/multi/empty) via the Fido Emit transport + sibling-temp dirty-directory sink through go build ./... vs goldens; transport-only OCaml, tracked Go is Fido-headed generated output ✓"

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

# Regenerate the tracked canonical Go module: build (and load) the `sync` image — the pristine
# `generated-module` layer built from the CURRENT working-tree proof inputs, plus the filesystem-only apply
# CLI — then run it with the repository root bind-mounted so the SAME Fido_sink synchronizes /generated into
# the repo (preserving foreign non-Go files, rejecting foreign Go/module + nested .fido, updating tracked
# go.mod + recursive .go, removing stale Fido-owned .go).  It never invokes an independent renderer.  After
# it runs, stage go.mod + recursive *.go and commit; the pre-commit staged-index check verifies byte-exactness.
regenerate: builder
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) --target sync --load -t fido-sync .
	docker run --rm -u $$(id -u):$$(id -g) -v "$(CURDIR)":/dest fido-sync
	@echo "fido: regenerate OK — the pristine canonical module was synced into the repo root via Fido_sink."
	@echo "      Stage + commit:  git add -A -- go.mod ':(top,glob)**/*.go' && git commit"

ocaml-origin-gate:
	@sh tools/ocaml-origin-gate.sh

# Zero project axioms are enforced inside the pinned `prove` stage: gate/axiom_gate.v (Print Assumptions on
# the public surfaces) + the Rocq-native `Fido Audit Assumptions` WHOLE-certified-theory audit over
# constants + inductives + surviving named assumptions (module set DERIVED from dune's (modules ...) list so
# nothing escapes) + adversarial self-tests A-E.  No source-text scanner.

# GENERATED-OUTPUT POLICY GATE (replaces the deleted no-tracked-Go seal): tracked Go IS the reviewed
# canonical generated module — every tracked .go / root go.mod is Fido-headed, no nested go.mod, no tracked
# .fido/temp.  The byte-exact-vs-pristine check is the pre-commit staged-index Buildx job, not this gate.
generated-output-gate:
	@sh tools/generated-output-gate.sh

builder:
	@docker buildx inspect $(BUILDER) > /dev/null 2>&1 || \
	  docker buildx create --name $(BUILDER) --driver docker-container --bootstrap
	@docker buildx use $(BUILDER)

install-hooks:
	git config core.hooksPath .githooks
