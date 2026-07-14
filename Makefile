BUILDER := fido-builder
# The build platform is pinned to linux/amd64 — the 64-bit target the theory assumes (Ints: int/uint are
# 64-bit).  SEALED: `override` makes any command-line/env change inert (the e2e also asserts the running
# toolchain's GOOS/GOARCH/word size).  This is an operational pin, not a certified TargetConfig.
override PLATFORM := linux/amd64

.PHONY: check prove emit e2e regenerate ocaml-origin-gate generated-output-gate precommit-selftest verify-generated builder install-hooks prover-log
.DEFAULT_GOAL := check

# Fido (ARCHITECTURE.md): an LLM proposes a GoProgram (a ModuleSpec + a possibly-empty finite map of
# intrinsic FilePath keys to raw file ASTs); emission is available only after Rocq proves GoCompile (exact
# whole-program admissibility — whole-program typing via GoTypes + one-main-per-package, matching
# `go build ./...`) and GoSafe.  Chain:
#   GoProgram -> GoTypes (untyped GoConst -> context-resolved GoType, ProgramTyped) -> GoCompile
#     (+CompilationFacts) -> GoSafe -> direct GoRender (incl. go.mod) -> complete
#     DirectoryImage -> the general `Fido Emit` transport command -> foreign-Go-rejecting sibling-temp
#     sink -> go build ./...
# ALL Rocq/Go work runs in the PINNED container via buildx — host Rocq is NOT supported.

check: ocaml-origin-gate generated-output-gate precommit-selftest prove e2e verify-generated
	@echo "fido: check OK — proved the core axiom-free (whole-theory audit: constants+inductives+named, run in prove) AND emitted the pristine generated-module (rendered go.mod + witness/multi/empty) via the Fido Emit transport + sibling-temp dirty-directory sink through go build ./... vs goldens; the tracked generated go.mod + recursive .go byte-match the pristine artifact (exact path set + bytes); transport-only OCaml, tracked Go is Fido-headed generated output; staged-index gates self-tested unbypassable ✓"

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
	@tmp=$$(mktemp -d) && git checkout-index --ignore-skip-worktree-bits --all --prefix="$$tmp/" && sh "$$tmp/tools/ocaml-origin-gate.sh" "$$tmp"; rc=$$?; rm -rf "$$tmp"; exit $$rc

# Zero project axioms are enforced inside the pinned `prove` stage: gate/axiom_gate.v (Print Assumptions on
# the public surfaces) + the Rocq-native `Fido Audit Assumptions` WHOLE-certified-theory audit over
# constants + inductives + surviving named assumptions (module set DERIVED from dune's (modules ...) list so
# nothing escapes) + adversarial self-tests A-E.  No source-text scanner.

# GENERATED-OUTPUT POLICY GATE (replaces the deleted no-tracked-Go seal): tracked Go IS the reviewed
# canonical generated module — every tracked .go / root go.mod is Fido-headed, no nested go.mod, no tracked
# .fido/temp.  The byte-exact-vs-pristine check is the separate `verify-generated` Buildx job (in `check` and
# the pre-commit staged-index hook), not this gate.
generated-output-gate:
	@tmp=$$(mktemp -d) && git checkout-index --ignore-skip-worktree-bits --all --prefix="$$tmp/" && sh "$$tmp/tools/generated-output-gate.sh" "$$tmp"; rc=$$?; rm -rf "$$tmp"; exit $$rc

# STAGED-TREE-GATE SELF-TEST (contract §27): a Buildx-free host demonstration that the staged-index gates
# CANNOT be bypassed.  It builds synthetic exported-snapshot trees with the REAL gate scripts and asserts:
# staged bad OCaml/Go under ANY directory name (incl. hidden/underscore/testdata/vendor) is rejected — the
# gates are repository-content gates over the staged snapshot, NOT the runtime sink, so no directory is
# opaque; the STAGED gate implementation is the one executed; stale/modified/missing/extra generated files
# are rejected at every depth; a docs-only commit is fully verified; and the hook never mutates the
# index/working tree.  It walks no Rocq terms and needs no Docker.
precommit-selftest:
	sh tools/precommit-selftest.sh

# TRACKED GENERATED-BYTE VERIFICATION (contract §27 "no generated-byte delta"): export the Git INDEX, then
# materialize the PRISTINE generated-module (Buildx `generated-artifact`, built from the exported staged
# proof inputs — `.dockerignore` excludes the committed go.mod/.go, so the pristine is independent of the
# tracked bytes), and byte-compare the exported tracked go.mod + recursive .go against it (exact path set +
# bytes, both directions).  This is the SAME comparison the pre-commit staged-index hook runs; wiring it into
# `check` closes the generated-byte-drift hole — a header-preserving edit to `main.go` (or an extra
# Fido-headed `.go`) passes the output-policy gate and is invisible to proof/e2e (excluded from Buildx), so
# ONLY this check catches it.
verify-generated: builder
	@tmp=$$(mktemp -d); ctx="$$tmp/ctx"; \
	  git checkout-index --ignore-skip-worktree-bits --all --prefix="$$ctx/" && \
	  docker buildx build --builder $(BUILDER) --platform $(PLATFORM) --target generated-artifact \
	    --output "type=local,dest=$$tmp/pristine" "$$ctx" && \
	  sh "$$ctx/tools/staged-generated-compare.sh" "$$ctx" "$$tmp/pristine"; \
	  rc=$$?; rm -rf "$$tmp"; exit $$rc

builder:
	@docker buildx inspect $(BUILDER) > /dev/null 2>&1 || \
	  docker buildx create --name $(BUILDER) --driver docker-container --bootstrap
	@docker buildx use $(BUILDER)

install-hooks:
	git config core.hooksPath .githooks
