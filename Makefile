BUILDER := fido-builder
# The build platform is pinned to linux/amd64 — the 64-bit target the theory assumes (Ints: int/uint are
# 64-bit).  SEALED: `override` makes any command-line/env change inert (the e2e also asserts the running
# toolchain's GOOS/GOARCH/word size).  This is an operational pin, not a certified TargetConfig.
override PLATFORM := linux/amd64

.PHONY: check prove emit e2e regenerate builder install-hooks prover-log
.DEFAULT_GOAL := check

# Fido (ARCHITECTURE.md): an LLM proposes a GoProgram (a ModuleSpec + a possibly-empty finite map of
# intrinsic FilePath keys to raw file ASTs); emission is available only after Rocq proves GoCompile — the EXACT
# acceptance model for the pinned one-shot `go build ./...` (the fresh-build output preflight over the factored
# source rules: whole-program typing via GoTypes + PackageDeclsUnique + MainPackagesHaveEntry) — and GoSafe.  Chain:
#   GoProgram (GoFileMap source forest) -> GoTypes (untyped GoConst -> context-resolved GoType, ProgramTyped)
#     -> GoCompile (fresh-build preflight + SourceProgramValid = the one-shot `go build ./...` acceptance)
#     -> GoSafe -> direct GoRender (source-owned package clause + go.mod) -> complete
#     DirectoryImage -> `Fido Materialize` writes the authoritative pristine image DIRECTLY -> pinned
#     `go build ./...` VALIDATES it -> only then `Fido Emit` publishes the SAME bytes via the
#     foreign-Go-rejecting sibling-temp sink (validation-before-publication; a failed build blocks publish).
# ALL Rocq/Go work runs in the PINNED container via buildx — host Rocq is NOT supported.

# `make check` verifies the WORKING TREE, coherently and in ONE place.  It materializes the working-tree
# content of every relevant file — `git ls-files --cached --others --exclude-standard` enumerates candidate
# paths (tracked files WITH their uncommitted edits, PLUS untracked files that are not gitignored, so a rogue
# untracked `foreign.go` / `.ml` is caught; the gitignored local residue .fido/, *.fido-tmp-v1, *.vo, _build/
# is excluded, which a raw `find .` would instead wrongly flag); a `python3` filter keeps ONLY the candidate
# paths that EXIST ON DISK (so a tracked file DELETED in the working tree is NOT reintroduced from the index —
# its absence then surfaces in the byte-compare; PRESENCE is disk-determined, not index membership), and then
# PLAIN `tar` (NO --ignore-failed-read) archives them into a temp tree — so an existing-but-UNREADABLE `.go`
# makes tar FAIL loudly rather than being silently omitted (a rogue that would otherwise pass).  Over that
# temp tree it runs the lightweight
# repository-policy gates over THAT tree (transport-only OCaml; tracked Go/go.mod Fido-headed, no nested
# go.mod), and byte-compares its generated go.mod + recursive .go against a pristine `generated-module` layer
# built from the SAME working-tree proof inputs (`.dockerignore` excludes the committed go.mod/.go, so the
# pristine is independent of the tracked bytes — this closes the byte-drift hole a header-preserving `main.go`
# edit would otherwise slip through).  `prove`/`e2e` build from the working-tree Buildx context.  It does NOT
# export or compare the staged INDEX snapshot — that is the pre-commit hook's coherent, separate job.  (The
# exact-Git-mode-100644 gate is a committed-policy check and runs ONLY in the hook; on the working tree the
# generated-output gate's own -L/-f/-x file-type tests are authoritative.)
check: prove e2e builder
	@tmp=$$(mktemp -d); tree="$$tmp/tree"; mkdir -p "$$tree"; \
	  git ls-files -z --cached --others --exclude-standard \
	    | python3 -c 'import sys,os;d=sys.stdin.buffer.read().split(b"\x00");sys.stdout.buffer.write(b"\x00".join(p for p in d if p and os.path.lexists(p)))' > "$$tmp/list.nul" && \
	  tar --null -T "$$tmp/list.nul" -cf "$$tmp/tree.tar" && \
	  tar -xf "$$tmp/tree.tar" -C "$$tree" && \
	  sh tools/ocaml-origin-gate.sh    "$$tree" && \
	  sh tools/generated-output-gate.sh "$$tree" && \
	  docker buildx build --builder $(BUILDER) --platform $(PLATFORM) --target generated-artifact \
	    --output "type=local,dest=$$tmp/pristine" . && \
	  sh tools/staged-generated-compare.sh "$$tree" "$$tmp/pristine"; \
	  rc=$$?; rm -rf "$$tmp"; \
	  if [ $$rc -eq 0 ]; then echo "fido: check OK (working tree) — proved the core axiom-free (whole-theory audit run in prove) AND emitted the pristine generated-module via the Fido Emit transport + sibling-temp sink through go build ./... vs goldens; the working-tree generated go.mod + recursive .go byte-match the pristine artifact (exact path set + bytes); transport-only OCaml, tracked Go is Fido-headed generated output ✓"; fi; \
	  exit $$rc

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

# Zero project axioms are enforced inside the pinned `prove` stage: gate/axiom_gate.v (Print Assumptions on
# the public surfaces) + the Rocq-native `Fido Audit Assumptions` WHOLE-certified-theory audit over
# constants + inductives + surviving named assumptions (module set DERIVED from dune's (modules ...) list so
# nothing escapes) + adversarial self-tests A-E.  No source-text scanner.
#
# The generated-output POLICY GATE (tools/generated-output-gate.sh, run over the working tree by `check` and
# over the exported index by the hook): tracked Go IS the reviewed canonical generated module — every tracked
# .go / root go.mod is Fido-headed, no nested go.mod, no tracked .fido/temp.

# The INDEX-authoritative Git-mode gate (tools/generated-mode-gate.sh — every tracked generated go.mod + .go
# has EXACT stage-0 index mode 100644, read from `git ls-files -s`, catching a mode-120000/100755 entry a
# `core.symlinks=false` export would hide) is a STAGED/committed-policy check, so it runs ONLY in the
# pre-commit hook.  `make check` verifies the WORKING TREE, where the generated-output gate's own
# `-L`/`-f`/`-x` file-type tests on the real files are authoritative for mode.

builder:
	@docker buildx inspect $(BUILDER) > /dev/null 2>&1 || \
	  docker buildx create --name $(BUILDER) --driver docker-container --bootstrap
	@docker buildx use $(BUILDER)

install-hooks:
	git config core.hooksPath .githooks
