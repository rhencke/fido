BUILDER := fido-builder
# The build platform is pinned to linux/amd64 — the 64-bit target the theory assumes (Integer: int/uint are
# 64-bit).  SEALED: `override` makes any command-line/env change inert (the e2e also asserts the running
# toolchain's GOOS/GOARCH/word size).  This is an operational pin, not a certified TargetConfig.
override PLATFORM := linux/amd64

.PHONY: check prove emit e2e regenerate regen-guard builder install-hooks prover-log prove-errors fmt names \
        fcb fcb-write claims profile
.DEFAULT_GOAL := check

# The certified pipeline and the transport boundary are the charter (ARCHITECTURE.md); they are not restated
# here.  ALL Rocq/Go work runs in the PINNED container via buildx — host Rocq is NOT supported.

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
check: names fcb claims prove e2e builder
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
	  if [ $$rc -eq 0 ]; then echo "fido: check OK (working tree) — proved the core axiom-free (whole-theory audit run in prove) AND materialized the pristine generated-module (Fido Materialize) + validated it through go build ./... vs goldens (the internal sibling-temp sink exercised separately); the working-tree generated go.mod + recursive .go byte-match the pristine artifact (exact path set + bytes); transport-only OCaml, tracked Go is Fido-headed generated output ✓"; fi; \
	  exit $$rc

# The reproducible container proof: dune compiles the modules + the always-run assumptions gate.
prove: builder
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) --target prover .

prover-log: builder
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) --progress=plain --target prover .

# Diagnostic only — never a gate, never wired into `check` or the hook.  Recompiles ONE module with
# `rocq c -time` against the dune-built dependencies and ranks its sentences and declarations by cost, so a
# slow build can be attributed instead of guessed at.  `make profile FILE=Typing.v TOP=25`.
FILE ?= Compilable.v
TOP  ?= 40
profile: builder
	@out=$${TMPDIR:-/tmp}/fido-profile; rm -rf "$$out"; mkdir -p "$$out"; \
	  docker buildx build --builder $(BUILDER) --platform $(PLATFORM) --progress=plain \
	    --target profile-log --build-arg PROFILE_FILE=$(FILE) --no-cache-filter profile \
	    --output "type=local,dest=$$out" . && \
	  python3 tools/rocq-profile.py $(FILE) "$$out/time.log" $(TOP); \
	  rc=$$?; echo "fido: raw -time log kept at $$out/time.log"; exit $$rc

# The emit stage alone (intermediate): Dune-cached theory + plugin build, then each witness MATERIALIZES its
# authoritative pristine image (`Fido Materialize`, explicit rocq c on the witness — not a .vo side effect);
# the INTERNAL publication sink is exercised SEPARATELY against dirty + adversarial trees (sink_test).  There
# is NO public `Fido Emit` command — the sink is reached in production only through the validated `make
# regenerate` workflow.  The FRESH-BUILD VALIDATION that gates real publication runs in `e2e` (`go build
# ./...`); this intermediate stage is wired into `check` via `e2e`.
emit: builder
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) --progress=plain --target emit .

# The full last-mile e2e (part of `check`): emit the whole tree, then the pinned Go toolchain runs
# `go build ./...` over it and runs the witness, comparing stdout/stderr/exit to the reviewed goldens.
e2e: builder
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) --progress=plain --target go-e2e .

# Regenerate the tracked canonical Go module through the ONE supported validate-before-publish workflow.  Building
# the `sync` target FORCES the go-e2e stage (the pinned `go build ./...`) via the Docker DAG (`sync` COPYs
# go-e2e's /fresh-build-ok) — so a failed fresh build makes `sync` unbuildable and no sink effect occurs.  The
# sync image bakes in the pristine `generated-module` layer + the tiny internal apply adapter; run with the
# repository root bind-mounted at /dest, Sink synchronizes /generated into the repo (preserving foreign
# non-Go files, rejecting foreign Go/module + nested .fido, updating tracked go.mod + recursive .go, removing
# stale Fido-owned .go).  It publishes the ORIGINAL generated-module bytes, never a post-build byte.  After it
# runs, stage go.mod + recursive *.go and commit; the pre-commit staged-index check verifies byte-exactness.
regenerate: builder
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) --target sync --load -t fido-sync .
	docker run --rm -u $$(id -u):$$(id -g) -v "$(CURDIR)":/dest fido-sync
	@echo "fido: regenerate OK — building 'sync' forced the pinned go build ./... (Docker DAG), then the SAME pristine bytes were synced into the repo root via Sink."
	@echo "      Stage + commit:  git add -A -- go.mod ':(top,glob)**/*.go' && git commit"

# Structural regression proving the validate-before-publish DAG edge is load-bearing: with go-e2e forced to
# FAIL (on a temp Dockerfile copy), `--target sync` must be UNBUILDABLE; on the unmodified tree it must build.
# So `make regenerate` cannot publish unless the pinned `go build ./...` validated the pristine first.
regen-guard: builder
	BUILDER=$(BUILDER) PLATFORM=$(PLATFORM) sh tools/regen-guard-test.sh

# The INDEX-authoritative Git-mode gate (tools/generated-mode-gate.sh — every tracked generated go.mod + .go
# has EXACT stage-0 index mode 100644, read from `git ls-files -s`, catching a mode-120000/100755 entry a
# `core.symlinks=false` export would hide) is a STAGED/committed-policy check, so it runs ONLY in the
# pre-commit hook.  `make check` verifies the WORKING TREE, where the generated-output gate's own
# `-L`/`-f`/`-x` file-type tests on the real files are authoritative for mode.

# Whitespace/format check against `.editorconfig`.  Property resolution is delegated to the EditorConfig
# reference implementation (apt: `editorconfig`), so glob matching, nesting and inheritance are the spec's.
# It REPORTS and never rewrites — this tree is full of byte-exact artifacts (generated Go byte-compared against
# the pristine build, reviewed goldens pinning control characters, frozen evidence cited by hash elsewhere).
# Deliberately NOT wired into `check` or the pre-commit hook: those stay code-level gates, and every whitespace
# case that can actually break something is already caught by a stronger, semantic check.
fmt:
	@python3 tools/fmt-check.py

# A005 scoped-name policy gate.  The compiler verifies Rocq names for free; documentation
# has no verifier at all, so this is the only checker the prose gets.  Reports, never rewrites.
names:
	@python3 tools/naming-gate.py

# The live-FCB document gates, in one place so they stay one thing rather than three lines that drift.
# Each has ONE implementation shared by its writer and its checker, so a checker cannot drift from what
# generates the file, and each runs its adversarial controls FIRST — a gate that has never been shown to
# fail is not evidence.
#
#   D-07  open human acts are DISCOVERED from `FIDO_FCB_HUMAN_ACTS.tsv`, never hand-copied;
#         `FIDO_FCB_HUMAN_REVIEW_INDEX.md` is its generated view.
#   D-24  every OPERATIONAL path the live FCB names resolves at the same exact ref, or is explicitly typed
#         off-tree with a stated availability.  The corpus DECLARES those references in
#         `FIDO_FCB_REFERENCES.tsv`; it is not scanned for backticked strings, because a scanner needs an
#         exception list and an exception list is where a dangling path hides.
#   the spec-closure ledger's human view is regenerated from the canonical 491-row CSV, so its own claim to
#         be generated is true rather than decorative.
# The repair-18 claim-to-theorem matrix.  Freeze prose is not gated by anything, so it can drift past what
# the public statements carry — which is how the previous candidate blocked.  Each load-bearing completion
# claim names the exact surface, fixture and gate that establish it, and this verifies they EXIST under
# those exact names.  It does not judge theorem strength; a human does that.
claims:
	@python3 tools/claim-matrix-gate.py --self-test
	@python3 tools/claim-matrix-gate.py

fcb:
	@python3 tools/human-review-index.py --self-test
	@python3 tools/human-review-index.py --check
	@python3 tools/fcb-reference-gate.py --self-test
	@python3 tools/fcb-reference-gate.py
	@python3 tools/closure-ledger-view.py --check

# regenerate every generated FCB view from its canonical source
fcb-write:
	@python3 tools/human-review-index.py --write
	@python3 tools/closure-ledger-view.py --write

# Just the Rocq File/Error lines from the pinned prover log.  On failure Buildx echoes the ENTIRE prove
# recipe back as its error trailer — hundreds of lines — which buries the two lines that say what actually
# broke.  This extracts them.  Never a substitute for `prove`: it reports, it does not verify.
prove-errors:
	@$(MAKE) --no-print-directory prover-log > /tmp/fido-prover.log 2>&1 || true
	@grep -E '(^|[0-9.# ]+)(File "|Error:)' /tmp/fido-prover.log | sed 's/^[0-9.# ]*//' | sort -u | head -40 \
	  || echo "fido: no File/Error lines — see /tmp/fido-prover.log"

builder:
	@docker buildx inspect $(BUILDER) > /dev/null 2>&1 || \
	  docker buildx create --name $(BUILDER) --driver docker-container --bootstrap
	@docker buildx use $(BUILDER)

install-hooks:
	git config core.hooksPath .githooks
