BUILDER := fido-builder
# The 64-bit target the theory assumes; `override` makes a command-line or environment change inert.
override PLATFORM := linux/amd64

.PHONY: check prove emit e2e regenerate regen-guard builder install-hooks prover-log prove-errors fmt names \
        fcb fcb-write claims diet audit-fresh profile
.DEFAULT_GOAL := check

# All Rocq and Go work runs in the pinned container through buildx; host Rocq is not supported.

# `make check` verifies the WORKING TREE.  Three choices in the recipe below are load-bearing:
#   `git ls-files --cached --others --exclude-standard` catches a rogue untracked `.go`/`.ml` that `find`
#     would miss, and skips the gitignored residue that `find` would wrongly flag;
#   the python3 filter keeps only paths that exist ON DISK, so a tracked file deleted in the working tree is
#     not reintroduced from the index — its absence surfaces in the byte-compare instead;
#   plain `tar` (no --ignore-failed-read) makes an existing-but-unreadable file fail loudly.
# `.dockerignore` hides the committed go.mod and .go from Buildx, so the pristine is independent of the
# tracked bytes — which is what catches a header-preserving edit to a tracked `.go`.  The staged snapshot,
# and the exact-Git-mode gate over it, are the pre-commit hook's job rather than this one's.
check: names fcb claims diet prove e2e builder
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

# Diagnostic only, never a gate.  Recompiles ONE module with `-time` and ranks its sentences by cost, so a
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

# The emit stage alone: theory and plugin, then each witness materializes its pristine image through an
# explicit `rocq c`, not a .vo side effect.  The internal sink is exercised separately, against dirty and
# adversarial trees.  The fresh-build validation that gates real publication is in `e2e`.
emit: builder
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) --progress=plain --target emit .

# Emit the whole tree, then the pinned Go toolchain builds it and runs the witness against the goldens.
e2e: builder
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) --progress=plain --target go-e2e .

# Regenerate the tracked module through the one validate-before-publish workflow.  Building `sync` FORCES
# the pinned `go build ./...` through the Docker DAG (`sync` COPYs go-e2e's /fresh-build-ok), so a failed
# fresh build makes `sync` unbuildable and no sink effect occurs.  It publishes the original pristine bytes,
# never a post-build one.
regenerate: builder
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) --target sync --load -t fido-sync .
	docker run --rm -u $$(id -u):$$(id -g) -v "$(CURDIR)":/dest fido-sync
	@echo "fido: regenerate OK — building 'sync' forced the pinned go build ./... (Docker DAG), then the SAME pristine bytes were synced into the repo root via Sink."
	@echo "      Stage + commit:  git add -A -- go.mod ':(top,glob)**/*.go' && git commit"

# Force the proof gate and the whole-tree e2e to RUN rather than report a Buildx cache hit.  A cached
# verdict is valid, but an audit should observe its assertions rather than infer them from a cache key.
audit-fresh: builder
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) --progress=plain \
	  --no-cache-filter prover --target prover .
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) --progress=plain \
	  --no-cache-filter go-e2e --target go-e2e .

# With go-e2e forced to FAIL on a temp Dockerfile copy, `--target sync` must be unbuildable, and on the
# unmodified tree it must build — so `make regenerate` cannot publish without a validated fresh build.
regen-guard: builder
	BUILDER=$(BUILDER) PLATFORM=$(PLATFORM) sh tools/regen-guard-test.sh

# Whitespace check against `.editorconfig`, with property resolution delegated to the EditorConfig reference
# implementation.  It reports and never rewrites, because this tree is full of byte-exact artifacts.
# Deliberately not a gate: every whitespace case that can break something is caught by a stronger check.
fmt:
	@python3 tools/fmt-check.py

# The scoped-name policy gate.  The compiler verifies Rocq names for free; prose has no verifier at all,
# so this is the only one it gets.
names:
	@python3 tools/naming-gate.py

# The claim-to-theorem matrix.  Freeze prose is gated by nothing else, so it can drift past what the public
# statements carry.  Each completion claim names the exact surface, fixture and gate that establish it, and
# this verifies they exist under those exact names.  It does not judge theorem strength; a human does that.
claims:
	@python3 tools/claim-matrix-gate.py --self-test
	@python3 tools/claim-matrix-gate.py

# The live-FCB document gates.  Each has ONE implementation shared by its writer and its checker, and each
# runs its adversarial controls FIRST — a gate that has never been shown to fail is not evidence.
# The M1 source diet: the .v comment law, the exception relation both ways, and one disposition per file.
# Its adversarial controls run first, so a green here is one the checker can still earn.
# The PERMANENT source-comment policy, and only that.  The M1 baseline, metric direction, file
# disposition and code identity are one checkpoint's exit evidence: they are proved by
# `--verify-m1-evidence` at M1 review and never here, because a permanent gate that enforced them would
# reject every later file, every later declaration and every larger tree forever.
diet:
	@python3 tools/source-diet.py --self-test
	@python3 tools/source-diet.py --check
	@python3 tools/source-diet.py --wiring

fcb:
	@python3 tools/human-review-index.py --self-test
	@python3 tools/human-review-index.py --check
	@python3 tools/fcb-reference-gate.py --self-test
	@python3 tools/fcb-reference-gate.py
	@python3 tools/closure-ledger-view.py --check
	@python3 tools/gate-mutation-test.py

# regenerate every generated FCB view from its canonical source
fcb-write:
	@python3 tools/human-review-index.py --write
	@python3 tools/closure-ledger-view.py --write

# Just the Rocq File/Error lines.  On failure Buildx echoes the entire recipe back as its error trailer,
# hundreds of lines, which buries the two that say what broke.  It reports; it does not verify.
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
