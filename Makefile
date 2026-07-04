BUILDER  := fido-builder
IMAGE    := fido
TAG      ?= latest
PLATFORM ?= linux/$(shell uname -m | sed 's/x86_64/amd64/;s/aarch64/arm64/')

.PHONY: builder build bake push run run-extracted extract go-run install-hooks check golden negtest printer printer-verify emit-verify emit-demo smart-ctor-gate axiom-authority-selftest prover-log go-verify print-goimage toolchain-gate toolchain-selftest go-verify-selftest
.DEFAULT_GOAL := build

# THE ONE Go-toolchain image authority, DIGEST-PINNED (mutable tags drift; these runs justify
# go-run-verified semantic pins). `override` makes command-line/environment assignments INERT — a
# second toolchain is unrepresentable, not merely rejected. This line is the ONLY Go-image spelling
# in the repo: every docker run uses $(GOIMAGE), every docker build receives it via --build-arg
# (the Dockerfile ARG has NO default — a build that bypasses make fails loudly), and the pre-commit
# hook consumes it via `make -s print-goimage`. [toolchain-gate] + [toolchain-selftest] (both
# `check` prerequisites) enforce all of this.
override GOIMAGE := golang:1.23-alpine@sha256:383395b794dffa5b53012a212365d40c8e37109a626ca30d6151c8348d380b5f
print-goimage:
	@echo $(GOIMAGE)

# Run the extracted program (Go's println writes to stderr → capture 2>&1).
GORUN := docker run --rm -v "$(PWD)":/w -w /w $(GOIMAGE) go run .
# `go vet` gate: `go run` already BUILDS the emitted Go (so a type error
# anywhere fails), but vet catches suspicious-but-COMPILING constructs (bad printf verbs,
# unreachable code, lost cancels, self-assignment, …) that a plugin bug could emit silently.
# The no-import `package main` vets offline.  Wired into [check] and [golden] below.
GOVET := docker run --rm -v "$(PWD)":/w -w /w $(GOIMAGE) go vet .

# One-time setup: activate git hooks from .githooks/.
install-hooks:
	git config core.hooksPath .githooks

# One-time setup: create a docker-container buildx builder capable of multi-platform builds.
builder:
	docker buildx inspect $(BUILDER) > /dev/null 2>&1 || \
	  docker buildx create --name $(BUILDER) --driver docker-container --bootstrap
	docker buildx use $(BUILDER)

# Fast local build (native platform only, loads into local docker daemon).
build:
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) --build-arg GOIMAGE=$(GOIMAGE) --load -t $(IMAGE):$(TAG) .

# Extract generated Go sources from the prover stage into the repo.
# Wipes all *.go files first so renamed/deleted theories don't leave strays.
extract:
	rm -f *.go *.go.raw
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) --build-arg GOIMAGE=$(GOIMAGE) \
	  --output type=local,dest=. --target go-src .
	# Canonicalise with gofmt (the plugin emits valid but non-canonical whitespace).
	# gofmt is a TRUSTED normaliser OUTSIDE the printer-proof claim; the guard below is a COARSE net (strips
	# all whitespace, asserts the rest is byte-equal) — it catches gofmt altering a non-whitespace byte, but
	# it is NOT token-stream preservation.
	for f in *.go; do cp "$$f" "$$f.raw"; done
	docker run --rm -v "$(PWD)":/w -w /w $(GOIMAGE) gofmt -w *.go
	for f in *.go; do \
	  if [ "`tr -d '[:space:]' < "$$f.raw"`" != "`tr -d '[:space:]' < "$$f"`" ]; then \
	    echo "fido: GOFMT ALTERED A NON-WHITESPACE BYTE in $$f — gofmt is not whitespace-only here; refusing."; \
	    rm -f *.go.raw; exit 1; \
	  fi; \
	done
	rm -f *.go.raw
	@echo "fido: gofmt (TRUSTED normaliser) altered whitespace only — coarse guard passed (NOT a token-preservation proof) ✓"

# Run the extracted Go sources directly without Docker.
run-local: extract
	go run .

# Fail-closed regression harness: compile each negtests/*.v and assert it ABORTS extraction with its
# declared `(* EXPECT: … *)` message (a reopened fail-closed site is the defect the golden cannot see).
negtest:
	dune build
	@sh negtests/run.sh

# Code-discipline gate: the structural / smart-ctor checks (enumerated in plugin/smart-ctor-gate.sh — that
# file is the single source for what they are). Runs here, in the pre-commit hook, and non-bypassably in the
# Docker prover stage (so `make check` enforces it).
smart-ctor-gate:
	@sh plugin/smart-ctor-gate.sh

# Axiom-authority self-test: pin that the manifest axiom gate of record — Rocq's own `Print Assumptions`,
# captured by the Docker manifest gate — catches an axiom in EVERY declaration form (Local/Global/Polymorphic
# Axiom, attributes, …) or that the kernel rejects it. Needs host rocq (compiles tiny snippets). Runs
# non-bypassably in the Docker prover stage; this is the local mirror.
axiom-authority-selftest:
	@sh plugin/axiom-authority-selftest.sh

# Shared gate for the VERIFIED printer: compile the digits -> GoAst -> GoPrint source set STANDALONE (Stdlib only, no plugin
# — sidesteps the build circularity, since the plugin links printer.ml extracted FROM GoPrint.v) and assert
# ZERO axioms. Leaves the freshly-extracted printer.ml in the CWD for the caller. Recursively-expanded (=) so
# each user inlines it into a single recipe line.
GOPRINT_GATE = { rocq c -Q . Fido digits.v > /tmp/printer.log 2>&1 && rocq c -Q . Fido GoAst.v >> /tmp/printer.log 2>&1 && rocq c -Q . Fido GoPrint.v >> /tmp/printer.log 2>&1; } || { echo "fido: digits.v/GoAst.v/GoPrint.v failed to compile:"; cat /tmp/printer.log; exit 1; }; \
	if grep -q '^Axioms:' /tmp/printer.log; then \
	  echo "fido: VERIFIED-PRINTER AXIOM/ADMITTED — a GoAst/GoPrint theorem depends on an axiom (Print Assumptions):"; \
	  cat /tmp/printer.log; rm -f digits.vo digits.glob .digits.aux GoAst.vo GoAst.glob .GoAst.aux GoPrint.vo GoPrint.glob .GoPrint.aux printer.ml; exit 1; \
	fi
GOPRINT_CLEAN = rm -f digits.vo digits.glob .digits.aux GoAst.vo GoAst.glob .GoAst.aux GoPrint.vo GoPrint.glob .GoPrint.aux printer.ml

# Gate for the BLESSED-EMISSION spine: compile GoAst/GoPrint/GoTypes/GoSafe/GoEmit standalone (dependency
# order) and assert ZERO axioms across the whole trust base. Separate from GOPRINT_GATE (printer.ml-only).
GOEMIT_GATE = { rocq c -Q . Fido digits.v > /tmp/emit.log 2>&1 && rocq c -Q . Fido GoAst.v >> /tmp/emit.log 2>&1 && rocq c -Q . Fido GoPrint.v >> /tmp/emit.log 2>&1 && rocq c -Q . Fido GoTypes.v >> /tmp/emit.log 2>&1 && rocq c -Q . Fido GoSafe.v >> /tmp/emit.log 2>&1 && rocq c -Q . Fido GoEmit.v >> /tmp/emit.log 2>&1; } || { echo "fido: digits/GoAst/GoPrint/GoTypes/GoSafe/GoEmit failed to compile:"; cat /tmp/emit.log; exit 1; }; \
	if grep -q '^Axioms:' /tmp/emit.log; then \
	  echo "fido: SPINE AXIOM/ADMITTED — a GoAst/GoPrint/GoTypes/GoSafe/GoEmit theorem depends on an axiom (Print Assumptions):"; \
	  cat /tmp/emit.log; exit 1; \
	fi
GOEMIT_CLEAN = rm -f digits.vo digits.glob .digits.aux GoAst.vo GoAst.glob .GoAst.aux GoPrint.vo GoPrint.glob .GoPrint.aux GoTypes.vo GoTypes.glob .GoTypes.aux GoSafe.vo GoSafe.glob .GoSafe.aux GoEmit.vo GoEmit.glob .GoEmit.aux printer.ml

# Regenerate the VERIFIED printer's OCaml (plugin/printer.ml) from the digits/GoAst/GoPrint source set.  A PROPER file
# dependency: remade only when digits.v / GoAst.v / GoPrint.v is newer.  The recipe runs the shared gate (compile +
# zero-axiom) then moves the fresh extraction into place.  Commit plugin/printer.ml afterwards (a GENERATED
# file, like the *.go); `make check` (Docker) re-derives it and FAILS on drift.
plugin/printer.ml: digits.v GoAst.v GoPrint.v
	@set -e; $(GOPRINT_GATE); \
	  mv -f printer.ml plugin/printer.ml; rm -f digits.vo digits.glob .digits.aux GoAst.vo GoAst.glob .GoAst.aux GoPrint.vo GoPrint.glob .GoPrint.aux; \
	  echo "fido: regenerated plugin/printer.ml from GoAst/GoPrint — zero axioms ✓ (commit it, like *.go)"
printer: plugin/printer.ml

# Read-only LOCAL mirror of the Docker prover-stage printer gate: compile the digits/GoAst/GoPrint source set, assert ZERO
# axioms, and assert the committed plugin/printer.ml is EXACTLY GoPrint.v's extraction (drift = the PROVED
# printer differs from the EXECUTED one).  Modifies nothing — run after editing GoAst.v/GoPrint.v / before
# committing, for a fast check without the full Docker `make check` (digits.v included in the scanned log).
printer-verify:
	@set -e; $(GOPRINT_GATE); \
	  if ! diff plugin/printer.ml printer.ml > /dev/null; then \
	    echo "fido: PRINTER DRIFT — committed plugin/printer.ml != GoPrint.v's extraction; run 'make printer' and commit it."; \
	    $(GOPRINT_CLEAN); exit 1; \
	  fi; \
	  $(GOPRINT_CLEAN); echo "fido: GoAst/GoPrint OK — zero axioms, plugin/printer.ml in sync ✓"

# Read-only LOCAL mirror of the Docker prover-stage EMISSION-spine gate: compile digits/GoAst/GoPrint/GoTypes/GoSafe/GoEmit
# standalone and assert ZERO axioms across the whole blessed-emission trust base (printer + supportedness gate
# + certified emitter).  Modifies nothing.
emit-verify:
	@set -e; $(GOEMIT_GATE); $(GOEMIT_CLEAN); \
	  echo "fido: GoAst/GoPrint/GoSafe/GoEmit OK — zero axioms (blessed-emission trust base) ✓"

# emit-demo: the end-to-end certified-emission check. GOEMIT_GATE (zero-axiom spine) → extract
# GoEmit.demo_emit (bytes pinned by demo_emit_bytes) → write emitdemo/spine_demo.go → assert the real Go
# toolchain ACCEPTS it (gofmt-clean + go build + go vet). spine_demo.go is generated on demand (gitignored).
# A dependency of `make check`, so the blessed path runs on every verify. (main.go is still the legacy path.)
EMITDEMO_CLEAN =rm -f emitdemo/emit_demo.vo emitdemo/emit_demo.glob emitdemo/.emit_demo.aux emitdemo/emit_demo.ml emitdemo/emit_demo.mli emitdemo/*.cmi emitdemo/*.cmo _emit_writer
emit-demo:
	@set -e; $(GOEMIT_GATE); \
	  rocq c -Q . Fido emitdemo/emit_demo.v > /dev/null 2>&1; \
	  ocamlfind ocamlc -I emitdemo emitdemo/emit_demo.mli emitdemo/emit_demo.ml emitdemo/write_emit.ml -o _emit_writer > /dev/null; \
	  ./_emit_writer; \
	  docker run --rm -v "$$(pwd)":/w -w /w $(GOIMAGE) \
	    sh -c 'test -z "$$(gofmt -l emitdemo/spine_demo.go)" && go build -o /dev/null emitdemo/spine_demo.go && go vet emitdemo/spine_demo.go' \
	    || { echo "fido: emit-demo — Go toolchain REJECTED the certified output (gofmt/build/vet)"; $(GOEMIT_CLEAN); $(EMITDEMO_CLEAN); exit 1; }; \
	  $(GOEMIT_CLEAN); $(EMITDEMO_CLEAN); \
	  echo "fido: emit-demo OK — GoEmit.demo_emit (zero-axiom spine) -> emitdemo/spine_demo.go, Go toolchain BUILDS it (gofmt-clean + go build + go vet) ✓"

# Run the freshly-extracted program (Dockerised). DEPENDS ON [extract] so it can never use stale Go; this
# (or [check]) is the only sanctioned way to run the program — a bare `go run` bypasses extraction.
run-extracted: extract
	@$(GORUN)

# Run the image built for the native platform.
run: build
	docker run --rm --platform $(PLATFORM) $(IMAGE):$(TAG)

# Golden-file regression check: extract, run, diff vs expected_output.txt (cheap end-to-end check that a
# Rocq/plugin change altered no observable behaviour). DEPENDS ON [extract] (never stale Go) and [emit-demo]
# (the certified-emission path is exercised on every verify, not just ad-hoc). go vet gates it.
check: toolchain-gate toolchain-selftest go-verify-selftest extract emit-demo
	@echo "fido: go vet (suspicious-but-compiling constructs)..."; \
	if ! $(GOVET); then \
	  echo "fido: GO VET FAILED — the emitted Go has a vet diagnostic (a real defect even though it compiles); fix the plugin/.v, not the Go."; \
	  exit 1; \
	fi
	@# SELECTOR-BRIDGE fixture (regression gate): EXTRACT the generated Embed_arith function and require it
	@# EXACTLY (byte-for-byte, fixture-scoped — NOT a substring grep).  A bridge re-broadening (d.Animal.Legs), a
	@# pp_expr peel_embedded regression ((d.Animal).Legs), or any other body edit changes this block — a
	@# SOURCE-byte regression the runtime golden can't see (same value either way).
	@expected=$$(printf 'func (d Dog) Embed_arith(k int64) int64 {\n\treturn d.Legs + k\n}'); \
	actual=$$(awk '/^func \(d Dog\) Embed_arith\(/{f=1} f{print} f&&/^}/{exit}' main.go); \
	if [ "$$actual" != "$$expected" ]; then \
	  echo "fido: SELECTOR-BRIDGE FIXTURE FAILED — the generated Embed_arith is not the exact peeled block (ESel bridge / pp_expr peel_embedded regressed onto the embedded receiver):"; \
	  printf 'expected:\n%s\nactual:\n%s\n' "$$expected" "$$actual"; \
	  exit 1; \
	fi; \
	echo "fido: selector-bridge fixture OK — Embed_arith matches the exact peeled block 'return d.Legs + k' ✓"
	@set +e; $(GORUN) > /tmp/fido_out.txt 2>&1; rc=$$?; set -e; \
	if [ $$rc -ne 0 ]; then \
	  echo "fido: PROGRAM EXITED NON-ZERO (status $$rc) — an uncaught panic / crash, NOT a benign diff:"; \
	  echo ""; cat /tmp/fido_out.txt; \
	  echo ""; echo "fido: a faithful Fido program runs to completion (exit 0)."; \
	  exit 1; \
	fi; \
	if diff -u expected_output.txt /tmp/fido_out.txt; then \
	  echo "fido: output matches golden ✓"; \
	else \
	  echo ""; echo "fido: OUTPUT DIFFERS from golden (above)."; \
	  echo "fido: if the change is intended, run 'make golden' to update."; \
	  exit 1; \
	fi

# Regenerate the golden baseline after an intended behaviour change.  Depends on
# [extract] so the baseline is captured from freshly-extracted Go, never stale, AND
# SHOWS THE DELTA it is about to bless (old golden → new output) before overwriting —
# so blessing can never happen blind: the diff check is part of the bless, not a manual
# step done beside it.  Review the printed delta; if it is more than you intended, your
# change had an unexpected effect somewhere.
golden: extract
	@echo "fido: go vet (gate before bless)..."; \
	if ! $(GOVET); then \
	  echo "fido: REFUSING TO BLESS — go vet reports a diagnostic on the emitted Go; fix it first."; \
	  exit 1; \
	fi
	@set +e; $(GORUN) > /tmp/fido_new.txt 2>&1; rc=$$?; set -e; \
	if [ $$rc -ne 0 ]; then \
	  echo "fido: REFUSING TO BLESS — program EXITED NON-ZERO (status $$rc), an uncaught panic / crash:"; \
	  echo ""; cat /tmp/fido_new.txt; \
	  echo ""; echo "fido: fix the crash before re-blessing (a faithful Fido program exits 0)."; \
	  exit 1; \
	fi; \
	echo "fido: golden delta (committed → new), review before blessing:"; \
	diff -u expected_output.txt /tmp/fido_new.txt || true; \
	cp /tmp/fido_new.txt expected_output.txt; \
	echo "fido: updated expected_output.txt"

# Proof-error DIAGNOSIS: rebuild the PROVER stage (the same stage `make check` runs) and stream its
# full PLAIN log — for reading a failing proof's error / idtac output (the plain progress is encoded
# here, not left to terminal defaults). Changes nothing locally; pipe/grep the output as needed.
# THE sanctioned spelling of this loop (no ad-hoc docker invocations).
prover-log:
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) --build-arg GOIMAGE=$(GOIMAGE) --progress=plain --target prover .

# gc GROUND-TRUTHING: run a scratch Go program under $(GOIMAGE) (the digest-pinned toolchain) to
# verify Go's ACTUAL semantics before modelling them (witness values, panic payloads — the
# go-run-verified pins). FAIL-CLOSED: GO must be set to an EXISTING directory containing main.go —
# checked BEFORE docker, and mounted READONLY via --mount (which, unlike -v, refuses a missing
# source instead of creating it). println writes to stderr → captured.
go-verify:
	@test -n "$(GO)" || { echo "fido: go-verify needs GO=<dir containing ONLY main.go>"; exit 1; }
	@test -f "$(abspath $(GO))/main.go" || { echo "fido: go-verify — no main.go in '$(GO)' (missing/typo'd dir; nothing created)"; exit 1; }
	@extra=$$(find "$(abspath $(GO))" -maxdepth 1 -name '*.go' ! -name main.go); \
	test -z "$$extra" || { echo "fido: go-verify — main.go must be the ONLY .go file (file-mode run would silently IGNORE siblings):"; echo "$$extra"; exit 1; }
	docker run --rm --mount type=bind,src="$(abspath $(GO))",target=/w,readonly \
	  -w /w -e GOCACHE=/tmp/gocache $(GOIMAGE) sh -c 'go run main.go 2>&1'

# The tooling gates, wired into [check] — each DELEGATES to its plugin/ script, whose header IS
# the single statement of what it enforces/tests (no duplicated lists here).
MKFILE := $(firstword $(MAKEFILE_LIST))
toolchain-gate:
	@sh plugin/toolchain-gate.sh $(MKFILE) '$(GOIMAGE)' Dockerfile
toolchain-selftest:
	@sh plugin/toolchain-selftest.sh '$(MAKE)' $(MKFILE) '$(GOIMAGE)'
go-verify-selftest:
	@sh plugin/go-verify-selftest.sh '$(MAKE)'


# Multi-platform build (does not load locally — use push to ship).
bake:
	docker buildx bake --builder $(BUILDER) --set '*.args.GOIMAGE=$(GOIMAGE)'

# Multi-platform build + push to registry.
push:
	docker buildx bake --builder $(BUILDER) --set '*.args.GOIMAGE=$(GOIMAGE)' --push
