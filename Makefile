BUILDER  := fido-builder
IMAGE    := fido
TAG      ?= latest
PLATFORM ?= linux/$(shell uname -m | sed 's/x86_64/amd64/;s/aarch64/arm64/')

.PHONY: builder build bake push run run-extracted extract go-run install-hooks check golden negtest printer printer-verify emit-verify emit-demo smart-ctor-gate gosem-verify
.DEFAULT_GOAL := build

# Run the extracted program (Go's println writes to stderr → capture 2>&1).
GORUN := docker run --rm -v "$(PWD)":/w -w /w golang:1.23-alpine go run .
# `go vet` gate (review #4 R10): `go run` already BUILDS the emitted Go (so a type error
# anywhere fails), but vet catches suspicious-but-COMPILING constructs (bad printf verbs,
# unreachable code, lost cancels, self-assignment, …) that a plugin bug could emit silently.
# The no-import `package main` vets offline.  Wired into [check] and [golden] below.
GOVET := docker run --rm -v "$(PWD)":/w -w /w golang:1.23-alpine go vet .

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
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) --load -t $(IMAGE):$(TAG) .

# Extract generated Go sources from the prover stage into the repo.
# Wipes all *.go files first so renamed/deleted theories don't leave strays.
extract:
	rm -f *.go *.go.raw
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) \
	  --output type=local,dest=. --target go-src .
	# Canonicalise with gofmt: the plugin emits valid Go, but gofmt's operator-
	# spacing heuristic (e.g. tightening `1.5 + 2.25` to `1.5+2.25`) is depth/
	# operand-dependent and not worth replicating in the plugin.  This guarantees
	# the committed Go is gofmt-clean regardless.
	#
	# ⚠️ HONEST STATUS (review #9): gofmt is a TRUSTED post-step / normaliser — it runs OUTSIDE the verified
	# printer-proof claim.  The check below is a COARSE safety net, NOT a real tokenizer: it strips ALL
	# whitespace ([tr -d]) from the plugin's raw output and from gofmt's, and asserts the rest is byte-equal —
	# so it CATCHES gofmt altering any non-whitespace byte, but it is whitespace-stripping, NOT token-stream
	# preservation (it cannot reason about token boundaries or string/comment interiors).  Do NOT read it as a
	# proof that the verified printer's tokens reach the file unchanged.
	# ★RUTHLESS FOLLOW-ON (tracked): make the verified printer emit gofmt-CLEAN text and run gofmt as a CHECK
	# ONLY ([gofmt -l] → fail if it would rewrite), removing gofmt from the trusted path entirely.
	for f in *.go; do cp "$$f" "$$f.raw"; done
	docker run --rm -v "$(PWD)":/w -w /w golang:1.23-alpine gofmt -w *.go
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

# Fail-closed regression harness (review #4 R10 — the negative-fixture gate). Compiles each
# negative fixture in negtests/ and asserts it ABORTS extraction with its declared
# `(* EXPECT: … *)` message. A reopened fail-closed site (the plugin emitting plausible-but-
# wrong Go where rule 2 demands a loud `unsupported`) is exactly the defect class the
# happy-path golden CANNOT see — run this after any plugin change. Local (host rocq, like
# run-local); the canonical Docker build is unaffected (negtests/ is outside the Fido theory).
negtest:
	dune build
	@sh negtests/run.sh

# Smart-constructor + dead-architecture gate (reviews #4, #9, checklist): (1) ban the DIRECT proof-carrying
# Printer constructors [GTNamed]/[EId] outside the smart-constructor block (their erased Rocq proof
# makes a direct call a trust hole); (2) RECURRENCE GUARD — fail if any torn-down SRaw-overlay name
# (SRaw/raw_ok/build_atom/build_goexpr/Printer.print_expr/…, plus the retired pre-split printer-file and
# printer-module names) reappears in active code (*.v + go.ml), so cleanups can't silently regress.  Static; runs
# here, in the pre-commit hook, and NON-bypassably in the Docker prover stage (so `make check` enforces it).
smart-ctor-gate:
	@sh plugin/smart-ctor-gate.sh

# Shared gate for the VERIFIED printer: compile the GoAst -> GoPrint spine STANDALONE (Stdlib only, no plugin
# — sidesteps the build circularity, since the plugin LINKS printer.ml which is extracted FROM GoPrint.v) and
# assert its Print-Assumptions show ZERO axioms (GoAst/GoPrint are part of the trust base, not just
# main_effect).  GoPrint.v `From Fido Require Import GoAst`, so both compile under `-Q . Fido`.  On success it
# leaves the freshly-extracted printer.ml + build artifacts in the CWD for the caller to use.  Recursively-
# expanded (=) so each user inlines it into a SINGLE recipe line (one shell, `set -e` honoured).
GOPRINT_GATE = { rocq c -Q . Fido GoAst.v > /tmp/printer.log 2>&1 && rocq c -Q . Fido GoPrint.v >> /tmp/printer.log 2>&1; } || { echo "fido: GoAst.v/GoPrint.v failed to compile:"; cat /tmp/printer.log; exit 1; }; \
	if grep -q '^Axioms:' /tmp/printer.log; then \
	  echo "fido: VERIFIED-PRINTER AXIOM/ADMITTED — a GoAst/GoPrint theorem depends on an axiom (Print Assumptions):"; \
	  cat /tmp/printer.log; rm -f GoAst.vo GoAst.glob .GoAst.aux GoPrint.vo GoPrint.glob .GoPrint.aux printer.ml; exit 1; \
	fi
GOPRINT_CLEAN = rm -f GoAst.vo GoAst.glob .GoAst.aux GoPrint.vo GoPrint.glob .GoPrint.aux printer.ml

# Gate for the BLESSED-EMISSION spine: GoSafe + GoEmit are now ALSO part of the trust base (emit_supported is
# the official gate; SupportedProgram is the certificate), so compile the WHOLE spine standalone and assert
# ZERO axioms across all four.  Separate from GOPRINT_GATE (which the printer.ml extraction reuses and must
# stay GoAst/GoPrint-only).  Compiles in dependency order; GoPrint re-emits printer.ml as a side effect (the
# clean step removes it).
GOEMIT_GATE = { rocq c -Q . Fido GoAst.v > /tmp/emit.log 2>&1 && rocq c -Q . Fido GoPrint.v >> /tmp/emit.log 2>&1 && rocq c -Q . Fido GoSafe.v >> /tmp/emit.log 2>&1 && rocq c -Q . Fido GoEmit.v >> /tmp/emit.log 2>&1; } || { echo "fido: GoAst/GoPrint/GoSafe/GoEmit failed to compile:"; cat /tmp/emit.log; exit 1; }; \
	if grep -q '^Axioms:' /tmp/emit.log; then \
	  echo "fido: SPINE AXIOM/ADMITTED — a GoAst/GoPrint/GoSafe/GoEmit theorem depends on an axiom (Print Assumptions):"; \
	  cat /tmp/emit.log; exit 1; \
	fi
GOEMIT_CLEAN = rm -f GoAst.vo GoAst.glob .GoAst.aux GoPrint.vo GoPrint.glob .GoPrint.aux GoSafe.vo GoSafe.glob .GoSafe.aux GoEmit.vo GoEmit.glob .GoEmit.aux printer.ml

# Regenerate the VERIFIED printer's OCaml (plugin/printer.ml) from the GoAst/GoPrint spine.  A PROPER file
# dependency: remade only when GoAst.v / GoPrint.v is newer.  The recipe runs the shared gate (compile +
# zero-axiom) then moves the fresh extraction into place.  Commit plugin/printer.ml afterwards (a GENERATED
# file, like the *.go); `make check` (Docker) re-derives it and FAILS on drift.
plugin/printer.ml: GoAst.v GoPrint.v
	@set -e; $(GOPRINT_GATE); \
	  mv -f printer.ml plugin/printer.ml; rm -f GoAst.vo GoAst.glob .GoAst.aux GoPrint.vo GoPrint.glob .GoPrint.aux; \
	  echo "fido: regenerated plugin/printer.ml from GoAst/GoPrint — zero axioms ✓ (commit it, like *.go)"
printer: plugin/printer.ml

# Read-only LOCAL mirror of the Docker prover-stage printer gate: compile the GoAst/GoPrint spine, assert ZERO
# axioms, and assert the committed plugin/printer.ml is EXACTLY GoPrint.v's extraction (drift = the PROVED
# printer differs from the EXECUTED one).  Modifies nothing — run after editing GoAst.v/GoPrint.v / before
# committing, for a fast check without the full Docker `make check`.
printer-verify:
	@set -e; $(GOPRINT_GATE); \
	  if ! diff plugin/printer.ml printer.ml > /dev/null; then \
	    echo "fido: PRINTER DRIFT — committed plugin/printer.ml != GoPrint.v's extraction; run 'make printer' and commit it."; \
	    $(GOPRINT_CLEAN); exit 1; \
	  fi; \
	  $(GOPRINT_CLEAN); echo "fido: GoAst/GoPrint OK — zero axioms, plugin/printer.ml in sync ✓"

# Read-only LOCAL mirror of the Docker prover-stage EMISSION-spine gate: compile GoAst/GoPrint/GoSafe/GoEmit
# standalone and assert ZERO axioms across the whole blessed-emission trust base (printer + supportedness gate
# + certified emitter).  Modifies nothing.
emit-verify:
	@set -e; $(GOEMIT_GATE); $(GOEMIT_CLEAN); \
	  echo "fido: GoAst/GoPrint/GoSafe/GoEmit OK — zero axioms (blessed-emission trust base) ✓"

# Local convenience gate for the FIRST behavioral-semantics slice (GoSem.v): force a fresh recompile of
# GoSem.vo and assert its `Print Assumptions gosem_demo_output` shows ZERO axioms (no `^Axioms:` line —
# zero-axiom prints "Closed under the global context").  Unlike printer-verify / emit-verify (which compile a
# plugin-FREE Stdlib-only spine with bare `rocq c`), GoSem bridges builtins/cmd and so NEEDS the plugin loaded
# — hence it goes through `dune build` (which builds the plugin + deps) rather than a standalone `rocq c`.
# `--root .` pins the project root to the current dir (robust whether run from the canonical checkout or a
# nested git worktree).  The CANONICAL, non-bypassable gate is still the Docker prover stage: `make check`
# compiles GoSem (it is in the dune `(modules …)`) and the axiom-manifest gate FAILS the build on ANY axiom
# GoSem's `Print Assumptions` would surface.  This target is the fast local mirror.
gosem-verify:
	@set -e; rm -f _build/default/GoSem.vo; \
	  dune build --root . GoSem.vo > /tmp/gosem.log 2>&1 || { echo "fido: GoSem.v failed to compile:"; cat /tmp/gosem.log; exit 1; }; \
	  if grep -q '^Axioms:' /tmp/gosem.log; then \
	    echo "fido: GoSem AXIOM/ADMITTED — a GoSem theorem depends on an axiom (Print Assumptions):"; \
	    cat /tmp/gosem.log; exit 1; \
	  fi; \
	  echo "fido: GoSem.v OK — compiles, zero axioms (first behavioral-semantics slice) ✓"

# emit-demo: the certified emitter ACTUALLY produces a Go FILE that the Go COMPILER builds (review RED item —
# "GoEmit is not yet the actual file-emission path").  Steps: (1) GOEMIT_GATE — compile GoAst/GoPrint/GoSafe/
# GoEmit standalone and assert ZERO axioms, so "certified" is backed (demo_emit's whole trust base is
# axiom-free); (2) extract GoEmit.demo_emit (exact bytes machine-checked by GoEmit.demo_emit_bytes) to OCaml
# (native string) via emitdemo/emit_demo.v; (3) write emitdemo/spine_demo.go with emitdemo/write_emit.ml;
# (4) assert the real Go toolchain ACCEPTS it — gofmt-clean AND `go build` (a real COMPILE) AND `go vet`.
# That is the end-to-end check connecting the zero-axiom proven bytes to the Go compiler.  spine_demo.go is
# GENERATED on demand (gitignored; bytes already pinned by demo_emit_bytes), so nothing can go stale.  Host
# rocq + ocaml (like printer-verify); Docker go (like the golden gofmt step).  WIRED INTO `make check` (it is a
# dependency of `check` below), so the blessed-path demo runs in the normal verification loop.  (The legacy
# plugin still separately produces main.go; this demo is the certificate-gated path.)
EMITDEMO_CLEAN = rm -f emitdemo/emit_demo.vo emitdemo/emit_demo.glob emitdemo/.emit_demo.aux emitdemo/emit_demo.ml emitdemo/emit_demo.mli emitdemo/*.cmi emitdemo/*.cmo _emit_writer
emit-demo:
	@set -e; $(GOEMIT_GATE); \
	  rocq c -Q . Fido emitdemo/emit_demo.v > /dev/null 2>&1; \
	  ocamlfind ocamlc -I emitdemo emitdemo/emit_demo.mli emitdemo/emit_demo.ml emitdemo/write_emit.ml -o _emit_writer > /dev/null; \
	  ./_emit_writer; \
	  docker run --rm -v "$$(pwd)":/w -w /w golang:1.23-alpine \
	    sh -c 'test -z "$$(gofmt -l emitdemo/spine_demo.go)" && go build -o /dev/null emitdemo/spine_demo.go && go vet emitdemo/spine_demo.go' \
	    || { echo "fido: emit-demo — Go toolchain REJECTED the certified output (gofmt/build/vet)"; $(GOEMIT_CLEAN); $(EMITDEMO_CLEAN); exit 1; }; \
	  $(GOEMIT_CLEAN); $(EMITDEMO_CLEAN); \
	  echo "fido: emit-demo OK — GoEmit.demo_emit (zero-axiom spine) -> emitdemo/spine_demo.go, Go toolchain BUILDS it (gofmt-clean + go build + go vet) ✓"

# Run the freshly-extracted program (Dockerised; the env may lack a host Go).  DEPENDS
# ON [extract] exactly like [check]/[golden], so an ad-hoc "what does it print?" run can
# NEVER use stale Go.  This (or [check]) is the ONLY sanctioned way to run the program —
# a bare `go run` / `docker run … go run` bypasses extraction and is forbidden.  For
# VERIFYING a change, prefer [check] (runs AND diffs against the golden); use this only
# when you want the raw output with no diff.
run-extracted: extract
	@$(GORUN)

# Run the image built for the native platform.
run: build
	docker run --rm --platform $(PLATFORM) $(IMAGE):$(TAG)

# Golden-file regression check: run the extracted program and diff its output
# against expected_output.txt.  Cheap end-to-end check that a Rocq/plugin change
# did not alter observable behaviour anywhere (not just the demo in focus).
# DEPENDS ON [extract]: a stale main.go must be IMPOSSIBLE here — checking
# against Go that does not reflect current *.v/plugin source would be a false
# green.  [extract] re-runs the prover (Docker layers cached if unchanged), so
# this always validates freshly-extracted Go (and fails loud if a proof broke).
# ALSO DEPENDS ON [emit-demo] (external review 2026-06-29): the certified-emission
# bridge is no longer optional — every `make check` now also asserts the zero-axiom
# GoEmit.demo_emit BUILDS via the real Go toolchain, so the blessed path is exercised
# on the normal verify step, not only on an ad-hoc target.
check: extract emit-demo
	@echo "fido: go vet (suspicious-but-compiling constructs)..."; \
	if ! $(GOVET); then \
	  echo "fido: GO VET FAILED — the emitted Go has a vet diagnostic (a real defect even though it compiles); fix the plugin/.v, not the Go."; \
	  exit 1; \
	fi
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

# Multi-platform build (does not load locally — use push to ship).
bake:
	docker buildx bake --builder $(BUILDER)

# Multi-platform build + push to registry.
push:
	docker buildx bake --builder $(BUILDER) --push
