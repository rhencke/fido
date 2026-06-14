BUILDER  := fido-builder
IMAGE    := fido
TAG      ?= latest
PLATFORM ?= linux/$(shell uname -m | sed 's/x86_64/amd64/;s/aarch64/arm64/')

.PHONY: builder build bake push run extract go-run install-hooks check golden
.DEFAULT_GOAL := build

# Run the extracted program (Go's println writes to stderr → capture 2>&1).
GORUN := docker run --rm -v "$(PWD)":/w -w /w golang:1.23-alpine go run .

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
	rm -f *.go
	docker buildx build --builder $(BUILDER) --platform $(PLATFORM) \
	  --output type=local,dest=. --target go-src .
	# Canonicalise with gofmt: the plugin emits valid Go, but gofmt's operator-
	# spacing heuristic (e.g. tightening `1.5 + 2.25` to `1.5+2.25`) is depth/
	# operand-dependent and not worth replicating in the plugin.  This guarantees
	# the committed Go is gofmt-clean regardless.
	docker run --rm -v "$(PWD)":/w -w /w golang:1.23-alpine gofmt -w *.go

# Run the extracted Go sources directly without Docker.
run-local: extract
	go run .

# Run the image built for the native platform.
run: build
	docker run --rm --platform $(PLATFORM) $(IMAGE):$(TAG)

# Golden-file regression check: run the extracted program and diff its output
# against expected_output.txt.  Cheap end-to-end check that a Rocq/plugin change
# did not alter observable behaviour anywhere (not just the demo in focus).
# Assumes main.go is current (run `make extract` first).
check:
	@$(GORUN) > /tmp/fido_out.txt 2>&1 || true; \
	if diff -u expected_output.txt /tmp/fido_out.txt; then \
	  echo "fido: output matches golden ✓"; \
	else \
	  echo ""; echo "fido: OUTPUT DIFFERS from golden (above)."; \
	  echo "fido: if the change is intended, run 'make golden' to update."; \
	  exit 1; \
	fi

# Regenerate the golden baseline after an intended behaviour change.
golden:
	@$(GORUN) > expected_output.txt 2>&1
	@echo "fido: updated expected_output.txt"

# Multi-platform build (does not load locally — use push to ship).
bake:
	docker buildx bake --builder $(BUILDER)

# Multi-platform build + push to registry.
push:
	docker buildx bake --builder $(BUILDER) --push
