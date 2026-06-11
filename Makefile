BUILDER  := fido-builder
IMAGE    := fido
TAG      ?= latest
PLATFORM ?= linux/$(shell uname -m | sed 's/x86_64/amd64/;s/aarch64/arm64/')

.PHONY: builder build bake push run extract go-run install-hooks
.DEFAULT_GOAL := build

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

# Run the extracted Go sources directly without Docker.
run-local: extract
	go run .

# Run the image built for the native platform.
run: build
	docker run --rm --platform $(PLATFORM) $(IMAGE):$(TAG)

# Multi-platform build (does not load locally — use push to ship).
bake:
	docker buildx bake --builder $(BUILDER)

# Multi-platform build + push to registry.
push:
	docker buildx bake --builder $(BUILDER) --push
