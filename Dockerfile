# syntax=docker/dockerfile:1

# The certified pipeline, reproducibly: pinned Rocq builds the spine + proves the bytes, standard extraction
# emits the closed certified output, a build-generated one-line writer prints it to a .go, and the pinned Go
# toolchain accepts it.  NO handwritten OCaml backend; NO custom extraction plugin.

# The Go-toolchain image comes ONLY from the Makefile's digest-pinned GOIMAGE (--build-arg by every make
# target).  DELIBERATELY default-less: a build that bypasses make fails loudly here, not on an unpinned Go.
ARG GOIMAGE

# ── Stage 1: Rocq/OCaml toolchain ─────────────────────────────────────────────
FROM ocaml/opam:debian-12-ocaml-5.3 AS rocq-builder
RUN --mount=type=cache,id=fido-apt-builder,target=/var/cache/apt,sharing=locked \
    sudo apt-get update \
    && sudo apt-get install -y --no-install-recommends \
        make build-essential pkg-config libgmp-dev linux-libc-dev ca-certificates \
    && sudo rm -rf /var/lib/apt/lists/*
WORKDIR /workspace
RUN --mount=type=cache,id=fido-opam,uid=1000,gid=1000,target=/home/opam/.opam/download-cache \
    opam repo add rocq-released https://rocq-prover.org/opam/released \
    && for attempt in 1 2 3; do \
         opam install -y rocq-core.9.2.0 rocq-stdlib.9.1.0 dune.3.21.1 && break; \
         echo "attempt $attempt failed — retrying in 20 s..."; sleep 20; \
       done \
    && opam clean --all

# ── Stage 2: minimal Rocq runtime ─────────────────────────────────────────────
FROM debian:12-slim AS rocq-base
RUN --mount=type=cache,id=fido-apt-base,target=/var/cache/apt,sharing=locked \
    apt-get update \
    && apt-get install -y --no-install-recommends \
        bash ca-certificates gcc libc6-dev libgmp-dev linux-libc-dev make pkg-config tar \
    && rm -rf /var/lib/apt/lists/* \
       /usr/share/doc/* /usr/share/info/* /usr/share/locale/* /usr/share/man/* \
    && useradd -m -s /bin/bash opam
COPY --from=rocq-builder --chown=opam:opam /home/opam/.opam/5.3 /home/opam/.opam/5.3
ENV OPAM_SWITCH_PREFIX="/home/opam/.opam/5.3"
ENV CAML_LD_LIBRARY_PATH="/home/opam/.opam/5.3/lib/stublibs"
ENV OCAML_TOPLEVEL_PATH="/home/opam/.opam/5.3/lib/toplevel"
ENV OCAMLTOP_INCLUDE_PATH="/home/opam/.opam/5.3/lib/toplevel"
ENV PATH="/home/opam/.opam/5.3/bin:${PATH}"
RUN mkdir -p /workspace && chown opam:opam /workspace
WORKDIR /workspace
USER opam

# ── Stage 3: prove the spine + emit the certified bytes ───────────────────────
# spine-gate compiles digits..GoEmit STANDALONE and asserts ZERO axioms (Rocq's own Print Assumptions).
# Then standard extraction turns GoEmit.demo_emit into OCaml, and a build-generated one-line writer prints
# the certified bytes to spine_demo.go.  The writer is generated here, never tracked.
FROM rocq-base AS prover
ARG TARGETARCH
COPY --chown=opam:opam dune-project dune ./
COPY --chown=opam:opam tools/ tools/
COPY --chown=opam:opam *.v ./
COPY --chown=opam:opam emitdemo/ emitdemo/
RUN --mount=type=cache,id=fido-dune-rocq-9.2.0-${TARGETARCH},uid=1000,gid=1000,target=/workspace/_build,sharing=locked \
    sh tools/spine-gate.sh emit /tmp/spine.log \
    && rocq c -Q . Fido emitdemo/emit_demo.v \
    && printf 'let () = print_string Emit_demo.demo_emit\n' > emitdemo/gen_write.ml \
    && ocamlc -I emitdemo emitdemo/emit_demo.mli emitdemo/emit_demo.ml emitdemo/gen_write.ml -o /tmp/emit_writer \
    && /tmp/emit_writer > /tmp/spine_demo.go \
    && test -s /tmp/spine_demo.go

# ── Stage 4: the pinned Go toolchain ACCEPTS the certified bytes ───────────────
# gofmt -l is a NO-OP check (the canonical printer is already gofmt-stable — we never rewrite certified bytes),
# then go build + go vet.
FROM ${GOIMAGE} AS builder
WORKDIR /check
COPY --from=prover /tmp/spine_demo.go ./
RUN test -z "$(gofmt -l spine_demo.go)" \
    && go build -o /dev/null spine_demo.go \
    && go vet spine_demo.go

# ── Stage 5: export the certified .go back to the host (make build) ───────────
FROM scratch AS go-src
COPY --from=builder /check/spine_demo.go ./
