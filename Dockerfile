# syntax=docker/dockerfile:1

# ── Stage 1: build the Rocq/OCaml toolchain ──────────────────────────────────
FROM ocaml/opam:debian-12-ocaml-5.3 AS rocq-builder

RUN --mount=type=cache,id=fido-apt-builder,target=/var/cache/apt,sharing=locked \
    sudo apt-get update \
    && sudo apt-get install -y --no-install-recommends \
        make build-essential pkg-config libgmp-dev linux-libc-dev ca-certificates \
    && sudo rm -rf /var/lib/apt/lists/*

WORKDIR /workspace
COPY --chown=opam:opam rocq-go-extraction.opam dune-project ./

RUN --mount=type=cache,id=fido-opam,uid=1000,gid=1000,target=/home/opam/.opam/download-cache \
    opam repo add rocq-released https://rocq-prover.org/opam/released \
    && for attempt in 1 2 3; do \
         opam install -y rocq-core.9.2.0 rocq-stdlib.9.1.0 dune.3.21.1 && break; \
         echo "attempt $attempt failed — retrying in 20 s..."; sleep 20; \
       done \
    && opam clean --all

# ── Stage 2: minimal Rocq runtime ────────────────────────────────────────────
FROM debian:12-slim AS rocq-base

RUN --mount=type=cache,id=fido-apt-base,target=/var/cache/apt,sharing=locked \
    apt-get update \
    && apt-get install -y --no-install-recommends \
        bash ca-certificates gcc libc6-dev libgmp-dev linux-libc-dev \
        make pkg-config tar \
    && rm -rf /var/lib/apt/lists/* \
       /usr/share/doc/* /usr/share/info/* /usr/share/locale/* /usr/share/man/* \
    && useradd -m -s /bin/bash opam

COPY --from=rocq-builder --chown=opam:opam /home/opam/.opam/5.3 /home/opam/.opam/5.3

ENV OPAM_SWITCH_PREFIX="/home/opam/.opam/5.3"
ENV CAML_LD_LIBRARY_PATH="/home/opam/.opam/5.3/lib/stublibs"
ENV OCAML_TOPLEVEL_PATH="/home/opam/.opam/5.3/lib/toplevel"
ENV OCAMLTOP_INCLUDE_PATH="/home/opam/.opam/5.3/lib/toplevel"
ENV PATH="/home/opam/.opam/5.3/bin:${PATH}"

# Minimal opam shim so `opam exec -- cmd` still works in scripts.
RUN printf '%s\n' \
      '#!/bin/sh' 'set -eu' \
      'if [ "$#" -ge 1 ] && [ "$1" = "exec" ]; then' \
      '  shift; [ "$#" -ge 1 ] && [ "$1" = "--" ] && shift; exec "$@"' \
      'fi' \
      'echo "opam shim: only exec -- supported" >&2; exit 2' \
      > /usr/local/bin/opam \
    && chmod +x /usr/local/bin/opam

RUN mkdir -p /workspace && chown opam:opam /workspace
WORKDIR /workspace
USER opam

# ── Stage 3: prove and extract ────────────────────────────────────────────────
FROM rocq-base AS prover

COPY --chown=opam:opam dune-project dune-project
COPY --chown=opam:opam rocq-go-extraction.opam rocq-go-extraction.opam
COPY --chown=opam:opam plugin/ plugin/
COPY --chown=opam:opam dune  ./
COPY --chown=opam:opam *.v   ./

# The extracted *.go are produced as a SIDE EFFECT of compiling the extraction-driver
# theories (the `Go Main Extraction` vernac); dune does NOT track them as build
# outputs.  So with a warm _build cache dune skips recompiling an unchanged driver and
# never regenerates its *.go — and it has cleaned the stale copy — making `cp` fail (or,
# worse, ship nothing).  Force every extraction driver to recompile so the *.go are
# ALWAYS freshly and reproducibly extracted from the current .v sources, while the
# (heavy) proof libraries stay cached.  Drivers are auto-detected, so adding another
# `Go Main Extraction` theory needs no change here.
RUN --mount=type=cache,id=fido-dune,uid=1000,gid=1000,target=/workspace/_build \
    for v in $(grep -l 'Go Main Extraction' *.v); do rm -f "_build/default/${v%.v}.vo"; done \
    && dune build \
    && test -n "$(ls _build/default/*.go 2>/dev/null)" \
    && cp -r _build/default/*.go /tmp/

# ── Stage 4: export generated Go sources back to the host ────────────────────
FROM scratch AS go-src
COPY --from=prover /tmp/*.go ./

# ── Stage 5: compile extracted Go into a static binary ───────────────────────
FROM golang:1.23-alpine AS builder

WORKDIR /fido
COPY go.mod ./
COPY --from=prover /tmp/*.go ./
RUN CGO_ENABLED=0 go build -o /out/fido .

# ── Stage 5: minimal runtime image ───────────────────────────────────────────
FROM gcr.io/distroless/static:nonroot
COPY --from=builder /out/fido /fido
ENTRYPOINT ["/fido"]
