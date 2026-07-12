# syntax=docker/dockerfile:1

# Fido under a FOUNDATION RESET (checkpoint 65): the pinned Rocq toolchain compiles the surviving syntax
# layer (digits, GoAst, GoPrint) and asserts GoPrint's declared Print-Assumptions surfaces axiom-free.  There is NO emitted Go and NO Go toolchain this
# round — the false compile/emit authority was deleted (a smaller root-only repo beats a green demo on a
# false compile certificate).  The Go stage returns only when a proof-backed typed emission path exists.

# ── Stage 1: Rocq/OCaml toolchain ─────────────────────────────────────────────
FROM ocaml/opam:debian-12-ocaml-5.3@sha256:bbaac53e502f6602013d8967c3a54cfcb898b556f453ab72e8e23966c3c681df AS rocq-builder
RUN --mount=type=cache,id=fido-apt-builder,target=/var/cache/apt,sharing=locked \
    sudo apt-get update \
    && sudo apt-get install -y --no-install-recommends \
        make build-essential pkg-config libgmp-dev linux-libc-dev ca-certificates \
    && sudo rm -rf /var/lib/apt/lists/*
WORKDIR /workspace
# Install the pinned Rocq/Dune; the retry loop must FAIL if every attempt failed (not fall through to clean),
# and we verify the executables are actually present.
RUN --mount=type=cache,id=fido-opam,uid=1000,gid=1000,target=/home/opam/.opam/download-cache \
    opam repo add rocq-released https://rocq-prover.org/opam/released \
    && installed=false \
    && for attempt in 1 2 3; do \
         if opam install -y rocq-core.9.2.0 rocq-stdlib.9.1.0 dune.3.21.1; then installed=true; break; fi; \
         echo "attempt $attempt failed — retrying in 20 s..."; sleep 20; \
       done \
    && test "$installed" = true \
    && command -v rocq && command -v ocamlc \
    && opam clean --all

# ── Stage 2: minimal Rocq runtime ─────────────────────────────────────────────
FROM debian:12-slim@sha256:60eac759739651111db372c07be67863818726f754804b8707c90979bda511df AS rocq-base
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
ENV PATH="/home/opam/.opam/5.3/bin:${PATH}"
RUN mkdir -p /workspace && chown opam:opam /workspace
WORKDIR /workspace
USER opam

# ── Stage 3: prove — compile the surviving modules, assert GoPrint's declared Print-Assumptions surfaces axiom-free ────────
FROM rocq-base AS prover
ARG TARGETARCH
COPY --chown=opam:opam dune-project dune ./
COPY --chown=opam:opam tools/ tools/
COPY --chown=opam:opam *.v ./
RUN --mount=type=cache,id=fido-dune-rocq-9.2.0-${TARGETARCH},uid=1000,gid=1000,target=/workspace/_build,sharing=locked \
    command -v rocq && command -v ocamlc \
    && sh tools/spine-gate.sh printer /tmp/spine.log
