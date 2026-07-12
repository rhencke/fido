# syntax=docker/dockerfile:1

# Fido under a FOUNDATION RESET (checkpoint 65): the pinned Rocq toolchain compiles the surviving syntax
# layer (digits, GoAst, GoPrint) and asserts GoPrint's declared Print-Assumptions surfaces are axiom-free.
# The false compile/emit AUTHORITY was deleted.  The `e2e-check` stage is a MINIMAL SMOKE TEST — it prints
# ONE known program with [print_program], extracts those (Rocq-checked) bytes, and confirms the pinned Go
# toolchain accepts them.  It is NOT a compiler-soundness or certified-emission claim for arbitrary programs.

# The Go-toolchain image comes ONLY from the Makefile's digest-pinned GOIMAGE (--build-arg by make).
ARG GOIMAGE

# ── Stage 1: Rocq/OCaml toolchain ─────────────────────────────────────────────
FROM ocaml/opam:debian-12-ocaml-5.3@sha256:bbaac53e502f6602013d8967c3a54cfcb898b556f453ab72e8e23966c3c681df AS rocq-builder
RUN --mount=type=cache,id=fido-apt-builder,target=/var/cache/apt,sharing=locked \
    sudo apt-get update \
    && sudo apt-get install -y --no-install-recommends \
        make build-essential pkg-config libgmp-dev linux-libc-dev ca-certificates \
    && sudo rm -rf /var/lib/apt/lists/*
WORKDIR /workspace
# Install the pinned Rocq/Dune; the retry loop must FAIL if every attempt failed (not fall through to clean).
# (rocq/ocamlc presence is verified in the prover stage, where the switch's bin is on PATH via ENV.)
RUN --mount=type=cache,id=fido-opam,uid=1000,gid=1000,target=/home/opam/.opam/download-cache \
    opam repo add rocq-released https://rocq-prover.org/opam/released \
    && installed=false \
    && for attempt in 1 2 3; do \
         if opam install -y rocq-core.9.2.0 rocq-stdlib.9.1.0 dune.3.21.1; then installed=true; break; fi; \
         echo "attempt $attempt failed — retrying in 20 s..."; sleep 20; \
       done \
    && test "$installed" = true \
    && opam clean --all
# (the prover stage — where the opam switch's bin is on PATH via ENV — verifies rocq/ocamlc are present)

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

# ── Stage 3: prove — dune compiles the modules (into the mounted _build cache, so a leaf edit is
#    incremental); then the ASSUMPTIONS GATE (gate/axiom_gate.v — the sole Print-Assumptions target) is
#    compiled fresh EVERY build against the dune-built .vo, so a warm/poisoned cache can never skip it.
#    Fail-closed BOTH ways: zero '^Axioms:' lines AND exactly as many 'Closed under the global context'
#    lines as the gate file has 'Print Assumptions' commands — an empty or partial gate log FAILS.
FROM rocq-base AS prover
ARG TARGETARCH
COPY --chown=opam:opam dune-project dune ./
COPY --chown=opam:opam *.v ./
COPY --chown=opam:opam gate/ gate/
COPY --chown=opam:opam e2e/ e2e/
RUN --mount=type=cache,id=fido-dune-rocq-9.2.0-${TARGETARCH},uid=1000,gid=1000,target=/workspace/_build,sharing=locked \
    if dune build > /tmp/build.log 2>&1; then cat /tmp/build.log; else cat /tmp/build.log; echo "fido: dune build FAILED"; exit 1; fi \
    && rm -f gate/*.vo gate/*.glob gate/.*.aux \
    && if ! rocq c -Q _build/default Fido gate/axiom_gate.v > /tmp/gate.log 2>&1; then \
         cat /tmp/gate.log; echo "fido: ASSUMPTIONS GATE failed to compile"; exit 1; \
       fi \
    && if grep -q '^Axioms:' /tmp/gate.log; then \
         echo "fido: SPINE AXIOM — a gated surface depends on an assumption:"; grep -A3 '^Axioms:' /tmp/gate.log; exit 1; \
       fi \
    && want=$(grep -c '^Print Assumptions' gate/axiom_gate.v) \
    && got=$(grep -c '^Closed under the global context' /tmp/gate.log) \
    && if [ "$want" -ne "$got" ]; then \
         echo "fido: ASSUMPTIONS GATE INCOMPLETE — $want surfaces declared, only $got confirmed closed (a vacuous/partial gate run is a FAILURE)"; exit 1; \
       fi \
    && echo "fido: prover OK — dune compiled the theory (cached in _build); assumptions gate confirmed $got/$want surfaces closed" \
    && rocq c -Q _build/default Fido -Q e2e Fido e2e/e2e.v \
    && printf 'let () = print_string E2e.e2e_bytes\n' > e2e/gen_write.ml \
    && ocamlc -I e2e e2e/e2e.mli e2e/e2e.ml e2e/gen_write.ml -o /tmp/e2e_writer \
    && /tmp/e2e_writer > /tmp/e2e.go \
    && test -s /tmp/e2e.go \
    && echo "fido: e2e — printed one known program via print_program -> /tmp/e2e.go"

# ── Stage 4: e2e smoke test — the pinned Go toolchain ACCEPTS the printed program ─────────────────────────
# gofmt -l is a NO-OP check (the printer is gofmt-stable); then go build + go vet.  This is a last-mile
# integration alarm for ONE known program, NOT a compiler-soundness theorem.
FROM ${GOIMAGE} AS e2e-check
WORKDIR /check
COPY --from=prover /tmp/e2e.go ./
RUN test -z "$(gofmt -l e2e.go)" \
    && go build -o /dev/null e2e.go \
    && go vet e2e.go \
    && echo "fido: e2e-check OK — the pinned Go toolchain accepts the printed program (gofmt-clean + build + vet)"
