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
COPY --chown=opam:opam EXPECTED_ASSUMPTIONS.txt ./
COPY --chown=opam:opam negtests/ negtests/

# The extracted *.go are produced as a SIDE EFFECT of compiling the extraction-driver
# theories (the `Go Main Extraction` vernac); dune does NOT track them as build outputs.
# In a warm _build cache that breaks BOTH ways, so we counter both:
#  (1) REMOVAL — if a driver .v is deleted/renamed, its stale *.go orphan lingers in the
#      cached _build and would be shipped.  So nuke ALL generated *.go up front; only the
#      drivers that still exist will recreate theirs.
#  (2) STALENESS — dune skips recompiling an unchanged driver, so its *.go is never
#      regenerated.  So force every current driver's .vo out, making it recompile and
#      re-extract afresh.  (Drivers auto-detected; the heavy proof libraries stay cached.)
# Then a `test -n` guard fails LOUD rather than shipping nothing.
#  (3) AXIOM-MANIFEST GATE (review #4 R10): the driver re-compile runs `Print Assumptions
#      main_effect`, emitting the trust base.  Capture it and assert it EXACTLY equals the
#      committed EXPECTED_ASSUMPTIONS.txt (the PrimInt63/PrimFloat substrate).  A NEW axiom
#      reaching the extracted program — a stray `Require` pulling in funext/Classical, an
#      `Admitted` that slipped the grep, etc. — is a trust-base regression (rule 3) and FAILS
#      the build here, not silently in a `Print Assumptions` nobody reads.  (The pre-commit hook
#      greps for DECLARED axioms; this catches TRANSITIVE/imported ones too.)
#  (4) NEGTEST HARNESS (review #4 R10): `negtests/run.sh` compiles each negative fixture and
#      asserts extraction ABORTS with its declared message.  A fixture that EXTRACTS instead =
#      a reopened fail-closed site (plausible-but-wrong Go where rule 2 demands `unsupported`),
#      the defect class the happy-path golden cannot see.  Now NON-bypassable (runs every build).
RUN --mount=type=cache,id=fido-dune,uid=1000,gid=1000,target=/workspace/_build \
    rm -f _build/default/*.go \
    && for v in $(grep -l 'Go Main Extraction' *.v); do rm -f "_build/default/${v%.v}.vo"; done \
    && (dune build > /tmp/build.log 2>&1; rc=$?; cat /tmp/build.log; exit $rc) \
    && awk '/^Axioms:/{f=1;next} /^Extracted to/{f=0} f && /^[A-Za-z_][A-Za-z0-9_.]* :/ {print $1}' /tmp/build.log \
         | LC_ALL=C sort -u > /tmp/got_axioms.txt \
    && if ! diff EXPECTED_ASSUMPTIONS.txt /tmp/got_axioms.txt; then \
         echo "fido: AXIOM-MANIFEST DRIFT ('<' = expected, '>' = actual) — main_effect's trust base changed."; \
         echo "fido: a NEW axiom reaching the extracted program is a trust-base regression (rule 3); if the change is intended, regenerate EXPECTED_ASSUMPTIONS.txt."; \
         exit 1; \
       fi \
    && sh negtests/run.sh \
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
