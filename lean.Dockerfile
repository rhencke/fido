# The Lean 4 POC toolchain (lean/README.md).  Separate from the certified Dockerfile on purpose: `make check`
# never consumes this image, and the graph/host-python gates govern the certified graph only.  Pinned the same
# way the certified bases are — the base by digest, the official release tarball by sha256.
FROM debian:bookworm-slim@sha256:5ae3c39ebd15e229dcedd5cee596b2497182493d41ff162e824ba13fc1b2b867 AS lean-fetch
ARG LEAN_VERSION=4.33.1
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates curl zstd && rm -rf /var/lib/apt/lists/*
RUN curl -fsSL -o /tmp/lean.tar.zst \
      "https://github.com/leanprover/lean4/releases/download/v${LEAN_VERSION}/lean-${LEAN_VERSION}-linux.tar.zst" \
    && sha256sum /tmp/lean.tar.zst | tee /tmp/lean.sha256

FROM lean-fetch AS lean-base
# the release tarball's sha256 (v4.33.1, linux x86_64); a mismatch fails the build
ARG LEAN_SHA256=890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235
RUN actual=$(cut -d' ' -f1 /tmp/lean.sha256); echo "fido-lean: tarball sha256 $actual"; \
    [ -n "$LEAN_SHA256" ] || { echo "fido-lean: LEAN_SHA256 is not pinned — set it to the digest above"; exit 1; }; \
    [ "$actual" = "$LEAN_SHA256" ] || { echo "fido-lean: tarball sha256 MISMATCH (expected $LEAN_SHA256)"; exit 1; }
RUN mkdir -p /opt/lean && tar --zstd -xf /tmp/lean.tar.zst -C /opt/lean --strip-components=1 && rm /tmp/lean.tar.zst \
    && /opt/lean/bin/lean --version && /opt/lean/bin/lake --version
ENV PATH=/opt/lean/bin:$PATH
WORKDIR /work
