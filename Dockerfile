# syntax=docker/dockerfile:1

# Fido — GoProgram (nonempty finite map of intrinsic FilePath keys to raw file ASTs) -> GoCompile
# (whole-program, +CompilationFacts) -> GoSafe -> GoRender -> abstract DirectoryImage, then the general
# `Fido Emit` transport command + a dirty-directory filesystem sink + the pinned Go toolchain.  Stages:
# (prover) dune-compiles the theory and the always-run assumptions gate confirms every declared surface
# axiom-free; (emit) dune compiles theory+plugin (shared cache), then explicitly runs `Fido Emit` (rocq c
# on the witness) to synchronize the whole tree, and exercises the sink on dirty/adversarial trees;
# (go-e2e) the pinned Go toolchain runs `go build ./...` over the whole tree and runs the witness vs goldens.

# ── Stage 1: Rocq/OCaml toolchain ─────────────────────────────────────────────
FROM ocaml/opam:debian-12-ocaml-5.3@sha256:bbaac53e502f6602013d8967c3a54cfcb898b556f453ab72e8e23966c3c681df AS rocq-builder
RUN --mount=type=cache,id=fido-apt-builder,target=/var/cache/apt,sharing=locked \
    sudo apt-get update \
    && sudo apt-get install -y --no-install-recommends \
        make build-essential pkg-config libgmp-dev linux-libc-dev ca-certificates \
    && sudo rm -rf /var/lib/apt/lists/*
WORKDIR /workspace
# Install the pinned Rocq/Dune; the retry loop must FAIL if every attempt failed (not fall through to clean).
RUN --mount=type=cache,id=fido-opam,uid=1000,gid=1000,target=/home/opam/.opam/download-cache \
    opam repo add rocq-released https://rocq-prover.org/opam/released \
    && installed=false \
    && for attempt in 1 2 3; do \
         if opam install -y rocq-core.9.2.0 rocq-stdlib.9.1.0 dune.3.21.1; then installed=true; break; fi; \
         echo "attempt $attempt failed — retrying in 20 s..."; sleep 20; \
       done \
    && test "$installed" = true \
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

# ── Stage 3: prove — dune compiles the modules; the assumptions gate (gate/axiom_gate.v — the sole
#    Print-Assumptions target) is compiled fresh against the dune-built .vo and is fail-closed both ways:
#    zero '^Axioms:' AND exactly as many 'Closed under the global context' lines as declared surfaces.
FROM rocq-base AS prover
ARG TARGETARCH
COPY --chown=opam:opam dune-project dune ./
COPY --chown=opam:opam *.v ./
COPY --chown=opam:opam gate/ gate/
RUN --mount=type=cache,id=fido-dune-rocq-9.2.0-${TARGETARCH},uid=1000,gid=1000,target=/workspace/_build,sharing=locked \
    if dune build > /tmp/build.log 2>&1; then cat /tmp/build.log; else cat /tmp/build.log; echo "fido: dune build FAILED"; exit 1; fi \
    && rm -f gate/*.vo gate/*.glob gate/.*.aux \
    && if ! rocq c -Q _build/default Fido gate/axiom_gate.v > /tmp/gate.log 2>&1; then \
         cat /tmp/gate.log; echo "fido: ASSUMPTIONS GATE failed to compile"; exit 1; \
       fi \
    && if grep -q '^Axioms:' /tmp/gate.log; then \
         echo "fido: AXIOM — a gated surface depends on an assumption:"; grep -A3 '^Axioms:' /tmp/gate.log; exit 1; \
       fi \
    && want=$(grep -c '^Print Assumptions' gate/axiom_gate.v) \
    && got=$(grep -c '^Closed under the global context' /tmp/gate.log) \
    && if [ "$want" -ne "$got" ]; then \
         echo "fido: ASSUMPTIONS GATE INCOMPLETE — $want surfaces declared, only $got confirmed closed"; exit 1; \
       fi \
    && echo "fido: prove OK — dune compiled the theory (cached in _build); assumptions gate confirmed $got/$want surfaces closed"

# ── Stage 4: emit — Dune compiles the theory AND the Fido Emit transport plugin (one shared cache id
#    with the prover stage).  Then, in EXPLICIT always-run steps (never Dune .vo side effects): the
#    general `Fido Emit` command (rocq c on the witness) decodes a proved DirectoryImage and the sink
#    SYNCHRONIZES the whole tree; and a standalone driver exercises the dirty-directory sink against a
#    dirty tree (marked control dir, stale generated files cleaned, foreign preserved) and ADVERSARIAL
#    foreign entries it must refuse-and-preserve (foreign at target, symlinked root, foreign control
#    dir, foreign stage dir).  The plugin decodes only final (path, bytes) data; it walks no program.
FROM rocq-base AS emit
ARG TARGETARCH
COPY --chown=opam:opam dune-project dune ./
COPY --chown=opam:opam *.v ./
COPY --chown=opam:opam gate/ gate/
COPY --chown=opam:opam plugin/ plugin/
COPY --chown=opam:opam e2e/ e2e/
RUN --mount=type=cache,id=fido-dune-rocq-9.2.0-${TARGETARCH},uid=1000,gid=1000,target=/workspace/_build,sharing=locked <<'SH'
set -eu
fail() { echo "fido: emit FAILED — $*"; exit 1; }
rm -rf /workspace/e2e-out /workspace/adv-*
O=/workspace/e2e-out
# cached: Dune compiles the proved theory + the transport plugin (shared cache id)
if ! dune build @install > /tmp/emit-build.log 2>&1; then cat /tmp/emit-build.log; fail "theory/plugin build FAILED"; fi
export OCAMLPATH=/workspace/_build/install/default/lib:${OCAMLPATH:-}
# always-run (NOT a Dune side effect): the GENERAL Fido Emit command synchronizes the whole tree
if ! rocq c -Q _build/default/. Fido e2e/Witness.v > /tmp/emit.log 2>&1; then cat /tmp/emit.log; fail "Fido Emit FAILED"; fi
cat /tmp/emit.log
[ -f "$O/main.go" ] || fail "the emitted tree has no main.go"
[ -d "$O/.fido" ]   || fail "the emission left no marked control directory"
echo "fido: emitted tree:"; echo ----; ( cd "$O" && find . -type f | sort ); echo ----; cat "$O/main.go"; echo ----
# differential witness: a whole program with TWO main packages (root + sub/) + an empty file
if ! rocq c -Q _build/default/. Fido e2e/WitnessMulti.v > /tmp/emit-multi.log 2>&1; then cat /tmp/emit-multi.log; fail "Fido Emit (multi-package) FAILED"; fi
{ [ -f /workspace/e2e-multi/main.go ] && [ -f /workspace/e2e-multi/extra.go ] && [ -f /workspace/e2e-multi/sub/main.go ]; } || fail "multi-package tree incomplete"
echo "fido: multi-package tree:"; ( cd /workspace/e2e-multi && find . -name '*.go' | sort )
# provenance: a forged raw transport (not a DirectoryImage) is rejected BEFORE any effect (Fail fixtures)
if ! rocq c -Q _build/default/. Fido e2e/WitnessNeg.v > /tmp/emit-neg.log 2>&1; then cat /tmp/emit-neg.log; fail "a forged raw transport was NOT rejected"; fi
[ ! -e /workspace/e2e-neg ] || fail "a rejected Fido Emit still created its target directory"
echo "fido: provenance enforced — forged raw transports rejected before any effect"

# --- SOUND zero-project-axiom audit: enumerate the compiled global env (not a text scanner) ---
if ! rocq c -Q _build/default/. Fido gate/assumptions_audit.v > /tmp/audit.log 2>&1; then cat /tmp/audit.log; fail "assumption audit FAILED"; fi
grep -q 'assumption audit OK' /tmp/audit.log || { cat /tmp/audit.log; fail "audit did not confirm zero Fido axioms"; }
# audit self-test: a planted axiom in a Fido-namespaced module MUST be caught (not fail-open)
mkdir -p /tmp/fa; printf 'Axiom planted_axiom : True.\n' > /tmp/fa/Planted.v
rocq c -R /tmp/fa Fido /tmp/fa/Planted.v > /tmp/fa/plant.log 2>&1 || { cat /tmp/fa/plant.log; fail "could not compile the audit self-test module"; }
printf 'From Fido Require Import Planted.\nDeclare ML Module "fido.emit".\nFido Audit Assumptions.\n' > /tmp/fa/Check.v
if rocq c -R /tmp/fa Fido -Q _build/default/. Fido /tmp/fa/Check.v > /tmp/fa/check.log 2>&1; then fail "the audit did NOT catch a planted Fido axiom (fail-open)"; fi
echo "fido: assumption audit OK — zero Fido axioms; self-test confirms a planted Fido axiom is caught"

# --- exercise the dirty-directory sink directly (the §17 algorithm) ---
cp plugin/fido_sink.ml e2e/sink_test.ml /tmp/
if ! ( cd /tmp && ocamlfind ocamlopt -package unix -linkpkg fido_sink.ml sink_test.ml -o /workspace/sink_test ) > /tmp/sink.log 2>&1; then cat /tmp/sink.log; fail "sink_test compile FAILED"; fi
hdr=$(head -1 "$O/main.go")   # DERIVE the ownership header from actual output (no hardcoded literal)
stages() { find "$1" -name '.fido-stage-*' 2>/dev/null; }
# (1) clean-dir sync produces a marked control dir + main.go; no stage dir leaks after success
mkdir -p /workspace/adv-1; ./sink_test /workspace/adv-1 || fail "clean sync failed"
[ -f /workspace/adv-1/main.go ] && [ -f /workspace/adv-1/.fido/marker ] || fail "no main.go/control marker"
[ -z "$(stages /workspace/adv-1)" ] || fail "a stage dir leaked after a successful sync"
# (2) dirty re-sync: a stale generated .go is cleaned; foreign files/dirs preserved
printf '%s\n\npackage main\n' "$hdr" > /workspace/adv-1/stale.go
printf 'keep me\n' > /workspace/adv-1/keep.txt
mkdir -p /workspace/adv-1/handwritten; printf 'package hand\n' > /workspace/adv-1/handwritten/h.go
./sink_test /workspace/adv-1 || fail "dirty re-sync failed"
[ ! -e /workspace/adv-1/stale.go ] || fail "stale generated .go not cleaned"
[ -f /workspace/adv-1/keep.txt ] || fail "foreign file deleted"
[ -f /workspace/adv-1/handwritten/h.go ] || fail "foreign .go (no header) deleted"
# (3) adversarial refuse-and-preserve; a handled failure leaves no stage dir behind
mkdir -p /workspace/adv-a; printf 'FOREIGN\n' > /workspace/adv-a/main.go
if ./sink_test /workspace/adv-a; then fail "overwrote a foreign main.go"; fi
[ "$(cat /workspace/adv-a/main.go)" = "FOREIGN" ] || fail "a foreign main.go was altered"
[ -z "$(stages /workspace/adv-a)" ] || fail "a stage dir leaked after a handled failure"
mkdir -p /workspace/adv-b-real; printf 'sentinel\n' > /workspace/adv-b-real/keep; ln -s /workspace/adv-b-real /workspace/adv-b
if ./sink_test /workspace/adv-b; then fail "wrote through a symlinked root"; fi
[ ! -e /workspace/adv-b-real/main.go ] && [ "$(cat /workspace/adv-b-real/keep)" = "sentinel" ] || fail "disturbed a symlinked root"
mkdir -p /workspace/adv-c/.fido; printf 'not the marker\n' > /workspace/adv-c/.fido/marker
if ./sink_test /workspace/adv-c; then fail "touched a foreign .fido control dir"; fi
[ "$(cat /workspace/adv-c/.fido/marker)" = "not the marker" ] || fail "altered a foreign control dir"
mkdir -p /workspace/adv-d/.fido-stage-deadbeef/sub; printf 'nested\n' > /workspace/adv-d/.fido-stage-deadbeef/sub/s
./sink_test /workspace/adv-d || fail "a foreign (unmarked) stage dir must be left alone, not abort"
[ "$(cat /workspace/adv-d/.fido-stage-deadbeef/sub/s)" = "nested" ] || fail "removed an unmarked stage lookalike"
echo "fido: emit OK — general Fido Emit synced the tree; sink dirty/adversarial cases all pass"
SH

# ── Stage 5: go-e2e — the LAST-MILE integration check (never a proof).  The pinned Go toolchain builds
#    the COMPLETE emitted tree with `go build ./...` and runs the witness package; stdout/stderr/exit
#    must match the reviewed goldens.  A reviewed handwritten go.mod (the module shell, OUTSIDE the
#    generated map) is added; the sink wrote only generated .go.  gofmt is a NO-OP CHECK.  A Go
#    build/run failure here is a hard red — GoCompile/rendering/transport is wrong, never a known issue.
FROM golang:1.23-alpine@sha256:383395b794dffa5b53012a212365d40c8e37109a626ca30d6151c8348d380b5f AS go-e2e
WORKDIR /e2e
COPY --from=emit /workspace/e2e-out/ ./tree/
COPY --from=emit /workspace/e2e-multi/ ./multi/
COPY e2e/golden.stdout e2e/golden.stderr e2e/golden.exit ./
RUN <<'SH'
set -u
cd tree
echo "fido e2e: emitted tree under test:"; echo ----; find . -name '*.go' | sort | while read f; do echo "== $f =="; cat "$f"; done; echo ----
gv=$(go env GOVERSION); goos=$(go env GOOS); goarch=$(go env GOARCH)
echo "fido e2e: toolchain GOVERSION=$gv GOOS=$goos GOARCH=$goarch (operational pin: go1.23/linux/amd64, a 64-bit target)"
case "$gv" in go1.23*) : ;; *) echo "fido e2e: Go version $gv != pinned go1.23"; exit 1;; esac
[ "$goos" = linux ]  || { echo "fido e2e: GOOS $goos != pinned linux"; exit 1; }
[ "$goarch" = amd64 ] || { echo "fido e2e: GOARCH $goarch != pinned amd64"; exit 1; }
# the reviewed module shell (foreign to the generated map; the sink never writes it)
printf 'module fidoe2e\n\ngo 1.23\n' > go.mod
if [ -n "$(gofmt -l .)" ]; then echo "fido e2e: emitted Go is not gofmt-clean:"; gofmt -l .; exit 1; fi
if ! go vet ./...; then echo "fido e2e: go vet failed on the emitted tree"; exit 1; fi
# the WHOLE tree must compile
if ! go build ./...; then echo "fido e2e: go build ./... FAILED (a certified tree must always compile)"; exit 1; fi
# run the witness (root) package and compare to the reviewed goldens
if ! go build -o prog .; then echo "fido e2e: go build of the witness package FAILED"; exit 1; fi
./prog > out.stdout 2> out.stderr; ec=$?
echo "fido e2e: exit=$ec stdout=[$(cat out.stdout)] stderr=[$(cat out.stderr)]"
printf '%s\n' "$ec" > out.exit
diff ../golden.exit   out.exit   || { echo "fido e2e: EXIT mismatch";   exit 1; }
diff ../golden.stdout out.stdout || { echo "fido e2e: STDOUT mismatch"; exit 1; }
diff ../golden.stderr out.stderr || { echo "fido e2e: STDERR mismatch"; exit 1; }

# --- DIFFERENTIAL: the whole-program directory/package rules must agree with `go build ./...` ---
cd /e2e/multi
printf 'module fidomulti\n\ngo 1.23\n' > go.mod
echo "fido e2e diff: ACCEPTED multi-package tree (root main + sub/ main + empty file):"; find . -name '*.go' | sort
if [ -n "$(gofmt -l .)" ]; then echo "fido e2e diff: multi tree not gofmt-clean"; gofmt -l .; exit 1; fi
go vet ./... || { echo "fido e2e diff: go vet failed on the ACCEPTED multi-package tree"; exit 1; }
go build ./... || { echo "fido e2e diff: go build ./... REJECTED a GoCompile-ACCEPTED multi-package tree (model bug)"; exit 1; }
# DISCOVERY: every emitted-file directory must be a package `go list ./...` actually selects (no file
# certified into a go-ignored directory).  Compare the two directory sets exactly.
emitted_dirs=$(find . -name '*.go' -exec dirname {} \; | sort -u)
listed_dirs=$(go list -f '{{.Dir}}' ./... | sed "s#^$(pwd)#.#; s#^\.\$#.#" | sort -u)
echo "fido e2e diff: emitted dirs=[$(echo $emitted_dirs)] go-list dirs=[$(echo $listed_dirs)]"
[ "$emitted_dirs" = "$listed_dirs" ] || { echo "fido e2e diff: emitted package dirs != go list ./... selection (a file was certified into a go-undiscovered directory)"; exit 1; }
# hand-written REJECTED fixtures: `go build ./...` must reject exactly what GoCompile makes impossible
mkdir -p /tmp/rej-nomain && cd /tmp/rej-nomain && printf 'module rej\n\ngo 1.23\n' > go.mod
printf '// fido generated.  do not edit.\n\npackage main\n' > x.go   # a main package with NO func main
if go build ./... 2>/dev/null; then echo "fido e2e diff: go build accepted a package with no main (GoCompile rejects this)"; exit 1; fi
echo "fido e2e diff: a no-main package is rejected by go build (matches GoCompile: exactly one main per package)"
mkdir -p /tmp/rej-dup && cd /tmp/rej-dup && printf 'module rej\n\ngo 1.23\n' > go.mod
printf '// fido generated.  do not edit.\n\npackage main\n\nfunc main() {}\nfunc main() {}\n' > x.go   # duplicate main
if go build ./... 2>/dev/null; then echo "fido e2e diff: go build accepted duplicate main (GoCompile rejects this)"; exit 1; fi
echo "fido e2e diff: duplicate main is rejected by go build (matches GoCompile)"

echo "fido e2e OK — pinned Go built the whole tree (go build ./...) + the multi-package differential, ran the witness vs goldens, and rejected the no-main/dup-main fixtures exactly as GoCompile does"
SH
