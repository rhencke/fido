# syntax=docker/dockerfile:1

# Fido build stages — ONE program: GoProgram -> GoTypes -> GoCompile (= the pinned one-shot `go build ./...`
# acceptance) -> GoSafe -> GoRender -> DirectoryImage -> `Fido Materialize` (the SOLE Rocq transport vernac) ->
# pinned Go.  There is NO public `Fido Emit`; the publication SINK is internal (sink_test + the validated
# `make regenerate` apply CLI).
#   prover:  dune-compiles the theory; the always-run gate confirms every declared surface axiom-free.
#   emit:    compiles theory+plugin (shared cache), MATERIALIZES each witness image DIRECTLY into a pristine
#            root, and exercises the sink SEPARATELY on dirty/adversarial trees (sink_test).
#   go-e2e:  the pinned Go toolchain VALIDATES the pristine with `go build ./...` (rendered go.mod) + goldens.
#   sync:    only after that validation marker does `make regenerate` publish the SAME validated bytes via the sink.

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
        bash ca-certificates diffutils gcc libc6-dev libgmp-dev linux-libc-dev make pkg-config tar \
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
COPY --chown=opam:opam plugin/ plugin/
# `make prove` is the COMPLETE proof gate: Dune builds the theory AND the audit/transport plugin; then the
# readable Print-Assumptions surfaces, the certified-module coverage check, the WHOLE-certified-theory
# assumption-closure audit (constants + mutual INDUCTIVES + surviving named assumptions, descending opaque Qed
# bodies, rejecting every Printer.Axiom category AND Printer.Variable), and the adversarial self-tests A-E run
# HERE — so a retained internal declaration depending on an assumption fails even when it is not a public theorem.
RUN --mount=type=cache,id=fido-dune-rocq-9.2.0-${TARGETARCH},uid=1000,gid=1000,target=/workspace/_build,sharing=locked <<'SH'
set -eu
fail() { echo "fido: prove FAILED — $*"; exit 1; }
# (a) Dune builds the certified theory AND the audit/transport plugin (one shared cache id with emit/e2e)
if ! dune build @install @all > /tmp/build.log 2>&1; then cat /tmp/build.log; fail "dune build FAILED"; fi
cat /tmp/build.log
export OCAMLPATH=/workspace/_build/install/default/lib:${OCAMLPATH:-}
# (b) readable Print-Assumptions surfaces, fresh against the dune-built .vo, fail-closed both ways
rm -f gate/*.vo gate/*.glob gate/.*.aux
if ! rocq c -Q _build/default Fido gate/axiom_gate.v > /tmp/gate.log 2>&1; then cat /tmp/gate.log; fail "assumptions gate failed to compile"; fi
if grep -q '^Axioms:' /tmp/gate.log; then grep -A3 '^Axioms:' /tmp/gate.log; fail "a gated surface depends on an assumption"; fi
want=$(grep -c '^Print Assumptions' gate/axiom_gate.v); got=$(grep -c '^Closed under the global context' /tmp/gate.log)
[ "$want" -eq "$got" ] || fail "readable gate incomplete — $want surfaces declared, $got closed"
echo "fido: readable Print-Assumptions gate OK — $got/$want surfaces closed"
# (c) certified-module coverage: tracked root .v == dune (modules ...) (test/gate/e2e .v are outside)
mods=$(sed -n 's/.*(modules \([^)]*\)).*/\1/p' dune); [ -n "$mods" ] || fail "no (modules ...) in dune"
tracked_mods=$(ls *.v | sed 's/\.v$//' | sort | tr '\n' ' ')
declared_mods=$(printf '%s\n' $mods | sort | tr '\n' ' ')
[ "$tracked_mods" = "$declared_mods" ] || fail "certified-module coverage mismatch — tracked=[$tracked_mods] dune=[$declared_mods]"
echo "fido: certified-module coverage OK — tracked root .v == dune (modules ...)"
# (d) the WHOLE-certified-theory assumption audit over constants + inductives + surviving named assumptions
{ printf 'From Fido Require Import %s.\n' "$mods"; printf 'Declare ML Module "fido.emit".\nFido Audit Assumptions.\n'; } > /tmp/audit.v
if ! rocq c -Q _build/default/. Fido /tmp/audit.v > /tmp/audit.log 2>&1; then cat /tmp/audit.log; fail "whole-theory audit FAILED"; fi
grep -q 'assumption audit OK' /tmp/audit.log || { cat /tmp/audit.log; fail "audit did not confirm zero assumptions"; }
echo "fido: whole-certified-theory audit OK — constants + inductives + named ($mods)"
# (e) adversarial self-tests — the audit must REJECT A-D and ACCEPT E (all fixtures transient, none tracked)
reject() { # <dir> <label>: the audit over module in <dir> must fail with the PROJECT AXIOMS reason
  printf 'From Fido Require Import T.\nDeclare ML Module "fido.emit".\nFido Audit Assumptions.\n' > "$1/Check.v"
  if rocq c -R "$1" Fido -Q _build/default/. Fido "$1/Check.v" > "$1/c.log" 2>&1; then cat "$1/c.log"; fail "self-test $2: audit did NOT reject"; fi
  grep -q 'PROJECT AXIOMS' "$1/c.log" || { cat "$1/c.log"; fail "self-test $2: rejected but NOT by the closure audit"; }
  echo "fido: audit self-test $2 — rejected (as required)"; }
compile() { rocq c "$@" || { fail "self-test fixture compile FAILED: $*"; }; }
# A — an UNUSED Fido axiom
mkdir -p /tmp/tA; printf 'Axiom unused_ax : True.\n' > /tmp/tA/T.v
compile -R /tmp/tA Fido /tmp/tA/T.v > /dev/null 2>&1; reject /tmp/tA A
# B — an EXTERNAL axiom reached through a Fido-namespaced OPAQUE (Qed) theorem
mkdir -p /tmp/extB /tmp/tB; printf 'Axiom ext_ax : True.\n' > /tmp/extB/E.v
compile -R /tmp/extB Ext /tmp/extB/E.v > /dev/null 2>&1
printf 'From Ext Require Import E.\nLemma opaque_thm : True. Proof. exact E.ext_ax. Qed.\n' > /tmp/tB/T.v
compile -R /tmp/extB Ext -R /tmp/tB Fido /tmp/tB/T.v > /dev/null 2>&1
printf 'From Fido Require Import T.\nDeclare ML Module "fido.emit".\nFido Audit Assumptions.\n' > /tmp/tB/Check.v
if rocq c -R /tmp/extB Ext -R /tmp/tB Fido -Q _build/default/. Fido /tmp/tB/Check.v > /tmp/tB/c.log 2>&1; then cat /tmp/tB/c.log; fail "self-test B: audit did NOT reject"; fi
grep -q 'PROJECT AXIOMS' /tmp/tB/c.log || { cat /tmp/tB/c.log; fail "self-test B: rejected but NOT by the closure audit"; }
echo "fido: audit self-test B — rejected (as required)"
# C — an UNUSED certified inductive admitted with positivity DISABLED and elimination schemes SUPPRESSED, so
#     no constant references it and the audit MUST seed the inductive itself (via IndRef) to catch it
mkdir -p /tmp/tC
printf 'Unset Positivity Checking.\nUnset Elimination Schemes.\nInductive Bad : Type := mkBad : (Bad -> False) -> Bad.\n' > /tmp/tC/T.v
compile -R /tmp/tC Fido /tmp/tC/T.v > /dev/null 2>&1; reject /tmp/tC C
# D — a surviving NAMED assumption reachable in the audit context (a section Variable, audit run in-section)
mkdir -p /tmp/tD
{ printf 'From Fido Require Import %s.\n' "$mods"; printf 'Declare ML Module "fido.emit".\nSection S.\nVariable surviving : True.\nFido Audit Assumptions.\nEnd S.\n'; } > /tmp/tD/Check.v
if rocq c -Q _build/default/. Fido /tmp/tD/Check.v > /tmp/tD/c.log 2>&1; then cat /tmp/tD/c.log; fail "self-test D: audit did NOT reject a surviving section Variable"; fi
grep -q 'PROJECT AXIOMS' /tmp/tD/c.log || { cat /tmp/tD/c.log; fail "self-test D: rejected but NOT by the closure audit"; }
echo "fido: audit self-test D — surviving named assumption rejected (as required)"
# E — a normal closed Section theorem (variable correctly generalized) must be ACCEPTED, not falsely rejected
mkdir -p /tmp/tE
printf 'Section S.\nVariable x : nat.\nLemma triv : x = x. Proof. reflexivity. Qed.\nEnd S.\n' > /tmp/tE/T.v
compile -R /tmp/tE Fido /tmp/tE/T.v > /dev/null 2>&1
printf 'From Fido Require Import T.\nDeclare ML Module "fido.emit".\nFido Audit Assumptions.\n' > /tmp/tE/Check.v
if ! rocq c -R /tmp/tE Fido -Q _build/default/. Fido /tmp/tE/Check.v > /tmp/tE/c.log 2>&1; then cat /tmp/tE/c.log; fail "self-test E: a closed Section theorem was FALSELY rejected"; fi
grep -q 'assumption audit OK' /tmp/tE/c.log || { cat /tmp/tE/c.log; fail "self-test E: closed Section theorem not accepted"; }
echo "fido: audit self-test E — closed Section theorem accepted (as required)"
echo "fido: prove OK — dune build; readable gate $got/$want; module coverage; whole-theory audit (constants+inductives+named); self-tests A-E"
SH

# ── Stage 4: emit — Dune compiles the theory AND the Fido transport plugin (shared cache id with prover).
#    Then, in EXPLICIT always-run steps (never .vo side effects): `Fido Materialize` writes each witness's
#    authoritative pristine image DIRECTLY (witness, multi, EMPTY), and the emit-time assumption-closure guard
#    rejects TRANSIENTLY-generated forged images.  A standalone driver (sink_test) exercises the dirty-directory
#    sink separately (foreign/nested-.fido rejection, sibling-temp two-phase recovery, crash/cleanup/EXDEV/ownership).
FROM rocq-base AS emit
ARG TARGETARCH
COPY --chown=opam:opam dune-project dune ./
COPY --chown=opam:opam *.v ./
COPY --chown=opam:opam gate/ gate/
COPY --chown=opam:opam plugin/ plugin/
COPY --chown=opam:opam e2e/ e2e/
# pre-create the cross-mount test root as the emit (opam) user, so it stays opam-owned when the RUN below
# mounts a distinct-device (opam-owned) cache at its nested `sub/` parent — the real cross-mount gate.
RUN mkdir -p /workspace/adv-mount
RUN --mount=type=cache,id=fido-dune-rocq-9.2.0-${TARGETARCH},uid=1000,gid=1000,target=/workspace/_build,sharing=locked --mount=type=cache,id=fido-crossmnt-${TARGETARCH},uid=1000,gid=1000,sharing=private,target=/workspace/adv-mount/sub <<'SH'
set -eu
fail() { echo "fido: emit FAILED — $*"; exit 1; }
rm -rf /workspace/e2e-out /workspace/e2e-multi /workspace/e2e-empty /workspace/e2e-bytes /workspace/e2e-forge* /workspace/e2e-neg /workspace/adv-* /workspace/sreal /workspace/slink /workspace/sink_test /workspace/generated /workspace/generated-multi /workspace/generated-empty /workspace/generated-bytes 2>/dev/null || true
# cached: Dune compiles the proved theory + the transport plugin (shared cache id)
if ! dune build @install @all > /tmp/emit-build.log 2>&1; then cat /tmp/emit-build.log; fail "theory/plugin build FAILED"; fi
export OCAMLPATH=/workspace/_build/install/default/lib:${OCAMLPATH:-}
# --- each witness ONLY MATERIALIZES its authoritative pristine image (`Fido Materialize`): EXACTLY the rendered
#     go.mod + recursive .go, NO .fido/lock/temp — what the `generated-module` layer + go-e2e VALIDATE with a
#     fresh `go build ./...`.  The sink is exercised separately (sink_test), reached in production only via `make regenerate`. ---
G=/workspace/generated
if ! rocq c -Q _build/default/. Fido e2e/Witness.v > /tmp/emit.log 2>&1; then cat /tmp/emit.log; fail "Fido Materialize (witness) FAILED"; fi
cat /tmp/emit.log
[ -f "$G/go.mod" ]  || fail "the materialized pristine has no rendered go.mod"
[ -f "$G/main.go" ] || fail "the materialized pristine has no main.go"
[ -z "$(find "$G" -name '.fido*' -o -name '*.fido-tmp-v1')" ] || fail "generated: control/temp residue in the materialized pristine module"
[ "$(find "$G" -name '*.go' | wc -l)" -ge 1 ] || fail "generated: the materialized pristine canonical module has no .go file"
echo "fido: pristine generated-module tree (materialized DIRECTLY from the certified image):"; echo ----; ( cd "$G" && find . -type f | sort ); echo ----; cat "$G/go.mod"; echo ----; cat "$G/main.go"; echo ----
# the go.mod is the Rocq-rendered module file (header first line, exact module/go directives)
head -1 "$G/go.mod" | grep -q '^// fido generated' || fail "rendered go.mod is not Fido-headed"
grep -qx 'module fido.local/generated' "$G/go.mod" || { cat "$G/go.mod"; fail "rendered go.mod module directive unexpected"; }
grep -qx 'go 1.23' "$G/go.mod" || { cat "$G/go.mod"; fail "rendered go.mod go directive unexpected"; }

# differential witness: TWO main packages (root + sub/) + an empty file + the rendered go.mod
if ! rocq c -Q _build/default/. Fido e2e/WitnessMulti.v > /tmp/emit-multi.log 2>&1; then cat /tmp/emit-multi.log; fail "Fido Materialize (multi-package) FAILED"; fi
{ [ -f /workspace/generated-multi/go.mod ] && [ -f /workspace/generated-multi/main.go ] && [ -f /workspace/generated-multi/extra.go ] && [ -f /workspace/generated-multi/sub/main.go ]; } || fail "multi-package pristine tree incomplete"
echo "fido: multi-package pristine tree:"; ( cd /workspace/generated-multi && find . -type f | sort )

# empty-program witness: a valid module with NO source files -> go.mod and zero .go
if ! rocq c -Q _build/default/. Fido e2e/WitnessEmpty.v > /tmp/emit-empty.log 2>&1; then cat /tmp/emit-empty.log; fail "Fido Materialize (empty program) FAILED"; fi
[ -f /workspace/generated-empty/go.mod ] || fail "empty program materialized no go.mod"
[ -z "$(find /workspace/generated-empty -name '*.go')" ] || fail "empty program materialized a .go file"
echo "fido: empty-program pristine tree:"; ( cd /workspace/generated-empty && find . -type f | sort )

# boundary-byte string witness: a println of a string with bytes 0x00/0x1f/0x7f/0x80/0xff -> a separate
# tree the go-e2e byte-exact oracle builds, runs, and compares (od hex) against the reviewed golden.
if ! rocq c -Q _build/default/. Fido e2e/WitnessBytes.v > /tmp/emit-bytes.log 2>&1; then cat /tmp/emit-bytes.log; fail "Fido Materialize (boundary bytes) FAILED"; fi
[ -f /workspace/generated-bytes/main.go ] || fail "boundary-byte witness materialized no main.go"
echo "fido: boundary-byte pristine tree:"; ( cd /workspace/generated-bytes && find . -type f | sort ); cat /workspace/generated-bytes/main.go

# --- the multi/empty/bytes materialized pristine exports carry NO .fido/lock/temp (the materializer writes
#     none); the go-e2e fresh-build validation consumes these AUTHORITATIVE PRE-BUILD images directly. ---
check_pristine() {  # <materialized-pristine>
  [ -d "$1" ] || fail "pristine $1: the witness did not materialize it"
  [ -z "$(find "$1" -name '.fido*' -o -name '*.fido-tmp-v1')" ] || fail "pristine $1: control/temp residue in the materialized tree"
}
check_pristine /workspace/generated-multi
check_pristine /workspace/generated-empty
check_pristine /workspace/generated-bytes
echo "fido: pristine multi/empty/bytes exports assembled (no .fido)"

# provenance (1): a forged raw transport (not a DirectoryImage) is rejected BEFORE any effect (Fail fixtures)
if ! rocq c -Q _build/default/. Fido e2e/WitnessNeg.v > /tmp/emit-neg.log 2>&1; then cat /tmp/emit-neg.log; fail "a forged raw transport was NOT rejected"; fi
[ ! -e /workspace/e2e-neg ] || fail "a rejected Fido Materialize still created its target directory"

# provenance (2): a FORGED image — the right TYPE but a non-empty assumption closure — is rejected by the
# transport-time closure check (the shared `decode_guarded`) BEFORE any effect.  The axiom/variable fixtures
# are GENERATED TRANSIENTLY (never tracked): a DIRECT axiom, an axiom behind an opaque Qed, a DIRECT section
# variable, and a TRANSITIVE section variable — each errors `rocq c` (no `Fail`) and we assert the reason + no target.
mkdir -p /tmp/forge
cat > /tmp/forge/preamble <<'EOF'
From Stdlib Require Import List String.
From Fido Require Import FilePath Collections ModulePath GoVersion GoAST GoCompile GoSafe GoRender GoEmit.
Import ListNotations.
Definition fgm : string := "forged"%string.
Definition ff : Collections.FileMapBase.t string :=
  Collections.FileMapBase.add (mkFP "main.go" eq_refl) "forged"%string (Collections.FileMapBase.empty string).
EOF
cat /tmp/forge/preamble - > /tmp/forge/Direct.v <<'EOF'
Axiom p : exists sp, fgm = render_go_mod_of sp /\ ff = render_map sp.
Definition img : DirectoryImage := mkImage fgm ff p.
Declare ML Module "fido.emit".
Fido Materialize img To "/workspace/e2e-forge".
EOF
cat /tmp/forge/preamble - > /tmp/forge/Opaque.v <<'EOF'
Axiom a : exists sp, fgm = render_go_mod_of sp /\ ff = render_map sp.
Lemma p : exists sp, fgm = render_go_mod_of sp /\ ff = render_map sp. Proof. exact a. Qed.
Definition img : DirectoryImage := mkImage fgm ff p.
Declare ML Module "fido.emit".
Fido Materialize img To "/workspace/e2e-forge-op".
EOF
cat /tmp/forge/preamble - > /tmp/forge/Var.v <<'EOF'
Declare ML Module "fido.emit".
Section S.
Variable p : exists sp, fgm = render_go_mod_of sp /\ ff = render_map sp.
Definition img : DirectoryImage := mkImage fgm ff p.
Fido Materialize img To "/workspace/e2e-forge-var".
End S.
EOF
cat /tmp/forge/preamble - > /tmp/forge/VarIndirect.v <<'EOF'
Declare ML Module "fido.emit".
Section S.
Variable v : exists sp, fgm = render_go_mod_of sp /\ ff = render_map sp.
Definition q : exists sp, fgm = render_go_mod_of sp /\ ff = render_map sp := v.
Definition img : DirectoryImage := mkImage fgm ff q.
Fido Materialize img To "/workspace/e2e-forge-vi".
End S.
EOF
forge_reject() {   # <file> <target-dir> <label>
  if rocq c -Q _build/default/. Fido "$1" > /tmp/emit-forge.log 2>&1; then cat /tmp/emit-forge.log; fail "$3: a forged image was NOT rejected"; fi
  grep -q 'provenance depends on an axiom' /tmp/emit-forge.log || { cat /tmp/emit-forge.log; fail "$3: rejected, but NOT by the assumption-closure check (wrong reason)"; }
  [ ! -e "$2" ] || fail "$3: a rejected forged materialize still created its target directory"
  echo "fido: provenance enforced — $3 rejected before any effect"
}
forge_reject /tmp/forge/Direct.v      /workspace/e2e-forge     "direct axiom"
forge_reject /tmp/forge/Opaque.v      /workspace/e2e-forge-op  "axiom behind an opaque Qed proof"
forge_reject /tmp/forge/Var.v         /workspace/e2e-forge-var "direct section variable"
forge_reject /tmp/forge/VarIndirect.v /workspace/e2e-forge-vi  "transitive section variable"

# The whole-certified-theory assumption audit + coverage + self-tests A-E run in the `prover` stage (NOT
# duplicated here); this stage keeps only the emit-time provenance guard above and the sink exercise below.

# --- exercise the dirty-directory sink directly (sibling `.fido-tmp-v1` staging + two-phase recovery + foreign rejection) ---
cp plugin/fido_sink.ml e2e/sink_test.ml /tmp/
if ! ( cd /tmp && ocamlfind ocamlopt -package unix -linkpkg fido_sink.ml sink_test.ml -o /workspace/sink_test ) > /tmp/sink.log 2>&1; then cat /tmp/sink.log; fail "sink_test compile FAILED"; fi
cd /workspace
hdr=$(head -1 "$G/go.mod")     # DERIVE the ownership header from the materialized pristine output (no hardcoded literal)
temps() { find "$1" -name '*.fido-tmp-v1' 2>/dev/null; }   # any reserved sibling temp = residue
residue() { temps "$1"; }

# ============================ Clean / dirty sync ============================
# clean sync → rendered go.mod + main.go + control marker; no temp residue (sink_test byte-verifies each installed file).
mkdir -p adv-1; ./sink_test adv-1 || fail "clean sync failed"
{ [ -f adv-1/go.mod ] && [ -f adv-1/main.go ] && [ -f adv-1/.fido/marker ]; } || fail "missing go.mod/main.go/marker"
[ "$(ls adv-1/.fido)" = "marker" ] || fail "control dir holds more than the marker after a released run"
[ -z "$(residue adv-1)" ] || fail "sibling-temp residue leaked after a successful sync"
# Fido-owned files UPDATE, a stale owned .go is REMOVED, foreign non-Go is PRESERVED
./sink_test adv-1 multi || fail "multi re-sync failed"
[ -f adv-1/sub/main.go ] || fail "multi re-sync did not create sub/main.go"
printf 'keep\n' > adv-1/notes.txt
./sink_test adv-1 || fail "single re-sync failed"
[ ! -e adv-1/sub/main.go ] || fail "a stale owned .go was not removed on re-sync"
[ -f adv-1/notes.txt ] || fail "a foreign non-Go file was removed on re-sync"
# empty program removes ALL owned .go, keeps the owned go.mod + foreign files
./sink_test adv-1 empty || fail "empty re-sync failed"
[ ! -e adv-1/main.go ] || fail "empty program did not remove the owned main.go"
[ -f adv-1/go.mod ] || fail "empty program removed the owned go.mod"
[ -f adv-1/notes.txt ] || fail "empty program removed a foreign file"
[ -z "$(residue adv-1)" ] || fail "residue after empty re-sync"
#a DUPLICATE desired path is REJECTED before any filesystem effect (the standard-map builder
# refuses rather than letting `add` silently overwrite); nothing is materialized.
mkdir -p adv-dup
if ./sink_test adv-dup dup 2>/tmp/dup.log; then fail "a duplicate desired path was NOT rejected"; fi
grep -q 'duplicate output path' /tmp/dup.log || { cat /tmp/dup.log; fail "dup rejected for the wrong reason"; }
{ [ ! -e adv-dup/go.mod ] && [ ! -e adv-dup/.fido ] && [ ! -e adv-dup/main.go ]; } || fail "a rejected duplicate still materialized files"
#PERMUTED transport entries produce a byte-IDENTICAL tree (output is keyed by path, not order).
mkdir -p adv-perm
./sink_test adv-perm perm || fail "permuted transport entries produced a different tree"
# byte-distinct OWNED replacement: an owned go.mod/.go with DIFFERENT bytes is replaced (ownership = header)
mkdir -p adv-repl
printf '%s\n\nmodule stale/old\n\ngo 1.23\n' "$hdr" > adv-repl/go.mod
printf '%s\n// STALE — replace me\npackage main\n\nfunc main() {}\n' "$hdr" > adv-repl/main.go
cp adv-repl/go.mod /tmp/repl-gm; cp adv-repl/main.go /tmp/repl-mg
./sink_test adv-repl || fail "repl: sync failed replacing byte-distinct owned files"
if cmp -s /tmp/repl-gm adv-repl/go.mod;  then fail "repl: the owned go.mod was NOT replaced"; fi
if cmp -s /tmp/repl-mg adv-repl/main.go; then fail "repl: the owned main.go was NOT replaced"; fi

# ============================ Foreign inputs ============================
# each foreign class REJECTS before any generated-file mutation; the foreign input survives byte-unchanged.
mkdir -p adv-fr; printf 'package main\nfunc main(){}\n' > adv-fr/foreign.go
if ./sink_test adv-fr; then fail "a foreign root .go was NOT rejected"; fi
[ -f adv-fr/foreign.go ] && [ ! -e adv-fr/main.go ] || fail "foreign root .go: input removed or generated file written"
mkdir -p adv-fn/pkg; printf 'package pkg\n' > adv-fn/pkg/f.go
if ./sink_test adv-fn; then fail "a foreign nested .go was NOT rejected"; fi
[ -f adv-fn/pkg/f.go ] && [ ! -e adv-fn/main.go ] || fail "foreign nested .go: input removed or generated file written"
mkdir -p adv-sl; ln -s /etc/hostname adv-sl/link.go
if ./sink_test adv-sl; then fail "a .go symlink was NOT rejected"; fi
[ -L adv-sl/link.go ] || fail "a .go symlink was removed/followed"
mkdir -p adv-gm; printf 'module foreign\n' > adv-gm/go.mod
if ./sink_test adv-gm; then fail "a foreign root go.mod was NOT rejected"; fi
printf 'module foreign\n' | cmp -s - adv-gm/go.mod || fail "a foreign root go.mod was altered"
mkdir -p adv-gms; ln -s /etc/hostname adv-gms/go.mod
if ./sink_test adv-gms; then fail "a go.mod symlink was NOT rejected"; fi
[ -L adv-gms/go.mod ] || fail "a go.mod symlink was removed/followed"
mkdir -p adv-ngm/sub; printf 'module x\n' > adv-ngm/sub/go.mod
if ./sink_test adv-ngm; then fail "a nested go.mod was NOT rejected"; fi
[ -f adv-ngm/sub/go.mod ] || fail "a nested go.mod was removed"
# DIRECTORY-shaped Go inputs must reject too (not be traversed as ordinary directories): a directory named
# `foreign.go`, and a nested `go.mod` DIRECTORY — each rejects before any generated mutation and is preserved.
mkdir -p adv-dgo/foreign.go
if ./sink_test adv-dgo; then fail "a directory named foreign.go was NOT rejected"; fi
[ -d adv-dgo/foreign.go ] && [ ! -e adv-dgo/main.go ] || fail "foreign .go dir: input removed or generated file written"
mkdir -p adv-dgm/sub/go.mod
if ./sink_test adv-dgm; then fail "a nested go.mod directory was NOT rejected"; fi
[ -d adv-dgm/sub/go.mod ] && [ ! -e adv-dgm/main.go ] || fail "nested go.mod dir: input removed or generated file written"
mkdir -p adv-ur/locked; chmod 000 adv-ur/locked
if ./sink_test adv-ur; then chmod 755 adv-ur/locked; fail "an unreadable directory did NOT fail closed"; fi
chmod 755 adv-ur/locked
# foreign rejection PRESERVES pre-existing generated finals (the scan precedes any generated-file mutation)
mkdir -p adv-p1; ./sink_test adv-p1 || fail "p1: seed sync failed"
cp adv-p1/go.mod /tmp/p1-gm; cp adv-p1/main.go /tmp/p1-mg
printf 'package foreign\nfunc F(){}\n' > adv-p1/foreign.go
if ./sink_test adv-p1; then fail "p1: a foreign .go was not rejected with prior finals present"; fi
cmp -s /tmp/p1-gm adv-p1/go.mod || fail "p1: the prior go.mod was mutated before the refusal"
cmp -s /tmp/p1-mg adv-p1/main.go || fail "p1: the prior main.go was mutated before the refusal"

# ============================ Control namespace ============================
# exact root .fido (marker + optional lock) accepted; a foreign/unexpected/nested .fido rejects + preserves.
mkdir -p adv-ffido/.fido; printf 'nope\n' > adv-ffido/.fido/marker
if ./sink_test adv-ffido; then fail "a foreign .fido control dir was NOT refused"; fi
printf 'nope\n' | cmp -s - adv-ffido/.fido/marker || fail "a foreign .fido marker was altered"
mkdir -p adv-shape; ./sink_test adv-shape || fail "shape: init"
printf 'surprise\n' > adv-shape/.fido/surprise
if ./sink_test adv-shape; then fail "shape: an unexpected .fido entry was not refused"; fi
[ -f adv-shape/.fido/surprise ] || fail "shape: the unexpected entry was removed"
# nested .fido of ANY type below root rejects + preserves (directory / symlink / regular file)
mkdir -p adv-nfd/sub/.fido
if ./sink_test adv-nfd; then fail "nfd: a nested .fido directory was not rejected"; fi
[ -d adv-nfd/sub/.fido ] || fail "nfd: the nested .fido directory was removed"
mkdir -p adv-nfl/sub; ln -s /etc adv-nfl/sub/.fido
if ./sink_test adv-nfl; then fail "nfl: a nested .fido symlink was not rejected"; fi
[ -L adv-nfl/sub/.fido ] || fail "nfl: the nested .fido symlink was removed/followed"
mkdir -p adv-nfr/sub; printf 'x\n' > adv-nfr/sub/.fido
if ./sink_test adv-nfr; then fail "nfr: a nested .fido regular file was not rejected"; fi
[ -f adv-nfr/sub/.fido ] || fail "nfr: the nested .fido file was removed"

# ============================ Reserved temp suffix ============================
# an abandoned REGULAR reserved-suffix temp (root and nested) is removed after a complete successful scan.
mkdir -p adv-t1; ./sink_test adv-t1 || fail "t1: init"
printf 'junk\n' > adv-t1/go.mod.fido-tmp-v1
mkdir -p adv-t1/sub; printf 'junk\n' > adv-t1/sub/leftover.go.fido-tmp-v1
./sink_test adv-t1 || fail "t1: sync failed with abandoned temps present"
[ -z "$(temps adv-t1)" ] || fail "t1: abandoned regular temps were not removed"
# MULTIPLE temps are collected before deletion: an INVALID path elsewhere refuses BEFORE any temp is deleted.
mkdir -p adv-t2; ./sink_test adv-t2 || fail "t2: init"
printf 'a\n' > adv-t2/x.go.fido-tmp-v1; printf 'b\n' > adv-t2/y.go.fido-tmp-v1
printf 'package foreign\n' > adv-t2/foreign.go            # invalid (foreign .go) elsewhere in the tree
if ./sink_test adv-t2; then fail "t2: a foreign .go did not refuse the run"; fi
{ [ -f adv-t2/x.go.fido-tmp-v1 ] && [ -f adv-t2/y.go.fido-tmp-v1 ]; } || fail "t2: a collected temp was deleted before the complete scan succeeded (two-phase violated)"
rm -f adv-t2/foreign.go
# a temp that is a SYMLINK / DIRECTORY / special is NOT owned → refuse + preserve.
mkdir -p adv-tsl; ./sink_test adv-tsl || fail "tsl: init"; ln -s /etc/hostname adv-tsl/main.go.fido-tmp-v1
if ./sink_test adv-tsl; then fail "tsl: a reserved-suffix symlink was not rejected"; fi
[ -L adv-tsl/main.go.fido-tmp-v1 ] || fail "tsl: the reserved-suffix symlink was removed/followed"
mkdir -p adv-tdir; ./sink_test adv-tdir || fail "tdir: init"; mkdir -p adv-tdir/main.go.fido-tmp-v1
if ./sink_test adv-tdir; then fail "tdir: a reserved-suffix directory was not rejected"; fi
[ -d adv-tdir/main.go.fido-tmp-v1 ] || fail "tdir: the reserved-suffix directory was removed"
mkdir -p adv-tsp; ./sink_test adv-tsp || fail "tsp: init"; mkfifo adv-tsp/main.go.fido-tmp-v1
if ./sink_test adv-tsp; then fail "tsp: a reserved-suffix special (fifo) was not rejected"; fi
[ -p adv-tsp/main.go.fido-tmp-v1 ] || fail "tsp: the reserved-suffix fifo was removed"
# a REGULAR reserved-suffix file whose suffix-stripped path MAPS to a Fido final path (root go.mod or a
# filepath_ok .go) is Fido-owned (forgeable convention) and removed; a NON-MAPPABLE one is PRESERVED, refused clearly.
mkdir -p adv-town; ./sink_test adv-town || fail "town: init"
printf 'x\n' > adv-town/notused.go.fido-tmp-v1                 # notused.go is filepath_ok → mappable → owned
mkdir -p adv-town/sub; printf 'x\n' > adv-town/sub/leftover.go.fido-tmp-v1
./sink_test adv-town || fail "town: sync failed with mappable abandoned temps present"
[ -z "$(temps adv-town)" ] || fail "town: mappable reserved-suffix temps were not collected+removed"
for bad in notes.fido-tmp-v1 hand-written.fido-tmp-v1 UPPER.go.fido-tmp-v1 a_b.go.fido-tmp-v1; do
  d=/workspace/adv-tng-$(echo "$bad" | tr './' '__'); mkdir -p "$d"; ./sink_test "$d" || fail "tng: init $bad"
  printf 'keep me\n' > "$d/$bad"
  if ./sink_test "$d"; then fail "tng: a non-mappable reserved-suffix entry ($bad) was NOT refused"; fi
  printf 'keep me\n' | cmp -s - "$d/$bad" || fail "tng: a non-mappable reserved-suffix entry ($bad) was altered/removed"
done
# DOT/UNDERSCORE-prefixed non-mappable reserved-suffix FILES at the traversed root are NOT beneath a skipped
# directory TREE (only ignored dir TREES are opaque), so they must still REFUSE fail-closed + stay byte-exact
# the reserved-suffix classification runs before the dot/underscore-name skip.
for bad in .notes.fido-tmp-v1 _draft.fido-tmp-v1; do
  d=/workspace/adv-osf-$(echo "$bad" | tr './' '__'); mkdir -p "$d"; ./sink_test "$d" || fail "osf: init $bad"
  printf 'keep me\n' > "$d/$bad"
  if ./sink_test "$d"; then fail "osf: a dot/underscore non-mappable reserved-suffix file ($bad) was NOT refused"; fi
  printf 'keep me\n' | cmp -s - "$d/$bad" || fail "osf: a dot/underscore reserved-suffix file ($bad) was altered/removed"
done
# a non-mappable suffix entry in a VISIBLE (Go-discoverable) subdir also refuses + is preserved.
mkdir -p adv-tngv/visible-dir; ./sink_test adv-tngv || fail "tngv: init"
printf 'bin\n' > adv-tngv/visible-dir/arbitrary.bin.fido-tmp-v1
if ./sink_test adv-tngv; then fail "tngv: a non-mappable suffix entry under a visible dir was NOT refused"; fi
printf 'bin\n' | cmp -s - adv-tngv/visible-dir/arbitrary.bin.fido-tmp-v1 || fail "tngv: the visible-dir suffix entry was altered/removed"

# ============ Go-discovered namespace scoping (hidden / underscore / testdata / vendor) ============
# hidden/underscore/testdata/vendor trees are OPAQUE: never inspected, classified, cleaned, or rejected —
# so a repo's .git metadata (incl. .go and .fido-tmp-v1 NAMES) is untouched and never blocks a clean sync.
mkdir -p adv-git/.git/refs/heads adv-git/.git/logs/refs/heads
printf 'GITHEAD-A\n'  > adv-git/.git/refs/heads/release.go
printf 'GITHEAD-B\n'  > adv-git/.git/refs/heads/release.fido-tmp-v1
printf 'GITHEAD-C\n'  > adv-git/.git/logs/refs/heads/release.fido-tmp-v1
mkdir -p adv-git/_private; printf 'UND-A\n' > adv-git/_private/x.go; printf 'UND-B\n' > adv-git/_private/y.fido-tmp-v1
mkdir -p adv-git/.hidden; printf 'HID-A\n' > adv-git/.hidden/z.go
mkdir -p adv-git/testdata; printf 'TD-A\n' > adv-git/testdata/t.go
mkdir -p adv-git/vendor/pkg; printf 'VN-A\n' > adv-git/vendor/pkg/v.go
before=$(find adv-git/.git adv-git/_private adv-git/.hidden adv-git/testdata adv-git/vendor -type f -exec sha256sum {} \; | sort)
./sink_test adv-git || fail "git: a clean sync was rejected because of hidden/VCS metadata"
{ [ -f adv-git/go.mod ] && [ -f adv-git/main.go ]; } || fail "git: the clean sync did not install the generated files"
after=$(find adv-git/.git adv-git/_private adv-git/.hidden adv-git/testdata adv-git/vendor -type f -exec sha256sum {} \; | sort)
[ "$before" = "$after" ] || { echo "$before"; echo '---'; echo "$after"; fail "git: a byte under an opaque skipped tree was altered/removed"; }
[ -f adv-git/.git/refs/heads/release.fido-tmp-v1 ] || fail "git: a .git suffix-named file was adopted/removed as Fido temp"
# a Go-ignored DIRECTORY whose OWN name ends in the reserved suffix (`.cache.fido-tmp-v1`/`_priv.fido-tmp-v1`)
# is OPAQUE (dot/underscore prefix) — the opaque-dir skip must run BEFORE reserved-suffix classification, so
# it is SKIPPED + preserved, NOT stripped-and-rejected as a non-mappable temp.
mkdir -p adv-osd/.cache.fido-tmp-v1 adv-osd/_priv.fido-tmp-v1
printf 'DOTDIR\n' > adv-osd/.cache.fido-tmp-v1/data; printf 'UNDDIR\n' > adv-osd/_priv.fido-tmp-v1/data
osd_before=$(find adv-osd/.cache.fido-tmp-v1 adv-osd/_priv.fido-tmp-v1 -type f -exec sha256sum {} \; | sort)
./sink_test adv-osd || fail "osd: a clean sync was rejected because of an opaque suffix-named directory"
{ [ -f adv-osd/go.mod ] && [ -f adv-osd/main.go ]; } || fail "osd: the clean sync did not install the generated files"
osd_after=$(find adv-osd/.cache.fido-tmp-v1 adv-osd/_priv.fido-tmp-v1 -type f -exec sha256sum {} \; | sort)
[ "$osd_before" = "$osd_after" ] || fail "osd: a byte under an opaque suffix-named directory was altered/removed"
{ [ -d adv-osd/.cache.fido-tmp-v1 ] && [ -d adv-osd/_priv.fido-tmp-v1 ]; } || fail "osd: an opaque suffix-named directory was removed"
# but a VISIBLE ordinary directory (uppercase/hyphenated name Go may still discover) IS scanned: a foreign
# .go there still rejects.
mkdir -p adv-vis/My-Pkg; printf 'package foreign\n' > adv-vis/My-Pkg/f.go
if ./sink_test adv-vis; then fail "vis: a foreign .go in a visible non-Fido-named dir was NOT rejected"; fi
[ -f adv-vis/My-Pkg/f.go ] || fail "vis: the visible foreign .go was removed"

# ============================ Reserved path + prefix symlink (rejected before any effect) ============================
if ./sink_test /workspace/adv-resv reserved; then fail "a desired path inside .fido was NOT rejected"; fi
[ ! -e /workspace/adv-resv ] || fail "a reserved-path rejection created the root (effect before validation)"
mkdir -p /workspace/sreal; printf 'x\n' > /workspace/sreal/keep; ln -s /workspace/sreal /workspace/slink
if ./sink_test /workspace/slink/child; then fail "wrote through a prefix symlink"; fi
[ ! -e /workspace/sreal/child ] || fail "a prefix symlink created a child in the referent"
# every path OUTSIDE the intrinsic FilePath `.go` domain (mirrors FilePath.path_ok) rejects BEFORE any
# effect, materializing nothing — no file, no parent dir, and CRUCIALLY no nested .fido from ensure_dir_chain.
for pm in p-nestedfido p-vendor p-testdata p-upper p-underscore p-dotdot p-nongo; do
  d=/workspace/adv-$pm; rm -rf "$d"; mkdir -p "$d"
  if ./sink_test "$d" "$pm"; then fail "$pm: a path outside the intrinsic FilePath domain was NOT rejected"; fi
  [ -z "$(find "$d" -mindepth 1)" ] || { find "$d"; fail "$pm: a rejected out-of-domain path materialized something under the root"; }
done
echo "fido: out-of-domain path rejection OK — nested/first .fido, vendor/testdata, upper/underscore/dotdot/non-.go"
# ARBITRARY-LENGTH PATH: a very long canonical `.go` path is IN the domain (no magic length cap) — it must be
# ACCEPTED and materialized like any other path (a numeric bound is not a correctness invariant).
d=/workspace/adv-long; rm -rf "$d"; mkdir -p "$d"
./sink_test "$d" p-long || fail "long: a valid arbitrary-length .go path was rejected"
longname="$(printf 'a%.0s' $(seq 1 205)).go"
[ -f "$d/$longname" ] || { find "$d"; fail "long: the 205-byte .go path did not materialize"; }
echo "fido: arbitrary-length path OK — a 205-byte canonical .go path materializes (no PATH_MAX-style cap)"

# ============================ Complete staging ============================
# crash-after-staging: EVERY desired sibling temp exists before the FIRST install (staging precedes install).
mkdir -p adv-stage
if ./sink_test adv-stage multi crash-after-staging; then fail "stage: the crash did not terminate the process"; fi
{ [ -f adv-stage/go.mod.fido-tmp-v1 ] && [ -f adv-stage/main.go.fido-tmp-v1 ] && [ -f adv-stage/sub/main.go.fido-tmp-v1 ]; } || fail "stage: not every sibling temp was staged before install"
{ [ ! -e adv-stage/go.mod ] && [ ! -e adv-stage/main.go ] && [ ! -e adv-stage/sub/main.go ]; } || fail "stage: a file was installed before staging completed"
rm -f adv-stage/.fido/index.lock; ./sink_test adv-stage multi || fail "stage: no converge after clearing the stale lock"
[ -z "$(residue adv-stage)" ] || fail "stage: residue survived recovery"
# a later-stage WRITE failure (sub/) changes NO prior FINAL and, once cleanup succeeds, leaves no residue.
mkdir -p adv-latew; ./sink_test adv-latew multi || fail "latew: init"
cp adv-latew/go.mod /tmp/lw-gm; cp adv-latew/main.go /tmp/lw-mg; cp adv-latew/sub/main.go /tmp/lw-sg
if ./sink_test adv-latew multi fail-write-sub 2>/dev/null; then fail "latew: a later-stage write failure was not surfaced"; fi
{ cmp -s /tmp/lw-gm adv-latew/go.mod && cmp -s /tmp/lw-mg adv-latew/main.go && cmp -s /tmp/lw-sg adv-latew/sub/main.go; } || fail "latew: a prior final changed after a later-stage write failure"
[ -z "$(residue adv-latew)" ] || fail "latew: temp residue survived a handled write failure (cleanup succeeded)"
./sink_test adv-latew multi || fail "latew: no converge"
# a handled failure after the first staged file removes EVERY created temp (cleanup succeeds); finals intact.
mkdir -p adv-late; ./sink_test adv-late || fail "late: init"
cp adv-late/go.mod /tmp/late-gm; cp adv-late/main.go /tmp/late-mg
if ./sink_test adv-late fail-after-first-payload 2>/dev/null; then fail "late: a handled staging failure was not surfaced"; fi
cmp -s /tmp/late-gm adv-late/go.mod || fail "late: a prior final go.mod changed"
cmp -s /tmp/late-mg adv-late/main.go || fail "late: a prior final main.go changed"
[ -z "$(residue adv-late)" ] || fail "late: temp residue survived a handled failure"
[ ! -e adv-late/.fido/index.lock ] || fail "late: the lock was not released after a handled failure"
./sink_test adv-late || fail "late: did not converge on a clean rerun"
# a HANDLED failure right after a temp is exclusively CREATED (before its bytes) still removes that temp
# (registered on creation, not after the write), leaves finals intact, releases the lock, and converges.
mkdir -p adv-fac; ./sink_test adv-fac || fail "fac: init"
cp adv-fac/go.mod /tmp/fac-gm; cp adv-fac/main.go /tmp/fac-mg
if ./sink_test adv-fac fail-after-create 2>/dev/null; then fail "fac: a handled after-create failure was not surfaced"; fi
[ -z "$(residue adv-fac)" ] || fail "fac: a temp created before the failure was not cleaned up (registered too late?)"
cmp -s /tmp/fac-gm adv-fac/go.mod || fail "fac: a prior final go.mod changed"
cmp -s /tmp/fac-mg adv-fac/main.go || fail "fac: a prior final main.go changed"
[ ! -e adv-fac/.fido/index.lock ] || fail "fac: the lock was not released"
./sink_test adv-fac || fail "fac: no converge"
# a cleanup failure reports BOTH the initiating body error AND the cleanup error, then a clean rerun converges.
mkdir -p adv-cuf
if out=$(./sink_test adv-cuf fail-after-first-payload+unlink-fail 2>&1); then fail "cuf: the compound failure was not surfaced"; fi
echo "$out" | grep -q 'injected handled failure' || { echo "$out"; fail "cuf: the initiating body error was hidden"; }
echo "$out" | grep -q 'cleanup FAILED' || { echo "$out"; fail "cuf: the cleanup failure was not reported"; }
[ ! -e adv-cuf/.fido/index.lock ] || fail "cuf: the lock was not released after a cleanup failure"
rm -f adv-cuf/*.fido-tmp-v1; ./sink_test adv-cuf || fail "cuf: no converge after removing residue"

# ============================ Crash / recovery ============================
# crash WHILE WRITING (after create, before bytes) leaves lock + a PARTIAL (empty) temp; crash AFTER STAGING
# leaves lock + ALL temps + old finals; crash DURING INSTALL leaves lock + mixed finals + remaining temps.
# Each: a rerun REFUSES on the held lock; after the stale lock is cleared, a rerun removes the temps + converges.
crash_recover() {  # <mode> <label>
  d=/workspace/adv-crash-$2; mkdir -p "$d"; ./sink_test "$d" multi || fail "$2: initial sync failed"
  if ./sink_test "$d" multi "$1"; then fail "$2: the crash did not terminate the process"; fi
  [ -e "$d/.fido/index.lock" ] || fail "$2: a crash must leave the lock held (no finalizer ran)"
  [ -n "$(temps "$d")" ] || fail "$2: the crash left no sibling-temp residue to recover"
  if ./sink_test "$d" multi; then fail "$2: ran despite the crash-held lock"; fi
  rm -f "$d/.fido/index.lock"
  ./sink_test "$d" multi || fail "$2: did not converge after clearing the stale lock"
  [ -z "$(temps "$d")" ] || fail "$2: temp residue survived recovery"
  { [ -f "$d/go.mod" ] && [ -f "$d/main.go" ] && [ -f "$d/sub/main.go" ]; } || fail "$2: files missing after convergence"
}
crash_recover crash-after-create        writing
crash_recover crash-after-staging       staged
crash_recover crash-after-first-install installing
# the write-crash specifically leaves a created-but-EMPTY partial temp, then recovers it.
mkdir -p adv-partial; ./sink_test adv-partial || fail "partial: init"
if ./sink_test adv-partial crash-after-create; then fail "partial: the crash did not terminate"; fi
pt=$(temps adv-partial | head -1); [ -n "$pt" ] || fail "partial: no temp left by the write crash"
[ ! -s "$pt" ] || fail "partial: the crash-after-create temp is not empty ($(wc -c < "$pt") bytes) — not a partial"
[ -e adv-partial/.fido/index.lock ] || fail "partial: the lock was not left held by the crash"
rm -f adv-partial/.fido/index.lock; ./sink_test adv-partial || fail "partial: no converge after clearing the lock"
[ -z "$(temps adv-partial)" ] || fail "partial: the partial temp survived recovery"

# ============================ Rename / ownership ============================
# EXDEV fails LOUD with no copy fallback; nothing installed; lock released.
mkdir -p adv-exdev
if out=$(./sink_test adv-exdev exdev 2>&1); then fail "exdev: a cross-device rename did not fail"; fi
echo "$out" | grep -q 'cross-device' || { echo "$out"; fail "exdev: not the cross-device failure"; }
{ [ ! -e adv-exdev/go.mod ] && [ ! -e adv-exdev/main.go ]; } || fail "exdev: a file was installed despite EXDEV (copy fallback?)"
[ ! -e adv-exdev/.fido/index.lock ] || fail "exdev: the lock was not released"
# OVERWRITE ownership rechecked immediately: a target that becomes foreign right before its overwrite aborts.
mkdir -p adv-race; ./sink_test adv-race || fail "race: init"
if ./sink_test adv-race foreign-before-install; then fail "race: overwrote a target that became foreign"; fi
printf 'FOREIGN not a fido file\n' | cmp -s - adv-race/main.go || fail "race: the now-foreign main.go was overwritten"
# STALE-DELETE ownership rechecked immediately: a stale owned .go that becomes foreign right before its
# stale-delete recheck ABORTS fail-closed and survives with its foreign bytes.
mkdir -p adv-del; ./sink_test adv-del multi || fail "del: init"
if out=$(./sink_test adv-del foreign-before-delete 2>&1); then fail "del: a delete-time mismatch did not abort"; fi
echo "$out" | grep -q 'no longer Fido-owned' || { echo "$out"; fail "del: not the delete-time ownership abort"; }
printf 'FOREIGN not a fido file\n' | cmp -s - adv-del/sub/main.go || fail "del: a stale file that became foreign was deleted"
[ ! -e adv-del/.fido/index.lock ] || fail "del: the lock was not released after the delete-time abort"
# a sibling temp resides BESIDE each nested final, and a REAL nested mount (distinct device) is supported: the
# sub/ temp is a sibling on the mount device, so its rename is atomic (a central-staging design would EXDEV).
rm -rf /workspace/adv-mount/sub/* /workspace/adv-mount/sub/.[!.]* 2>/dev/null || true
[ -w /workspace/adv-mount ] || fail "mount: the cross-mount test root is not writable by the emit user"
[ -w /workspace/adv-mount/sub ] || fail "mount: the nested mount is not writable by the emit user"
devr=$(stat -c '%d' /workspace/adv-mount); devs=$(stat -c '%d' /workspace/adv-mount/sub)
[ "$devr" != "$devs" ] || fail "mount: adv-mount/sub (dev $devs) is not a distinct device from root (dev $devr)"
./sink_test /workspace/adv-mount multi || fail "mount: a nested cross-mount parent was rejected"
{ [ -f /workspace/adv-mount/go.mod ] && [ -f /workspace/adv-mount/main.go ] && [ -f /workspace/adv-mount/sub/main.go ]; } || fail "mount: nested cross-mount tree incomplete"
[ -z "$(residue /workspace/adv-mount)" ] || fail "mount: residue after a cross-mount success"
echo "fido: cross-mount OK — a nested sibling temp on a distinct device (dev $devs != root dev $devr) renamed atomically"

# ============================ First-time init rollback ============================
# a failed FIRST-TIME .fido init (umask 0777 → .fido mode 000 → marker EACCES, and the rollback lstat also
# EACCES) still ROLLS BACK, keeps the INITIATING error visible, aggregates, and a normal rerun converges.
mkdir -p adv-umask
if out=$( umask 0777; ./sink_test adv-umask 2>&1 ); then fail "umask: a failed first-time .fido init did not surface"; fi
echo "$out" | grep -q 'init failed' || { echo "$out"; fail "umask: the init failure was not reported"; }
echo "$out" | grep -q 'Permission denied' || { echo "$out"; fail "umask: the INITIATING (marker EACCES) error was hidden"; }
[ ! -e adv-umask/.fido ] || fail "umask: the partial mode-000 .fido was not rolled back"
./sink_test adv-umask || fail "umask: a normal rerun did not converge after rollback"

echo "fido: emit OK — Fido Materialize wrote the witness / multi / EMPTY / boundary-byte pristine trees (rendered go.mod); forged/raw images rejected before any effect; the INTERNAL sink (sink_test) passed foreign-Go/module + nested-.fido rejection, sibling-temp two-phase recovery, complete-image staging, crash points, handled/cleanup-failure aggregation, EXDEV no-copy, ownership rechecks, first-time rollback, and REAL cross-mount staging"
SH

# ── Stage 4b: generated-module — ONE content-addressed layer holding EXACTLY the pristine canonical generated
#    module (/generated/go.mod + /generated/**/*.go, no .fido/lock/temp/proof/fixture bytes).  Its cache key
#    derives from the emit stage's authoritative generation inputs (certified .v, dune, plugin, toolchain,
#    witness) — NEVER the committed generated bytes.  Every canonical-output workflow (go-e2e, staged-index
#    verification, `make regenerate`) consumes THIS layer.
FROM scratch AS generated-module
COPY --from=emit /workspace/generated/ /generated/

# ── Stage 4c: generated-artifact — the pristine module at the image root (for local export / bind-apply).
FROM scratch AS generated-artifact
COPY --from=generated-module /generated/ /

# ── Stage 4d: sync (the `make regenerate` image) is defined AFTER go-e2e below, because it COPYs go-e2e's
#    fresh-build validation marker (a stage may only COPY --from an EARLIER stage).

# ── Stage 5: go-e2e — the LAST-MILE integration check (never a proof).  The pinned Go toolchain builds the
#    canonical generated module (from the `generated-module` layer, NOT re-generated) with `go build ./...`
#    using the RENDERED go.mod and runs the witness vs reviewed goldens.  `go build ./...` is the blocking
#    acceptance alarm; `go vet` is DIAGNOSTIC ONLY.  A failure here is a hard red — GoCompile/rendering/transport
#    is wrong, never a known issue.
FROM golang:1.23-alpine@sha256:383395b794dffa5b53012a212365d40c8e37109a626ca30d6151c8348d380b5f AS go-e2e
WORKDIR /e2e
COPY --from=generated-module /generated/ ./tree/
COPY --from=emit /workspace/generated-multi/ ./multi/
COPY --from=emit /workspace/generated-empty/ ./empty/
COPY --from=emit /workspace/generated-bytes/ ./bytes/
COPY e2e/golden.stdout e2e/golden.stderr e2e/golden.exit e2e/golden.bytes.hex ./
RUN <<'SH'
set -u
# fixed process modes: a deterministic umask so every materialized file/dir gets fixed 0644/0755 modes.
umask 022
# closed-world integration: force the local pinned toolchain, no workspace, no network proxy, and NO ambient
# go env / flag / sumdb state — export the COMPLETE pinned environment so no case inherits host config.
export GOWORK=off GOTOOLCHAIN=local GOPROXY=off GOENV=off GOFLAGS= GOSUMDB=off GO111MODULE=on GOOS=linux GOARCH=amd64

# ── The ONE fresh-build runner: runs the pinned `go build ./...` ONCE in a FRESH disposable copy.  FAIL-CLOSED,
#    distinguishing a real Go run from a setup/runner/filesystem/infra failure: it RESETS its outputs on entry
#    (no prior run's log/flag leaks); a setup failure BEFORE `go build` returns sentinel 125 with _FRESH_GO_RAN=0
#    + EMPTY _FRESH_BUILD_LOG; only after `go build` runs does it set _FRESH_GO_RAN=1 + _FRESH_BUILD_LOG=<this
#    run's log> and return Go's status.  Callers MUST [require_go_ran] before judging acceptance/rejection.
fresh_go_build() {  # <src-tree> <out-var-for-fresh-root>
  _src=$1; _out=${2:-_frv}
  _FRESH_GO_RAN=0; _FRESH_BUILD_LOG=          # reset — a stale log/flag can NEVER satisfy the next caller
  _fresh=$(mktemp -d /tmp/fido-fresh.XXXXXX)          || { echo "fresh_go_build: mktemp -d FAILED"; return 125; }
  cp -a -- "$_src/." "$_fresh/"                       || { echo "fresh_go_build: cp FAILED"; rm -rf "$_fresh"; return 125; }
  _log=$(mktemp /tmp/fido-buildlog.XXXXXX)            || { echo "fresh_go_build: mktemp log FAILED"; rm -rf "$_fresh"; return 125; }
  ( cd "$_fresh" && go build ./... ) > "$_log" 2>&1
  _rc=$?
  _FRESH_GO_RAN=1; _FRESH_BUILD_LOG=$_log     # the go build actually RAN — THIS run's log is authoritative
  [ "$_rc" = 0 ] || { echo "fresh_go_build: go build ./... exit $_rc in $_fresh:"; sed 's/^/  | /' "$_log"; }
  eval "$_out=\$_fresh"
  return $_rc
}

# a judge may accept a Go OUTCOME only if the go build actually RAN.  A setup/runner/filesystem/infra failure
# (mktemp/cp; sentinel 125, _FRESH_GO_RAN=0) is NOT a Go rejection — it aborts the e2e fail-closed.
require_go_ran() {  # <label>
  [ "$_FRESH_GO_RAN" = 1 ] || { echo "fido e2e: $1 — the fresh go build ./... did NOT run (setup/runner/filesystem/infra failure); cannot judge Go acceptance/rejection"; exit 1; }
}

# ---- fail-closed FAULT SELF-TESTS for the fresh-build runner (fault injection, before any real fixture) ----
# (1) SETUP / COMMAND-NOT-RUN failure: a nonexistent source makes cp fail, so go build never runs.
_fault_rc=0; fresh_go_build /nonexistent-fault-src _FF || _fault_rc=$?
[ "$_FRESH_GO_RAN" = 0 ]   || { echo "fido e2e fault: a setup failure reported the go command as RUN"; exit 1; }
[ -z "$_FRESH_BUILD_LOG" ] || { echo "fido e2e fault: a setup failure left a build log (stale-log risk)"; exit 1; }
[ "$_fault_rc" = 125 ]     || { echo "fido e2e fault: a setup failure did not return the infra sentinel (got $_fault_rc)"; exit 1; }
# (2) STALE-OUTPUT contamination: a REAL go run leaves a non-empty log; a following setup failure MUST clear it,
#     so a later negative judge can NEVER grep the previous run's diagnostic.
_sd=/tmp/fresh-fault-ok; rm -rf "$_sd"; mkdir -p "$_sd"
printf 'module ff\n\ngo 1.23\n' > "$_sd/go.mod"
printf 'package main\nfunc main() { println(int8(128)) }\n' > "$_sd/x.go"   # a real rejection -> non-empty log
fresh_go_build "$_sd" _FF || true
{ [ "$_FRESH_GO_RAN" = 1 ] && [ -n "$_FRESH_BUILD_LOG" ] && [ -s "$_FRESH_BUILD_LOG" ]; } || { echo "fido e2e fault: a real go run left no current-run log"; exit 1; }
_stale_log=$_FRESH_BUILD_LOG; rm -rf "${_FF:-/nonexistent}"
fresh_go_build /nonexistent-fault-src _FF2 || true
{ [ "$_FRESH_BUILD_LOG" != "$_stale_log" ] && [ -z "$_FRESH_BUILD_LOG" ] && [ "$_FRESH_GO_RAN" = 0 ]; } || { echo "fido e2e fault: a setup failure did NOT clear the prior run's log/flag (stale-output risk)"; exit 1; }
rm -rf "$_sd"
echo "fido e2e fault: fresh-build runner fail-closed — setup/command-not-run distinguished (sentinel 125, no run), no stale log/flag leaks"

cd tree
# the generated-module layer is the PRISTINE canonical module: it must carry NO .fido / lock / temp residue
if [ -n "$(find . -name '.fido*' -o -name '*.fido-tmp-v1')" ]; then echo "fido e2e: the generated-module layer contains control/temp residue:"; find . -name '.fido*' -o -name '*.fido-tmp-v1'; exit 1; fi
echo "fido e2e: canonical generated-module tree under test:"; echo ----; find . -type f | sort | while read f; do echo "== $f =="; cat "$f"; done; echo ----
gv=$(go env GOVERSION); goos=$(go env GOOS); goarch=$(go env GOARCH)
echo "fido e2e: toolchain GOVERSION=$gv GOOS=$goos GOARCH=$goarch (operational pin: go1.23/linux/amd64, a 64-bit target)"
case "$gv" in go1.23*) : ;; *) echo "fido e2e: Go version $gv != pinned go1.23"; exit 1;; esac
[ "$goos" = linux ]  || { echo "fido e2e: GOOS $goos != pinned linux"; exit 1; }
[ "$goarch" = amd64 ] || { echo "fido e2e: GOARCH $goarch != pinned amd64"; exit 1; }
# the go.mod is the RENDERED module file (no handwritten injection)
[ -f go.mod ] || { echo "fido e2e: the emitted tree has no rendered go.mod"; exit 1; }
head -1 go.mod | grep -q '^// fido generated' || { echo "fido e2e: go.mod is not Fido-generated"; cat go.mod; exit 1; }
grep -qx 'module fido.local/generated' go.mod || { echo "fido e2e: unexpected module directive"; cat go.mod; exit 1; }
grep -qx 'go 1.23' go.mod || { echo "fido e2e: unexpected go directive"; cat go.mod; exit 1; }
if [ -n "$(gofmt -l .)" ]; then echo "fido e2e: emitted Go is not gofmt-clean:"; gofmt -l .; exit 1; fi
# go vet is DIAGNOSTIC ONLY (nonblocking); go build acceptance is the contract
if ! go vet ./...; then echo "fido e2e: go vet reported diagnostics (nonblocking)"; fi
# the WHOLE tree must compile — routed through the FRESH-BUILD RUNNER (a disposable materialization of the
# PRISTINE tree; /— never build in the authoritative tree, never copy a post-build byte back)
fresh_go_build /e2e/tree WFRESH || { require_go_ran fresh-go-build; cat "${WFRESH:-/dev/null}/.build.err" 2>/dev/null; echo "fido e2e: go build ./... FAILED in a fresh root (a certified tree must always compile)"; exit 1; }
echo "fido e2e: witness go build ./... OK in a fresh materialized root ($WFRESH)"
# the sole-main `go build ./...` ALREADY wrote the default executable to the fresh root — RUN THAT and compare to
# the reviewed goldens (NO second build in the same root; the runner runs `go build ./...` exactly once)
WEXE=$(find "$WFRESH" -maxdepth 1 -type f -perm -u+x)
{ [ -n "$WEXE" ] && [ "$(printf '%s\n' "$WEXE" | wc -l)" = 1 ] && [ -x "$WEXE" ]; } || { echo "fido e2e: the sole-main go build ./... produced not-exactly-one default executable [$WEXE]"; rm -rf "$WFRESH"; exit 1; }
"$WEXE" > out.stdout 2> out.stderr; ec=$?
echo "fido e2e: exit=$ec stdout=[$(cat out.stdout)] stderr=[$(cat out.stderr)]"
printf '%s\n' "$ec" > out.exit
echo "fido e2e: out.stderr hex (for golden review):"; od -An -v -tx1 out.stderr | tr -s ' '
diff ../golden.exit   out.exit   || { echo "fido e2e: EXIT mismatch";   exit 1; }
diff ../golden.stdout out.stdout || { echo "fido e2e: STDOUT mismatch"; exit 1; }
diff ../golden.stderr out.stderr || { echo "fido e2e: STDERR mismatch"; exit 1; }
rm -rf "$WFRESH"

# --- BYTE-EXACT boundary-byte oracle: a `println` of bytes 0x00/0x1f/0x7f/0x80/0xff must emit exactly those
#     five (+ newline) to stderr, compared as HEX (od) against the reviewed golden `golden.bytes.hex`. ---
# the bytes tree is the PRISTINE export (generated-bytes; no .fido) — route acceptance through the fresh runner.
[ -f /e2e/bytes/main.go ] || { echo "fido e2e bytes: no boundary-byte main.go"; exit 1; }
if [ -n "$( cd /e2e/bytes && gofmt -l . )" ]; then echo "fido e2e bytes: boundary-byte Go is not gofmt-clean"; ( cd /e2e/bytes && gofmt -l . ); exit 1; fi
fresh_go_build /e2e/bytes BFRESH || { require_go_ran fresh-go-build; cat "${BFRESH:-/dev/null}/.build.err" 2>/dev/null; echo "fido e2e bytes: go build ./... FAILED in a fresh root"; exit 1; }
# run the default executable the sole-main `go build ./...` already produced (NO second build in the same root)
BEXE=$(find "$BFRESH" -maxdepth 1 -type f -perm -u+x)
{ [ -n "$BEXE" ] && [ "$(printf '%s\n' "$BEXE" | wc -l)" = 1 ] && [ -x "$BEXE" ]; } || { echo "fido e2e bytes: the sole-main go build ./... produced not-exactly-one default executable [$BEXE]"; rm -rf "$BFRESH"; exit 1; }
"$BEXE" > /e2e/bytes.out 2> /e2e/bytes.err; bec=$?
[ "$bec" = 0 ] || { echo "fido e2e bytes: boundary-byte witness exited $bec"; rm -rf "$BFRESH"; exit 1; }
b_actual=$(od -An -v -tx1 /e2e/bytes.err | tr -dc '0-9a-f')
b_want=$(tr -dc '0-9a-f' < /e2e/golden.bytes.hex)
echo "fido e2e bytes: actual stderr hex=[$b_actual] golden=[$b_want]"
[ "$b_actual" = "$b_want" ] || { echo "fido e2e bytes: BYTE MISMATCH — the boundary-byte string did not round-trip through Go"; rm -rf "$BFRESH"; exit 1; }
echo "fido e2e bytes: boundary-byte string round-trips EXACTLY through pinned Go via the fresh runner (0x00/0x1f/0x7f/0x80/0xff + newline)"; rm -rf "$BFRESH"

# --- EMPTY program: a rendered go.mod + ZERO .go files → `go build ./...` accepts (zero packages), via the runner. ---
[ -f /e2e/empty/go.mod ] || { echo "fido e2e empty: no rendered go.mod"; exit 1; }
[ -z "$(find /e2e/empty -name '*.go')" ] || { echo "fido e2e empty: unexpected .go file"; exit 1; }
fresh_go_build /e2e/empty EFRESH || { require_go_ran fresh-go-build; cat "${EFRESH:-/dev/null}/.build.err" 2>/dev/null; echo "fido e2e empty: go build ./... REJECTED a module with zero packages"; exit 1; }
echo "fido e2e empty: go build ./... accepted a module with zero packages via the fresh runner (rendered go.mod)"; rm -rf "$EFRESH"

# --- DIFFERENTIAL: the whole-program directory/package rules must agree with `go build ./...`, via the runner ---
[ -f /e2e/multi/go.mod ] || { echo "fido e2e diff: no rendered go.mod"; exit 1; }
echo "fido e2e diff: ACCEPTED multi-package tree (root main + sub/ main + empty file):"; ( cd /e2e/multi && find . -type f | sort )
if [ -n "$( cd /e2e/multi && gofmt -l . )" ]; then echo "fido e2e diff: multi tree not gofmt-clean"; ( cd /e2e/multi && gofmt -l . ); exit 1; fi
fresh_go_build /e2e/multi MFRESH || { require_go_ran fresh-go-build; cat "${MFRESH:-/dev/null}/.build.err" 2>/dev/null; echo "fido e2e diff: go build ./... REJECTED a GoCompile-ACCEPTED multi-package tree (model bug)"; exit 1; }
( cd "$MFRESH" && if ! go vet ./...; then echo "fido e2e diff: go vet reported diagnostics (nonblocking)"; fi )
# DISCOVERY: every emitted-file directory must be a package `go list ./...` actually selects (in the fresh root).
emitted_dirs=$( cd "$MFRESH" && find . -name '*.go' -exec dirname {} \; | sort -u )
listed_dirs=$( cd "$MFRESH" && go list -f '{{.Dir}}' ./... | sed "s#^$MFRESH#.#; s#^\.\$#.#" | sort -u )
echo "fido e2e diff: emitted dirs=[$(echo $emitted_dirs)] go-list dirs=[$(echo $listed_dirs)]"
[ "$emitted_dirs" = "$listed_dirs" ] || { echo "fido e2e diff: emitted package dirs != go list ./... selection"; rm -rf "$MFRESH"; exit 1; }
rm -rf "$MFRESH"
# (the no-main / duplicate-main rejections are the A-AD cases C/D/E/F below, routed through the fresh runner.)
# hand-written REJECTED integer-conversion fixtures (via the fresh runner): a constant conversion that overflows
# or converts a non-integer is rejected by `go build` EXACTLY as GoTypes makes impossible (a disagreement is a MODEL BUG).
rej_conv() { # <label> <main-body>
  d="/tmp/rej-conv-$1"; rm -rf "$d"; mkdir -p "$d"
  printf 'module rej\n\ngo 1.23\n' > "$d/go.mod"
  printf '// fido generated.  do not edit.\n\npackage main\n\nfunc main() {\n\t%s\n}\n' "$2" > "$d/x.go"
  _rc=0; fresh_go_build "$d" FR || _rc=$?
  _flog=$_FRESH_BUILD_LOG            # THIS run's log (empty on a setup/infra failure)
  require_go_ran "$1: $2"           # a setup/runner/fs/infra failure is NOT a Go rejection
  rm -rf "${FR:-/nonexistent}" 2>/dev/null || true
  [ "$_rc" != 0 ] || { echo "fido e2e diff: go build ./... ACCEPTED an invalid conversion [$1: $2] that GoTypes rejects (MODEL BUG)"; exit 1; }
  { [ -n "$_flog" ] && [ -s "$_flog" ]; } || { echo "fido e2e diff: [$1: $2] rejected but produced NO current-run build log"; exit 1; }
  # CLASS-SPECIFIC evidence in THIS run's log: a CONVERSION / TYPE-CHECK diagnostic (overflow / truncation /
  # cannot-convert / cannot-use / mismatched), not a collision, missing/dup main, or infra failure.
  grep -qiE 'overflow|truncated|cannot convert|cannot use|mismatched' "$_flog" \
    || { echo "fido e2e diff: [$1: $2] rejected but NOT with a conversion/type-check class:"; cat "$_flog"; exit 1; }
  echo "fido e2e diff: go build ./... (exit $_rc) rejects [$1] $2 with a conversion/type-check diagnostic — matches GoTypes"; }
rej_conv int8-over   'println(int8(128))'
rej_conv int8-under  'println(int8(-129))'
rej_conv uint8-neg   'println(uint8(-1))'
rej_conv uint8-over  'println(uint8(256))'
rej_conv int64-over  'println(int64(9223372036854775808))'
rej_conv uint64-over 'println(uint64(18446744073709551616))'
rej_conv nested-over 'println(uint8(int(300)))'
rej_conv conv-bool   'println(int8(true))'
rej_conv conv-str    'println(uint64("x"))'
# hand-written REJECTED float-conversion fixtures: F32/F64 overflow, a fractional/out-of-range float->int
# constant, and wrong-type conversions — all rejected by `go build` EXACTLY as GoTypes makes impossible.
rej_conv f32-over    'println(float32(1e39))'
rej_conv f64-over    'println(float64(1e309))'
rej_conv int-frac    'println(int(3.5))'
rej_conv int8-fl-over 'println(int8(128.0))'
rej_conv uint8-fl-neg 'println(uint8(-1.0))'
rej_conv f32-bool    'println(float32(true))'
rej_conv f64-str     'println(float64("x"))'
# hand-written REJECTED complex-conversion fixtures: a real / imaginary component overflow, a
# nonzero-imaginary or fractional/out-of-range complex->scalar conversion, and wrong-type complex conversions
# all rejected by `go build` EXACTLY as GoTypes/GoCompile make impossible (round_typed_complex component
# overflow / complex_real_if_imag_zero None / cross-kind reject).  A disagreement is a MODEL BUG.
rej_conv c64-real-over  'println(complex64(complex(1e39, 0)))'
rej_conv c64-imag-over  'println(complex64(complex(0, 1e39)))'
rej_conv c128-over      'println(complex128(complex(1e309, 0)))'
rej_conv int-of-cfrac   'println(int(complex(3.5, 0)))'
rej_conv int-of-cimag   'println(int(complex(3, 1)))'
rej_conv f32-of-cimag   'println(float32(complex(1.5, 1)))'
rej_conv c64-bool       'println(complex64(true))'
rej_conv c128-str       'println(complex128("x"))'
# §C0 complex-underflow scalar-conversion scar: 1e-50 is a nonzero exact rational that UNDERFLOWS binary32
# to +0.  The UNTYPED complex(3, 1e-50) has a nonzero imaginary, so int(...) is rejected; but the explicit
# complex64 boundary rounds that imaginary to exact zero, after which int(complex64(...)) is accepted as 3.
# Pinned Go 1.23 must agree with GoTypes on BOTH sides — the reject is a rej_conv, the accept-and-value-3 is
# an acc_conv (a standalone fixture, so the canonical witness/goldens are untouched).
rej_conv int-of-ctinyimag 'println(int(complex(3, 1e-50)))'
acc_conv() { # <label> <main-body> <expected-stderr>
  d="/tmp/acc-conv-$1"; rm -rf "$d"; mkdir -p "$d"
  printf 'module accm\n\ngo 1.23\n' > "$d/go.mod"
  printf '// fido generated.  do not edit.\n\npackage main\n\nfunc main() {\n\t%s\n}\n' "$2" > "$d/x.go"
  fresh_go_build "$d" FR || { require_go_ran fresh-go-build; rm -rf "$FR"; echo "fido e2e diff: go build ./... REJECTED [$1: $2] that GoTypes ACCEPTS (MODEL BUG)"; exit 1; }
  _e=$(find "$FR" -maxdepth 1 -type f -perm -u+x)
  { [ -n "$_e" ] && [ "$(printf '%s\n' "$_e" | wc -l)" = 1 ]; } || { echo "fido e2e diff: acc_conv [$1] produced not-exactly-one default exe [$_e]"; rm -rf "$FR"; exit 1; }
  _o=$("$_e" 2>&1 1>/dev/null)   # println writes to STDERR
  [ "$_o" = "$3" ] || { echo "fido e2e diff: [$1] printed [$_o] != Go-expected [$3] (MODEL/GOLDEN BUG)"; rm -rf "$FR"; exit 1; }
  rm -rf "$FR"; echo "fido e2e diff: go build ./... accepts + runs [$1] $2 -> $3 — matches GoTypes"; }
acc_conv int-of-c64-tinyimag 'println(int(complex64(complex(3, 1e-50))))' '3'

# ── FRESH-IMAGE DIRECTORY-COLLISION DIFFERENTIAL MATRIX.  `go build ./...` computes a SOLE main package's
#    default executable name and, if it is an EXISTING root DIRECTORY, FAILS before compiling (0 or >=2 main
#    packages write no default output).  GoCompile models exactly this (the fresh-build output preflight);
#    pinned go1.23 must AGREE — a disagreement is a MODEL BUG.  Every build runs through the ONE fresh-build runner.
cd /e2e
mk_tree() {  # <dir> <module-path> <rel-main.go>...
  _d=$1; _mp=$2; shift 2; rm -rf "$_d"; mkdir -p "$_d"
  printf 'module %s\n\ngo 1.23\n' "$_mp" > "$_d/go.mod"
  for _f in "$@"; do mkdir -p "$_d/$(dirname "$_f")"; printf 'package main\n\nfunc main() {}\n' > "$_d/$_f"; done
}
expect_reject() {  # <dir> <label> <expected-class-regex>
  _rc=0; fresh_go_build "$1" FR || _rc=$?
  _flog=$_FRESH_BUILD_LOG   # THIS run's log (empty on a setup/infra failure); captured before the root is removed
  require_go_ran "$2"       # a setup/runner/fs/infra failure is NOT a Go rejection
  rm -rf "${FR:-/nonexistent}" 2>/dev/null || true
  [ "$_rc" != 0 ] || { echo "fido e2e diff: go build ./... ACCEPTED $2 (GoCompile REJECTS — MODEL BUG)"; exit 1; }
  # CLASS-SPECIFIC evidence in THIS run's log: the failure must be exactly the expected class (directory
  # collision vs missing/dup main vs typing) — not merely nonzero (which a collision, a package-rule violation,
  # and a type error all share) and not an empty/stale log.
  [ -n "$3" ] || { echo "fido e2e diff: $2 — expect_reject called with no expected class regex (internal test error)"; exit 1; }
  { [ -n "$_flog" ] && [ -s "$_flog" ]; } || { echo "fido e2e diff: $2 — rejected but produced NO current-run build log"; exit 1; }
  grep -qiE "$3" "$_flog" || { echo "fido e2e diff: $2 — rejected but NOT with the expected class /$3/:"; cat "$_flog"; exit 1; }
  echo "fido e2e diff: go build ./... (exit $_rc) rejected $2 with the expected class /$3/ (matches GoCompile)"
}
expect_accept() {  # <dir> <label>
  fresh_go_build "$1" FR || { require_go_ran fresh-go-build; cat "${FR:-/dev/null}/.build.err" 2>/dev/null; rm -rf "$FR"; echo "fido e2e diff: go build ./... REJECTED $2 (GoCompile ACCEPTS — MODEL BUG)"; exit 1; }
  echo "fido e2e diff: go build ./... accepted $2 (matches GoCompile)"; rm -rf "$FR"
}
# 20.3 sole child sub/main.go: output "sub" collides with the root directory "sub" -> REJECT
mk_tree /tmp/dc-sub example.com/m sub/main.go;   expect_reject /tmp/dc-sub "sub/main.go (sole-main output sub = root dir sub)" 'directory|write output|cannot create'
# 20.6 a/v2/main.go: /v2 major-version element stripped -> output "a", root dir "a" exists -> REJECT
mk_tree /tmp/dc-av2 example.com/m a/v2/main.go;  expect_reject /tmp/dc-av2 "a/v2/main.go (output a after /v2 strip = root dir a)" 'directory|write output|cannot create'
# 20.2 root main.go: output "m" (module basename), no root dir "m" -> ACCEPT
mk_tree /tmp/dc-root example.com/m main.go;      expect_accept /tmp/dc-root "root main.go (output m, no collision)"
# 20.5 a/b/main.go: output "b", the root directory is "a" not "b" -> ACCEPT
mk_tree /tmp/dc-ab example.com/m a/b/main.go;    expect_accept /tmp/dc-ab "a/b/main.go (output b, root dir a)"
# 20.7 v2/main.go: output "m" (module basename, after /v2 strip), root dir "v2" -> ACCEPT
mk_tree /tmp/dc-v2 example.com/m v2/main.go;     expect_accept /tmp/dc-v2 "v2/main.go (output m, root dir v2)"
# 20.8 two main packages a/main.go + b/main.go: >=2 mains -> NO default output -> ACCEPT and write NO exe
mk_tree /tmp/dc-multi example.com/m a/main.go b/main.go
fresh_go_build /tmp/dc-multi FR || { require_go_ran fresh-go-build; cat "${FR:-/dev/null}/.build.err" 2>/dev/null; rm -rf "$FR"; echo "fido e2e diff: go build ./... REJECTED the two-main tree (MODEL BUG)"; exit 1; }
# a/ and b/ are the package DIRECTORIES; a default executable would be a REGULAR FILE named a or b (there is none).
{ [ ! -f "$FR/a" ] && [ ! -f "$FR/b" ]; } || { echo "fido e2e diff: a two-main go build ./... wrote a default executable (a/b) — unexpected"; ls -la "$FR"; rm -rf "$FR"; exit 1; }
echo "fido e2e diff: go build ./... accepted the two-main tree and wrote NO default executable (matches FBDDiscardMultiple)"; rm -rf "$FR"
# 20.10 / 20.11 — REGULAR-FILE OVERWRITE: a sole-main output name that is an existing REGULAR file (the root
#   go.mod, or the root source file) is NOT a directory collision -> ACCEPT; the sole-main build OVERWRITES that
#   fresh file with the executable, and the AUTHORITATIVE tree stays byte-identical (the runner builds in a
#   disposable copy — ).  A build-in-place design would corrupt the module/source.
overwrite_accept() {  # <dir> <module-path> <output-name-that-is-a-regular-file> <label>
  cp "$1/$3" /tmp/ov-auth
  fresh_go_build "$1" FR || { require_go_ran fresh-go-build; cat "${FR:-/dev/null}/.build.err" 2>/dev/null; rm -rf "$FR"; echo "fido e2e diff: go build ./... REJECTED $4 (GoCompile ACCEPTS — MODEL BUG)"; exit 1; }
  if cmp -s "$FR/$3" "$1/$3"; then echo "fido e2e diff: the fresh $3 was NOT overwritten by the sole-main build ($4)"; rm -rf "$FR"; exit 1; fi
  cmp -s /tmp/ov-auth "$1/$3" || { echo "fido e2e diff: the AUTHORITATIVE $3 was mutated by a fresh build ($4) — isolation broken"; rm -rf "$FR"; exit 1; }
  echo "fido e2e diff: go build ./... accepted $4, overwrote the FRESH $3, left the authoritative bytes intact (matches GoCompile)"; rm -rf "$FR"
}
mk_tree /tmp/ov-gomod example.com/go.mod  main.go; overwrite_accept /tmp/ov-gomod example.com/go.mod  go.mod  "the go.mod-overwrite tree (output go.mod = regular go.mod)"
mk_tree /tmp/ov-src   example.com/main.go main.go; overwrite_accept /tmp/ov-src   example.com/main.go main.go "the source-overwrite tree (output main.go = regular main.go)"

# ── A-AD — the COMPLETE required external differential matrix, every case through the ONE fresh runner.
#    Helpers for custom source + default-output-presence assertions.  A disagreement on a REPRESENTABLE case is
#    a MODEL BUG; the FUTURE-ORACLE cases (constructs Fido cannot yet emit — init/methods/generics/wrong sig/
#    var-main/mixed clauses/_test/_ignored/doc-only) pin the real pinned-go behaviour for when Fido supports them.
mk_gomod() { rm -rf "$1"; mkdir -p "$1"; printf 'module %s\n\ngo 1.23\n' "$2" > "$1/go.mod"; }
put()     { mkdir -p "$1/$(dirname "$2")"; printf '%b' "$3" > "$1/$2"; }   # <dir> <rel> <content-with-\n>
expect_accept_exe() {   # <dir> <label>: accept AND exactly ONE default executable at the fresh root
  fresh_go_build "$1" FR || { require_go_ran fresh-go-build; rm -rf "$FR"; echo "fido e2e diff: go build ./... REJECTED $2 (expected ACCEPT — MODEL BUG)"; exit 1; }
  _e=$(find "$FR" -maxdepth 1 -type f -perm -u+x)
  { [ -n "$_e" ] && [ "$(printf '%s\n' "$_e" | wc -l)" = 1 ]; } || { echo "fido e2e diff: $2 accepted but produced not-exactly-one default exe [$_e]"; rm -rf "$FR"; exit 1; }
  echo "fido e2e diff: go build ./... accepted $2 + wrote its default executable"; rm -rf "$FR"
}
expect_accept_noexe() { # <dir> <label>: accept AND NO default executable (0 or >=2 packages)
  fresh_go_build "$1" FR || { require_go_ran fresh-go-build; rm -rf "$FR"; echo "fido e2e diff: go build ./... REJECTED $2 (expected ACCEPT — MODEL BUG)"; exit 1; }
  _e=$(find "$FR" -maxdepth 1 -type f -perm -u+x)
  [ -z "$_e" ] || { echo "fido e2e diff: $2 wrote an UNEXPECTED default executable [$_e]"; rm -rf "$FR"; exit 1; }
  echo "fido e2e diff: go build ./... accepted $2 with NO default executable"; rm -rf "$FR"
}
# A. go.mod only -> success, no packages, no executable
mk_gomod /tmp/A example.com/m;                                        expect_accept_noexe /tmp/A "A: go.mod only (no packages)"
# B. valid root main, absent output -> success, executable created
mk_gomod /tmp/B example.com/m; put /tmp/B main.go 'package main\n\nfunc main() {}\n'
expect_accept_exe /tmp/B "B: valid root main (output m absent)"
# C. package main with no func main -> failure (output target not a directory: compile misses main)
mk_gomod /tmp/C example.com/m; put /tmp/C main.go 'package main\n\nvar _ = 0\n'
expect_reject /tmp/C "C: package main with no func main" 'undeclared|function main'
# D. duplicate main in one file -> failure
mk_gomod /tmp/D example.com/m; put /tmp/D main.go 'package main\n\nfunc main() {}\nfunc main() {}\n'
expect_reject /tmp/D "D: duplicate main in one file" 'redeclared'
# E. duplicate main across files -> failure
mk_gomod /tmp/E example.com/m; put /tmp/E main.go 'package main\n\nfunc main() {}\n'; put /tmp/E other.go 'package main\n\nfunc main() {}\n'
expect_reject /tmp/E "E: duplicate main across files" 'redeclared'
# F. three main declarations -> failure
mk_gomod /tmp/F example.com/m; put /tmp/F main.go 'package main\n\nfunc main() {}\nfunc main() {}\nfunc main() {}\n'
expect_reject /tmp/F "F: three main declarations" 'redeclared'
# G. two valid command packages -> success, default outputs discarded (no exe)
mk_gomod /tmp/G example.com/m; put /tmp/G a/main.go 'package main\n\nfunc main() {}\n'; put /tmp/G b/main.go 'package main\n\nfunc main() {}\n'
expect_accept_noexe /tmp/G "G: two valid command packages"
# H. valid and invalid package together -> failure (the invalid package fails to compile)
mk_gomod /tmp/H example.com/m; put /tmp/H a/main.go 'package main\n\nfunc main() {}\n'; put /tmp/H b/main.go 'package main\n\nfunc main() { var x int = "s"; _ = x }\n'
expect_reject /tmp/H "H: valid + invalid package together" 'cannot use|cannot convert|mismatched'
# I. empty file plus main elsewhere -> success (one main package: main.go + an extra source file)
mk_gomod /tmp/I example.com/m; put /tmp/I main.go 'package main\n\nfunc main() {}\n'; put /tmp/I extra.go 'package main\n'
expect_accept_exe /tmp/I "I: empty extra file + root main"
# Q. existing absent output -> create (== B, output name absent at root)
mk_gomod /tmp/Q example.com/mtool; put /tmp/Q main.go 'package main\n\nfunc main() {}\n'
expect_accept_exe /tmp/Q "Q: absent output name -> executable created"
# S. existing directory output -> reject (== J, covered above by dc-sub; restate distinctly)
mk_gomod /tmp/S example.com/m; put /tmp/S out/main.go 'package main\n\nfunc main() {}\n'
expect_reject /tmp/S "S: sole out/main.go, output out = existing root directory" 'directory|write output|cannot create'
# K. sole sub/main.go with an INVALID source: the directory-collision preflight takes PRECEDENCE over the
#    compile error (cmd/go checks the sole-main output BEFORE compiling), so the failure is the DIRECTORY
#    collision, NOT the type error — asserted through the fresh runner on the exact go stderr.
mk_gomod /tmp/K example.com/m; put /tmp/K sub/main.go 'package main\n\nfunc main() { _ = int8(300) }\n'
_rc=0; fresh_go_build /tmp/K FR || _rc=$?
_flog=$_FRESH_BUILD_LOG
require_go_ran "K sub/main.go+invalid-source"    # a setup/infra failure is NOT a Go rejection
# precedence: the build must fail with the DIRECTORY-COLLISION class, not the type error, proven from THIS run's log.
[ "$_rc" != 0 ] || { echo "fido e2e diff: K accepted a colliding invalid sub/main.go (MODEL BUG)"; rm -rf "$FR"; exit 1; }
{ [ -n "$_flog" ] && [ -s "$_flog" ]; } || { echo "fido e2e diff: K rejected but produced NO current-run build log"; rm -rf "$FR"; exit 1; }
if grep -qiE 'overflow|constant.*int8|cannot use|truncated' "$_flog"; then echo "fido e2e diff: K failed with the COMPILE error, not the directory collision (precedence violated):"; cat "$_flog"; rm -rf "$FR"; exit 1; fi
grep -qiE 'directory|write output|cannot create' "$_flog" || { echo "fido e2e diff: K failed but not with a recognizable directory-collision class:"; cat "$_flog"; rm -rf "$FR"; exit 1; }
echo "fido e2e diff: K sub/main.go+invalid-source -> DIRECTORY-COLLISION failure (precedence over the type error, matches GoCompile)"; rm -rf "$FR"

# --- FUTURE ORACLES (Fido cannot yet emit these constructs; pin the pinned-go behaviour). ---
# T. two init functions plus valid main -> success
mk_gomod /tmp/T example.com/m; put /tmp/T main.go 'package main\n\nfunc init() {}\nfunc init() {}\nfunc main() {}\n'
expect_accept_exe /tmp/T "T (future): two init + main"
# U. method named main without package-level main -> missing-entry failure
mk_gomod /tmp/U example.com/m; put /tmp/U main.go 'package main\n\ntype T struct{}\nfunc (T) main() {}\n'
expect_reject /tmp/U "U (future): method main, no package-level main" 'undeclared|no main|function main'
# V. method named main plus package-level main -> success
mk_gomod /tmp/V example.com/m; put /tmp/V main.go 'package main\n\ntype T struct{}\nfunc (T) main() {}\nfunc main() {}\n'
expect_accept_exe /tmp/V "V (future): method main + package main"
# W. wrong-signature main -> failure
mk_gomod /tmp/W example.com/m; put /tmp/W main.go 'package main\n\nfunc main(x int) {}\n'
expect_reject /tmp/W "W (future): wrong-signature main" 'must have no arguments|no return values'
# X. generic main -> failure
mk_gomod /tmp/X example.com/m; put /tmp/X main.go 'package main\n\nfunc main[T any]() {}\n'
expect_reject /tmp/X "X (future): generic main" 'type parameter'
# Y. var named main (no func main) -> failure
mk_gomod /tmp/Y example.com/m; put /tmp/Y main.go 'package main\n\nvar main = 0\n'
expect_reject /tmp/Y "Y (future): var named main, no func main" 'cannot declare main|must be func'
# Z. mixed package clauses in one directory -> package-load failure (before output preflight)
mk_gomod /tmp/Z example.com/m; put /tmp/Z a.go 'package main\n\nfunc main() {}\n'; put /tmp/Z b.go 'package other\n'
expect_reject /tmp/Z "Z (future): mixed package clauses in one dir" 'found packages|expected package'
# AA. _test.go duplicate main only -> ignored by build (the _test.go is not a build input) -> success
mk_gomod /tmp/AA example.com/m; put /tmp/AA main.go 'package main\n\nfunc main() {}\n'; put /tmp/AA main_test.go 'package main\n\nfunc main() {}\n'
expect_accept_exe /tmp/AA "AA (future): _test.go duplicate main ignored"
# AB. _ignored.go duplicate main only -> ignored (leading underscore file excluded by go tooling) -> success
mk_gomod /tmp/AB example.com/m; put /tmp/AB main.go 'package main\n\nfunc main() {}\n'; put /tmp/AB _ignored.go 'package main\n\nfunc main() {}\n'
expect_accept_exe /tmp/AB "AB (future): _ignored.go duplicate main ignored"
# AC. package documentation only (a non-main package with just a package clause) -> compiled, no selected main, no exe
mk_gomod /tmp/AC example.com/m; put /tmp/AC doc/doc.go '// Package doc documents nothing.\npackage doc\n'
expect_accept_noexe /tmp/AC "AC (future): documentation-only package (no main selected)"
# AD. two modules, EQUAL file layout, DIFFERENT module basename -> DIFFERENT default output names / plans
mk_gomod /tmp/AD1 example.com/aa; put /tmp/AD1 v2/main.go 'package main\n\nfunc main() {}\n'
mk_gomod /tmp/AD2 example.com/bb; put /tmp/AD2 v2/main.go 'package main\n\nfunc main() {}\n'
fresh_go_build /tmp/AD1 FR1 || { require_go_ran fresh-go-build; rm -rf "$FR1"; echo "fido e2e diff: AD1 rejected (MODEL BUG)"; exit 1; }
fresh_go_build /tmp/AD2 FR2 || { require_go_ran fresh-go-build; rm -rf "$FR1" "$FR2"; echo "fido e2e diff: AD2 rejected (MODEL BUG)"; exit 1; }
_n1=$(basename "$(find "$FR1" -maxdepth 1 -type f -perm -u+x)"); _n2=$(basename "$(find "$FR2" -maxdepth 1 -type f -perm -u+x)")
[ "$_n1" = aa ] && [ "$_n2" = bb ] && [ "$_n1" != "$_n2" ] || { echo "fido e2e diff: AD default exe names [$_n1] [$_n2] not the distinct module basenames aa/bb"; rm -rf "$FR1" "$FR2"; exit 1; }
echo "fido e2e diff: AD equal-layout different-module -> distinct default output names ($_n1 vs $_n2) — matches the ModuleSpec-dependent plan"; rm -rf "$FR1" "$FR2"
echo "fido e2e diff: A-AD differential matrix COMPLETE (representable cases match GoCompile; future oracles pinned)"
cd /e2e/tree

echo "fido e2e OK — pinned Go built the whole tree in a fresh copy (go build ./...) with the RENDERED go.mod, accepted the empty module, ran the witness vs goldens (ten integer conversions + the float + complex sections incl. the double-round scars), checked the multi-package + go-list differential, rejected the no-main/dup-main + out-of-range/non-integer/float-overflow/fractional/wrong-type/complex-overflow/nonzero-imaginary fixtures exactly as GoCompile does, and confirmed the fresh-image directory-collision differential matrix (go vet nonblocking)"
# The FRESH-BUILD-OK Docker DAG edge — a tiny marker written ONLY after every check above passed.  It carries no
# bytes or digest and proves nothing on its own; it exists only so the `sync` image (below) cannot build unless
# this go-e2e stage completed successfully (validate-before-publish for the supported workflow).
: > /fresh-build-ok
SH

# ── Stage 4d (defined last): sync — the `make regenerate` image.  It compiles the tiny internal filesystem
#    adapter (linking Fido_sink) and bakes in the pristine `generated-module` layer; run with the repo root
#    bind-mounted at /dest, its ENTRYPOINT synchronizes /generated into /dest through the sink.  It never
#    re-generates or renders.  VALIDATE-BEFORE-PUBLISH: it COPYs the go-e2e /fresh-build-ok DAG edge, so building
#    `sync` FORCES go-e2e (the pinned `go build ./...`) to succeed first — a failing fresh build makes this stage
#    unbuildable — and it publishes the ORIGINAL generated-module layer, never a go-e2e build directory.
FROM emit AS sync
COPY --from=go-e2e /fresh-build-ok /fresh-build-ok
RUN cp /workspace/plugin/fido_sink.ml /workspace/e2e/fido_apply.ml /tmp/ \
    && ( cd /tmp && ocamlfind ocamlopt -package unix -linkpkg fido_sink.ml fido_apply.ml -o /workspace/fido-apply ) \
    && chmod 0755 /workspace/fido-apply
COPY --from=generated-module /generated/ /generated/
ENTRYPOINT ["/workspace/fido-apply", "/dest"]
