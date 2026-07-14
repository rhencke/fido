# syntax=docker/dockerfile:1

# Fido — GoProgram (ModuleSpec + a possibly-empty finite map of intrinsic FilePath keys to raw file ASTs)
# -> GoCompile (whole-program, +CompilationFacts) -> GoSafe -> GoRender (incl. the go.mod) -> the complete
# DirectoryImage (exact go.mod bytes + the .go map), then the general `Fido Emit` transport command + a
# dirty-directory filesystem sink + the pinned Go toolchain.  Stages: (prover) dune-compiles the theory and
# the always-run assumptions gate confirms every declared surface axiom-free; (emit) dune compiles
# theory+plugin (shared cache), then explicitly runs `Fido Emit` (rocq c on the witnesses) to synchronize
# each tree, and exercises the sink on dirty/adversarial trees (local staging + records, foreign-Go
# rejection, record-driven recovery); (go-e2e) the pinned Go toolchain runs `go build ./...` over the whole
# tree — using the RENDERED go.mod — and runs the witness vs goldens.

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
# `make prove` is the COMPLETE proof gate (contract §2): Dune builds the theory AND the audit/transport
# plugin; then the readable Print-Assumptions surfaces, the certified-module coverage check, the WHOLE-
# certified-theory assumption-closure audit (over constants + mutual INDUCTIVES + surviving named
# assumptions, descending opaque Qed bodies, rejecting every Printer.Axiom category AND Printer.Variable),
# and the adversarial audit self-tests A-E all run HERE — so a retained internal declaration that depends on
# an assumption fails `make prove` even when it is not a selected public theorem and emission never runs.
RUN --mount=type=cache,id=fido-dune-rocq-9.2.0-${TARGETARCH},uid=1000,gid=1000,target=/workspace/_build,sharing=locked <<'SH'
set -eu
fail() { echo "fido: prove FAILED — $*"; exit 1; }
# (a) Dune builds the certified theory AND the audit/transport plugin (one shared cache id with emit/e2e)
if ! dune build @install > /tmp/build.log 2>&1; then cat /tmp/build.log; fail "dune build FAILED"; fi
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

# ── Stage 4: emit — Dune compiles the theory AND the Fido Emit transport plugin (one shared cache id with
#    the prover stage).  Then, in EXPLICIT always-run steps (never Dune .vo side effects): the general
#    `Fido Emit` command (rocq c on the witnesses) decodes a proved DirectoryImage — the exact go.mod bytes
#    plus the .go map — and the sink SYNCHRONIZES each tree (witness, multi-package, and the EMPTY module);
#    the emit-time assumption-closure guard rejects TRANSIENTLY-generated forged images (never tracked);
#    and a standalone driver exercises the dirty-directory sink: clean/dirty sync, foreign-Go/module and
#    nested-.fido REJECTION (§8), sibling `.fido-tmp-v1` staging with two-phase (inspect-then-delete)
#    abandoned-temp recovery (regular/forged temps removed; symlink/dir/special temps fail-closed and
#    preserved), complete-image staging before install, crash points (writing / staged / installing) that
#    leave the lock + temps for a rerun, handled-failure + cleanup-failure aggregation, EXDEV no-copy, and
#    overwrite + delete-time ownership rechecks.  The plugin guards provenance (typecheck +
#    assumption-closure) then decodes only the final (go.mod, entries) transport; it walks no program.
FROM rocq-base AS emit
ARG TARGETARCH
COPY --chown=opam:opam dune-project dune ./
COPY --chown=opam:opam *.v ./
COPY --chown=opam:opam gate/ gate/
COPY --chown=opam:opam plugin/ plugin/
COPY --chown=opam:opam e2e/ e2e/
# pre-create the cross-mount test root as the emit (opam) user, so it stays opam-owned when the RUN below
# mounts a distinct-device (opam-owned) cache at its nested `sub/` parent — the real cross-mount §26 gate.
RUN mkdir -p /workspace/adv-mount
RUN --mount=type=cache,id=fido-dune-rocq-9.2.0-${TARGETARCH},uid=1000,gid=1000,target=/workspace/_build,sharing=locked --mount=type=cache,id=fido-crossmnt-${TARGETARCH},uid=1000,gid=1000,sharing=private,target=/workspace/adv-mount/sub <<'SH'
set -eu
fail() { echo "fido: emit FAILED — $*"; exit 1; }
rm -rf /workspace/e2e-out /workspace/e2e-multi /workspace/e2e-empty /workspace/e2e-forge* /workspace/e2e-neg /workspace/adv-* /workspace/sreal /workspace/slink /workspace/sink_test 2>/dev/null || true
O=/workspace/e2e-out
# cached: Dune compiles the proved theory + the transport plugin (shared cache id)
if ! dune build @install > /tmp/emit-build.log 2>&1; then cat /tmp/emit-build.log; fail "theory/plugin build FAILED"; fi
export OCAMLPATH=/workspace/_build/install/default/lib:${OCAMLPATH:-}

# --- the general Fido Emit transport synchronizes each witness tree (go.mod + .go files) ---
if ! rocq c -Q _build/default/. Fido e2e/Witness.v > /tmp/emit.log 2>&1; then cat /tmp/emit.log; fail "Fido Emit FAILED"; fi
cat /tmp/emit.log
[ -f "$O/go.mod" ]  || fail "the emitted tree has no rendered go.mod"
[ -f "$O/main.go" ] || fail "the emitted tree has no main.go"
[ -d "$O/.fido" ]   || fail "the emission left no marked control directory"
echo "fido: emitted tree:"; echo ----; ( cd "$O" && find . -type f | sort ); echo ----; cat "$O/go.mod"; echo ----; cat "$O/main.go"; echo ----
# the go.mod is the Rocq-rendered module file (header first line, exact module/go directives)
head -1 "$O/go.mod" | grep -q '^// fido generated' || fail "rendered go.mod is not Fido-headed"
grep -qx 'module fido.local/generated' "$O/go.mod" || { cat "$O/go.mod"; fail "rendered go.mod module directive unexpected"; }
grep -qx 'go 1.23' "$O/go.mod" || { cat "$O/go.mod"; fail "rendered go.mod go directive unexpected"; }

# --- assemble the PRISTINE canonical generated module (contract §17): exactly the witness go.mod + its
#     recursive .go files, with NO .fido / lock / temp / proof / fixture bytes.  The `generated-module`
#     scratch stage copies THIS directory into an ordinary content-addressed layer (never a cache mount);
#     go-e2e, staged verification, and `make regenerate` all consume that single layer. ---
G=/workspace/generated; rm -rf "$G"; mkdir -p "$G"
cp "$O/go.mod" "$G/go.mod"
( cd "$O" && find . -name '*.go' -not -path './.fido/*' | while read -r f; do
    d=$(dirname "$f"); [ "$d" = "." ] || mkdir -p "$G/$d"; cp "$f" "$G/$f"; done )
[ -f "$G/go.mod" ] || fail "generated: the pristine module has no go.mod"
[ -z "$(find "$G" -name '.fido*' -o -name '*.fido-tmp-v1')" ] || fail "generated: control/temp residue leaked into the pristine module"
[ "$(find "$G" -name '*.go' | wc -l)" -ge 1 ] || fail "generated: the pristine canonical module has no .go file"
echo "fido: pristine generated-module tree:"; ( cd "$G" && find . -type f | sort )

# differential witness: TWO main packages (root + sub/) + an empty file + the rendered go.mod
if ! rocq c -Q _build/default/. Fido e2e/WitnessMulti.v > /tmp/emit-multi.log 2>&1; then cat /tmp/emit-multi.log; fail "Fido Emit (multi-package) FAILED"; fi
{ [ -f /workspace/e2e-multi/go.mod ] && [ -f /workspace/e2e-multi/main.go ] && [ -f /workspace/e2e-multi/extra.go ] && [ -f /workspace/e2e-multi/sub/main.go ]; } || fail "multi-package tree incomplete"
echo "fido: multi-package tree:"; ( cd /workspace/e2e-multi && find . -type f | sort )

# empty-program witness: a valid module with NO source files → go.mod and zero .go
if ! rocq c -Q _build/default/. Fido e2e/WitnessEmpty.v > /tmp/emit-empty.log 2>&1; then cat /tmp/emit-empty.log; fail "Fido Emit (empty program) FAILED"; fi
[ -f /workspace/e2e-empty/go.mod ] || fail "empty program emitted no go.mod"
[ -z "$(find /workspace/e2e-empty -name '*.go')" ] || fail "empty program emitted a .go file"
echo "fido: empty-program tree:"; ( cd /workspace/e2e-empty && find . -type f | sort )

# provenance (1): a forged raw transport (not a DirectoryImage) is rejected BEFORE any effect (Fail fixtures)
if ! rocq c -Q _build/default/. Fido e2e/WitnessNeg.v > /tmp/emit-neg.log 2>&1; then cat /tmp/emit-neg.log; fail "a forged raw transport was NOT rejected"; fi
[ ! -e /workspace/e2e-neg ] || fail "a rejected Fido Emit still created its target directory"

# provenance (2): a FORGED image — the right TYPE but a non-empty assumption closure — is rejected by the
# emit-time closure check BEFORE any effect.  The axiom/variable-bearing fixtures are GENERATED TRANSIENTLY
# here (never tracked — the repo policy is zero project axioms): a DIRECT axiom, an axiom behind an opaque
# Qed proof, a DIRECT section variable, and a TRANSITIVE section variable.  Each runs WITHOUT `Fail` (which
# absorbs the message in batch mode), so `rocq c` errors and we assert the rejection REASON + no target.
mkdir -p /tmp/forge
cat > /tmp/forge/preamble <<'EOF'
From Stdlib Require Import List String.
From Fido Require Import FilePath FMap ModulePath GoVersion GoAST GoCompile GoSafe GoRender GoEmit.
Import ListNotations.
Definition fgm : string := "forged"%string.
Definition ff : fmap FilePath string := fm_singleton (mkFP "main.go" eq_refl) "forged"%string.
EOF
cat /tmp/forge/preamble - > /tmp/forge/Direct.v <<'EOF'
Axiom p : exists sp, fgm = render_go_mod_of sp /\ ff = render_map sp.
Definition img : DirectoryImage := mkImage fgm ff p.
Declare ML Module "fido.emit".
Fido Emit img To "/workspace/e2e-forge".
EOF
cat /tmp/forge/preamble - > /tmp/forge/Opaque.v <<'EOF'
Axiom a : exists sp, fgm = render_go_mod_of sp /\ ff = render_map sp.
Lemma p : exists sp, fgm = render_go_mod_of sp /\ ff = render_map sp. Proof. exact a. Qed.
Definition img : DirectoryImage := mkImage fgm ff p.
Declare ML Module "fido.emit".
Fido Emit img To "/workspace/e2e-forge-op".
EOF
cat /tmp/forge/preamble - > /tmp/forge/Var.v <<'EOF'
Declare ML Module "fido.emit".
Section S.
Variable p : exists sp, fgm = render_go_mod_of sp /\ ff = render_map sp.
Definition img : DirectoryImage := mkImage fgm ff p.
Fido Emit img To "/workspace/e2e-forge-var".
End S.
EOF
cat /tmp/forge/preamble - > /tmp/forge/VarIndirect.v <<'EOF'
Declare ML Module "fido.emit".
Section S.
Variable v : exists sp, fgm = render_go_mod_of sp /\ ff = render_map sp.
Definition q : exists sp, fgm = render_go_mod_of sp /\ ff = render_map sp := v.
Definition img : DirectoryImage := mkImage fgm ff q.
Fido Emit img To "/workspace/e2e-forge-vi".
End S.
EOF
forge_reject() {   # <file> <target-dir> <label>
  if rocq c -Q _build/default/. Fido "$1" > /tmp/emit-forge.log 2>&1; then cat /tmp/emit-forge.log; fail "$3: a forged image was NOT rejected"; fi
  grep -q 'provenance depends on an axiom' /tmp/emit-forge.log || { cat /tmp/emit-forge.log; fail "$3: rejected, but NOT by the assumption-closure check (wrong reason)"; }
  [ ! -e "$2" ] || fail "$3: a rejected forged emit still created its target directory"
  echo "fido: provenance enforced — $3 rejected before any effect"
}
forge_reject /tmp/forge/Direct.v      /workspace/e2e-forge     "direct axiom"
forge_reject /tmp/forge/Opaque.v      /workspace/e2e-forge-op  "axiom behind an opaque Qed proof"
forge_reject /tmp/forge/Var.v         /workspace/e2e-forge-var "direct section variable"
forge_reject /tmp/forge/VarIndirect.v /workspace/e2e-forge-vi  "transitive section variable"

# The complete whole-certified-theory assumption audit + coverage + adversarial self-tests A-E now run in
# the `prover` stage (contract §2: `make prove` is the complete proof gate) — they are NOT duplicated here.
# This stage keeps only the emit-time provenance guard above and the dirty-directory sink exercise below.

# --- exercise the dirty-directory sink directly (local per-parent staging + records + foreign rejection) ---
cp plugin/fido_sink.ml e2e/sink_test.ml /tmp/
if ! ( cd /tmp && ocamlfind ocamlopt -package unix -linkpkg fido_sink.ml sink_test.ml -o /workspace/sink_test ) > /tmp/sink.log 2>&1; then cat /tmp/sink.log; fail "sink_test compile FAILED"; fi
cd /workspace
hdr=$(head -1 "$O/go.mod")     # DERIVE the ownership header from actual emitted output (no hardcoded literal)
temps() { find "$1" -name '*.fido-tmp-v1' 2>/dev/null; }   # any reserved sibling temp = residue
residue() { temps "$1"; }

# ============================ Clean / dirty sync ============================
# clean sync → rendered go.mod + main.go + control marker (marker + optional lock only); no temp residue.
# (sink_test itself byte-verifies each installed file against its own staged bytes on every successful sync.)
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
# a REGULAR foreign file using the reserved suffix is INTENTIONALLY classified Fido-owned and removed
# (public, forgeable convention — an accepted tradeoff under the single-owner threat model).
mkdir -p adv-tforge; ./sink_test adv-tforge || fail "tforge: init"
printf 'not really fido\n' > adv-tforge/hand-written.fido-tmp-v1
./sink_test adv-tforge || fail "tforge: sync failed with a forged reserved-suffix temp"
[ ! -e adv-tforge/hand-written.fido-tmp-v1 ] || fail "tforge: a regular reserved-suffix file was not collected+removed"

# ============================ Reserved path + prefix symlink (rejected before any effect) ============================
if ./sink_test /workspace/adv-resv reserved; then fail "a desired path inside .fido was NOT rejected"; fi
[ ! -e /workspace/adv-resv ] || fail "a reserved-path rejection created the root (effect before validation)"
mkdir -p /workspace/sreal; printf 'x\n' > /workspace/sreal/keep; ln -s /workspace/sreal /workspace/slink
if ./sink_test /workspace/slink/child; then fail "wrote through a prefix symlink"; fi
[ ! -e /workspace/sreal/child ] || fail "a prefix symlink created a child in the referent"

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
# a cleanup failure reports BOTH the initiating body error AND the cleanup error, then a clean rerun converges.
mkdir -p adv-cuf
if out=$(./sink_test adv-cuf fail-after-first-payload+unlink-fail 2>&1); then fail "cuf: the compound failure was not surfaced"; fi
echo "$out" | grep -q 'injected handled failure' || { echo "$out"; fail "cuf: the initiating body error was hidden"; }
echo "$out" | grep -q 'cleanup FAILED' || { echo "$out"; fail "cuf: the cleanup failure was not reported"; }
[ ! -e adv-cuf/.fido/index.lock ] || fail "cuf: the lock was not released after a cleanup failure"
rm -f adv-cuf/*.fido-tmp-v1; ./sink_test adv-cuf || fail "cuf: no converge after removing residue"

# ============================ Crash / recovery ============================
# crash WHILE WRITING leaves lock + a PARTIAL temp; crash AFTER STAGING leaves lock + ALL temps + old finals;
# crash DURING INSTALL leaves lock + mixed finals + remaining temps.  Each: a rerun REFUSES on the held lock;
# after the stale lock is deliberately cleared, a rerun removes the temps and converges.
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
crash_recover crash-after-first-payload writing
crash_recover crash-after-staging       staged
crash_recover crash-after-first-install installing

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

echo "fido: emit OK — general Fido Emit synced the witness / multi-package / EMPTY trees (rendered go.mod); forged images rejected; sink foreign-Go/module + nested-.fido rejection, sibling-temp two-phase recovery (abandoned/forged/symlink/dir/special temps), complete-image staging, crash points (writing/staged/installing), handled-failure + cleanup-failure aggregation, EXDEV no-copy, overwrite + delete-time ownership rechecks, first-time rollback, and REAL cross-mount nested staging all pass"
SH

# ── Stage 4b: generated-module — ONE ordinary content-addressed layer holding EXACTLY the pristine canonical
#    generated module (contract §17): /generated/go.mod + /generated/**/*.go, no .fido/lock/temp/proof/
#    fixture bytes.  Its cache key derives from the emit stage's authoritative generation inputs (certified
#    .v, dune, plugin, pinned toolchain, canonical witness) — NEVER from the committed generated bytes.  Every
#    canonical-output workflow (go-e2e, staged-index verification, `make regenerate`) consumes THIS layer.
FROM scratch AS generated-module
COPY --from=emit /workspace/generated/ /generated/

# ── Stage 4c: generated-artifact — the pristine module at the image root (for local export / bind-apply).
FROM scratch AS generated-artifact
COPY --from=generated-module /generated/ /

# ── Stage 4d: sync — the `make regenerate` image.  It compiles the filesystem-only apply CLI (linking the
#    SAME Fido_sink) and bakes in the pristine `generated-module` layer; run with the repository root
#    bind-mounted at /dest, its ENTRYPOINT synchronizes /generated into /dest through the sink (preserving
#    foreign non-Go files, rejecting foreign Go/module + nested .fido, updating tracked go.mod + .go,
#    removing stale Fido-owned .go).  It never re-generates and never renders.
FROM emit AS sync
RUN cp /workspace/plugin/fido_sink.ml /workspace/e2e/fido_apply.ml /tmp/ \
    && ( cd /tmp && ocamlfind ocamlopt -package unix -linkpkg fido_sink.ml fido_apply.ml -o /workspace/fido-apply ) \
    && chmod 0755 /workspace/fido-apply
COPY --from=generated-module /generated/ /generated/
ENTRYPOINT ["/workspace/fido-apply", "/generated", "/dest"]

# ── Stage 5: go-e2e — the LAST-MILE integration check (never a proof).  The pinned Go toolchain builds the
#    canonical generated module (consumed from the `generated-module` layer, NOT re-generated here) with
#    `go build ./...` using the Rocq-RENDERED go.mod, and runs the witness package; stdout/stderr/exit must
#    match the reviewed goldens.  `go build ./...` is the blocking compiler-acceptance alarm; `go vet` is
#    DIAGNOSTIC ONLY (nonblocking).  A build/run failure here is a hard red — GoCompile/rendering/transport
#    is wrong, never a known issue.
FROM golang:1.23-alpine@sha256:383395b794dffa5b53012a212365d40c8e37109a626ca30d6151c8348d380b5f AS go-e2e
WORKDIR /e2e
COPY --from=generated-module /generated/ ./tree/
COPY --from=emit /workspace/e2e-multi/ ./multi/
COPY --from=emit /workspace/e2e-empty/ ./empty/
COPY e2e/golden.stdout e2e/golden.stderr e2e/golden.exit ./
RUN <<'SH'
set -u
# closed-world integration: force the local pinned toolchain, no workspace, no network proxy
export GOWORK=off GOTOOLCHAIN=local GOPROXY=off
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

# --- EMPTY program: a rendered go.mod and ZERO .go files → `go build ./...` accepts (zero packages) ---
cd /e2e/empty
[ -f go.mod ] || { echo "fido e2e empty: no rendered go.mod"; exit 1; }
[ -z "$(find . -name '*.go')" ] || { echo "fido e2e empty: unexpected .go file"; exit 1; }
if ! go build ./... 2> empty.err; then cat empty.err; echo "fido e2e empty: go build ./... REJECTED a module with zero packages"; exit 1; fi
echo "fido e2e empty: go build ./... accepted a module with zero packages (rendered go.mod)"

# --- DIFFERENTIAL: the whole-program directory/package rules must agree with `go build ./...` ---
cd /e2e/multi
[ -f go.mod ] || { echo "fido e2e diff: no rendered go.mod"; exit 1; }
echo "fido e2e diff: ACCEPTED multi-package tree (root main + sub/ main + empty file):"; find . -type f | sort
if [ -n "$(gofmt -l .)" ]; then echo "fido e2e diff: multi tree not gofmt-clean"; gofmt -l .; exit 1; fi
if ! go vet ./...; then echo "fido e2e diff: go vet reported diagnostics (nonblocking)"; fi
go build ./... || { echo "fido e2e diff: go build ./... REJECTED a GoCompile-ACCEPTED multi-package tree (model bug)"; exit 1; }
# DISCOVERY: every emitted-file directory must be a package `go list ./...` actually selects.
emitted_dirs=$(find . -name '*.go' -exec dirname {} \; | sort -u)
listed_dirs=$(go list -f '{{.Dir}}' ./... | sed "s#^$(pwd)#.#; s#^\.\$#.#" | sort -u)
echo "fido e2e diff: emitted dirs=[$(echo $emitted_dirs)] go-list dirs=[$(echo $listed_dirs)]"
[ "$emitted_dirs" = "$listed_dirs" ] || { echo "fido e2e diff: emitted package dirs != go list ./... selection"; exit 1; }
# hand-written REJECTED fixtures: `go build ./...` must reject exactly what GoCompile makes impossible
mkdir -p /tmp/rej-nomain && cd /tmp/rej-nomain && printf 'module rej\n\ngo 1.23\n' > go.mod
printf '// fido generated.  do not edit.\n\npackage main\n' > x.go   # a main package with NO func main
if go build ./... 2>/dev/null; then echo "fido e2e diff: go build accepted a package with no main (GoCompile rejects this)"; exit 1; fi
echo "fido e2e diff: a no-main package is rejected by go build (matches GoCompile: exactly one main per package)"
mkdir -p /tmp/rej-dup && cd /tmp/rej-dup && printf 'module rej\n\ngo 1.23\n' > go.mod
printf '// fido generated.  do not edit.\n\npackage main\n\nfunc main() {}\nfunc main() {}\n' > x.go   # duplicate main
if go build ./... 2>/dev/null; then echo "fido e2e diff: go build accepted duplicate main (GoCompile rejects this)"; exit 1; fi
echo "fido e2e diff: duplicate main is rejected by go build (matches GoCompile)"

echo "fido e2e OK — pinned Go built the whole tree (go build ./...) using the RENDERED go.mod, accepted the empty module, ran the witness vs goldens, checked the multi-package differential + go list discovery, and rejected the no-main/dup-main fixtures exactly as GoCompile does (go vet nonblocking)"
SH

# ── Stage 6: verify-staged-generated — the PRE-COMMIT staged-index check (contract §23).  The hook exports
#    the Git INDEX once and hands THAT staged tree as the Buildx context; this stage rebuilds the pristine
#    `generated-module` from the staged proof/generation inputs and compares the STAGED root go.mod + every
#    staged recursive .go against /generated — EXACT relative path set AND exact bytes, both directions
#    (modified bytes, a missing staged file, a newly-generated file absent from the index, or a stale staged
#    file all fail).  It reads only the staged tree (never the unstaged working tree) and never auto-stages.
FROM golang:1.23-alpine@sha256:383395b794dffa5b53012a212365d40c8e37109a626ca30d6151c8348d380b5f AS verify-staged-generated
WORKDIR /v
COPY --from=generated-module /generated/ ./pristine/
COPY . ./staged/
RUN <<'SH'
set -eu
cd /v
[ -f staged/go.mod ] || { echo "fido: STAGED-GENERATED — the proposed commit has no tracked root go.mod"; exit 1; }
mkdir -p staged-gen; cp staged/go.mod staged-gen/go.mod
( cd staged && find . -name '*.go' -type f | while IFS= read -r f; do
    d=$(dirname "$f"); [ "$d" = "." ] || mkdir -p "/v/staged-gen/$d"; cp "$f" "/v/staged-gen/$f"; done )
mism=0
# every pristine file must be present + byte-identical in the staged generated set
for f in $(cd pristine && find . -type f | LC_ALL=C sort); do
  if ! cmp -s "pristine/$f" "staged-gen/$f"; then echo "fido: STAGED-GENERATED MISMATCH — $f (modified bytes, or missing from the index)"; mism=1; fi
done
# no staged generated file may exist that certified generation does not produce (stale)
for f in $(cd staged-gen && find . -type f | LC_ALL=C sort); do
  [ -f "pristine/$f" ] || { echo "fido: STAGED-GENERATED MISMATCH — $f is staged but not produced by certified generation (stale)"; mism=1; }
done
if [ "$mism" -ne 0 ]; then
  echo "fido: the staged generated module does not byte-match the pristine certified build."
  echo "      Run:  make regenerate && git add -A -- go.mod ':(top,glob)**/*.go' && git commit"
  exit 1
fi
echo "fido: staged-generated verify OK — the staged root go.mod + recursive .go byte-match /generated (exact path set + bytes)"
SH
