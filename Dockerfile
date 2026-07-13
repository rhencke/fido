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

# ── Stage 4: emit — Dune compiles the theory AND the Fido Emit transport plugin (one shared cache id with
#    the prover stage).  Then, in EXPLICIT always-run steps (never Dune .vo side effects): the general
#    `Fido Emit` command (rocq c on the witnesses) decodes a proved DirectoryImage — the exact go.mod bytes
#    plus the .go map — and the sink SYNCHRONIZES each tree (witness, multi-package, and the EMPTY module);
#    the emit-time assumption-closure guard rejects TRANSIENTLY-generated forged images (never tracked);
#    and a standalone driver exercises the dirty-directory sink: clean/dirty sync, foreign-Go/module
#    REJECTION (§9), local per-parent staging with root-owned records, record-driven recovery of crashed
#    residue at every point, malformed/escaping/mismatched/symlinked-stage records fail-closed, a nonce
#    collision aborts preserving the colliding entry, and a cleanup/recovery unlink failure is surfaced then
#    converges.  The plugin guards provenance (typecheck + assumption-closure) then decodes only the final
#    (go.mod, entries) transport; it walks no program.
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

# --- SOUND zero-project-axiom audit: enumerate the compiled global env (not a text scanner).  The set of
#     modules loaded (hence audited) is DERIVED from dune's authoritative (modules ...) list, so a new
#     theory module cannot silently escape the audit. ---
mods=$(sed -n 's/.*(modules \([^)]*\)).*/\1/p' dune)
[ -n "$mods" ] || fail "could not read the (modules ...) list from dune"
{ printf 'From Fido Require Import %s.\n' "$mods"
  printf 'Declare ML Module "fido.emit".\n'
  printf 'Fido Audit Assumptions.\n'; } > /tmp/assumptions_audit.v
echo "fido: assumption audit covers (from dune): $mods"
if ! rocq c -Q _build/default/. Fido /tmp/assumptions_audit.v > /tmp/audit.log 2>&1; then cat /tmp/audit.log; fail "assumption audit FAILED"; fi
grep -q 'assumption audit OK' /tmp/audit.log || { cat /tmp/audit.log; fail "audit did not confirm zero Fido axioms"; }
# audit self-test: a planted axiom in a Fido-namespaced module MUST be caught (not fail-open)
mkdir -p /tmp/fa; printf 'Axiom planted_axiom : True.\n' > /tmp/fa/Planted.v
rocq c -R /tmp/fa Fido /tmp/fa/Planted.v > /tmp/fa/plant.log 2>&1 || { cat /tmp/fa/plant.log; fail "could not compile the audit self-test module"; }
printf 'From Fido Require Import Planted.\nDeclare ML Module "fido.emit".\nFido Audit Assumptions.\n' > /tmp/fa/Check.v
if rocq c -R /tmp/fa Fido -Q _build/default/. Fido /tmp/fa/Check.v > /tmp/fa/check.log 2>&1; then fail "the audit did NOT catch a planted Fido axiom (fail-open)"; fi
echo "fido: assumption audit OK — zero Fido axioms; self-test confirms a planted Fido axiom is caught"

# --- exercise the dirty-directory sink directly (local per-parent staging + records + foreign rejection) ---
cp plugin/fido_sink.ml e2e/sink_test.ml /tmp/
if ! ( cd /tmp && ocamlfind ocamlopt -package unix -linkpkg fido_sink.ml sink_test.ml -o /workspace/sink_test ) > /tmp/sink.log 2>&1; then cat /tmp/sink.log; fail "sink_test compile FAILED"; fi
cd /workspace
records() { find "$1/.fido/stage-records" -mindepth 1 2>/dev/null; }
stages()  { find "$1" -name '.fido-stage-*' 2>/dev/null; }
residue() { records "$1"; stages "$1"; }

# (1) clean sync → rendered go.mod + main.go + control marker; no stage/record residue.  (sink_test itself
#     byte-verifies each installed file against its own staged bytes on every successful sync.)
mkdir -p adv-1; ./sink_test adv-1 || fail "clean sync failed"
{ [ -f adv-1/go.mod ] && [ -f adv-1/main.go ] && [ -f adv-1/.fido/marker ]; } || fail "missing go.mod/main.go/marker"
[ -z "$(residue adv-1)" ] || fail "stage/record residue leaked after a successful sync"
# (2) re-sync: a stale OWNED .go (owned, not desired) is removed; foreign non-Go is preserved
./sink_test adv-1 multi || fail "multi re-sync failed"
[ -f adv-1/sub/main.go ] || fail "multi re-sync did not create sub/main.go"
printf 'keep\n' > adv-1/notes.txt
./sink_test adv-1 || fail "single re-sync failed"
[ ! -e adv-1/sub/main.go ] || fail "a stale owned .go was not removed on re-sync"
[ -f adv-1/notes.txt ] || fail "a foreign non-Go file was removed on re-sync"
# (2b) empty re-sync removes ALL owned .go, keeps the owned go.mod + foreign files
./sink_test adv-1 empty || fail "empty re-sync failed"
[ ! -e adv-1/main.go ] || fail "empty program did not remove the owned main.go"
[ -f adv-1/go.mod ] || fail "empty program removed the owned go.mod"
[ -f adv-1/notes.txt ] || fail "empty program removed a foreign file"
[ -z "$(residue adv-1)" ] || fail "residue after empty re-sync"

# (3) FOREIGN Go/module inputs REJECT before any generated-file mutation (§9); the foreign input survives
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
# foreign .fido (no exact marker) → refuse and preserve
mkdir -p adv-ffido/.fido; printf 'nope\n' > adv-ffido/.fido/marker
if ./sink_test adv-ffido; then fail "a foreign .fido control dir was NOT refused"; fi
printf 'nope\n' | cmp -s - adv-ffido/.fido/marker || fail "a foreign .fido marker was altered"

# (4) reserved namespace + prefix symlink: rejected BEFORE any effect
if ./sink_test /workspace/adv-resv reserved; then fail "a desired path inside .fido was NOT rejected"; fi
[ ! -e /workspace/adv-resv ] || fail "a reserved-path rejection created the root (effect before validation)"
mkdir -p /workspace/sreal; printf 'x\n' > /workspace/sreal/keep; ln -s /workspace/sreal /workspace/slink
if ./sink_test /workspace/slink/child; then fail "wrote through a prefix symlink"; fi
[ ! -e /workspace/sreal/child ] || fail "a prefix symlink created a child in the referent"
printf 'x\n' | cmp -s - /workspace/sreal/keep || fail "a prefix symlink mutated the referent"

# (5) MULTI-parent staging: root + sub each get a separate local stage; success installs both, no residue
mkdir -p adv-multi; ./sink_test adv-multi multi || fail "multi-parent sync failed"
{ [ -f adv-multi/go.mod ] && [ -f adv-multi/main.go ] && [ -f adv-multi/sub/main.go ]; } || fail "multi-parent tree incomplete"
[ -z "$(residue adv-multi)" ] || fail "multi-parent residue after success"
# SAME-parent sharing: go.mod + main.go share ONE root stage (crash-after-staging freezes the complete image)
mkdir -p adv-share
if ./sink_test adv-share crash-after-staging; then fail "share: the crash did not terminate the process"; fi
nst=$(stages adv-share | wc -l); [ "$nst" -eq 1 ] || fail "share: expected ONE root stage, found $nst"
nin=$(find $(stages adv-share) -type f | wc -l); [ "$nin" -eq 2 ] || fail "share: the shared stage should hold go.mod + main.go, found $nin"
[ ! -e adv-share/main.go ] && [ ! -e adv-share/go.mod ] || fail "share: a file was installed before staging completed (staging must precede install)"
rm -f adv-share/.fido/index.lock; ./sink_test adv-share || fail "share: no converge after clearing the stale lock"
[ -z "$(residue adv-share)" ] || fail "share: residue survived recovery"

# (6) CRASH at each staging point → the lock stays held, residue is left, a rerun REFUSES on the lock, and
#     after the stale lock is cleared the record-driven recovery cleans the residue and converges.
crash_recover() {  # <mode> <label>
  d=/workspace/adv-crash-$2; mkdir -p "$d"; ./sink_test "$d" || fail "$2: initial sync failed"
  if ./sink_test "$d" "$1"; then fail "$2: the crash mode did not terminate the process"; fi
  [ -e "$d/.fido/index.lock" ] || fail "$2: a crash must leave the lock held (no finalizer ran)"
  [ -n "$(residue "$d")" ] || fail "$2: the crash left no record/stage residue to recover"
  if ./sink_test "$d"; then fail "$2: ran despite the crash-held lock"; fi
  rm -f "$d/.fido/index.lock"
  ./sink_test "$d" || fail "$2: did not converge after clearing the stale lock"
  [ -z "$(residue "$d")" ] || fail "$2: residue survived recovery"
  { [ -f "$d/go.mod" ] && [ -f "$d/main.go" ]; } || fail "$2: files missing after convergence"
}
crash_recover crash-after-record        record
crash_recover crash-after-mkdir         mkdir
crash_recover crash-after-first-payload payload
crash_recover crash-after-staging       staging

# (7) RECOVERY is record-driven and fail-closed:
#   a valid record + its real stage dir → BOTH removed;
mkdir -p adv-rec2; ./sink_test adv-rec2 || fail "rec2: init"
mkdir -p adv-rec2/.fido-stage-abcd; printf 'x\n' > adv-rec2/.fido-stage-abcd/f
printf 'fido-stage-record v1\nabcd\n\n.fido-stage-abcd\n' > adv-rec2/.fido/stage-records/abcd
./sink_test adv-rec2 || fail "rec2: sync failed with a valid abandoned record"
{ [ ! -e adv-rec2/.fido-stage-abcd ] && [ ! -e adv-rec2/.fido/stage-records/abcd ]; } || fail "rec2: recovery did not remove the record-owned stage + record"
#   a recordless .fido-stage-* lookalike → PRESERVED;
mkdir -p adv-look; ./sink_test adv-look || fail "look: init"
mkdir -p adv-look/.fido-stage-deadbeef; printf 'x\n' > adv-look/.fido-stage-deadbeef/f
./sink_test adv-look || fail "look: sync failed with a recordless lookalike present"
[ -d adv-look/.fido-stage-deadbeef ] || fail "look: a recordless lookalike stage was removed"
#   a malformed record → fail closed (preserved);
mkdir -p adv-badrec; ./sink_test adv-badrec || fail "badrec: init"
printf 'garbage\n' > adv-badrec/.fido/stage-records/abcd
if ./sink_test adv-badrec; then fail "badrec: a malformed record did not fail closed"; fi
[ -f adv-badrec/.fido/stage-records/abcd ] || fail "badrec: the malformed record was removed"
#   a record whose parent escapes root → fail closed;
mkdir -p adv-outrec; ./sink_test adv-outrec || fail "outrec: init"
printf 'fido-stage-record v1\nabcd\n..\n../.fido-stage-abcd\n' > adv-outrec/.fido/stage-records/abcd
if ./sink_test adv-outrec; then fail "outrec: an escaping record did not fail closed"; fi
#   a nonce/filename mismatch → fail closed;
mkdir -p adv-mmrec; ./sink_test adv-mmrec || fail "mmrec: init"
printf 'fido-stage-record v1\nWRONG\n\n.fido-stage-WRONG\n' > adv-mmrec/.fido/stage-records/abcd
if ./sink_test adv-mmrec; then fail "mmrec: a nonce/filename mismatch did not fail closed"; fi
#   a recorded stage that is a symlink (not a directory) → fail closed, symlink preserved.
mkdir -p adv-slrec; ./sink_test adv-slrec || fail "slrec: init"
ln -s /etc adv-slrec/.fido-stage-abcd
printf 'fido-stage-record v1\nabcd\n\n.fido-stage-abcd\n' > adv-slrec/.fido/stage-records/abcd
if ./sink_test adv-slrec; then fail "slrec: a symlinked stage did not fail closed"; fi
[ -L adv-slrec/.fido-stage-abcd ] || fail "slrec: the symlink stage was removed/followed"

# (8) a fixed-nonce COLLISION with a pre-existing stage aborts (retry exhausted), preserving the entry
mkdir -p adv-coll; ./sink_test adv-coll || fail "coll: init"
mkdir -p adv-coll/.fido-stage-00112233445566778899aabbccddeeff
if ./sink_test adv-coll collide; then fail "coll: a fixed-nonce collision did not abort"; fi
[ -d adv-coll/.fido-stage-00112233445566778899aabbccddeeff ] || fail "coll: the colliding entry was removed"
[ -z "$(records adv-coll)" ] || fail "coll: a record leaked from the aborted collision"

# (9) an [unlink] failure during recovery aborts fail-loud (residue preserved, lock released), then a clean
#     rerun converges; and an [unlink] failure in the cleanup phase surfaces the failure, leaves the record,
#     and a clean rerun recovers it.
mkdir -p adv-ruf; ./sink_test adv-ruf || fail "ruf: init"
mkdir -p adv-ruf/.fido-stage-abcd; printf 'x\n' > adv-ruf/.fido-stage-abcd/f
printf 'fido-stage-record v1\nabcd\n\n.fido-stage-abcd\n' > adv-ruf/.fido/stage-records/abcd
if ./sink_test adv-ruf unlink-fail; then fail "ruf: a recovery unlink failure did not abort"; fi
[ -d adv-ruf/.fido-stage-abcd ] || fail "ruf: the stage was removed despite the unlink failure"
[ ! -e adv-ruf/.fido/index.lock ] || fail "ruf: the lock was not released after a recovery abort"
./sink_test adv-ruf || fail "ruf: did not converge on a clean rerun"
[ -z "$(residue adv-ruf)" ] || fail "ruf: residue survived convergence"
mkdir -p adv-cuf
if ./sink_test adv-cuf unlink-fail; then fail "cuf: an unlink failure in the cleanup phase was not surfaced"; fi
[ ! -e adv-cuf/.fido/index.lock ] || fail "cuf: the lock was not released after a cleanup failure"
./sink_test adv-cuf || fail "cuf: did not converge on a clean rerun"
[ -z "$(residue adv-cuf)" ] || fail "cuf: residue survived convergence"

echo "fido: emit OK — general Fido Emit synced the witness / multi-package / EMPTY trees (rendered go.mod); forged images rejected; sink foreign-Go rejection + local-staging + record-driven recovery (crash points, malformed/escaping/mismatched/symlinked records, collision, unlink-failure) all pass"
SH

# ── Stage 5: go-e2e — the LAST-MILE integration check (never a proof).  The pinned Go toolchain builds the
#    COMPLETE emitted tree with `go build ./...` — using the Rocq-RENDERED go.mod (no handwritten shell) —
#    and runs the witness package; stdout/stderr/exit must match the reviewed goldens.  `go build ./...` is
#    the blocking compiler-acceptance alarm; `go vet` is DIAGNOSTIC ONLY (nonblocking).  A build/run failure
#    here is a hard red — GoCompile/rendering/transport is wrong, never a known issue.
FROM golang:1.23-alpine@sha256:383395b794dffa5b53012a212365d40c8e37109a626ca30d6151c8348d380b5f AS go-e2e
WORKDIR /e2e
COPY --from=emit /workspace/e2e-out/ ./tree/
COPY --from=emit /workspace/e2e-multi/ ./multi/
COPY --from=emit /workspace/e2e-empty/ ./empty/
COPY e2e/golden.stdout e2e/golden.stderr e2e/golden.exit ./
RUN <<'SH'
set -u
# closed-world integration: force the local pinned toolchain, no workspace, no network proxy
export GOWORK=off GOTOOLCHAIN=local GOPROXY=off
cd tree
echo "fido e2e: emitted tree under test:"; echo ----; find . -type f | sort | while read f; do echo "== $f =="; cat "$f"; done; echo ----
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
