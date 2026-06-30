#!/bin/sh
# AXIOM-AUTHORITY self-test — proves the Fido axiom gate of record is COMPLETE against the declaration-form
# bypasses that defeat a source-text regex (the str_ltb / `Local Axiom` trap).
#
# The gate of record is Rocq's OWN `Print Assumptions` output: when `dune build` compiles a module, each
# `Print Assumptions T` runs and reports EVERY axiom `T` depends on — regardless of HOW the axiom was declared
# (plain / `Local` / `Global` / `Polymorphic` / attribute-qualified / imported / transitive).  The Docker
# manifest gate captures every module's `Axioms:` report (the awk no longer stops at `Extracted to`) and FAILS
# on any (EXPECTED_ASSUMPTIONS.txt is empty — rule 3).  So GoSem axiom-freedom is gated by Rocq itself, not by a
# grep over GoSem.v — immune to the syntax a scanner misses.
#
# This self-test PINS that completeness for Fido's pinned Rocq: every axiom-DECLARATION form is either
#   - CAUGHT   : it compiles, and a theorem using it makes `Print Assumptions` emit "^Axioms:" (and the SAME awk
#                the manifest gate uses extracts the name); or
#   - REJECTED : the Rocq kernel refuses the form, so it cannot introduce an axiom at all.
# A form that COMPILES yet does NOT surface as an assumption would be a real bypass — this fails the build.
# (Section-local `Context` is deliberately NOT a bypass: it is discharged at section close, so Print Assumptions
#  reports nothing — which is exactly why the source-scan tripwire must not ban it, and the Rocq authority does
#  not either.)
set -e
work=$(mktemp -d); trap 'rm -rf "$work"' EXIT
# == the Docker manifest gate's extraction awk (Dockerfile prover stage); kept identical on purpose.
manifest_awk() { awk '/^Axioms:/{f=1;next} f && /^[A-Za-z_][A-Za-z0-9_.]* :/ {print $1}'; }
run_form() {  # $1 = a leading declaration; compile it + a theorem that USES `forged`, capture all output.
  printf '%s\nTheorem forged_thm : False. Proof. exact forged. Qed.\nPrint Assumptions forged_thm.\n' "$1" > "$work/s.v"
  (cd "$work" && rocq c s.v 2>&1 || true)
  rm -f "$work/s.vo" "$work/.s.aux" "$work/s.glob"
}
caught() {
  out=$(run_form "$1")
  printf '%s' "$out" | grep -q '^Axioms:' || { echo "fido: AXIOM-AUTHORITY — Print Assumptions did NOT catch a COMPILING axiom form: $1"; echo "$out"; exit 1; }
  [ "$(printf '%s' "$out" | manifest_awk)" = forged ] || { echo "fido: AXIOM-AUTHORITY — manifest awk did NOT extract the axiom name for: $1"; echo "$out"; exit 1; }
}
rejected() {
  out=$(run_form "$1")
  printf '%s' "$out" | grep -q '^Error:'  || { echo "fido: AXIOM-AUTHORITY — expected the Rocq kernel to REJECT this form, but it was accepted: $1"; echo "$out"; exit 1; }
  printf '%s' "$out" | grep -q '^Axioms:' && { echo "fido: AXIOM-AUTHORITY — a REJECTED form still surfaced an axiom: $1"; echo "$out"; exit 1; } || true
}

# COMPILING axiom forms a bare-keyword / single-attribute regex misses — all must be CAUGHT by the authority.
caught   'Axiom forged : False.'
caught   'Local Axiom forged : False.'
caught   'Global Axiom forged : False.'
caught   'Polymorphic Axiom forged : False.'
caught   'Local Parameter forged : False.'
caught   '#[local] Axiom forged : False.'
# Forms Codex flagged that Fido's pinned Rocq REJECTS outright (so they are not bypasses here).
rejected 'Private Axiom forged : False.'
rejected 'Context (forged : False).'

# Positive control: an axiom-free theorem must surface NOTHING (so "no ^Axioms:" is a real signal, not vacuous).
printf 'Theorem t : True. Proof. exact I. Qed.\nPrint Assumptions t.\n' > "$work/s.v"
ctl=$(cd "$work" && rocq c s.v 2>&1 || true); rm -f "$work/s.vo" "$work/.s.aux" "$work/s.glob"
printf '%s' "$ctl" | grep -q '^Axioms:' && { echo "fido: AXIOM-AUTHORITY control FAILED — an axiom-free theorem surfaced Axioms:"; exit 1; } || true

echo "fido: axiom-authority self-test OK — Print Assumptions catches every compiling axiom form; the kernel rejects the rest ✓"
