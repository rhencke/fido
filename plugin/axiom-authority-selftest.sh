#!/bin/sh
# AXIOM-AUTHORITY self-test — pins that the Fido axiom gate of record (Rocq's OWN `Print Assumptions`, captured
# by the Docker manifest gate) catches an axiom introduced by every declaration form in the TABLE below, and
# that the kernel rejects the forms it does not accept.  This is the antidote to the str_ltb / `Local Axiom`
# trap: a source-text regex over Rocq declarations always has a bypass, but Rocq reports an assumption no matter
# HOW the axiom is declared.  The table is the enumerated grammar — locality modifiers, attribute stacks, the
# plural keywords, `Conjecture` — not a hand-picked sample; if a NEW accepted form appears, add a row.  This is
# a completeness claim ONLY over the rows here (the declaration grammar the gate/docs discuss), nothing wider.
#
# It also mirrors the real GoSem gate: the manifest extractor (plugin/manifest-axioms.sh — the SAME one the
# Docker gate uses) is run over `Print Assumptions` of a TUPLE that bundles an axiom-using lemma with a clean
# one, exactly as GoSem.v's `gosem_trust_surface` bundles its results — so an axiom anywhere in that surface's
# cone is reported.
set -e
work=$(mktemp -d); trap 'rm -rf "$work"' EXIT
extract() { sh plugin/manifest-axioms.sh; }   # == the Docker manifest gate's extractor (single source of truth)
compile() { (cd "$work" && rocq c "$1" 2>&1 || true); }
fresh()   { rm -f "$work"/*.vo "$work"/.*.aux "$work"/*.glob 2>/dev/null || true; }

# A theorem that USES `forged`, so the axiom is in its cone and Print Assumptions reports it.
USES='Theorem forged_thm : False. Proof. exact forged. Qed.\nPrint Assumptions forged_thm.\n'

# TABLE: "<EXPECT>|<declaration>".  CAUGHT = compiles and the manifest extractor yields the axiom name;
# REJECTED = the Rocq kernel refuses the form (so it cannot introduce an axiom at all).
TABLE='
CAUGHT|Axiom forged : False.
CAUGHT|Parameter forged : False.
CAUGHT|Axioms forged : False.
CAUGHT|Parameters forged : False.
CAUGHT|Conjecture forged : False.
CAUGHT|Local Axiom forged : False.
CAUGHT|Global Axiom forged : False.
CAUGHT|Polymorphic Axiom forged : False.
CAUGHT|Monomorphic Axiom forged : False.
CAUGHT|Local Parameter forged : False.
CAUGHT|#[local] Axiom forged : False.
CAUGHT|#[local] #[universes(polymorphic)] Axiom forged : False.
REJECTED|Private Axiom forged : False.
REJECTED|Context (forged : False).
'
printf '%s\n' "$TABLE" | while IFS='|' read -r expect decl; do
  [ -n "$expect" ] || continue
  printf "$decl\\n$USES" > "$work/s.v"
  out=$(compile s.v); fresh
  case "$expect" in
    CAUGHT)
      printf '%s' "$out" | grep -q '^Axioms:' || { echo "fido: AXIOM-AUTHORITY — Print Assumptions did NOT report a COMPILING axiom form: $decl"; echo "$out"; exit 1; }
      [ "$(printf '%s' "$out" | extract)" = forged ] || { echo "fido: AXIOM-AUTHORITY — manifest extractor missed the axiom name for: $decl"; echo "$out"; exit 1; } ;;
    REJECTED)
      printf '%s' "$out" | grep -q '^Error:'  || { echo "fido: AXIOM-AUTHORITY — expected the kernel to REJECT this form, but it was accepted: $decl"; echo "$out"; exit 1; }
      printf '%s' "$out" | grep -q '^Axioms:' && { echo "fido: AXIOM-AUTHORITY — a REJECTED form still surfaced an axiom: $decl"; echo "$out"; exit 1; } || : ;;
  esac
done || exit 1

# SURFACE-MIRROR: an axiom used by ONE member of a bundled tuple (the exact `gosem_trust_surface` shape) must be
# reported by the manifest extractor — a self-checking negative for the real GoSem gate.
printf 'Axiom hidden_ax : False.\nLemma uses_it : False. Proof. exact hidden_ax. Qed.\nLemma clean : True. Proof. exact I. Qed.\nDefinition surface := (uses_it, clean).\nPrint Assumptions surface.\n' > "$work/s.v"
mirror=$(compile s.v); fresh
[ "$(printf '%s' "$mirror" | extract)" = hidden_ax ] || { echo "fido: AXIOM-AUTHORITY — surface-mirror: an axiom in a bundled tuple's cone was NOT reported (the gosem_trust_surface gate would miss it)"; echo "$mirror"; exit 1; }

# APOSTROPHE NAME: primed identifiers (e.g. Cmd_rect') are valid Rocq; the extractor must report the FULL name,
# `forged'` not `forged` — an enumerated identifier char class silently dropped these.
printf "Axiom forged' : False.\nTheorem ap_thm : False. Proof. exact forged'. Qed.\nPrint Assumptions ap_thm.\n" > "$work/s.v"
ap=$(compile s.v); fresh
[ "$(printf '%s' "$ap" | extract)" = "forged'" ] || { echo "fido: AXIOM-AUTHORITY — the extractor missed/mangled an apostrophe axiom name (expected forged')"; echo "$ap"; exit 1; }

# POSITIVE CONTROL: an axiom-free theorem must surface NOTHING (so "no axioms" is a real signal, not vacuous).
printf 'Theorem t : True. Proof. exact I. Qed.\nPrint Assumptions t.\n' > "$work/s.v"
ctl=$(compile s.v); fresh
[ -z "$(printf '%s' "$ctl" | extract)" ] || { echo "fido: AXIOM-AUTHORITY control FAILED — an axiom-free theorem surfaced an axiom"; echo "$ctl"; exit 1; }

echo "fido: axiom-authority self-test OK — Print Assumptions + the shared extractor catch every tabled axiom form (and the tuple-surface shape); the kernel rejects the rest ✓"
