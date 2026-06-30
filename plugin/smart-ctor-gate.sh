#!/bin/sh
# Smart-constructor / dead-name / emission-discipline gate for the hand-written plugin OCaml.
#
# Three boring, structural-discipline checks (grep tripwires, NOT type-level seals — they catch the
# accidental/obvious bypass, not an aliased side door; the real guarantees are the Rocq proofs + the fact
# that the AST admits no raw-syntax constructor and GoEmit exports no `emit : Program -> string`):
#   1. SMART-CTOR BAN  — the extracted [Printer] exposes proof-carrying constructors ([GTNamed], [EId]) that
#      erase their Rocq validity proof to a bare string.  Only the smart constructors [mk_named_ty] /
#      [mk_goexpr_id] (which re-check [nominal_type_ident] / [go_ident]) may build them; nothing else may use
#      the raw [Printer.GTNamed] / [Printer.EId].
#   2. DEAD-NAME RECURRENCE — the torn-down SRaw expression-printer overlay and the charter-forbidden
#      raw-syntax constructor names must never reappear in ACTIVE code (history is allowed in docs only — see
#      LESSONS.md for the SRaw postmortem).
#   3. EMISSION DISCIPLINE — the raw [GoPrint.print_program] is for proofs/tests; the official path is the
#      certificate-gated [GoEmit.emit_supported], so nothing else may CALL print_program directly.
#
# Run from the repo root (make smart-ctor-gate, the pre-commit hook, and the Docker prover stage).
set -e

# Every hand-written plugin OCaml file EXCEPT the generated printer.ml (which DEFINES the constructors).
files=""
for f in plugin/*.ml plugin/*.mlg; do
  [ "$f" = plugin/printer.ml ] && continue
  files="$files $f"
done

# 1. SMART-CTOR BAN.  The smart-constructor block (markers in go.ml) is the only sanctioned site; assert the
# markers are present, then flag any Printer.GTNamed / Printer.EId use OUTSIDE that block in any plugin file.
if ! grep -q 'SMART-CONSTRUCTORS-BEGIN' plugin/go.ml || ! grep -q 'SMART-CONSTRUCTORS-END' plugin/go.ml; then
  echo "fido: SMART-CTOR GATE — the SMART-CONSTRUCTORS-BEGIN/END markers are missing from plugin/go.ml"
  exit 1
fi
offenders=$(awk '
  FNR==1 { s=0 }
  /SMART-CONSTRUCTORS-BEGIN/{s=1}
  /SMART-CONSTRUCTORS-END/{s=0; next}
  !s && /Printer\.GTNamed|Printer\.EId/ {print FILENAME ":" FNR ": " $0}
' $files)
if [ -n "$offenders" ]; then
  echo "fido: SMART-CTOR GATE — direct Printer.GTNamed / Printer.EId outside the smart-constructor block:"
  echo "$offenders"
  echo "fido: construct via mk_named_ty / mk_goexpr_id (which re-check nominal_type_ident / go_ident)."
  exit 1
fi
echo "fido: smart-ctor gate OK — no direct Printer.GTNamed / Printer.EId outside the block ✓"

# 2. DEAD-NAME RECURRENCE.  The SRaw-overlay names + the charter-forbidden raw-syntax constructor names +
# the retired structure names (goprint file, Front module) must not appear in active code.  Scope:
# hand-written Coq sources + plugin glue (docs/printer.ml excluded — historical mentions allowed there).
deadrefs=$(grep -nE 'SRaw|raw_ok|build_atom|build_apply|build_goexpr|GERaw|GEBin|\bEAtom\b|Printer\.print_expr|Printer\.print_prec|RawExpr|RawStmt|RawDecl|RawType|OpaqueExpr|TrustedExpr|goprint|\bFront\b' \
  *.v plugin/go.ml plugin/g_go_extraction.mlg 2>/dev/null || true)
if [ -n "$deadrefs" ]; then
  echo "fido: DEAD-NAME GATE — a torn-down-overlay or forbidden raw-syntax name is in active code:"
  echo "$deadrefs"
  echo "fido: these are deleted/forbidden (LESSONS.md SRaw postmortem); historical mentions belong only in docs."
  exit 1
fi
echo "fido: dead-name gate OK — no SRaw-era or forbidden raw-syntax names in active code ✓"

# 3. EMISSION DISCIPLINE.  No direct GoPrint.print_program CALL outside GoEmit.v (the blessed caller) /
# GoPrint.v (which defines it).  The regex matches an APPLICATION (print_program followed by '(' or an arg
# token), so a bracketed doc-comment ref [print_program] does not trip it.
ppcallers=$(grep -nE '\bprint_program\b[[:space:]]*[("a-zA-Z0-9_]' \
  $(for f in *.v; do [ "$f" = GoPrint.v ] || [ "$f" = GoEmit.v ] || echo "$f"; done) \
  plugin/go.ml plugin/g_go_extraction.mlg 2>/dev/null || true)
if [ -n "$ppcallers" ]; then
  echo "fido: EMISSION-DISCIPLINE GATE — a direct GoPrint.print_program CALL is in active code outside GoEmit.v:"
  echo "$ppcallers"
  echo "fido: emit ONLY through GoEmit.emit_supported (certificate-gated); print_program is for proofs/tests."
  exit 1
fi
echo "fido: emission-discipline gate OK — no direct print_program call outside GoEmit.v / GoPrint.v ✓"

# 4. CONVERSION-COVERAGE HONESTY (Codex 2026-06-30).  Two regression bans tied to the Stage-B bridge:
#   (a) IDENTITY-CONFLATION — a narrow→wide integer conversion ([i64_of_narrow]/[int_of_FW]) EMITS a real Go
#       cast [int(x)]/[int64(x)], NOT identity (a bare [x] at the narrow→wide boundary is invalid Go, review
#       #4 P1 #4).  Active prose must never call that lowering "identity" / a "no-op cast".  (The record-wrapper
#       erasure [MkU8]/[u8raw]→identity is a DIFFERENT legitimate claim — no widen/lowering word — and is spared.)
#   (b) VAGUE BRIDGE COVERAGE — the verified-printer bridge covers a FIXED set of source predicates (the live
#       list is the single-sourced $cov_preds below, echoed by the diagnostic so it cannot drift), NOT the
#       surface bytes (other producers — e.g. int->float32 [is_int_to_f32_ref] — emit the same
#       [int64(x)]/[float32(x)] unbridged).  Coverage docs must NAME the predicates (no numeric COUNT — counts
#       drift, see the stale-count guard), not "runtime scalar conversions", and must SPELL OUT
#       [operand_is_runtime] — never an `is_f64_to_f32_ref-runtime` shorthand that drops the guard.
# Forbidden CONVERSION-COVERAGE prose (stale identity-lowering + vague bridge-coverage).  Patterns are DENYLIST
# DATA.  Matching is SPAN-based and case-INsensitive (grep -oiE): each forbidden phrase matches as its OWN span,
# so an unrelated "NOT identity" elsewhere on the line can NEVER immunize it (the old whole-line "not identity"
# filter, which dropped the whole line, was the bug — deleted, no replacement: the anchored verb→identity
# patterns can't match a negated form, so "a real cast, NOT identity" simply never matches).  cov_scan reports
# single-line hits as file:line:match, PLUS a whitespace/newline-normalized pass so a phrase WRAPPED across
# lines is still caught (reported file: [wrapped] match).
cov_pat='(widen|lower)(s|ing|ed)?[[:space:]]*(is|=|->|→|to)[[:space:]]*identity|emitted as identity|no-op cast|recogni[sz]ed as identity|runtime scalar conversions|is_f64_to_f32_ref[^.]{0,4}runtime'
# Single source of truth for the bridged-predicate boundary, reused by the diagnostic so the gate cannot drift.
cov_preds='[is_i64_of_narrow_ref] / [is_f64_to_f32_ref]+[operand_is_runtime] / [is_f64_to_i64_ref] / [is_f64_to_u64_ref] / [is_int_of_fw] / [is_num_to_f64_ref]'
cov_line() { grep -noiE "$cov_pat" "$1" 2>/dev/null || true; }                                  # line:span (per line)
cov_flat() { tr '\n\t' '  ' < "$1" 2>/dev/null | tr -s ' ' | grep -oiE "$cov_pat" || true; }    # spans incl. wrapped
cov_scan() {                                                                                    # the live scanner
  cov_line "$1" | sed "s|^|$1:|"                                                                 # file:line:match
  cl=$(mktemp); cf=$(mktemp)
  cov_line "$1" | sed 's/^[0-9][0-9]*://' | sort > "$cl"; cov_flat "$1" | sort > "$cf"
  comm -23 "$cf" "$cl" | sed "s|^|$1: [wrapped] |"                                               # only newline-wrapped spans
  rm -f "$cl" "$cf"
}
# self-test exercises the LIVE cov_scan on a fixture (this script is not self-scanned) with an EXACT,
# LOCATION-based oracle — NOT broad substring greps (those passed even if the same-line "NOT identity" rows
# were dropped, because the bare phrase recurs on other lines).  Fixture: 1-9 single-line bans; 10-12 the same
# SPANS with "NOT identity" appended (the immunity-regression rows — must still hit BY LINE); 13-16 MIXED-CASE
# bans (vanish if -i is dropped); 17-18 + 19-20 one phrase each split across two lines (the wrapped path);
# 21-24 legitimate lines that must NOT match anywhere.
st_tmp=$(mktemp)
printf '%s\n' \
  'widen is identity' 'lowering is identity' 'lowers to identity' 'lowered to identity' 'widened to identity' \
  'emitted as identity' 'a no-op cast' 'runtime scalar conversions' 'is_f64_to_f32_ref-runtime' \
  'runtime scalar conversions; NOT identity' 'lowered to identity; NOT identity' 'is_f64_to_f32_ref-runtime; NOT identity' \
  'Lowering is identity' 'Runtime scalar conversions' 'No-op cast' 'Is_f64_to_f32_ref-Runtime' \
  'lowering is' 'identity' 'runtime scalar' 'conversions' \
  'a real cast, NOT identity' '[MkU8]/[u8raw] -> identity' 'Lowering correctness (each variable identity preserved)' \
  'is_f64_to_f32_ref + operand_is_runtime' > "$st_tmp"
out=$(cov_scan "$st_tmp"); rm -f "$st_tmp"
# per-line hits must be EXACTLY lines 1..16: includes 10-12 (drop a "NOT identity" row ⇒ FAIL) and 13-16
# (drop -i ⇒ FAIL); 17-24 must yield NO single-line hit.  wrapped spans must be EXACTLY the two split phrases
# (broken wrapped path, or a spared line leaking a wrapped span ⇒ FAIL).
pl=$(printf '%s\n' "$out" | grep -oE ':[0-9]+:' | tr -d ':' | sort -un | tr '\n' ' ')
wr=$(printf '%s\n' "$out" | sed -n 's/.*\[wrapped\] //p' | sort | tr '\n' '|')
mc=$(printf '%s\n' "$out" | grep -cF 'Runtime scalar conversions' || true)   # verbatim mixed-case span ⇒ -i is live
if [ "$pl" != "1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 " ] \
   || [ "$wr" != "lowering is identity|runtime scalar conversions|" ] || [ "$mc" -lt 1 ]; then
  echo "fido: CONVERSION-COVERAGE GATE self-test FAILED — per-line[$pl] (want 1..16, incl. 10-12 NOT-identity + 13-16 mixed-case); wrapped[$wr] (want the 2 split phrases); mixedcase[$mc]."; exit 1
fi
covbad=""
for f in $(ls *.v 2>/dev/null) plugin/go.ml plugin/g_go_extraction.mlg CLAUDE.md PROGRESS.md ARCHITECTURE.md SPEC_CONFORMANCE.md; do
  [ -f "$f" ] || continue
  h=$(cov_scan "$f"); [ -n "$h" ] && covbad="$covbad
$h"
done
if [ -n "$covbad" ]; then
  echo "fido: CONVERSION-COVERAGE GATE — stale identity-lowering claim or vague bridge-coverage phrase in active prose:"
  echo "$covbad"
  echo "fido: a narrow→wide conversion EMITS a real cast (NOT identity, review #4 P1 #4); name the bridge predicates"
  echo "fido: ($cov_preds, guard SPELLED OUT — no -runtime shorthand), not the surface int64(x)/float32(x)/uint64(x) bytes."
  exit 1
fi
echo "fido: conversion-coverage gate OK — no stale identity-lowering / vague bridge-coverage prose ✓"

# STALE-COUNT guard: bridge-coverage prose must NOT state a numeric COUNT of conversions (it drifts every time
# one is added — name the predicates instead), nor preserve the old conv_operand_demo two-output line "205 / true".
# sc_scan is the ONE scanner (single set of flags — case-INsensitive, so UPPERCASE "FOUR runtime conversions"
# can't slip past); the self-test and the active-file scan both call it, so they cannot diverge.  Scanned in
# active docs + sources (NOT this script — the self-test fixture holds the literal stale phrases).
sc_pat='(exactly[[:space:]]+)?(one|two|three|four|five|six|seven|eight|nine|ten|[0-9]+)[[:space:]]+runtime[[:space:]]+conversion|205[[:space:]]*/[[:space:]]*true'
sc_scan() { grep -rniE "$sc_pat" "$@" 2>/dev/null || true; }
# self-test exercises the LIVE sc_scan: all four stale forms (incl. UPPERCASE + numeric) must be caught, and
# "the runtime conversions" must be spared.
sc_tmp=$(mktemp)
printf '%s\n' 'four runtime conversions' 'FOUR runtime conversions' '4 runtime conversions' '205 / true' 'the runtime conversions' > "$sc_tmp"
sc_hit=$(sc_scan "$sc_tmp" | grep -c . || true)
sc_leak=$(sc_scan "$sc_tmp" | grep -ic 'the runtime conversions' || true)
rm -f "$sc_tmp"
if [ "$sc_hit" -ne 4 ] || [ "$sc_leak" -ne 0 ]; then
  echo "fido: STALE-COUNT GATE self-test broke (want 4 stale catches incl. UPPERCASE/numeric, 0 leak; got hit=$sc_hit leak=$sc_leak)"; exit 1
fi
scbad=$(sc_scan $(ls *.v 2>/dev/null) plugin/go.ml plugin/g_go_extraction.mlg CLAUDE.md PROGRESS.md ARCHITECTURE.md SPEC_CONFORMANCE.md)
if [ -n "$scbad" ]; then
  echo "fido: STALE-COUNT GATE — bridge-coverage prose states a numeric conversion count (drifts) or the old '205 / true' demo output:"
  echo "$scbad"
  echo "fido: name the bridge predicates instead of a count, and state the LIVE demo output."
  exit 1
fi
echo "fido: stale-count gate OK — no numeric conversion-count / old demo-output prose ✓"

# 5. BRIDGE-RECOGNIZER scoping: every conversion recognizer the verified-printer bridge uses (named in
# cov_preds) MUST be from_builtins-scoped.  A basename-only [List.mem (global_basename r) …] match is a
# SHADOWING FORGE HOLE — a user/global with the same basename (e.g. a hand-written [int_of_u8] in main.v)
# would be lowered to the cast instead of its real semantics (go.ml's own trust-boundary rule, ~line 197).
# recog_scoped: TRUE iff predicate $1's OWN definition body in file $2 applies the from_builtins guard.
# awk extracts ONLY that def — from its `let` line up to (EXCLUDING) the next top-level `let` OR `(*` comment,
# so it can NOT read a from_builtins guard out of a neighbouring def; inline comments are stripped so a
# `(* … from_builtins r … *)` mention does not satisfy it; the grep requires the GUARD SHAPE `from_builtins r`.
recog_scoped() {
  awk -v p="$1" '
    $0 ~ ("^let " p "([ =]|$)")           { inb=1; print; next }
    inb && (/^let [A-Za-z_]/ || /^\(\*/)  { exit }
    inb                                    { print }
  ' "$2" 2>/dev/null | sed -E 's/\(\*[^*]*\*\)//g' | grep -qE 'from_builtins[[:space:]]+r'
}
rg_tmp=$(mktemp)
cat > "$rg_tmp" <<'RGEOF'
let is_scoped_a r = from_builtins r && foo
let mid x = 1
let is_unscoped_b r =
  List.mem (global_basename r) ["z"]
let is_scoped_next r = from_builtins r && bar
let is_unscoped_c r = (* mentions from_builtins r only in a comment *) List.mem (global_basename r) ["w"]
let tail y = 2
RGEOF
# scoped_a PASSES; unscoped_b (immediately followed by a scoped def — the false-negative Codex found) FAILS;
# unscoped_c (from_builtins only inside a comment) FAILS.
if ! recog_scoped is_scoped_a "$rg_tmp" || recog_scoped is_unscoped_b "$rg_tmp" || recog_scoped is_unscoped_c "$rg_tmp"; then
  echo "fido: BRIDGE-RECOGNIZER GATE self-test broke (scoped must pass; unscoped-then-scoped + comment-only-from_builtins must fail)"; rm -f "$rg_tmp"; exit 1
fi
rm -f "$rg_tmp"
for pred in $(printf '%s' "$cov_preds" | grep -oE '\[is_[a-z0-9_]+\]' | tr -d '[]'); do
  recog_scoped "$pred" plugin/go.ml || { echo "fido: BRIDGE-RECOGNIZER GATE — $pred (a goexpr_bridge recognizer in cov_preds) is NOT from_builtins-scoped — basename-only matching is a shadowing forge hole; add 'from_builtins r &&' to its definition in plugin/go.ml."; exit 1; }
done
echo "fido: bridge-recognizer gate OK — every cov_preds recognizer is from_builtins-scoped ✓"
