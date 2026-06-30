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
#   (b) VAGUE BRIDGE COVERAGE — the verified-printer bridge covers EXACTLY [is_i64_of_narrow_ref] and
#       [is_f64_to_f32_ref]+[operand_is_runtime], NOT the surface bytes (other producers emit the same
#       [int64(x)]/[float32(x)] unbridged).  Coverage docs must name the predicates, not "runtime scalar
#       conversions", and must SPELL OUT [operand_is_runtime] — never an `is_f64_to_f32_ref-runtime` shorthand
#       that drops the guard (the non-runtime case stays on the trusted force-wrapper, NOT the verified printer).
# Forbidden CONVERSION-COVERAGE prose (stale identity-lowering + vague bridge-coverage).  Patterns are DENYLIST
# DATA.  Matching is SPAN-based and case-INsensitive (grep -oiE): each forbidden phrase matches as its OWN span,
# so an unrelated "NOT identity" elsewhere on the line can NEVER immunize it (the old whole-line "not identity"
# filter, which dropped the whole line, was the bug — deleted, no replacement: the anchored verb→identity
# patterns can't match a negated form, so "a real cast, NOT identity" simply never matches).  cov_scan reports
# single-line hits as file:line:match, PLUS a whitespace/newline-normalized pass so a phrase WRAPPED across
# lines is still caught (reported file: [wrapped] match).
cov_pat='(widen|lower)(s|ing|ed)?[[:space:]]*(is|=|->|→|to)[[:space:]]*identity|emitted as identity|no-op cast|recogni[sz]ed as identity|runtime scalar conversions|is_f64_to_f32_ref[^.]{0,4}runtime'
cov_line() { grep -noiE "$cov_pat" "$1" 2>/dev/null || true; }                                  # line:span (per line)
cov_flat() { tr '\n\t' '  ' < "$1" 2>/dev/null | tr -s ' ' | grep -oiE "$cov_pat" || true; }    # spans incl. wrapped
cov_scan() {                                                                                    # the live scanner
  cov_line "$1" | sed "s|^|$1:|"                                                                 # file:line:match
  cl=$(mktemp); cf=$(mktemp)
  cov_line "$1" | sed 's/^[0-9][0-9]*://' | sort > "$cl"; cov_flat "$1" | sort > "$cf"
  comm -23 "$cf" "$cl" | sed "s|^|$1: [wrapped] |"                                               # only newline-wrapped spans
  rm -f "$cl" "$cf"
}
# self-test exercises the LIVE cov_scan (this script is not self-scanned).  Fixture: single-line bans (incl. three
# with "NOT identity" on the SAME line), MIXED-CASE bans (would vanish if -i were dropped), a phrase split across
# two lines (the wrapped path), and four legitimate lines that must NOT match.
st_tmp=$(mktemp)
printf '%s\n' \
  'widen is identity' 'lowering is identity' 'lowers to identity' 'lowered to identity' 'widened to identity' \
  'emitted as identity' 'a no-op cast' 'runtime scalar conversions' 'is_f64_to_f32_ref-runtime' \
  'runtime scalar conversions; NOT identity' 'lowered to identity; NOT identity' 'is_f64_to_f32_ref-runtime; NOT identity' \
  'Lowering is identity' 'Runtime scalar conversions' 'No-op cast' 'Is_f64_to_f32_ref-Runtime' \
  'lowering is' 'identity' 'runtime scalar' 'conversions' \
  'a real cast, NOT identity' '[MkU8]/[u8raw] -> identity' 'Lowering correctness (each variable identity preserved)' \
  'is_f64_to_f32_ref + operand_is_runtime' > "$st_tmp"
out=$(cov_scan "$st_tmp"); rm -f "$st_tmp"; stf=""
for need in 'widen is identity' 'lowers to identity' 'lowered to identity' 'widened to identity' 'emitted as identity' \
            'no-op cast' 'runtime scalar conversions' 'is_f64_to_f32_ref-runtime'; do
  printf '%s' "$out" | grep -qiF "$need" || stf="$stf miss[$need]"; done
for need in 'Lowering is identity' 'Runtime scalar conversions' 'No-op cast' 'Is_f64_to_f32_ref-Runtime'; do   # case-INsensitivity
  printf '%s' "$out" | grep -qF "$need" || stf="$stf nocase[$need]"; done
printf '%s' "$out" | grep -qi 'wrapped' || stf="$stf no-wrapped-path"                                          # cross-line
for bad in 'operand_is_runtime' 'real cast' 'variable identity' 'u8raw'; do                                     # spared
  printf '%s' "$out" | grep -qiF "$bad" && stf="$stf falsecatch[$bad]"; done
if [ -n "$stf" ]; then echo "fido: CONVERSION-COVERAGE GATE self-test FAILED —$stf"; exit 1; fi
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
  echo "fido: ([is_i64_of_narrow_ref] / [is_f64_to_f32_ref]+[operand_is_runtime], guard SPELLED OUT — no -runtime shorthand),"
  echo "fido: not the surface [int64(x)]/[float32(x)] bytes."
  exit 1
fi
echo "fido: conversion-coverage gate OK — no stale identity-lowering / vague bridge-coverage prose ✓"
