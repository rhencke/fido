#!/bin/sh
# Smart-constructor gate (external review #4 directive; review #5 widened it to ALL plugin OCaml).
#
# The extracted [Printer] exposes proof-carrying constructors that erase their Rocq validity proof to a bare
# string in OCaml: [GTNamed] (a type name, [nominal_type_ident s = true]) and [EId] (an expression
# identifier, [go_ident s = true]).  A DIRECT [Printer.GTNamed s] / [Printer.EId s] would inject a name
# the verified round-trips ([parse_print_ty] / [parse_print_roundtrip]) never proved valid — re-opening the
# hand-written-printer trust hole through a side door.  (The old expression-printer constructors SIdent /
# SIntLit / SRaw / SSelector / AScanned / AStringLit were DELETED with the SRaw overlay teardown — see
# LESSONS.md; they no longer exist in printer.ml, so there is nothing left to guard there.)
#
# The [mk_named_ty] / [mk_goexpr_id] smart constructors (the SMART-CONSTRUCTORS block of plugin/go.ml) are
# the SOLE sanctioned construction sites: each re-checks its predicate and fail-louds / returns None
# otherwise.  This gate asserts NOTHING ELSE constructs [GTNamed] or [EId] directly — scanning EVERY
# hand-written plugin OCaml file (go.ml AND the .mlg vernac glue), not just go.ml, so a future helper file
# cannot reopen the hole (review #5 item 4).  The GENERATED plugin/printer.ml DEFINES the constructors, so it
# is the one file excluded.
#
# Run from the repo root: locally via `make smart-ctor-gate` and the pre-commit hook, and in the Docker
# prover stage (so `make check` always enforces it).
#
# LIMITATION (review #6 item 3): this is a STATIC-DISCIPLINE GATE, not a type-level seal.  It is a grep over
# the source, so it can be defeated by aliasing the constructor, a different module path, or by editing the
# gate itself.  The extracted `printer.ml` exposes [GTNamed] PUBLICLY.  The STRONGER architecture is a
# hand-written wrapper module (`Printer_checked`) with ABSTRACT types + smart constructors, with plugin code
# importing only that — so the raw constructor is simply unavailable.  Until then: do NOT describe this gate
# as "airtight" — it is a practical discipline gate that catches the easy/accidental bypass, not a proof
# boundary.
set -e

# The smart-constructor block lives in go.ml; assert its markers are present (so the in-block uses are
# correctly excluded below — deleting the markers makes the block's own uses read as offenders, which is
# a failure, not a bypass).
if ! grep -q 'SMART-CONSTRUCTORS-BEGIN' plugin/go.ml || ! grep -q 'SMART-CONSTRUCTORS-END' plugin/go.ml; then
  echo "fido: SMART-CTOR GATE — the SMART-CONSTRUCTORS-BEGIN/END markers are missing from plugin/go.ml"
  exit 1
fi

# Every hand-written plugin OCaml file EXCEPT the generated printer.ml.  (go.ml + g_go_extraction.mlg.)
files=""
for f in plugin/*.ml plugin/*.mlg; do
  [ "$f" = plugin/printer.ml ] && continue
  files="$files $f"
done

# Print "<file>:<lineno>: <text>" for any banned constructor use OUTSIDE the marker block (the block
# exists only in go.ml; in every other file there is no block, so [s] stays 0 and EVERY direct use is an
# offender).  FNR==1 resets the per-file skip flag; FNR is the per-file line number (clickable).
offenders=$(awk '
  FNR==1 { s=0 }
  /SMART-CONSTRUCTORS-BEGIN/{s=1}
  /SMART-CONSTRUCTORS-END/{s=0; next}
  !s && /Printer\.GTNamed|Printer\.EId/ {print FILENAME ":" FNR ": " $0}
' $files)

if [ -n "$offenders" ]; then
  echo "fido: SMART-CTOR GATE — direct proof-carrying Printer.GTNamed / Printer.EId OUTSIDE the smart-constructor block:"
  echo "$offenders"
  echo "fido: construct via mk_named_ty / mk_goexpr_id (which re-check the erased nominal_type_ident / go_ident invariant), never the raw constructor."
  exit 1
fi

echo "fido: smart-ctor gate OK — no direct Printer.GTNamed / Printer.EId outside the block ✓"

# ---- RECURRENCE / RAW-SYNTAX TRIPWIRE (external review checklist #3 + ARCHITECTURE.md §8 Rule 1): two name
# sets must never appear in ACTIVE code.  (1) The torn-down SRaw verified-EXPRESSION-printer overlay and its
# stale "Front not wired" wiring-status comments (three review rounds kept catching these resurfacing).  (2)
# The charter's ENUMERATED forbidden raw-syntax constructor names (RawExpr/RawStmt/RawDecl/RawType/OpaqueExpr/
# TrustedExpr).  (3) The post-split RETIRED structure names — `goprint` (the deleted file) and the `Front`
# module — which no longer exist; active code must say GoAst / GoPrint / Printer.  (Codex caught these
# surviving the f7d9383 split in stray comments — including one in main.v the first sweep missed; this
# tripwire now enforces the cleanup so it cannot regress.)
#   ⚠️ This is a NAME-REGRESSION TRIPWIRE, NOT structural protection.  It only catches these SPECIFIC names
#   reappearing; it does NOT — and a grep CANNOT — stop a differently-named raw-syntax hatch (e.g. a new
#   string-carrying GExpr/Program constructor under any other name).  The real, STRUCTURAL guarantee is that
#   the AST (GoAst, once written) admits NO raw Go-syntax text — its constructors take validated/semantic
#   payloads only (literal contents, validated idents), never a raw expr/stmt/type/decl string — a property
#   of the AST DEFINITION, enforced by review of that definition, not by this grep.  This tripwire is just the
#   loud backstop against the KNOWN regressions (an SRaw revival, these enumerated names).
# Historical mentions are allowed ONLY in the docs (LESSONS.md / CLAUDE.md / PROGRESS.md / ARCHITECTURE.md)
# and the GENERATED plugin/printer.ml — all excluded by scope below.  Scope: hand-written Coq sources (*.v) +
# plugin go.ml / .mlg glue.  (The "no raw emit" rule is likewise STRUCTURAL — GoEmit exports no
# emit : Program -> string — NOT a grep, since that text legitimately appears in explanatory comments.) ----
deadrefs=$(grep -nE 'SRaw|raw_ok|build_atom|build_apply|build_goexpr|GERaw|GEBin|\bEAtom\b|Printer\.print_expr|Printer\.print_prec|NOT yet wired|RawExpr|RawStmt|RawDecl|RawType|OpaqueExpr|TrustedExpr|goprint|\bFront\b' \
  *.v plugin/go.ml plugin/g_go_extraction.mlg 2>/dev/null || true)
if [ -n "$deadrefs" ]; then
  echo "fido: DEAD-ARCHITECTURE / RAW-SYNTAX GATE — a deleted-overlay or forbidden raw-syntax reference is in ACTIVE code:"
  echo "$deadrefs"
  echo "fido: these name the torn-down SRaw printer or a charter-forbidden raw-syntax constructor (LESSONS.md / ARCHITECTURE.md §8)."
  echo "fido: active code must not resurrect/introduce them; historical mentions belong ONLY in docs."
  exit 1
fi

echo "fido: dead-architecture / raw-syntax gate OK — no SRaw-era or forbidden raw-syntax references in active code ✓"

# ---- BLESSED-EMISSION DISCIPLINE TRIPWIRE (external review 2026-06-28 P1): the raw program printer
# [GoPrint.print_program] exists for proofs/tests, but the OFFICIAL emission path must go through the
# certificate-gated [GoEmit.emit_supported] (later [emit_safe]).  Assert NO OTHER active source CALLS
# print_program directly — scanning hand-written *.v (except GoPrint.v, which DEFINES it, and GoEmit.v, the
# blessed caller) + plugin glue.  The regex matches an APPLICATION (print_program followed by a '(' or an
# argument token), so the doc-comment ref `[print_program]` (bracketed, followed by ']') does NOT trip it.
#   ⚠️ Like the gates above this is a NAME/discipline tripwire, not a type seal: print_program is PUBLIC in
#   GoPrint.  The structural guarantee is that GoEmit exports no [emit : Program -> string] and the
#   certificate is required by [mkEmittable]; this grep just catches an accidental direct-call bypass.
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

# ---- DOC-EXACTNESS / DELETED-HELPER GATE (external review 2026-06-29 #8/#9): keep the float-constant predicate
# described with SINGLE-AUTHORITY honest wording.  [int_in_float_exact_interval] tests the CONTIGUOUS exact
# interval ([|z|<=2^53]/[2^24]), a CONSERVATIVE SUFFICIENT test — NOT the full set of exactly-representable
# integers.  Forbid (a) the stale/overclaiming names and the false "exact-integer range" / "only EXACT for"
# wording, plus archaeology of the renamed/deleted helpers ([int_repr_as_float], [float_exact_max],
# [complement_in]); and (b) the OVERCLAIM that crossing the interval CAUSES rounding — an outside-interval
# integer MAY be exact OR rounded, so "outside/beyond the interval ... ROUNDS" / "interval Go ROUNDS" is FALSE
# (the gate rejects outside-interval constants because it does not MODEL the sparse relation, not because they
# all round).  ACTIVE files only (postmortems belong in LESSONS.md, which is not scanned).
stale=$(grep -nE 'only EXACT for|EXACT-integer range|exact-integer range|int_repr_as_float|float_exact_max|complement_in' \
  GoSafe.v ARCHITECTURE.md PROGRESS.md 2>/dev/null || true)
stale="$stale$(grep -niE '(outside|beyond)[^.]*\bROUNDS\b|interval[^.]*\bROUNDS\b' \
  GoSafe.v ARCHITECTURE.md PROGRESS.md 2>/dev/null || true)"
if [ -n "$stale" ]; then
  echo "fido: DOC-EXACTNESS GATE — stale wording, deleted-helper archaeology, or a rounding OVERCLAIM in active files:"
  echo "$stale"
  echo "fido: use 'contiguous exact interval' (conservative sufficient) + the live names"
  echo "fido: (int_in_float_exact_interval / complement_const); an outside-interval int MAY be exact OR rounded —"
  echo "fido: say the gate does not MODEL the sparse relation, not that crossing the interval ROUNDS; postmortems -> LESSONS.md."
  exit 1
fi

echo "fido: doc-exactness / deleted-helper gate OK — honest single-authority float wording, no stale helper names ✓"

# ---- STRING-LITERAL EXACTNESS GATE (Codex stop-review 2026-06-29): the decoder [unescape_opt] accepts EXACTLY
# the printer image ([esc_string]'s byte set) — accepted == emitted.  The AUTHORITY for that claim is the LIVE
# Rocq theorem
#     unescape_opt_image : forall body s, unescape_opt body = Some s -> body = esc_string s
# (every accepted body is the canonical [esc_string] escaping of its decode), proved zero-axiom and enforced by
# the GoPrint Print-Assumptions gate — NOT by this shell grep.  This gate therefore does only two things: make
# that proof UNDELETABLE-by-stealth, and ban stale OLD-decoder wording:
#   (1) the THEOREM and its [Print Assumptions] must be PRESENT in GoPrint.v — deleting either silently drops the
#       exactness guarantee, and a MISSING theorem cannot fail the zero-axiom gate, so it must fail loud HERE; and
#   (2) forbid the DELETED lemma name [unescape_esc_byte] (the live lemma is [unescape_opt_esc_byte] — not a
#       substring, so this never matches the live one) and the false-exactness phrasings that described the OLD
#       SUPERSET decoder ("could never have produced" / "any byte except a newline").
# The shell does NOT itself certify exactness — it DEFERS to [unescape_opt_image].  Scope: GoPrint.v / GoAst.v /
# ARCHITECTURE.md / PROGRESS.md.
if ! grep -q 'Theorem unescape_opt_image' GoPrint.v || ! grep -q 'Print Assumptions unescape_opt_image' GoPrint.v; then
  echo "fido: STRING-EXACTNESS GATE — the exactness theorem unescape_opt_image (or its Print Assumptions) is MISSING from GoPrint.v."
  echo "fido: accepted == emitted is PROVEN by unescape_opt_image; without it the decoder could silently re-admit a superset."
  exit 1
fi
estr=$(grep -nE 'unescape_esc_byte|could never have produced|any byte [Ee][Xx][Cc][Ee][Pp][Tt] a newline' \
  GoPrint.v GoAst.v ARCHITECTURE.md PROGRESS.md 2>/dev/null || true)
if [ -n "$estr" ]; then
  echo "fido: STRING-EXACTNESS GATE — a deleted theorem name or a false-exactness phrasing is in active code:"
  echo "$estr"
  echo "fido: exactness is PROVEN by unescape_opt_image (accepted == emitted); the live lemma is unescape_opt_esc_byte,"
  echo "fido: so do not write 'could never have produced' / 'any byte except a newline' — defer to the theorem."
  exit 1
fi

echo "fido: string-exactness gate OK — unescape_opt_image present (accepted == emitted, proven zero-axiom); no stale wording ✓"

# ---- IDENTIFIER-BOUNDARY GUARD.  LIVE boundary: a free identifier is REJECTED; only the predeclared [nil]
# ([PtNil]) is admitted, as a slice/chan conversion operand.  [ibpat] is denylist DATA (machine tokens, not a
# description of any design) for stale spellings banned from active Coq sources + ARCHITECTURE/PROGRESS (history
# -> LESSONS.md).  Each file is WHITESPACE-NORMALIZED ([tr] newlines/tabs -> spaces, squeeze) before a
# CASE-INSENSITIVE match, so a split/wrapped/capitalized spelling cannot bypass it; the "deferred"/"identifier"
# proximity patterns use [^.]{1,40} (same-sentence window) so [close]/[delete]'s "deferred to GoSem." note is
# NOT matched.  [ib_scan] = normalize stdin then grep; reused by the self-test and the file loop.
ibpat='PtUnk|genuinely-unknown[^.]{1,40}identifier|bool/deferred|string/deferred|deferred[^.]{1,40}operand|deferred[^.]{1,40}identifier|identifier[^.]{1,40}deferr'
ib_scan() { tr '\n\t' '  ' | tr -s ' ' | grep -qiE "$ibpat"; }
# self-test (fixtures live HERE, not in scanned files): MUST catch each bad spelling (incl. cross-line and
# "deferred left operand"), MUST NOT catch the legitimate close/delete note or the live-boundary sentence.
for bad in 'deferred operand' 'DEFERRED
operand' 'deferred left operand' 'identifier is deferred' 'PtUnk'; do
  printf '%s' "$bad" | ib_scan || { echo "fido: IDENTIFIER-BOUNDARY GUARD self-test BUG — failed to catch [$bad]"; exit 1; }
done
for ok in 'close/delete add a constraint - deferred to GoSem. an operand here' 'a free identifier is REJECTED; only nil is admitted'; do
  if printf '%s' "$ok" | ib_scan; then echo "fido: IDENTIFIER-BOUNDARY GUARD self-test BUG — wrongly caught [$ok]"; exit 1; fi
done
stale_ident=""
for f in GoSafe.v GoAst.v GoPrint.v ARCHITECTURE.md PROGRESS.md; do
  if ib_scan < "$f"; then stale_ident="$stale_ident $f"; fi
done
if [ -n "$stale_ident" ]; then
  echo "fido: IDENTIFIER-BOUNDARY GUARD — a banned stale spelling (whitespace/case/newline-normalized) is in active guidance in:$stale_ident"
  echo "fido: state ONLY the live boundary (a free identifier is REJECTED; only [nil] is admitted, in a slice/chan conversion); history -> LESSONS.md."
  exit 1
fi

echo "fido: identifier-boundary guard OK — self-test passed; active guidance free of the banned stale spellings ✓"

# ---- GOSEM-LAYERING GATE (Codex stop-review 2026-06-29): core GoSem.v sits BELOW GoSafe/GoEmit in the spine
# (GoAst -> GoPrint -> GoSem -> GoSafe -> GoEmit), so it must import ONLY GoAst + the SHARED type-category
# module GoTypes (which is BELOW GoSem — it imports only GoAst) + the semantic substrate it bridges
# (cmd/builtins) — NEVER the UPPER emission layers (GoPrint/GoSafe/GoEmit), which would invert the dependency.
# (GoTypes is explicitly PERMITTED: it is the lower module GoSafe and GoSem both reuse for [ptype]/[svalue], so
# it does NOT appear in the banned set below.  The behavioral theorem over GoEmit.demo_prog lives DOWNSTREAM in
# GoSemDemo.v instead.)  The pattern matches an actual `Require` VERNAC line — anchored to line start, with an
# optional `From <lib>` prefix — so a prose mention of the spine (e.g. "GoAst -> GoPrint -> ... -> GoEmit") or of
# GoSemDemo in a COMMENT does NOT trip it (no `Require` keyword on those lines).  Self-tested below before scanning GoSem.v.
#   ⚠️ Like the gates above this is a discipline tripwire over the source, not a type-level seal; it catches the
#   accidental/obvious re-import, not an aliased side-door.
gosem_layer_pat='^[[:space:]]*(From[[:space:]]+[A-Za-z_.]+[[:space:]]+)?Require[[:space:]].*\b(GoPrint|GoSafe|GoEmit)\b'
gosem_scan() { grep -qE "$gosem_layer_pat"; }
# self-test (fixtures live HERE, not in scanned files): MUST catch a bad upper-layer import (incl. a bare
# `Require Import` with no `From`); MUST NOT catch a clean import or a prose/comment spine mention.
for bad in 'From Fido Require Import builtins cmd GoAst GoPrint.' 'Require Import GoEmit.' 'From Fido Require Import GoSafe.'; do
  printf '%s\n' "$bad" | gosem_scan || { echo "fido: GOSEM-LAYERING GATE self-test BUG — failed to catch [$bad]"; exit 1; }
done
for ok in 'From Fido Require Import builtins cmd GoAst GoTypes.' '    spine GoAst -> GoPrint -> GoSem -> GoSafe -> GoEmit (charter).' '(* the theorem over GoEmit.demo_prog lives in GoSemDemo.v *)'; do
  if printf '%s\n' "$ok" | gosem_scan; then echo "fido: GOSEM-LAYERING GATE self-test BUG — wrongly caught [$ok]"; exit 1; fi
done
gosem_offenders=$(grep -nE "$gosem_layer_pat" GoSem.v 2>/dev/null || true)
if [ -n "$gosem_offenders" ]; then
  echo "fido: GOSEM-LAYERING GATE — core GoSem.v Requires an UPPER emission layer (GoPrint/GoSafe/GoEmit), inverting the spine:"
  echo "$gosem_offenders"
  echo "fido: core GoSem must import only GoAst + the semantic substrate (cmd/builtins); the demo over GoEmit.demo_prog belongs in GoSemDemo.v."
  exit 1
fi

echo "fido: gosem-layering gate OK — core GoSem.v imports no upper emission layer (GoPrint/GoSafe/GoEmit) ✓"

# ---- (REMOVED) GOSEM BLANK-RHS VALIDITY GATE.  The old GoSem-local [rhs_effect_free] predicate it policed was
# DELETED (Codex stop-review 2026-06-29): GoSem's blank-assign [_ = e] is now gated by the SHARED
# [GoTypes.svalue] (= [ptype]-valid) — the SAME value-position authority GoSafe uses — so there is no second
# GoSem predicate to keep honest.  The validity guarantees are now PROVEN in-file by the GoSem regressions
# ([gosem_rejects_invalid_slice_conv] / [gosem_rejects_chan_conv_of_slice] / [gosem_rejects_map_literal] plus
# the type-blindness set [gosem_rejects_bool_conv] / [..._u8_slicelit_overflow] / [..._int_of_string] /
# [..._not_of_int] / [..._bool_ordering]), and by GoSafe's own [ptype] regressions — a real proof, not a grep.
