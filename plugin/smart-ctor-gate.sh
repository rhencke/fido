#!/bin/sh
# Smart-constructor / dead-name / emission-discipline / bridge-recognizer gate.
#
# FOUR boring, CODE-LEVEL structural-discipline checks (grep tripwires, NOT type-level seals — they catch the
# accidental/obvious bypass, not an aliased side door; the real guarantees are the Rocq proofs + the fact that
# the AST admits no raw-syntax constructor and GoEmit exports no `emit : Program -> string`):
#   1. SMART-CTOR BAN  — only the smart constructors [mk_named_ty]/[mk_goexpr_id]/[mk_goexpr_hex]/[mk_goexpr_sel]
#      (which re-check [nominal_type_ident]/[go_ident]/[hexz_ok]/[go_ident] on the field) may build the
#      proof-ERASING [Printer.GTNamed]/[EId]/[EHex]/[ESel] (each carries an erased refinement — [ESel]'s field is
#      an [Ident]).
#   2. DEAD-NAME RECURRENCE — the torn-down SRaw overlay + forbidden raw-syntax constructor names must not
#      reappear in ACTIVE code (historical mentions allowed only in explicit archaeology docs — LESSONS.md — not active specs).
#   3. EMISSION DISCIPLINE — the raw [GoPrint.print_program] is for proofs/tests; emit ONLY through the
#      certificate-gated [GoEmit.emit_supported].
#   4. BRIDGE-RECOGNIZER scoping — every conversion recognizer the live printer bridge routes through ([cov_preds]
#      below, machine-readable GATE DATA) is a scoped `let is_X = named_in [...]`, with the [from_builtins] guard
#      living ONCE in [named_in] (a raw [global_basename] match would lower a same-named user global).
#
# NOT policed here — GoSem axiom-freedom.  It is gated by Rocq's OWN assumption output, not by a grep over
# GoSem.v: GoSem.v's [Print Assumptions] run when `dune build` compiles it, and the Docker manifest gate FAILS
# on any of its surfaces' [Axioms:] reports (gosem_trust_surface among them; rule 3 — the manifest is empty).  Rocq reports an assumption for an axiom
# introduced by ANY declaration form (Local/Global/Polymorphic Axiom, attributes, imported, transitive), so this
# is immune to the syntax a source-text scan misses (the str_ltb / [Local Axiom] trap); plugin/axiom-authority-
# selftest.sh PINS that completeness.  Likewise GoSem-uses-the-model's-string-order is enforced in ROCQ — by
# GoSem.v's qualified-constant [str_cmp_*_model] branch pins (+ the GoSemAuthority.v tripwire); see the note
# after check 4.
#
# This gate polices CODE discipline only.  Documentation / prose honesty (bridge-coverage wording, the
# construction-vs-printing distinction) is the job of REVIEW, not this gate.  The human-facing bridge-coverage
# list lives in ONE place — PROGRESS.md's live-bridge paragraph; [cov_preds] below is NOT a second copy of it,
# only the bare recognizer-NAME set the bridge-recognizer check needs (gate data, not prose).
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
  !s && /Printer\.GTNamed|Printer\.EId|Printer\.EHex|Printer\.ESel/ {print FILENAME ":" FNR ": " $0}
' $files)
if [ -n "$offenders" ]; then
  echo "fido: SMART-CTOR GATE — direct Printer.GTNamed / Printer.EId / Printer.EHex / Printer.ESel outside the smart-constructor block:"
  echo "$offenders"
  echo "fido: construct via mk_named_ty / mk_goexpr_id / mk_goexpr_hex / mk_goexpr_sel (which re-check nominal_type_ident / go_ident / hexz_ok / go_ident-on-field)."
  exit 1
fi
echo "fido: smart-ctor gate OK — no direct Printer.GTNamed / Printer.EId / Printer.EHex / Printer.ESel outside the block ✓"

# 2. DEAD-NAME RECURRENCE.  The SRaw-overlay names + the charter-forbidden raw-syntax constructor names +
# the retired structure names (goprint file, Front module) must not appear in active code.  Scope:
# hand-written Coq sources + plugin glue (the generated printer.ml + explicit archaeology docs like LESSONS.md
# are out of scope — a historical mention there is allowed; an active spec is not).
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

# 4. BRIDGE-RECOGNIZER scoping — a grep TRIPWIRE (like checks 1-3: it catches the accidental/obvious regression,
# NOT an adversarial OCaml shadow/alias).  Every conversion recognizer the live printer bridge routes through is
# written as the scoped alias `let is_X = named_in [...]`, with the [from_builtins] guard living ONCE in
# [named_in].  This flags the COMMON accidental break the original is_int_of_fw P0 actually was: a recognizer
# doing a RAW [global_basename] match (which would lower a same-named user global to an intrinsic), or
# [named_in] losing [from_builtins].  Not a seal — a deliberate shadow inside the TRUSTED plugin (gap #10) is out
# of scope; a sound check would need to parse OCaml (compiler-libs), disproportionate for already-trusted code.
#
# [cov_preds] — GATE DATA, not prose: the bare recognizer-NAME set this check iterates (each must be a scoped
# `let is_X = named_in [...]`).  The human-facing description of the live bridge lives once, in PROGRESS.md.
cov_preds='[is_i64_of_narrow_ref] / [is_f64_to_f32_ref]+[operand_is_runtime] / [is_f64_to_i64_ref] / [is_f64_to_u64_ref] / [is_int_of_fw] / [is_num_to_f64_ref] / [is_int_to_f32_ref]'
recog_def()    { awk -v p="$1" '$0 ~ ("^let " p "([ =:(]|$)"){f=1;print;next} f&&(/^let [A-Za-z_]/||/^\(\*/){exit} f{print}' "$2" 2>/dev/null; }
recog_routed() { b=$(recog_def "$1" "$2"); printf '%s' "$b" | grep -q 'named_in' && ! printf '%s' "$b" | grep -q 'global_basename'; }
st_t=$(mktemp)
printf '%s\n' 'let is_ok = named_in ["a"]' 'let mid x = 1' 'let is_raw r = List.mem (global_basename r) ["a"]' 'let named_in ns r = from_builtins r && List.mem (global_basename r) ns' > "$st_t"
# the named_in alias is "routed"; a raw global_basename body is not; named_in carries from_builtins.
if ! recog_routed is_ok "$st_t" || recog_routed is_raw "$st_t" || ! recog_def named_in "$st_t" | grep -q 'from_builtins'; then
  echo "fido: BRIDGE-RECOGNIZER TRIPWIRE self-test broke"; rm -f "$st_t"; exit 1
fi
rm -f "$st_t"
recog_def named_in plugin/go.ml | grep -q 'from_builtins' || { echo "fido: BRIDGE-RECOGNIZER TRIPWIRE — [named_in] lost its [from_builtins] guard; raw basename matching is a shadowing forge."; exit 1; }
for pred in $(printf '%s' "$cov_preds" | grep -oE '\[is_[a-z0-9_]+\]' | tr -d '[]'); do
  recog_routed "$pred" plugin/go.ml || { echo "fido: BRIDGE-RECOGNIZER TRIPWIRE — $pred should be 'let $pred = named_in [\"lit\"; …]', routing its basename match through the from_builtins-scoped [named_in] rather than a raw [global_basename]."; exit 1; }
done
echo "fido: bridge-recognizer tripwire OK — cov_preds recognizers route through the from_builtins-scoped named_in ✓"

# 5. SELECTOR-BRIDGE guard invariant.  The ESel live-bridge ([mk_goexpr_sel]) may emit [local.Field] ONLY for
# a plain field of an [MLrel] receiver — the sole shape matching [pp_expr]'s peel_embedded/pp_atom rendering.
# Dropping [not (is_embedded_proj r)] or the [MLrel] receiver guard re-opens an embedded/nested byte
# divergence (d.Animal.Legs vs d.Legs) that the RUNTIME golden cannot see; assert both guards sit on the arm.
selctx=$(grep -B8 'mk_goexpr_sel ld' plugin/go.ml || true)
if ! printf '%s\n' "$selctx" | grep -q 'not (is_embedded_proj' || ! printf '%s\n' "$selctx" | grep -q 'MLrel _'; then
  echo "fido: SELECTOR-BRIDGE GATE — the ESel arm (mk_goexpr_sel) lost its 'not (is_embedded_proj r)' or 'MLrel' receiver guard; an embedded/nested selector would bridge to a peel-divergent form (invisible to the runtime golden)."
  exit 1
fi
echo "fido: selector-bridge gate OK — the ESel arm keeps its not-embedded + MLrel-receiver guards ✓"

# NOTE: "GoSem's string comparison uses the model's string order" is enforced in ROCQ, not by a shell grep
# (which legal Rocq syntax bypasses): GoSem.v pins each [str_cmp_op] branch to the FULLY QUALIFIED model
# constant [Fido.builtins.str_*] by reflexivity ([str_cmp_*_model]) — shadow-immune, so a fork that reroutes a
# branch breaks a pin.  GoSemAuthority.v is a secondary post-import top-level tripwire ([Fail Check
# Fido.GoSem.str_*]).  Scope: GoSem (the string-semantics layer); no claim about other modules.
#
# GoSem axiom-freedom is likewise gated in ROCQ, not here (see the header): the Docker manifest gate captures
# the dune-build Print Assumptions surfaces (single-sourced in PROGRESS.md "Current gates"; the spine has
# separate printer/emit gates) + axiom-authority-selftest.sh pins completeness.  A source-text
# axiom-vernacular grep was tried here and DELETED — legal forms ([Local Axiom], …) bypass it.
