#!/bin/sh
# Structural code-discipline gate — CODE-LEVEL grep tripwires (not type-level seals): smart-ctor
# ban / dead-name / emission-discipline / bridge-recognizer / selector-bridge / local-example.
# The real guarantees are the Rocq proofs; axiom-freedom is enforced in Rocq, prose honesty is
# review's job.  Run from the repo root (make smart-ctor-gate, pre-commit, Docker prover stage).
set -e

# Every hand-written plugin OCaml file EXCEPT the generated printer.ml (which DEFINES the constructors).
files=""
for f in plugin/*.ml plugin/*.mlg; do
  [ "$f" = plugin/printer.ml ] && continue
  files="$files $f"
done

# 1. SMART-CTOR BAN: no proof-erasing constructor use outside the sanctioned block.
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

# 2. DEAD-NAME RECURRENCE: torn-down / forbidden raw-syntax names must not reappear in active code.
deadrefs=$(grep -nE 'SRaw|raw_ok|build_atom|build_apply|build_goexpr|GERaw|GEBin|\bEAtom\b|Printer\.print_expr|Printer\.print_prec|RawExpr|RawStmt|RawDecl|RawType|OpaqueExpr|TrustedExpr|goprint|\bFront\b|\bSPtr\b|\bSPtr3\b|\bSPtrH\b|StructRep2|StructRep3|\bsptr_' \
  *.v plugin/go.ml plugin/g_go_extraction.mlg 2>/dev/null || true)
if [ -n "$deadrefs" ]; then
  echo "fido: DEAD-NAME GATE — a torn-down-overlay or forbidden raw-syntax name is in active code:"
  echo "$deadrefs"
  echo "fido: these are deleted/forbidden (LESSONS.md SRaw postmortem); historical mentions belong only in docs."
  exit 1
fi
echo "fido: dead-name gate OK — no SRaw-era or forbidden raw-syntax names in active code ✓"

# 3. EMISSION DISCIPLINE: no direct print_program CALL outside GoEmit.v / GoPrint.v (doc refs fine).
ppcallers=$(grep -nE '\bprint_program\b[[:space:]]*[("a-zA-Z0-9_]' \
  $(for f in *.v; do [ "$f" = GoPrint.v ] || [ "$f" = GoEmit.v ] || echo "$f"; done) \
  plugin/go.ml plugin/g_go_extraction.mlg 2>/dev/null || true)
if [ -n "$ppcallers" ]; then
  echo "fido: EMISSION-DISCIPLINE GATE — a direct GoPrint.print_program CALL is in active code outside GoEmit.v:"
  echo "$ppcallers"
  echo "fido: emit ONLY through GoEmit.emit_compiled (certificate-gated); print_program is for proofs/tests."
  exit 1
fi
echo "fido: emission-discipline gate OK — no direct print_program call outside GoEmit.v / GoPrint.v ✓"

# 4. BRIDGE-RECOGNIZER scoping: each recognizer is `let is_X = named_in [...]` (the from_model
# guard lives ONCE in named_in); a raw global_basename match is a shadowing forge.
cov_preds='[is_i64_of_narrow_ref] / [is_f64_to_f32_ref]+[operand_is_runtime] / [is_f64_to_i64_ref] / [is_f64_to_u64_ref] / [is_int_of_fw] / [is_num_to_f64_ref] / [is_int_to_f32_ref]'
recog_def()    { awk -v p="$1" '$0 ~ ("^let " p "([ =:(]|$)"){f=1;print;next} f&&(/^let [A-Za-z_]/||/^\(\*/){exit} f{print}' "$2" 2>/dev/null; }
recog_routed() { b=$(recog_def "$1" "$2"); printf '%s' "$b" | grep -q 'named_in' && ! printf '%s' "$b" | grep -q 'global_basename'; }
st_t=$(mktemp)
printf '%s\n' 'let is_ok = named_in ["a"]' 'let mid x = 1' 'let is_raw r = List.mem (global_basename r) ["a"]' 'let named_in ns r = from_model r && List.mem (global_basename r) ns' > "$st_t"
# the named_in alias is "routed"; a raw global_basename body is not; named_in carries from_model.
if ! recog_routed is_ok "$st_t" || recog_routed is_raw "$st_t" || ! recog_def named_in "$st_t" | grep -q 'from_model'; then
  echo "fido: BRIDGE-RECOGNIZER TRIPWIRE self-test broke"; rm -f "$st_t"; exit 1
fi
rm -f "$st_t"
recog_def named_in plugin/go.ml | grep -q 'from_model' || { echo "fido: BRIDGE-RECOGNIZER TRIPWIRE — [named_in] lost its [from_model] guard; raw basename matching is a shadowing forge."; exit 1; }
for pred in $(printf '%s' "$cov_preds" | grep -oE '\[is_[a-z0-9_]+\]' | tr -d '[]'); do
  recog_routed "$pred" plugin/go.ml || { echo "fido: BRIDGE-RECOGNIZER TRIPWIRE — $pred should be 'let $pred = named_in [\"lit\"; …]', routing its basename match through the from_model-scoped [named_in] rather than a raw [global_basename]."; exit 1; }
done
echo "fido: bridge-recognizer tripwire OK — cov_preds recognizers route through the from_model-scoped named_in ✓"

# 5. SELECTOR-BRIDGE: mk_goexpr_sel emits local.Field only for a plain field of an MLrel receiver;
# dropping either guard re-opens a peel divergence the golden misses.
selctx=$(grep -B8 'mk_goexpr_sel ld' plugin/go.ml || true)
if ! printf '%s\n' "$selctx" | grep -q 'not (is_embedded_proj' || ! printf '%s\n' "$selctx" | grep -q 'MLrel _'; then
  echo "fido: SELECTOR-BRIDGE GATE — the ESel arm (mk_goexpr_sel) lost its 'not (is_embedded_proj r)' or 'MLrel' receiver guard; an embedded/nested selector would bridge to a peel-divergent form (invisible to the runtime golden)."
  exit 1
fi
echo "fido: selector-bridge gate OK — the ESel arm keeps its not-embedded + MLrel-receiver guards ✓"

# 6. UN-AUDITED-LOCAL-REGRESSION gate: nothing consumes an [Example], so a LOCAL Example sits
# outside every Print Assumptions cone (unaudited).  Discipline: an Example is PUBLIC and
# surfaced, or it does not exist.  Detector: plugin/local-example-lint.awk (Rocq-lexical).
# Scope: every .v (only _build/.git excluded).  Self-test: one corpus case per scanner state
# the detector's header claims (nesting, cross-line attrs, embedded strings/comments); the
# pinned count below is the authority.
lx_detect() { find "$1" -name '*.v' -not -path '*/_build/*' -not -path '*/.git/*' -print0 2>/dev/null \
              | xargs -0 -r awk -f plugin/local-example-lint.awk 2>/dev/null || true; }
lx_t=$(mktemp -d); mkdir -p "$lx_t/sub"
cat > "$lx_t/pos1.v" <<'LXEOF'
  Local Example st_a : True.
Local  Example st_b : True.
Local
Example st_c : True.
Local (* between *) Example st_d : True.
Local (* a (* nested *) b *) Example st_p : True.
Definition st_t := "x\".
Local Example st_j : True.
LXEOF
cat > "$lx_t/sub/pos2.v" <<'LXEOF'
#[local] Example st_e : True.
#[local]
Example st_f : True.
#[local] (* between *) Example st_g : True.
#[local] #[deprecated(note="x")] Example st_h : True.
#[deprecated(note="x")] #[local] Example st_i : True.
#[deprecated(note="]"), local] Example st_k : True.
#[deprecated(note="]")] #[local] Example st_l : True.
#[(* note *) local] Example st_q : True.
#[local, deprecated(note="a""b")] Example st_r : True.
#[local,
deprecated(note="x")]
Example st_v : True.
LXEOF
printf 'Local\r\nExample st_m : True.\r\n#[local]\r\nExample st_n : True.\r\n#[local]\r\n#[deprecated(note="x")]\r\nExample st_o : True.\r\n' > "$lx_t/sub/pos3.v"
cat > "$lx_t/neg.v" <<'LXEOF'
Example st_ok : True.
Local Lemma st_ok2 : True.
(* Local Example commented_out : True. *)
(* (* *) Local Example st_w : True. *)
Definition st_s := "Local Example in a string".
#[global] Example st_ok3 : True.
#[deprecated(note="local")] Example st_ok4 : True.
#[deprecated(note="x") (* local *)] Example st_x : True.
#[deprecated(note="a""local""b")] Example st_y : True.
Definition st_u := "a""b". Example st_ok5 : True.
LXEOF
hits=$(lx_detect "$lx_t" | grep -c .) || true
neg=$(awk -f plugin/local-example-lint.awk "$lx_t/neg.v" | grep -c .) || true
[ "$hits" = "19" ] && [ "$neg" = "0" ] || { echo "fido: LOCAL-EXAMPLE GATE self-test broke (expected 19 positives / 0 negatives, got $hits/$neg)"; rm -rf "$lx_t"; exit 1; }
rm -rf "$lx_t"
localex=$(lx_detect .)
if [ -n "$localex" ]; then
  echo "fido: LOCAL-EXAMPLE GATE — un-audited Local proof artifact(s) outside every Print Assumptions cone (make the Example public + bundle it into a surface, or delete it):"
  printf '%s\n' "$localex"
  exit 1
fi
echo "fido: local-example gate OK — Rocq-lexical sweep of every .v (Local/#[local] decoration chains, strings/comments excluded) found none ✓"
