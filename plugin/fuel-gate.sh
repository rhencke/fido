#!/bin/sh
# fuel-gate.sh — the budget-identifier ratchet.  THIS SCRIPT IS THE MECHANICAL AUTHORITY
# for the fuel gate: the CLASS DEFINITIONS below (A/B/C, single-sourced in the variables)
# are the spec.  The selftest is a REGRESSION FIXTURE MATRIX derived from those same
# variables — every class-A alias, B stem, and C segment gets a generated FAIL fixture,
# plus shaped contextual cases (plans/fuel-free.md only summarizes this).
#
# IDENTIFIER-AND-CONTEXT scoped over the scanned files — the certified *.v AND the
# trusted plugin *.ml, with language-aware classes (comments stripped first, so
# prose mentions are not counted — the gate is code-level, never a prose linter):
#   CLASS A (unconditional budget identifiers, word-boundary, counted PER OCCURRENCE):
#     fuel gas run_blocks_fuel block_fuel countdown allowance step_limit steps_left
#     max_steps max_depth depth_limit cycle_limit max_iter max_iterations run_for
#     parse_bound   (budget *_cap NAMES are covered generically by the CAP CLASS)
#   CLASS B (budget-named binders in ( ) or { } groups typed nat — grouped and implicit
#     binders included, so [(need limit capacity bound : nat)] and [{steps : nat}] count;
#     relation declarations like [Inductive steps : nat -> ...] have no bracket group and pass):
#   CLASS C (top-level Definition/Let whose NAME contains a budget SEGMENT
#     fuel|limit|budget, underscore-bounded so e.g. [escape] never matches; the type
#     annotation is NOT required), plus the CAP CLASS: cap-segment identifiers
#     default-reject PER OCCURRENCE in both languages, behind the enumerated
#     domain-capacity allowlist (ALLOWCAP below):
# Small-step RELATIONS (Inductive/CoInductive step/steps/ustep) match no class.
#
# BASELINE = a PER-FILE occurrence MANIFEST (plugin/fuel-gate.baseline: "count<TAB>file").
# The ratchet fails if ANY file's count exceeds its manifest entry (a new fuel site cannot
# hide behind a deletion elsewhere, nor behind an already-matching line).  bless is
# DOWN-ONLY: it refuses if any file's count grew.
#
# Modes: (none) ratchet | bless (down-only) | selftest (fixture matrix).
set -eu
cd "$(dirname "$0")/.."
SCAN_DIR="${FG_SCAN_DIR:-.}"
BASELINE="${FG_BASELINE:-plugin/fuel-gate.baseline}"

ANAMES='fuel gas run_blocks_fuel block_fuel countdown allowance step_limit steps_left max_steps max_depth depth_limit cycle_limit max_iter max_iterations run_for parse_bound'
A="\\b($(echo $ANAMES | tr ' ' '|'))\\b"
BSTEMS='budget|limit|need|capacity|bound|step|steps'
CSEGS='fuel|limit|budget'
# CAP CLASS (default-reject, PER OCCURRENCE, both languages): every identifier
# containing an underscore-bounded 'cap' segment counts — as a declaration of ANY
# form, a binder, or a reference — UNLESS it is one of the enumerated Go-capacity
# DOMAIN symbols below (the cap builtin, the channel/slice capacity ops and lemmas,
# and their plugin recognizers).  Any NEW cap-segment name fails the ratchet until
# it is either renamed or consciously classified here as capacity-domain.
ALLOWCAP='cap|cap_slicelit_e|cap_demo|cap_aliases|chan_cap|chan_cap_send|chan_cap_recv|chan_cap_close|chan_cap_write_same|sh_cap|make_chan_cap|make_chan_buf_cap|is_cap_ref|is_make_chan_cap_ref|cstep_cap|cstep_cap_respected|csteps_cap|csteps_cap_respected|csteps_from_empty_cap_respected|rstep_at_some_cap|subslice_past_cap_panics'

count_cap() {  # stdin = stripped source.  FULL-TOKEN classification: extract complete
  # Rocq/OCaml identifiers (primes included), NORMALIZE by deleting primes, then keep
  # tokens whose normalized form has an underscore-bounded 'cap' segment and is not an
  # allowlisted domain stem.  So [chan_cap'] classifies as the domain stem chan_cap,
  # [loop_cap'] counts, and camouflage like [chan_cap'_budget] normalizes to
  # chan_cap_budget and counts.
  grep -oE "[A-Za-z_][A-Za-z0-9_']*" \
    | tr -d "'" \
    | grep -E "^(.*_)?cap(_.*)?$" \
    | grep -vxE "$ALLOWCAP" | wc -l
}
C="\\b(Definition|Let)[[:space:]]+([A-Za-z0-9']+_)*($CSEGS)(_[A-Za-z0-9']+)*\\b"
CML="\\blet([[:space:]]+rec)?[[:space:]]+([A-Za-z0-9_']+_)*($CSEGS)(_[A-Za-z0-9_']+)*\\b"

strip_comments() {
  awk 'BEGIN { d = 0 }
       { n = length($0); out = "";
         for (i = 1; i <= n; i++) {
           two = substr($0, i, 2);
           if (two == "(*") { d++; i++; continue }
           if (two == "*)" && d > 0) { d--; i++; continue }
           if (d == 0) out = out substr($0, i, 1);
         }
         print out }' "$1"
}

# CLASS B: a TOKEN-LEVEL scan of binder groups — every ( ... ) / { ... } group whose
# type annotation is exactly [nat] contributes ONE count PER budget-named identifier in
# the group, across whitespace AND newlines (so [(need limit capacity bound : nat)]
# counts 4, [{step steps : nat}] counts 2, and a line-broken group still counts).
count_b() {
  awk -v q="'" -v bs="$BSTEMS" '
    { gsub(/[(){}:]/, " & "); n = split($0, t, /[ \t]+/);
      for (i = 1; i <= n; i++) {
        tok = t[i]; if (tok == "") continue;
        if (tok == "(" || tok == "{") { d++; ids[d] = ""; col[d] = 0; typ[d] = "" }
        else if (tok == ")" || tok == "}") {
          if (d > 0) {
            if (col[d] && typ[d] == "nat") {
              m = split(ids[d], w, " ");
              for (j = 1; j <= m; j++)
                if (w[j] ~ ("^(" bs ")" q "*$")) cnt++
            }
            d--
          }
        }
        else if (tok == ":") { if (d > 0) col[d] = 1 }
        else if (d > 0) {
          if (!col[d]) ids[d] = ids[d] " " tok;
          else typ[d] = (typ[d] == "" ? tok : typ[d] " " tok)
        }
      }
    }
    END { print cnt + 0 }'
}

count_file() {  # per-OCCURRENCE count; classes are LANGUAGE-AWARE by file suffix:
  # class A everywhere; Rocq files get the binder-group scan (B) and Definition/Let
  # constants (C); OCaml files get top-level let/let-rec budget-segment bindings (CML);
  # the default-reject cap class applies in BOTH languages (count_cap).
  s=$(strip_comments "$1")
  a=$(printf '%s\n' "$s" | grep -oE "$A" | wc -l)
  case "$1" in
    *.ml)
      b=0
      c=$(printf '%s\n' "$s" | grep -oE "$CML" | wc -l) ;;
    *)
      b=$(printf '%s\n' "$s" | count_b)
      c=$(printf '%s\n' "$s" | grep -oE "$C" | wc -l) ;;
  esac
  k=$(printf '%s\n' "$s" | count_cap)
  echo $((a + b + c + k))
}

manifest() {  # "count<TAB>path" for every scanned file with count > 0, sorted by path.
  # Scope: the certified .v files AND the trusted plugin OCaml sources (comment syntax
  # is identical).  Shell/Make/doc surfaces are OUT of scope by design: the gate is
  # code-level (never a prose linter) and its own name contains the word.
  for f in "$SCAN_DIR"/*.v "$SCAN_DIR"/plugin/*.ml; do
    [ -e "$f" ] || continue
    c=$(count_file "$f")
    rel=${f#"$SCAN_DIR"/}
    [ "$c" = "0" ] || printf '%s\t%s\n' "$c" "$rel"
  done | LC_ALL=C sort -k2
}

grew() {  # exit 0 if any file's current count exceeds its baseline entry
  manifest | while IFS="$(printf '\t')" read -r c f; do
    b=$(awk -F'\t' -v f="$f" '$2 == f { print $1 }' "$BASELINE")
    [ -n "$b" ] || b=0
    if [ "$c" -gt "$b" ]; then
      echo "fido: FUEL GATE — $f has $c budget occurrences (baseline $b) — no new fuel under any name"
    fi
  done | grep . >&2
}

case "${1:-run}" in
  bless)
    if [ -f "$BASELINE" ] && grew; then
      echo "fido: fuel-gate bless REFUSED — the count grew somewhere; bless is DOWN-ONLY (delete the fuel, don't ratify it)"
      exit 1
    fi
    manifest > "$BASELINE"
    echo "fido: fuel-gate baseline blessed ($(wc -l < "$BASELINE") files carry fuel debt)"
    ;;
  selftest)
    tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
    cat > "$tmp/pass.v" <<'EOF'
Inductive step : nat -> nat -> Prop := | step_intro : forall n, step n n.
Inductive steps : nat -> Prop := | steps_zero : steps 0.
Inductive ustep : Type := | u_one.
Definition escape (n : nat) : nat := n.
Lemma acc_measure : forall s : list nat, Acc lt (length s) -> True.
Proof. auto. Qed.
(* prose mentions of fuel, block_fuel and max_steps do not count *)
EOF
    p=$(count_file "$tmp/pass.v")
    [ "$p" = "0" ] || { echo "fido: fuel-gate SELFTEST FAILED — PASS fixture counted $p"; exit 1; }
    i=0
    while IFS= read -r line; do
      i=$((i + 1))
      printf '%s\n' "$line" > "$tmp/fail$i.v"
      c=$(count_file "$tmp/fail$i.v")
      [ "$c" != "0" ] || { echo "fido: fuel-gate SELFTEST FAILED — undetected: $line"; exit 1; }
    done <<'EOF'
Definition block_fuel : nat := 1000.
Fixpoint run_blocks_fuel (fuel start : nat) (blocks : list nat) : nat := 0.
Definition run_blocks := run_blocks_fuel block_fuel.
Definition f (max_steps : nat) (countdown : nat) (allowance : nat) : nat := 0.
Definition parse (need limit capacity bound : nat) : nat := parse_bound.
Definition g (steps_left : nat) (max_iter : nat) (max_iterations : nat) : nat := 0.
Fixpoint run (steps : nat) : nat := 0.
Definition h {steps : nat} : nat := 0.
Definition loop_cap := 9.
EOF
    # EXHAUSTIVE derived fixtures — one per class-A alias, B stem, C segment, from the
    # SAME variables that define the gate (the matrix cannot lag the classes).
    for nm in $ANAMES; do
      printf 'Definition z := %s.\n' "$nm" > "$tmp/da.v"
      [ "$(count_file "$tmp/da.v")" != "0" ] || { echo "fido: fuel-gate SELFTEST FAILED — class-A alias undetected: $nm"; exit 1; }
    done
    for st in $(echo "$BSTEMS" | tr '|' ' '); do
      printf 'Definition t (%s : nat) : nat := 0.\n' "$st" > "$tmp/db.v"
      [ "$(count_file "$tmp/db.v")" = "1" ] || { echo "fido: fuel-gate SELFTEST FAILED — class-B stem not counted once: $st"; exit 1; }
      printf "Definition t (%s' : nat) : nat := 0.\n" "$st" > "$tmp/db2.v"
      [ "$(count_file "$tmp/db2.v")" = "1" ] || { echo "fido: fuel-gate SELFTEST FAILED — primed class-B stem not counted once: $st"; exit 1; }
    done
    for sg in $(echo "$CSEGS" | tr '|' ' '); do
      printf 'Definition my_%s : nat := 3.\n' "$sg" > "$tmp/dc.v"
      [ "$(count_file "$tmp/dc.v")" != "0" ] || { echo "fido: fuel-gate SELFTEST FAILED — class-C segment undetected (Definition): $sg"; exit 1; }
      printf 'Let %s_x : nat := 3.\n' "$sg" > "$tmp/dc2.v"
      [ "$(count_file "$tmp/dc2.v")" != "0" ] || { echo "fido: fuel-gate SELFTEST FAILED — class-C segment undetected (Let): $sg"; exit 1; }
    done
    # per-OCCURRENCE counting: one line, four class-A identifiers, count must be 4
    printf 'Definition z := fuel + gas + max_steps + run_for.\n' > "$tmp/multi.v"
    m=$(count_file "$tmp/multi.v")
    [ "$m" = "4" ] || { echo "fido: fuel-gate SELFTEST FAILED — multi-occurrence line counted $m, want 4"; exit 1; }
    # EXACT grouped-binder counts (occurrences, not groups; multiline-safe)
    printf 'Definition parse (need limit capacity bound : nat) : nat := 0.\n' > "$tmp/grp.v"
    g=$(count_file "$tmp/grp.v")
    [ "$g" = "4" ] || { echo "fido: fuel-gate SELFTEST FAILED — grouped binders counted $g, want 4"; exit 1; }
    printf 'Definition h {step steps : nat} : nat := 0.\n' > "$tmp/imp.v"
    g=$(count_file "$tmp/imp.v")
    [ "$g" = "2" ] || { echo "fido: fuel-gate SELFTEST FAILED — implicit group counted $g, want 2"; exit 1; }
    printf 'Definition p (need limit capacity bound\n : nat) : nat := 0.\n' > "$tmp/ml.v"
    g=$(count_file "$tmp/ml.v")
    [ "$g" = "4" ] || { echo "fido: fuel-gate SELFTEST FAILED — multiline group counted $g, want 4"; exit 1; }
    # PRIMED budget binders count per identifier too (Rocq [x'] spellings)
    printf "Definition pp (need' limit' capacity' bound' : nat) : nat := 0.\n" > "$tmp/pr.v"
    g=$(count_file "$tmp/pr.v")
    [ "$g" = "4" ] || { echo "fido: fuel-gate SELFTEST FAILED — primed group counted $g, want 4"; exit 1; }
    printf "Definition hp {step' steps' : nat} : nat := 0.\n" > "$tmp/pri.v"
    g=$(count_file "$tmp/pri.v")
    [ "$g" = "2" ] || { echo "fido: fuel-gate SELFTEST FAILED — primed implicit group counted $g, want 2"; exit 1; }
    # widening a PRIMED group must trip the ratchet
    mkdir "$tmp/scan3"
    printf "Definition r (need' : nat) : nat := 0.\n" > "$tmp/scan3/a.v"
    ( FG_SCAN_DIR="$tmp/scan3" FG_BASELINE="$tmp/base3" sh plugin/fuel-gate.sh bless >/dev/null )
    printf "Definition r (need' limit' : nat) : nat := 0.\n" > "$tmp/scan3/a.v"
    if ( FG_SCAN_DIR="$tmp/scan3" FG_BASELINE="$tmp/base3" sh plugin/fuel-gate.sh run >/dev/null 2>&1 ); then
      echo "fido: fuel-gate SELFTEST FAILED — widened primed group passed the ratchet"; exit 1
    fi
    # plugin OCaml sources are in scope, with OCaml-shaped classes: class-A aliases AND
    # lower-case let/let-rec budget-segment bindings are counted, per occurrence
    mkdir -p "$tmp/scanml/plugin"
    printf 'let block_fuel = 1000\n' > "$tmp/scanml/plugin/x.ml"
    ( FG_SCAN_DIR="$tmp/scanml" FG_BASELINE="$tmp/baseml" sh plugin/fuel-gate.sh bless >/dev/null )
    grep -q 'plugin/x.ml' "$tmp/baseml" || { echo "fido: fuel-gate SELFTEST FAILED — .ml budget identifier not manifested"; exit 1; }
    printf 'let loop_cap = 9\n' > "$tmp/scanml/plugin/y.ml"
    [ "$(count_file "$tmp/scanml/plugin/y.ml")" = "1" ] || { echo "fido: fuel-gate SELFTEST FAILED — OCaml let cap binding not counted"; exit 1; }
    printf 'let rec parse_budget n = n\n' > "$tmp/scanml/plugin/z.ml"
    [ "$(count_file "$tmp/scanml/plugin/z.ml")" = "1" ] || { echo "fido: fuel-gate SELFTEST FAILED — OCaml let-rec budget binding not counted"; exit 1; }
    # NEW *_cap names are budget spellings (default-reject) in BOTH languages,
    # while the enumerated domain-capacity symbols stay clean
    printf 'Definition cycle_cap := 1.\n' > "$tmp/capv.v"
    [ "$(count_file "$tmp/capv.v")" = "1" ] || { echo "fido: fuel-gate SELFTEST FAILED — new .v *_cap name not counted"; exit 1; }
    printf 'let parse_cap = 1\n' > "$tmp/capml.ml"
    [ "$(count_file "$tmp/capml.ml")" = "1" ] || { echo "fido: fuel-gate SELFTEST FAILED — new .ml *_cap name not counted"; exit 1; }
    printf 'Definition f (loop_cap : nat) : nat := loop_cap.\n' > "$tmp/capb.v"
    [ "$(count_file "$tmp/capb.v")" = "2" ] || { echo "fido: fuel-gate SELFTEST FAILED — cap binder+reference not counted per occurrence"; exit 1; }
    printf 'Fixpoint iteration_cap (n : nat) : nat := n.\n' > "$tmp/capf.v"
    [ "$(count_file "$tmp/capf.v")" = "1" ] || { echo "fido: fuel-gate SELFTEST FAILED — Fixpoint cap name not counted"; exit 1; }
    printf 'let f loop_cap = loop_cap\n' > "$tmp/capbml.ml"
    [ "$(count_file "$tmp/capbml.ml")" = "2" ] || { echo "fido: fuel-gate SELFTEST FAILED — .ml cap binder+reference not counted"; exit 1; }
    printf "Definition chan_cap' := 0.\n" > "$tmp/capprime.v"
    [ "$(count_file "$tmp/capprime.v")" = "0" ] || { echo "fido: fuel-gate SELFTEST FAILED — primed DOMAIN cap name counted"; exit 1; }
    printf "Definition loop_cap' := 1.\n" > "$tmp/capprimebad.v"
    [ "$(count_file "$tmp/capprimebad.v")" = "1" ] || { echo "fido: fuel-gate SELFTEST FAILED — primed BUDGET cap name not counted"; exit 1; }
    printf "Definition x := chan_cap'_budget.\n" > "$tmp/capcamo.v"
    [ "$(count_file "$tmp/capcamo.v")" = "1" ] || { echo "fido: fuel-gate SELFTEST FAILED — allowed-stem camouflage (chan_cap'_budget) not counted"; exit 1; }
    printf 'Definition make_chan_cap := 0.\nDefinition chan_cap := 0.\nDefinition cap := 0.\n' > "$tmp/capok.v"
    [ "$(count_file "$tmp/capok.v")" = "0" ] || { echo "fido: fuel-gate SELFTEST FAILED — domain-cap allowlist counted"; exit 1; }
    printf 'let is_cap_ref r = r\n' > "$tmp/capok.ml"
    [ "$(count_file "$tmp/capok.ml")" = "0" ] || { echo "fido: fuel-gate SELFTEST FAILED — .ml domain-cap allowlist counted"; exit 1; }
    # ratchet growth INSIDE a plugin .ml must fail
    ( FG_SCAN_DIR="$tmp/scanml" FG_BASELINE="$tmp/baseml2" sh plugin/fuel-gate.sh bless >/dev/null )
    printf 'let block_fuel = 1000\nlet step_limit = 2\n' > "$tmp/scanml/plugin/x.ml"
    if ( FG_SCAN_DIR="$tmp/scanml" FG_BASELINE="$tmp/baseml2" sh plugin/fuel-gate.sh run >/dev/null 2>&1 ); then
      echo "fido: fuel-gate SELFTEST FAILED — .ml ratchet growth passed"; exit 1
    fi
    # widening an EXISTING group must trip the ratchet
    mkdir "$tmp/scan2"
    printf 'Definition q (need : nat) : nat := 0.\n' > "$tmp/scan2/a.v"
    ( FG_SCAN_DIR="$tmp/scan2" FG_BASELINE="$tmp/base2" sh plugin/fuel-gate.sh bless >/dev/null )
    printf 'Definition q (need limit : nat) : nat := 0.\n' > "$tmp/scan2/a.v"
    if ( FG_SCAN_DIR="$tmp/scan2" FG_BASELINE="$tmp/base2" sh plugin/fuel-gate.sh run >/dev/null 2>&1 ); then
      echo "fido: fuel-gate SELFTEST FAILED — widened binder group passed the ratchet"; exit 1
    fi
    # manifest ratchet: a deletion in one file must NOT excuse a new site in another
    mkdir "$tmp/scan"
    printf 'Definition block_fuel : nat := 1.\nDefinition x := gas.\n' > "$tmp/scan/a.v"
    ( FG_SCAN_DIR="$tmp/scan" FG_BASELINE="$tmp/base" sh plugin/fuel-gate.sh bless >/dev/null )
    printf 'Definition block_fuel : nat := 1.\n' > "$tmp/scan/a.v"   # one removed...
    printf 'Definition y := countdown.\n' > "$tmp/scan/b.v"          # ...one added elsewhere
    if ( FG_SCAN_DIR="$tmp/scan" FG_BASELINE="$tmp/base" sh plugin/fuel-gate.sh run >/dev/null 2>&1 ); then
      echo "fido: fuel-gate SELFTEST FAILED — cross-file swap passed the ratchet"; exit 1
    fi
    # bless is DOWN-ONLY: with the grown scan dir, bless must refuse
    if ( FG_SCAN_DIR="$tmp/scan" FG_BASELINE="$tmp/base" sh plugin/fuel-gate.sh bless >/dev/null 2>&1 ); then
      echo "fido: fuel-gate SELFTEST FAILED — bless ratified growth"; exit 1
    fi
    echo "fido: fuel-gate selftest OK (pass fixture clean; $i shaped cases + exhaustive per-alias/stem/segment fixtures + multi-count + swap + bless-down)"
    ;;
  run|*)
    [ -f "$BASELINE" ] || { echo "fido: fuel-gate: missing $BASELINE (run: sh plugin/fuel-gate.sh bless)"; exit 1; }
    if grew; then
      echo "fido: FUEL GATE FAILED — delete the budget identifier or the construct that needs it (the class definitions ANAMES/BSTEMS/CSEGS near the top of plugin/fuel-gate.sh are the authority)"
      exit 1
    fi
    echo "fido: fuel-gate OK (no file above its baseline manifest entry)"
    ;;
esac
