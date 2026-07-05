#!/bin/sh
# fuel-gate.sh — the budget-identifier ratchet (steering memo, plans/fuel-free.md "REQUIRED GATE").
#
# IDENTIFIER-AND-CONTEXT scoped over the scanned *.v files (comments stripped first, so
# prose mentions are not counted — the gate is code-level, never a prose linter):
#   CLASS A (unconditional budget identifiers, word-boundary, counted PER OCCURRENCE):
#     fuel gas run_blocks_fuel block_fuel countdown allowance step_limit steps_left
#     max_steps max_depth depth_limit cycle_limit iteration_cap max_iter max_iterations
#     run_for parse_bound
#   CLASS B (budget-named binders in ( ) or { } groups typed nat — grouped and implicit
#     binders included, so [(need limit capacity bound : nat)] and [{steps : nat}] count;
#     relation declarations like [Inductive steps : nat -> ...] have no bracket group and pass):
#   CLASS C (top-level Definition/Let whose NAME contains a budget SEGMENT
#     fuel|limit|budget|cap, underscore-bounded so e.g. [escape] never matches; the type
#     annotation is NOT required, so [Definition loop_cap := 9] counts):
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

A='\b(fuel|gas|run_blocks_fuel|block_fuel|countdown|allowance|step_limit|steps_left|max_steps|max_depth|depth_limit|cycle_limit|iteration_cap|max_iter|max_iterations|run_for|parse_bound)\b'
B='[({][^(){}:]*\b(budget|limit|need|capacity|bound|step|steps)\b[^(){}:]*:[[:space:]]*nat'
C="\\b(Definition|Let)[[:space:]]+([A-Za-z0-9']+_)*(fuel|limit|budget|cap)(_[A-Za-z0-9']+)*\\b"

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

count_file() {  # per-OCCURRENCE count across the three classes
  s=$(strip_comments "$1")
  a=$(printf '%s\n' "$s" | grep -oE "$A" | wc -l)
  b=$(printf '%s\n' "$s" | grep -oE "$B" | wc -l)
  c=$(printf '%s\n' "$s" | grep -oE "$C" | wc -l)
  echo $((a + b + c))
}

manifest() {  # "count<TAB>file" for every scanned file with count > 0, sorted by file
  for f in "$SCAN_DIR"/*.v; do
    [ -e "$f" ] || continue
    c=$(count_file "$f")
    [ "$c" = "0" ] || printf '%s\t%s\n' "$c" "$(basename "$f")"
  done | LC_ALL=C sort -k2
}

grew() {  # exit 0 if any file's current count exceeds its baseline entry
  manifest | while IFS="$(printf '\t')" read -r c f; do
    b=$(awk -F'\t' -v f="$f" '$2 == f { print $1 }' "$BASELINE")
    [ -n "$b" ] || b=0
    if [ "$c" -gt "$b" ]; then
      echo "fido: FUEL GATE — $f has $c budget occurrences (baseline $b)"
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
    # per-OCCURRENCE counting: one line, four class-A identifiers, count must be 4
    printf 'Definition z := fuel + gas + max_steps + run_for.\n' > "$tmp/multi.v"
    m=$(count_file "$tmp/multi.v")
    [ "$m" = "4" ] || { echo "fido: fuel-gate SELFTEST FAILED — multi-occurrence line counted $m, want 4"; exit 1; }
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
    echo "fido: fuel-gate selftest OK (pass fixture clean; $i shapes + multi-count + swap + bless-down enforced)"
    ;;
  run|*)
    [ -f "$BASELINE" ] || { echo "fido: fuel-gate: missing $BASELINE (run: sh plugin/fuel-gate.sh bless)"; exit 1; }
    if grew; then
      echo "fido: FUEL GATE FAILED — no new fuel under any name (see plans/fuel-removal-steering.txt)"
      exit 1
    fi
    echo "fido: fuel-gate OK (no file above its baseline manifest entry)"
    ;;
esac
