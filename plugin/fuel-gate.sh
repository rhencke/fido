#!/bin/sh
# fuel-gate.sh — the budget-identifier ratchet (steering memo, plans/fuel-free.md "REQUIRED GATE").
#
# IDENTIFIER-AND-CONTEXT scoped over the root *.v files (comments stripped first, so
# prose mentions are not counted — the gate is code-level, never a prose linter):
#   CLASS A (unconditional budget identifiers, word-boundary):
#     fuel gas run_blocks_fuel block_fuel countdown allowance step_limit steps_left
#     max_steps max_depth depth_limit cycle_limit iteration_cap max_iter max_iterations
#     run_for parse_bound
#   CLASS B (nat-typed budget BINDERS in parens — catches step/steps/budget/limit/need/
#     capacity/bound USED AS an execution-cap parameter, while relation declarations
#     like [Inductive steps : nat -> ...] pass):
#     \((budget|limit|need|capacity|bound|step|steps)[ \t]*:[ \t]*nat\)
#   CLASS C (top-level nat cap CONSTANTS whose name embeds fuel/limit/budget/cap):
#     (Definition|Let) <name-containing-fuel|limit|budget|cap> : nat
# Small-step RELATIONS (Inductive/CoInductive step/steps/ustep) are NOT matched by any
# class — they are the prescribed replacement architecture, not fuel.
#
# Modes:
#   (none)    ratchet: total count must not EXCEED plugin/fuel-gate.baseline
#   bless     rewrite the baseline to the current (lower) count
#   selftest  fixture matrix in a temp dir: PASS/FAIL cases per the spec
set -eu
cd "$(dirname "$0")/.."

A='\b(fuel|gas|run_blocks_fuel|block_fuel|countdown|allowance|step_limit|steps_left|max_steps|max_depth|depth_limit|cycle_limit|iteration_cap|max_iter|max_iterations|run_for|parse_bound)\b'
B='\((budget|limit|need|capacity|bound|step|steps)[[:space:]]*:[[:space:]]*nat\)'
C='\b(Definition|Let)[[:space:]]+[A-Za-z0-9_]*(fuel|limit|budget|cap)[A-Za-z0-9_]*[[:space:]]*:[[:space:]]*nat\b'

# strip (possibly nested) Rocq comments, then count class matches.
count_file() {
  awk 'BEGIN { d = 0 }
       { n = split($0, ch, "");
         out = "";
         for (i = 1; i <= n; i++) {
           two = substr($0, i, 2);
           if (two == "(*") { d++; i++; continue }
           if (two == "*)" && d > 0) { d--; i++; continue }
           if (d == 0) out = out ch[i];
         }
         print out }' "$1" \
  | grep -E -c "$A|$B|$C" || true
}

count_all() {
  total=0
  for f in ./*.v; do
    c=$(count_file "$f")
    total=$((total + c))
  done
  echo "$total"
}

case "${1:-run}" in
  bless)
    count_all > plugin/fuel-gate.baseline
    echo "fido: fuel-gate baseline blessed: $(cat plugin/fuel-gate.baseline)"
    ;;
  selftest)
    tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
    # PASS fixtures: small-step relation declarations + non-budget uses — count must be 0.
    cat > "$tmp/pass.v" <<'EOF'
Inductive step : nat -> nat -> Prop := | step_intro : forall n, step n n.
Inductive steps : nat -> Prop := | steps_zero : steps 0.
Inductive ustep : Type := | u_one.
Lemma acc_measure : forall s : list nat, Acc lt (length s) -> True.
Proof. auto. Qed.
(* a comment mentioning fuel and block_fuel and max_steps is prose, not code *)
EOF
    p=$(count_file "$tmp/pass.v")
    [ "$p" = "0" ] || { echo "fido: fuel-gate SELFTEST FAILED — PASS fixture counted $p"; exit 1; }
    # FAIL fixtures: every canonical semantic-fuel shape must be detected.
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
Definition parse (need : nat) (limit : nat) (capacity : nat) (bound : nat) : nat := parse_bound.
Definition g (steps_left : nat) (max_iter : nat) (max_iterations : nat) : nat := 0.
Fixpoint run (steps : nat) : nat := 0.
Definition loop_cap : nat := 9.
EOF
    echo "fido: fuel-gate selftest OK (1 PASS fixture clean, $i FAIL fixtures detected)"
    ;;
  run|*)
    [ -f plugin/fuel-gate.baseline ] || { echo "fido: fuel-gate: missing plugin/fuel-gate.baseline (run: sh plugin/fuel-gate.sh bless)"; exit 1; }
    base=$(cat plugin/fuel-gate.baseline)
    cur=$(count_all)
    if [ "$cur" -gt "$base" ]; then
      echo "fido: FUEL GATE FAILED — budget-identifier count grew: $cur > baseline $base (no new fuel under any name; see plans/fuel-removal-steering.txt)"
      exit 1
    fi
    if [ "$cur" -lt "$base" ]; then
      echo "fido: fuel-gate OK ($cur <= $base) — count DROPPED; ratchet down with: sh plugin/fuel-gate.sh bless"
    else
      echo "fido: fuel-gate OK ($cur <= $base)"
    fi
    ;;
esac
