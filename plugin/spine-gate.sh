#!/bin/sh
# THE ONE spine-gate authority: compile the trust-boundary SOURCE SET standalone and assert
# ZERO axioms (grep '^Axioms:' over the one log every compile writes to).  Called by BOTH the
# Dockerfile prover stage and the Makefile local mirrors — a single definition, no drift path.
# EVERY failure path cleans the generated artifacts (vo/glob/aux of the ACTIVE file set +
# printer.ml), so read-only callers stay read-only even on a regression; on SUCCESS the
# artifacts are left for the caller (the printer flow consumes printer.ml, then CLEANs).
#   modes: printer | emit | selftest (no other mode exists — the gate is not a general runner)
set -eu

# run_gate <log> <file...> — the PRIVATE gate body; returns nonzero after cleaning on failure.
run_gate() {
  rg_log="$1"; shift
  : > "$rg_log"
  for rg_f in "$@"; do
    if ! rocq c -Q . Fido "$rg_f" >> "$rg_log" 2>&1; then
      echo "fido: spine ($*) failed to compile:"; cat "$rg_log"; clean_artifacts "$@"; return 1
    fi
  done
  if grep -q '^Axioms:' "$rg_log"; then
    echo "fido: SPINE AXIOM/ADMITTED — a gated spine theorem depends on an axiom (Print Assumptions over $*):"
    cat "$rg_log"; clean_artifacts "$@"; return 1
  fi
}
clean_artifacts() {
  for ca_f in "$@"; do ca_b="${ca_f%.v}"; rm -f "$ca_b.vo" "$ca_b.glob" ".$ca_b.aux"; done
  rm -f printer.ml
}

case "$1" in
  printer) run_gate "$2" digits.v GoAst.v GoPrint.v ;;
  emit)    run_gate "$2" digits.v GoAst.v GoPrint.v GoTypes.v GoCompile.v GoEmit.v ;;
  selftest)
    # The gate REQUIRES rocq: without it every [run_gate] would "fail" for the WRONG reason (a missing
    # compiler, not a rejected spine), so both failure branches would pass VACUOUSLY and print a misleading
    # OK.  Refuse LOUDLY instead — an unverifiable gate must never self-report success.
    command -v rocq >/dev/null 2>&1 || {
      echo "fido: spine-gate selftest CANNOT RUN — 'rocq' not found; the gate is unverifiable here" >&2
      exit 1; }
    # Verify the FULL contract in an isolated dir: the SUCCESS path (a clean spine compiles, [run_gate]
    # returns 0, and its .vo SURVIVES for the caller) AND both FAILURE branches (axiom + broken each reject
    # and clean up — nothing survives, even a good file already in the set + a sentinel printer.ml).
    d="$(mktemp -d)"
    printf 'Definition sg_ok : nat := 0.\n' > "$d/sg_ok.v"
    printf 'Axiom sg_ax : True.\nPrint Assumptions sg_ax.\n' > "$d/sg_ax.v"
    printf 'this is not gallina\n' > "$d/sg_broken.v"
    # (a) SUCCESS path — a real compile that PASSES leaves its artifact (proves the gate is not
    #     vacuously "OK": [run_gate] actually reached rocq and accepted a clean, axiom-free spine).
    ok=0
    ( cd "$d" || exit 5
      run_gate spine.log sg_ok.v >/dev/null 2>&1 || exit 6
      [ -e sg_ok.vo ] || exit 7
      exit 0 ) || ok=$?
    if [ "$ok" -ne 0 ]; then
      echo "fido: spine-gate selftest FAILED (success path, code $ok) — a clean spine must compile AND leave its .vo" >&2
      rm -rf "$d"; exit 1
    fi
    rm -f "$d/sg_ok.vo" "$d/sg_ok.glob" "$d/.sg_ok.aux" "$d/printer.ml"
    # (b) FAILURE paths — reject + clean.
    for bad in sg_ax sg_broken; do
      fail=0
      ( cd "$d" || exit 5
        printf 'sentinel\n' > printer.ml
        if run_gate spine.log sg_ok.v "$bad.v" >/dev/null 2>&1; then exit 3; fi
        for a in sg_ok.vo sg_ok.glob .sg_ok.aux "$bad.vo" "$bad.glob" ".$bad.aux" printer.ml; do
          if [ -e "$a" ]; then exit 4; fi
        done
        exit 0 ) || fail=$?
      if [ "$fail" -ne 0 ]; then
        echo "fido: spine-gate selftest FAILED (branch $bad, code $fail) — the cleanup contract is broken" >&2
        rm -rf "$d"; exit 1
      fi
    done
    rm -rf "$d"
    echo "fido: spine-gate selftest OK (rocq present; success path compiles+survives; axiom + compile failure branches reject+clean) ✓" ;;
  *) echo "spine-gate: unknown mode $1" >&2; exit 2 ;;
esac
