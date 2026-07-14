#!/bin/sh
# Pre-commit / staged-tree-gate SELF-TEST (contract §27) — a deterministic, Buildx-free host gate that
# DEMONSTRATES the staged-index verification cannot be bypassed.  It builds synthetic "exported staged
# snapshot" trees (exactly what `git checkout-index --prefix` produces) with the REAL gate scripts copied in,
# injects each adversarial scenario, and asserts the staged-tree gates behave correctly.  It walks no Rocq
# terms and needs no Docker, so it runs as a host gate inside `make check`.
#
# The five required demonstrations:
#   1. staged bad OCaml (hidden/underscore/testdata/vendor) + a safe working tree is REJECTED — the gate is a
#      repository-content gate over the staged snapshot, NOT the runtime sink, so no directory name is opaque;
#   2. a staged bad gate script + a safe working-tree script cannot bypass — the STAGED gate implementation is
#      the one executed, and weakening one gate does not defeat the independent others;
#   3. a stale / missing / modified / extra / symlinked / deep staged generated file is REJECTED (recursive,
#      no opaque-directory skip);
#   4. a docs-only ordinary commit still runs the COMPLETE verification (the hook has no changed-file skip list);
#   5. the hook never mutates the working tree or the index.
set -eu

here=$(CDPATH= cd "$(dirname "$0")/.." && pwd)
hook="$here/.githooks/pre-commit"
hdr='// fido generated.  do not edit.'
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
pass=0; fail=0
ok()  { printf 'fido: precommit-selftest — PASS: %s\n' "$1"; pass=$((pass + 1)); }
bad() { printf 'fido: precommit-selftest — FAIL: %s\n' "$1"; fail=$((fail + 1)); }

# a minimal VALID exported staged snapshot at $1: the real gate scripts + a byte-canonical go.mod + main.go.
# NB: sh has no locals — these helpers use `sd`/`pd` so they never clobber a caller's loop variable (`d`).
mk_snapshot() {
  sd=$1; mkdir -p "$sd/tools"
  cp "$here/tools/ocaml-origin-gate.sh" "$here/tools/generated-output-gate.sh" \
     "$here/tools/staged-generated-compare.sh" "$sd/tools/"
  printf '%s\nmodule fido.local/generated\n\ngo 1.23\n'      "$hdr" > "$sd/go.mod"
  printf '%s\npackage main\n\nfunc main() {}\n'              "$hdr" > "$sd/main.go"
}
# a pristine generated tree byte-identical to mk_snapshot's go.mod + main.go.
mk_pristine() {
  pd=$1; mkdir -p "$pd"
  printf '%s\nmodule fido.local/generated\n\ngo 1.23\n'      "$hdr" > "$pd/go.mod"
  printf '%s\npackage main\n\nfunc main() {}\n'              "$hdr" > "$pd/main.go"
}
reject() { desc=$1; shift; if "$@" >/dev/null 2>&1; then bad "$desc — a bad tree was ACCEPTED"; else ok "$desc"; fi; }
accept() { desc=$1; shift; if "$@" >/dev/null 2>&1; then ok "$desc"; else bad "$desc — a good tree was REJECTED"; fi; }

# ---- (1) staged bad OCaml / bad .go under every opaque directory name is caught ----
for d in .hidden _priv testdata vendor; do
  s="$work/s1-ml-$d"; mk_snapshot "$s"; mkdir -p "$s/$d"; printf 'let () = ()\n' > "$s/$d/rogue.ml"
  reject "staged foreign OCaml under $d/ rejected by ocaml-origin gate" sh "$s/tools/ocaml-origin-gate.sh" "$s"

  s="$work/s1-go-$d"; mk_snapshot "$s"; mkdir -p "$s/$d"; printf 'package x\n' > "$s/$d/rogue.go"
  reject "staged unheaded .go under $d/ rejected by generated-output gate" sh "$s/tools/generated-output-gate.sh" "$s"

  s="$work/s1-exe-$d"; mk_snapshot "$s"; mkdir -p "$s/$d"; printf '%s\npackage x\n' "$hdr" > "$s/$d/rogue.go"; chmod +x "$s/$d/rogue.go"
  reject "staged executable (mode 100755) .go under $d/ rejected" sh "$s/tools/generated-output-gate.sh" "$s"

  s="$work/s1-lnk-$d"; mk_snapshot "$s"; mkdir -p "$s/$d"; ln -s ../go.mod "$s/$d/rogue.go"
  reject "staged symlink .go under $d/ rejected" sh "$s/tools/generated-output-gate.sh" "$s"
done
# and a genuinely clean snapshot is accepted (no false positives from dropping the opaque-dir prune)
s="$work/s1-clean"; mk_snapshot "$s"
accept "a clean staged snapshot passes the ocaml-origin gate"     sh "$s/tools/ocaml-origin-gate.sh" "$s"
accept "a clean staged snapshot passes the generated-output gate" sh "$s/tools/generated-output-gate.sh" "$s"

# ---- (2) drive the ACTUAL hook under REAL staged/worktree divergence (Buildx-free via a fake docker) ----
# This creates a throwaway Git repo, diverges its index from its working tree, and runs the real
# .githooks/pre-commit — proving the hook checks the STAGED index (not the working tree) and executes the
# STAGED gate implementations.  A fake `docker` makes `buildx build` a sentinel (exit 7), so a run that gets
# PAST the staged structural gates into the Buildx phase is distinguishable from one rejected at a gate.
# Skipped when THIS run is itself nested under a hook (the commit-time hook runs the self-test with
# FIDO_SELFTEST_NESTED=1) — that both avoids infinite recursion and keeps commits fast, while scenarios
# 1/3/4/5 still run on the staged tree at commit time; the hook-driven divergence test runs under `make
# check` / the standalone `make precommit-selftest`.
if [ "${FIDO_SELFTEST_NESTED:-0}" = 1 ]; then
  ok "nested under a hook — hook-driven divergence test skipped to avoid recursion (scenarios 1/3/4/5 still ran on the staged tree)"
else
  set +e   # the raw git/hook commands below manage their own exit codes (a rejecting hook returns nonzero)
  repo="$work/hookrepo"; mkdir -p "$repo/tools" "$repo/.githooks"
  cp "$here/tools/ocaml-origin-gate.sh" "$here/tools/generated-output-gate.sh" \
     "$here/tools/staged-generated-compare.sh" "$here/tools/precommit-selftest.sh" "$repo/tools/"
  cp "$here/.githooks/pre-commit" "$repo/.githooks/pre-commit"
  printf '%s\nmodule fido.local/generated\n\ngo 1.23\n' "$hdr" > "$repo/go.mod"
  printf '%s\npackage main\n\nfunc main() {}\n'        "$hdr" > "$repo/main.go"
  ( cd "$repo"
    git init -q
    git config user.email t@fido.test; git config user.name fido-selftest; git config commit.gpgsign false
    git add -A && git commit -qm init ) >/dev/null 2>&1

  fakebin="$work/fakebin"; mkdir -p "$fakebin"
  { echo '#!/bin/sh'; echo 'case "$*" in'; echo '  *"buildx build"*) exit 7 ;;'; echo '  *) exit 0 ;;'; echo 'esac'; } > "$fakebin/docker"
  chmod +x "$fakebin/docker"
  # run a hook inside $repo with the fake docker; FIDO_SELFTEST_NESTED=1 stops the hook's own self-test from
  # re-entering this divergence test.  Combined stdout+stderr is captured; the caller reads $? for the code.
  run_hook() { ( cd "$repo"; PATH="$fakebin:$PATH" FIDO_SELFTEST_NESTED=1 sh "$1" ) 2>&1; }

  # divergence: stage bad OCaml under a hidden dir, then REMOVE it from the working tree (index != worktree).
  ( cd "$repo"; mkdir -p .hidden; printf 'let () = ()\n' > .hidden/rogue.ml; git add .hidden/rogue.ml; rm -rf .hidden )
  out=$(run_hook "$repo/.githooks/pre-commit"); rc=$?
  if [ "$rc" -ne 0 ] && [ "$rc" -ne 7 ] && printf '%s\n' "$out" | grep -q 'OCAML-ORIGIN GATE'; then
    ok "the REAL hook rejects staged bad OCaml with a CLEAN working tree (staged index authoritative; caught before Buildx)"
  else
    bad "the real hook did not reject staged bad OCaml with a clean working tree (rc=$rc)"
  fi

  # MUTATION (Codex's exact case): make the hook run the WORKING-TREE gate against '.' instead of staged $ctx.
  sed -E 's#^sh "\$ctx/tools/ocaml-origin-gate\.sh".*#sh "tools/ocaml-origin-gate.sh" "."#' \
      "$repo/.githooks/pre-commit" > "$repo/.githooks/pre-commit-mut"
  if ! grep -q 'ocaml-origin-gate.sh" "\."' "$repo/.githooks/pre-commit-mut"; then
    bad "self-test could not construct the working-tree-gate mutation (hook text changed?)"
  else
    out=$(run_hook "$repo/.githooks/pre-commit-mut"); rc=$?
    if [ "$rc" -eq 7 ] && ! printf '%s\n' "$out" | grep -q 'OCAML-ORIGIN GATE'; then
      ok "the working-tree-gate MUTATION lets the staged bad OCaml through to Buildx — the divergence test is load-bearing (has teeth)"
    else
      bad "the working-tree-gate mutation did NOT bypass — the divergence test lacks teeth (rc=$rc)"
    fi
  fi

  # a staged WEAKENED gate script (working-tree copy stays strict): the hook's STAGED self-test re-derives
  # gate behaviour and catches it — a bad staged gate cannot hide behind its safe working-tree copy.
  ( cd "$repo"
    git reset -q --hard HEAD; rm -f .githooks/pre-commit-mut
    cp tools/ocaml-origin-gate.sh "$work/strict-gate.bak"
    printf '#!/bin/sh\nexit 0\n' > tools/ocaml-origin-gate.sh; git add tools/ocaml-origin-gate.sh   # index = weakened
    cp "$work/strict-gate.bak" tools/ocaml-origin-gate.sh ) >/dev/null 2>&1                          # worktree = strict
  out=$(run_hook "$repo/.githooks/pre-commit"); rc=$?
  if [ "$rc" -ne 0 ] && [ "$rc" -ne 7 ] && printf '%s\n' "$out" | grep -q 'PRECOMMIT-SELFTEST FAILED'; then
    ok "a staged WEAKENED gate is caught by the hook's own staged self-test (a bad staged gate cannot hide behind its working-tree copy)"
  else
    bad "a staged weakened gate was not caught by the hook's staged self-test (rc=$rc)"
  fi
  set -e
fi

# ---- (3) stale / missing / modified / extra / deep / hidden staged generated files rejected ----
P="$work/pristine"; mk_pristine "$P"
s="$work/s3-mod";   mk_snapshot "$s"; printf '%s\npackage main\nfunc main(){ println(0) }\n' "$hdr" > "$s/main.go"
reject "MODIFIED staged generated bytes rejected"                         sh "$s/tools/staged-generated-compare.sh" "$s" "$P"
s="$work/s3-miss";  mk_snapshot "$s"; rm -f "$s/main.go"
reject "MISSING staged generated file rejected"                           sh "$s/tools/staged-generated-compare.sh" "$s" "$P"
s="$work/s3-deep";  mk_snapshot "$s"; mkdir -p "$s/pkg/deep"; printf '%s\npackage deep\n' "$hdr" > "$s/pkg/deep/x.go"
reject "EXTRA deep staged generated file rejected (recursive path set)"   sh "$s/tools/staged-generated-compare.sh" "$s" "$P"
s="$work/s3-hid";   mk_snapshot "$s"; mkdir -p "$s/.hidden"; printf '%s\npackage x\n' "$hdr" > "$s/.hidden/x.go"
reject "EXTRA staged .go under .hidden/ rejected (no opaque-dir skip)"     sh "$s/tools/staged-generated-compare.sh" "$s" "$P"
s="$work/s3-good";  mk_snapshot "$s"
accept "a byte-identical staged tree matches the pristine build"          sh "$s/tools/staged-generated-compare.sh" "$s" "$P"

# The structural checks (4)+(5) inspect the hook's CODE, not its prose — strip full-line comments first so
# an explanatory comment (e.g. mentioning `git commit --no-verify`) is not mistaken for a command.
hookcode=$(grep -v '^[[:space:]]*#' "$hook")

# ---- (4) a docs-only ordinary commit still runs the COMPLETE verification (no changed-file skip list) ----
# A changed-file skip list would need to diff the index/commit; the hook must contain no such diff.
if printf '%s\n' "$hookcode" | grep -Eq 'git[[:space:]]+diff|diff-index|diff-files|diff-tree|name-only'; then
  bad "pre-commit diffs changed paths — it may conditionally skip verification (a docs-only commit could be under-verified)"
else
  ok "pre-commit has no changed-file diff/skip list — a docs-only commit runs full verification"
fi
if printf '%s\n' "$hookcode" | grep -q 'target prover' \
   && printf '%s\n' "$hookcode" | grep -q 'target go-e2e' \
   && printf '%s\n' "$hookcode" | grep -q 'staged-generated-compare'; then
  ok "pre-commit unconditionally runs prover + go-e2e + the staged-generated byte compare"
else
  bad "pre-commit is missing an unconditional verification step"
fi

# ---- (5) the hook never mutates the working tree or the index ----
if printf '%s\n' "$hookcode" | grep -Eq 'git[[:space:]]+(add|commit|update-index|stash|reset|rm|mv|apply)\b|git[[:space:]]+checkout[[:space:]]'; then
  bad "pre-commit mutates the index/working tree (git add/commit/update-index/stash/reset/rm/checkout/...)"
else
  ok "pre-commit never mutates the index or working tree (only reads via checkout-index --prefix to a temp)"
fi
if printf '%s\n' "$hookcode" | grep -q 'checkout-index --all --prefix'; then
  ok "pre-commit exports the Git index read-only to a temp dir (checkout-index --prefix)"
else
  bad "pre-commit does not export the index via checkout-index --prefix"
fi

printf 'fido: precommit-selftest — %d passed, %d failed\n' "$pass" "$fail"
[ "$fail" -eq 0 ] || { echo "fido: PRECOMMIT-SELFTEST FAILED"; exit 1; }
echo "fido: precommit-selftest OK — staged-tree gates reject hidden/underscore/testdata/vendor foreign OCaml and stale/modified/missing/extra/deep/symlink/executable generated Go at every depth; the staged gate implementation is authoritative; the hook runs full verification every commit and never mutates the index or working tree."
