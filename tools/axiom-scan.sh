#!/bin/sh
# Anti-axiom DECLARATION scan — DEFENSE-IN-DEPTH run by `make check` (the AUTHORITY is Rocq's own
# `Print Assumptions`, asserted by gate/axiom_gate.v).  "Zero axioms" means zero, including UNUSED
# declarations, so this scans every tracked *.v for a forbidden declaration BEFORE any proof depends
# on it.  Forbidden anywhere: Axiom/Parameter(s)/Conjecture(s)/Admitted/the `admit` tactic.  Forbidden
# only at TOP LEVEL (outside a Section): Variable/Hypothesis/Context — a global assumption.  Sections
# are PERMITTED (their locals generalize into theorem parameters after End; they are not axioms).
# Comments are stripped first, so prose may use these words freely.  Has positive+negative self-tests.
set -eu

strip_comments() {
  awk 'BEGIN{d=0}{n=length($0);out="";i=1;while(i<=n){two=substr($0,i,2);
       if(two=="(*"){d++;out=out"  ";i+=2;continue}
       if(two=="*)"&&d>0){d--;out=out"  ";i+=2;continue}
       c=substr($0,i,1); if(d>0){out=out" "}else{out=out c}; i++}
       print out}' "$1"
}

# reads a comment-stripped Rocq stream on stdin; prints each violation; exits 3 if any, else 0.
scan_stream() {
  awk '
    BEGIN { depth=0; found=0 }
    { s=$0
      m="(#\\[[^]]*\\][ \t]*|Local[ \t]+|Global[ \t]+|Polymorphic[ \t]+|Monomorphic[ \t]+)*"
      if (s ~ ("(^|[.\t ])" m "(Axiom|Axioms|Parameter|Parameters|Conjecture|Conjectures)[ \t]")) { print "  Axiom/Parameter/Conjecture"; found=1 }
      if (s ~ /(^|[.\t ])Admitted[.\t ]/ || s ~ /(^|[.\t ])Admitted$/)                            { print "  Admitted";               found=1 }
      if (s ~ /(^|[^A-Za-z_])admit([^A-Za-z_]|$)/)                                                 { print "  admit tactic";           found=1 }
      if (s ~ /(^|[.\t ])Section[ \t]/) depth++
      else if (s ~ /(^|[.\t ])End[ \t]/) { if (depth>0) depth-- }
      if (depth==0 && s ~ ("(^|[.\t ])" m "(Variable|Variables|Hypothesis|Hypotheses|Context)[ \t]")) { print "  top-level Variable/Hypothesis/Context (global assumption)"; found=1 }
    }
    END { exit (found?3:0) }
  '
}

self_test() {
  fail=0
  # MUST be rejected (scan_stream exits nonzero):
  for t in 'Axiom a : True.' 'Parameter p : nat.' 'Conjecture c : True.' \
           'Lemma l : True. Proof. admit. Admitted.' 'Variable x : nat.' 'Hypothesis h : True.'; do
    if printf '%s\n' "$t" | scan_stream >/dev/null 2>&1; then echo "  self-test FAIL (should reject): $t"; fail=1; fi
  done
  # MUST pass (scan_stream exits 0): Section-local decls, and a clean development:
  if ! printf 'Section S.\nVariable x : nat.\nHypothesis h : x = x.\nEnd S.\n' | scan_stream >/dev/null 2>&1; then
    echo "  self-test FAIL (should pass): Section-local Variable/Hypothesis"; fail=1; fi
  if ! printf 'Definition d := 1.\nLemma l : True. Proof. exact I. Qed.\n' | scan_stream >/dev/null 2>&1; then
    echo "  self-test FAIL (should pass): clean file"; fail=1; fi
  [ "$fail" -eq 0 ] || { echo "fido: AXIOM-SCAN SELF-TESTS FAILED"; exit 1; }
}

self_test

found=0
for f in $(git ls-files '*.v'); do
  if ! strip_comments "$f" | scan_stream; then
    echo "fido: AXIOM-DECLARATION GATE — $f declares a forbidden global assumption (above)."
    found=1
  fi
done
[ "$found" -eq 0 ] || { echo "fido: zero-axiom guarantee forbids this; model the construct as a Definition."; exit 1; }

echo "fido: axiom-declaration scan OK — no Axiom/Parameter/Conjecture/Admitted/admit; no top-level assumptions (Sections permitted); self-tests passed ✓"
