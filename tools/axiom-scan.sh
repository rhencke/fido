#!/bin/sh
# Anti-axiom DECLARATION scan — DEFENSE-IN-DEPTH run by `make check` and the pre-commit hook (the
# AUTHORITY is Rocq's own `Print Assumptions`, asserted by gate/axiom_gate.v).  "Zero axioms" means zero,
# including UNUSED declarations, so this scans every tracked *.v for a forbidden declaration BEFORE any
# proof depends on it.  Forbidden anywhere: Axiom/Parameter(s)/Conjecture(s)/Admitted/the `admit` tactic.
# Forbidden only at TOP LEVEL (outside a Section): Variable/Hypothesis/Context — a global assumption.
# Sections are PERMITTED (their locals generalize into theorem parameters after End).
#
# Non-code is blanked FIRST by a Rocq-aware lexer that tracks STRINGS and NESTED comments, so a keyword
# that only appears inside a string literal or a (possibly nested) comment is NOT a declaration.  A naive
# comment stripper is fail-open here: `Definition m := "(*". Axiom hidden : True.` hides the axiom behind
# a string that looks like a comment opener.  Has positive + adversarial negative self-tests.
set -eu

# Blank every string literal and (nested) comment to spaces, preserving line structure and code
# punctuation; reads stdin, writes the code-only stream.  State persists across lines (strings/comments
# may span lines).  Coq comment/string delimiters are contiguous 2-char / 1-char tokens.
blank_noncode() {
  awk '
  BEGIN{ st=0; depth=0 }   # st: 0=code, 1=string, 2=comment
  {
    n=length($0); out=""; i=1
    while(i<=n){
      c=substr($0,i,1); two=substr($0,i,2)
      if(st==0){
        if(two=="(*"){ st=2; depth=1; out=out"  "; i+=2; continue }
        if(c=="\""){ st=1; out=out" "; i+=1; continue }
        out=out c; i+=1; continue
      } else if(st==1){                                   # inside a string literal
        if(c=="\""){
          if(substr($0,i+1,1)=="\""){ out=out"  "; i+=2; continue }   # "" = escaped quote, stay in string
          st=0; out=out" "; i+=1; continue
        }
        out=out" "; i+=1; continue
      } else {                                            # inside a (possibly nested) comment
        if(two=="(*"){ depth++; out=out"  "; i+=2; continue }
        if(two=="*)"){ depth--; out=out"  "; i+=2; if(depth==0) st=0; continue }
        out=out" "; i+=1; continue
      }
    }
    print out
  }'
}

# reads a comment/string-blanked Rocq stream on stdin; prints each violation; exits 3 if any, else 0.
scan_stream() {
  awk '
    BEGIN { depth=0; found=0 }
    { s=$0
      m="(#\\[[^]]*\\][ \t]*|Local[ \t]+|Global[ \t]+|Polymorphic[ \t]+|Monomorphic[ \t]+)*"
      if (s ~ ("(^|[.\t ])" m "(Axiom|Axioms|Parameter|Parameters|Conjecture|Conjectures)([ \t]|$)")) { print "  Axiom/Parameter/Conjecture"; found=1 }
      if (s ~ /(^|[.\t ])Admitted[.\t ]/ || s ~ /(^|[.\t ])Admitted$/)                            { print "  Admitted";               found=1 }
      if (s ~ /(^|[^A-Za-z_])admit([^A-Za-z_]|$)/)                                                 { print "  admit tactic";           found=1 }
      if (s ~ /(^|[.\t ])Section[ \t]/) depth++
      else if (s ~ /(^|[.\t ])End[ \t]/) { if (depth>0) depth-- }
      if (depth==0 && s ~ ("(^|[.\t ])" m "(Variable|Variables|Hypothesis|Hypotheses|Context)([ \t]|$)")) { print "  top-level Variable/Hypothesis/Context (global assumption)"; found=1 }
    }
    END { exit (found?3:0) }
  '
}

# a full pass: blank non-code, then scan.  exits 3 on a violation, else 0.
scan() { blank_noncode | scan_stream; }

self_test() {
  fail=0
  # MUST be rejected — a real declaration the blanker must NOT hide (strings/comments/modifiers/multi-sentence):
  for t in \
    'Axiom a : True.' 'Parameter p : nat.' 'Conjecture c : True.' \
    'Lemma l : True. Proof. admit. Admitted.' 'Variable x : nat.' 'Hypothesis h : True.' \
    'Definition marker := "(*". Axiom hidden : True.' \
    'Local Axiom la : True.' '#[global] Axiom ga : True.' \
    'Definition d := 1. Axiom two : True.' \
    '(* c *) Axiom after : True.' '(* outer (* inner *) still *) Axiom nested : True.'; do
    if printf '%s\n' "$t" | scan >/dev/null 2>&1; then echo "  self-test FAIL (should reject): $t"; fail=1; fi
  done
  # a multiline declaration (keyword line, type on the next) must still be caught:
  if printf 'Axiom\n  ml : True.\n' | scan >/dev/null 2>&1; then echo "  self-test FAIL (should reject): multiline Axiom"; fail=1; fi
  # MUST pass — keywords appearing only inside strings/comments, Section-local decls, and a clean file:
  if ! printf 'Definition s := "Axiom a : True.".\n' | scan >/dev/null 2>&1; then
    echo "  self-test FAIL (should pass): Axiom inside a string"; fail=1; fi
  if ! printf '(* Axiom a : True. *)\nDefinition d := 1.\n' | scan >/dev/null 2>&1; then
    echo "  self-test FAIL (should pass): Axiom inside a comment"; fail=1; fi
  if ! printf '(* nested (* Axiom x *) still *)\nDefinition d := 1.\n' | scan >/dev/null 2>&1; then
    echo "  self-test FAIL (should pass): Axiom inside a nested comment"; fail=1; fi
  if ! printf 'Section S.\nVariable x : nat.\nHypothesis h : x = x.\nEnd S.\n' | scan >/dev/null 2>&1; then
    echo "  self-test FAIL (should pass): Section-local Variable/Hypothesis"; fail=1; fi
  if ! printf 'Definition d := 1.\nLemma l : True. Proof. exact I. Qed.\n' | scan >/dev/null 2>&1; then
    echo "  self-test FAIL (should pass): clean file"; fail=1; fi
  [ "$fail" -eq 0 ] || { echo "fido: AXIOM-SCAN SELF-TESTS FAILED"; exit 1; }
}

self_test

found=0
for f in $(git ls-files '*.v'); do
  if ! scan < "$f"; then
    echo "fido: AXIOM-DECLARATION GATE — $f declares a forbidden global assumption (above)."
    found=1
  fi
done
[ "$found" -eq 0 ] || { echo "fido: zero-axiom guarantee forbids this; model the construct as a Definition."; exit 1; }

echo "fido: axiom-declaration scan OK — no Axiom/Parameter/Conjecture/Admitted/admit; no top-level assumptions (Sections permitted); string/comment-aware self-tests passed ✓"
