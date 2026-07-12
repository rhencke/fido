#!/bin/sh
# Anti-axiom DECLARATION scan — DEFENSE-IN-DEPTH run by `make check` and the pre-commit hook (the
# AUTHORITY for the public surfaces is Rocq's own `Print Assumptions`, asserted by gate/axiom_gate.v).
# "Zero project axioms" means zero, INCLUDING UNUSED declarations, so this scans every tracked *.v for a
# forbidden declaration.  It is a purpose-built LEXICAL command scanner, not a regex approximation:
#   pass 1 blanks string literals and NESTED comments (a state machine, across line boundaries) so a
#          keyword inside a string/comment is never mistaken for a declaration;
#   pass 2 tokenizes Rocq command SENTENCES and maintains a real scope STACK (Section / Module / Module
#          Type), so multiple commands per line, commands spanning lines, and same-line Section..End do
#          not corrupt it.
# Forbidden anywhere: Axiom(s)/Parameter(s)/Conjecture(s) (EXCEPT inside a Module Type interface),
# Admitted, the `admit` tactic.  Forbidden only OUTSIDE a Section: Variable(s)/Hypothesis(es)/Context
# (Section-local variables generalize into theorem parameters after End — permitted, review-sensitive).
set -eu

# Pass 1: blank strings + (nested) comments to spaces, preserving line structure.  Reads stdin.
blank_noncode() {
  awk '
  BEGIN { st=0; depth=0 }   # st: 0=code, 1=string, 2=comment
  {
    n=length($0); out=""; i=1
    while(i<=n){
      c=substr($0,i,1); two=substr($0,i,2)
      if(st==0){
        if(two=="(*"){ st=2; depth=1; out=out"  "; i+=2; continue }
        if(c=="\""){ st=1; out=out" "; i+=1; continue }
        out=out c; i+=1; continue
      } else if(st==1){
        if(c=="\""){ if(substr($0,i+1,1)=="\""){ out=out"  "; i+=2; continue } st=0; out=out" "; i+=1; continue }
        out=out" "; i+=1; continue
      } else {
        if(two=="(*"){ depth++; out=out"  "; i+=2; continue }
        if(two=="*)"){ depth--; out=out"  "; i+=2; if(depth==0) st=0; continue }
        out=out" "; i+=1; continue
      }
    }
    print out
  }'
}

# Pass 2: sentence-tokenize the blanked stream; a scope stack distinguishes Section / Module / Module
# Type.  Prints each violation; exits 3 if any, else 0.  Reads stdin.
sentence_scan() {
  awk '
  BEGIN { buf=""; found=0; sp=0 }
  { buf = buf $0 "\n" }
  END {
    n=length(buf); i=1; sent=""
    while(i<=n){
      c=substr(buf,i,1)
      if(c=="."){
        nx=substr(buf,i+1,1)
        if(nx==""||nx==" "||nx=="\t"||nx=="\n"){ process(sent); sent=""; i+=2; continue }
      }
      sent=sent c; i++
    }
    if(sent ~ /[^ \t\n]/) process(sent)
    exit (found?3:0)
  }
  function has(kind,   k){ for(k=1;k<=sp;k++) if(stack[k]==kind) return 1; return 0 }
  function process(s,   t){
    gsub(/[ \t\n]+/," ",s); sub(/^ +/,"",s); sub(/ +$/,"",s)
    if(s=="") return
    # the whole sentence text is scanned for admit/Admitted (they sit inside proofs, mid-sentence)
    if(s ~ /(^|[^A-Za-z_])admit([^A-Za-z_]|$)/){ print "  admit tactic"; found=1 }
    if(s ~ /(^|[^A-Za-z_])Admitted([^A-Za-z_]|$)/){ print "  Admitted"; found=1 }
    # strip leading attributes / locality modifiers to reach the command keyword
    t=s
    while(1){
      if(t ~ /^#\[[^]]*\] /){ sub(/^#\[[^]]*\] /,"",t); continue }
      if(t ~ /^(Local|Global|Polymorphic|Monomorphic) /){ sub(/^(Local|Global|Polymorphic|Monomorphic) /,"",t); continue }
      break
    }
    if(t ~ /^Section( |$)/){ sp++; stack[sp]="S"; return }
    if(t ~ /^Module Type( |$)/){ sp++; stack[sp]="MT"; return }
    if(t ~ /^Module( |$)/){ sp++; stack[sp]="M"; return }
    if(t ~ /^End( |$)/){ if(sp>0) sp--; return }
    if(t ~ /^(Axiom|Axioms|Parameter|Parameters|Conjecture|Conjectures)( |$)/){
      if(!has("MT")){ print "  Axiom/Parameter/Conjecture"; found=1 }; return }
    if(t ~ /^(Variable|Variables|Hypothesis|Hypotheses|Context)( |$)/){
      if(!has("S")){ print "  top-level Variable/Hypothesis/Context (global assumption)"; found=1 }; return }
  }
  '
}

scan() { blank_noncode | sentence_scan; }

self_test() {
  fail=0
  # MUST be rejected (real declarations the lexer must not hide, and the known bypasses):
  for t in \
    'Axiom a : True.' 'Parameter p : nat.' 'Conjecture c : True.' \
    'Lemma l : True. Proof. admit. Admitted.' 'Variable x : nat.' 'Hypothesis h : True.' \
    'Definition marker := "(*". Axiom hidden : True.' \
    'Local Axiom la : True.' '#[global] Axiom ga : True.' \
    'Definition d := 1. Axiom two : True.' \
    '(* c *) Axiom after : True.' '(* outer (* inner *) still *) Axiom nested : True.' \
    'Section S. End S. Variable escaped : nat.' \
    'Module M. Variable minner : nat. End M.'; do
    if printf '%s\n' "$t" | scan >/dev/null 2>&1; then echo "  self-test FAIL (should reject): $t"; fail=1; fi
  done
  if printf 'Axiom\n  ml : True.\n' | scan >/dev/null 2>&1; then echo "  self-test FAIL (should reject): multiline Axiom"; fail=1; fi
  # MUST pass (keywords in strings/comments; Section-local; Module-Type interface; clean):
  if ! printf 'Definition s := "Axiom a : True.".\n' | scan >/dev/null 2>&1; then
    echo "  self-test FAIL (should pass): Axiom inside a string"; fail=1; fi
  if ! printf '(* Axiom a : True. *)\nDefinition d := 1.\n' | scan >/dev/null 2>&1; then
    echo "  self-test FAIL (should pass): Axiom inside a comment"; fail=1; fi
  if ! printf '(* nested (* Axiom x *) still *)\nDefinition d := 1.\n' | scan >/dev/null 2>&1; then
    echo "  self-test FAIL (should pass): Axiom inside a nested comment"; fail=1; fi
  if ! printf 'Section S.\nVariable x : nat.\nHypothesis h : x = x.\nEnd S.\n' | scan >/dev/null 2>&1; then
    echo "  self-test FAIL (should pass): Section-local Variable/Hypothesis"; fail=1; fi
  if ! printf 'Module Type T.\nParameter p : nat.\nAxiom ax : p = p.\nEnd T.\n' | scan >/dev/null 2>&1; then
    echo "  self-test FAIL (should pass): Module-Type interface Parameter/Axiom"; fail=1; fi
  if ! printf 'Section S. Variable x : nat. End S.\nDefinition d := 1.\n' | scan >/dev/null 2>&1; then
    echo "  self-test FAIL (should pass): same-line Section..End then Section-local var"; fail=1; fi
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

echo "fido: axiom-declaration scan OK — no Axiom/Parameter/Conjecture/Admitted/admit; no top-level assumption; lexical (string/comment/scope-aware) self-tests passed ✓"
