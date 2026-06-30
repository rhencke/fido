#!/bin/sh
# THE axiom-manifest extractor — single source of truth.  Reads Rocq `Print Assumptions` output (a build log,
# or one snippet's output) on stdin and prints, one per line, the NAME of every axiom Rocq reported under an
# `Axioms:` block.  Used by BOTH the Docker manifest gate (Dockerfile prover stage) and the axiom-authority
# self-test, so the two can never drift.  Empty output == no axioms (the zero-axiom invariant, rule 3).
#
# `f` is armed only by an `^Axioms:` line, so a log with no `Axioms:` block yields nothing regardless of other
# content; once armed it collects the `name : type` lines Rocq lists.  An entry is matched STRUCTURALLY — a
# column-0 token followed by ` :` — NOT by enumerating identifier characters: a char class would silently miss
# valid Rocq names (apostrophes `foo'`, qualified `M.foo`, …), and "the gate misses some name shape" is exactly
# the recurring enumerated-charset bug.  The `^` anchor excludes indented type-continuation lines; the space
# before `:` excludes the `Axioms:` header itself.
exec awk '/^Axioms:/{f=1;next} f && /^[^[:space:]]+ :/ {print $1}'
