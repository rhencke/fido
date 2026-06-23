(* EXPECT: cannot extract constructor pair *)
(* N-ARY (3+) multiple-return values.  Go's `func f() (A, B, C)` is a FLAT tuple, but Coq's
   `A * B * C` is the LEFT-NESTED `(A * B) * C` with value `pair (pair a b) c`.  Fido lowers a
   FLAT 2-tuple (`pair a b` -> `return a, b`) but NOT a nested one — so a 3+ return currently
   ABORTS at the inner pair rather than emitting nested `(A, (B, C))` (invalid Go) or a wrong
   flattening.  This locks that fail-CLOSED boundary: when N-ary multi-return lands (flatten the
   left-spine at the type / return / both destructure sites), this fixture will EXTRACT and the
   harness will flag it for removal.  See SPEC_CONFORMANCE "multiple return values". *)
From Fido Require Import preamble.
Definition neg_bad (a b c : GoI64) : prod (prod GoI64 GoI64) GoI64 := pair (pair a b) c.
Go Main Extraction neg_out "neg_bad".
