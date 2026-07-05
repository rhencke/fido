(* EXPECT: local fixpoint value *)
(* A LIVE direct use of [List.repeat]: the decl is classified live and reaches emission,
   where its eta-collapsed body (a bare local fixpoint value) hits the fail-loud [MLfix] seal.
   A regression that re-suppresses the decl while the call prints, or prints the fix's
   internal name bare, would leave wrong-arity/undefined Go at `go build` = too late. *)
From Fido Require Import preamble.
From Fido Require Import GoNumeric.
Definition neg_bad (x : GoI64) : list GoI64 := List.repeat x 3.
Go Main Extraction neg_out "neg_bad".
