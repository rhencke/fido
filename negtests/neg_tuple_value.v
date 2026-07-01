(* EXPECT: only nat/bool/list/option constructors are modeled *)
(* A raw product/tuple VALUE (Coq's `pair` constructor) is NOT a modeled Go value: the model exposes only
   nat/bool/list/option constructors in value position (Go multiple-returns are produced by the effect
   sequencing, not as a first-class tuple value).  Extraction MUST abort on the unmodeled `pair` constructor
   rather than emit a bogus Go value.  Pins the generic unmodeled-constructor fail-closed guard (rule 2). *)
From Fido Require Import preamble.
Definition neg_bad : IO (GoI64 * GoI64) := ret ((1)%i64, (2)%i64).
Go Main Extraction neg_out "neg_bad".
