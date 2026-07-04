(* EXPECT: NONCANONICAL spec_float literal *)
(* The SUBTLE case: S754_finite false 1 0 is the VALUE 1.0 in a noncanonical
   representation (canonical 1.0 is mantissa 2^52 at exponent -52) — in-window by
   width and range, rejected ONLY by the exact canonical-mantissa condition.  The
   plugin's gate is SpecFloat.bounded itself (extracted), so this must abort. *)
From Fido Require Import preamble.
From Stdlib Require Import ZArith.
Definition neg_bad : GoFloat64 := S754_finite false 1%positive 0%Z.
Go Main Extraction neg_out "neg_bad".
