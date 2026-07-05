(* EXPECT: beyond the plugin's int64 fold subset *)
(* A CLOSED constant-arithmetic overflow inside an FConst numerator: 2^62 + 2^62 = 2^63
   exceeds signed int64 at the checked add.  The reasoned folder must classify it OVERFLOW
   (never "non-constant") and extraction abort. *)
From Fido Require Import preamble.
From Fido Require Import GoNumeric.
From Stdlib Require Import ZArith.
Definition neg_bad : GoFloat64 :=
  f64_of_fconst (mkFC (Z.shiftl 1 62 + Z.shiftl 1 62) 1%positive).
Go Main Extraction neg_out "neg_bad".
