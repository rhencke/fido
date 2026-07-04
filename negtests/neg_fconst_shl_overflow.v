(* EXPECT: beyond the plugin's int64 fold subset *)
(* [mkFC (Z.shiftl 1 63) 1] denotes the POSITIVE rational 2^63/1; an int64-wrapping fold
   would emit the NEGATIVE -2^63 — a wrong value.  The checked fold must DECLINE (the
   signed shift refuses a sign flip) and extraction abort.  (The checked shift is shared by both float widths.) *)
From Fido Require Import preamble.
From Stdlib Require Import ZArith.
Definition neg_bad : GoFloat64 := f64_of_fconst (mkFC (Z.shiftl 1 63) 1%positive).
Go Main Extraction neg_out "neg_bad".
