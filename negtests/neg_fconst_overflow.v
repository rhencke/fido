(* EXPECT: beyond the plugin's int64 fold subset *)
(* An [FConst] literal whose numerator exceeds int64 (2^63): the fields carry NO range
   proof, so the plugin's fold must DECLINE (checked literal parse) and extraction abort
   — a wrap-tolerant parse would silently fold a WRONG rational into the emitted Go. *)
From Fido Require Import preamble.
From Fido Require Import GoNumeric.
From Stdlib Require Import ZArith.
Definition neg_bad : GoFloat64 := f64_of_fconst (mkFC (9223372036854775808)%Z (1)%positive).
Go Main Extraction neg_out "neg_bad".
