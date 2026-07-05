(* EXPECT: ±Inf / NaN LITERAL *)
(* A compile-time float NaN/±Inf CONSTANT (`S754_nan` / `S754_infinity`) has NO faithful Go form: Go has no
   Inf/NaN constant, a constant `0.0/0.0` is a Go COMPILE error, and `math.NaN`/`math.Inf` need an import (on
   hold, rule 5).  So a literal NaN/Inf in value position is a PERMANENT fail-closed site — NOT an impl gap:
   the RUNTIME form (`f64_div 1 0` = +Inf) IS supported and demoed in main.v.  Extraction MUST abort here
   rather than emit invalid/uncompilable Go. *)
From Fido Require Import preamble.
From Fido Require Import GoNumeric.
Definition neg_bad : IO GoFloat32 := ret (f32_lit S754_nan).
Go Main Extraction neg_out "neg_bad".
