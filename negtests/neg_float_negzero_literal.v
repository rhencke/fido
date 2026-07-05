(* EXPECT: negative-zero literal *)
(* A compile-time float -0.0 CONSTANT (`S754_zero true`) has NO Go constant form: Go's `-0.0` source literal
   is just `0.0` (positive), and `math.Copysign(0, -1)` needs an import (on hold, rule 5).  So it is a
   PERMANENT fail-closed site — NOT an impl gap: the RUNTIME form (`f32_neg (f32_lit 0)` = -0.0) IS supported
   and demoed in main.v.  Extraction MUST abort rather than silently emit `0.0` (dropping the sign).
   Completes the float-CONSTANT-with-no-Go-form boundary alongside neg_float_nan_literal.v (±Inf / NaN). *)
From Fido Require Import preamble.
From Fido Require Import GoNumeric.
Definition neg_bad : IO GoFloat32 := ret (f32_lit (S754_zero true)).
Go Main Extraction neg_out "neg_bad".
