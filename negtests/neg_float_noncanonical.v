(* EXPECT: NONCANONICAL spec_float literal *)
(* A raw S754_finite with a 2^64 mantissa is NOT a canonical binary64 value — the model's
   GoFloat64 invariant (SFeqb/SFcompare are representation-sensitive) forbids storing it,
   and the plugin must REFUSE the literal rather than emit any rendering of it.  This also
   pins the structural mantissa path: a wrapped int64 reintroduction would emit 0x0p0
   instead of aborting, failing this fixture either way. *)
From Fido Require Import preamble.
From Stdlib Require Import ZArith.
Definition neg_bad : GoFloat64 := S754_finite false 18446744073709551616%positive 0%Z.
Go Main Extraction neg_out "neg_bad".
