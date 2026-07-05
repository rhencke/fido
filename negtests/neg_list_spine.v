(* EXPECT: non-literal spine *)
(* A `cons` whose TAIL is not statically known (here the parameter `rest`) cannot be unfolded to a
   statically-known element list, so the backend cannot synthesize the typed `[]T{…}` — it aborts
   rather than emit plausible-but-wrong Go.  The non-literal-spine half of the list-value boundary. *)
From Fido Require Import preamble.
From Fido Require Import GoNumeric.
Definition neg_bad (rest : list GoI64) : IO (list GoI64) := ret (cons (1)%i64 rest).
Go Main Extraction neg_out "neg_bad".
