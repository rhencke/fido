(* EXPECT: shift_count_tc was not found *)
(* The COUNT face of the category-authority seal: [shift_count_tc] reads a CONSTANT shift count
   directly off its authority's category value — count EXACTNESS is an instance obligation, so a
   forged classifier could fake a constant count for a runtime (or panicking) expression.  [Local]
   to GoSemDenote.v — the only live instantiation is [ptype] (the closed [shift_count] wrapper);
   this fixture asserts the forge surface is uncallable through the composed [GoSem] export. *)
From Fido Require Import GoSem.
Definition forge := shift_count_tc.
