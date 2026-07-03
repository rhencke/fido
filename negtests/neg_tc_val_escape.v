(* EXPECT: reval_val_tc was not found *)
(* The VALUE face of the category-authority seal: [reval_val_tc] is the top value pipeline over a
   parameterized authority.  [Local] to GoSemDenote.v — the only live instantiation is [ptype]
   (the closed [reval_val_with] wrapper); this fixture asserts the forge surface is uncallable
   through the composed [GoSem] export. *)
From Fido Require Import GoSem.
Definition forge := reval_val_tc.
