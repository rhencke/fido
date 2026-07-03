(* EXPECT: rexit_tc was not found *)
(* The EXIT face of the category-authority seal: [rexit_tc]'s conversion/typed/comparison arms
   dispatch on its authority's categories (a [PtRunInt t] one-arg call must be a conversion
   shape).  [Local] to GoSemDenote.v — the only live instantiation is [ptype] (the closed
   [rexit_with] wrapper); this fixture asserts the forge surface is uncallable through the
   composed [GoSem] export. *)
From Fido Require Import GoSem.
Definition forge := rexit_tc.
