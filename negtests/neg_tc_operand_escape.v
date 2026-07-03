(* EXPECT: typed_operand_tc was not found *)
(* The OPERAND face of the category-authority seal: [typed_operand_tc] admits/boxes operands by
   its authority's category; a forged classifier could route a wrong-width value into the typed
   ops.  [Local] to GoSemDenote.v — the only live instantiation is [ptype] (the closed
   [typed_operand] wrapper); this fixture asserts the forge surface is uncallable through the
   composed [GoSem] export. *)
From Fido Require Import GoSem.
Definition forge := typed_operand_tc.
