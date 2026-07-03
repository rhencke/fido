(* EXPECT: reval_int_tc was not found *)
(* THE CATEGORY-AUTHORITY SEAL: the [_tc] evaluator family takes its category authority as a
   PARAMETER, and every arm consumes SHAPE OBLIGATIONS of that authority (a [PtRunInt t] one-arg
   call is a conversion shape; the map key list is exact) — a forged classifier could smuggle
   behavior justified only for the proven instances.  The family is [Local] to GoSemDenote.v —
   invisible through EVERY public import path; the only instances live inside the file with their
   obligations discharged ([ptype] today; [type_expr]'s projection at locals rung 5b).  This
   fixture exercises the composed [GoSem] export and asserts the forge surface is UNCALLABLE. *)
From Fido Require Import GoSem.
Definition forge := reval_int_tc.
