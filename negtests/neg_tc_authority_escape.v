(* EXPECT: reval_int_tc was not found *)
(* THE CATEGORY-AUTHORITY SEAL: the [_tc] evaluator family takes its category authority as a
   PARAMETER, and every arm consumes SHAPE OBLIGATIONS of that authority (a [PtRunInt t] one-arg
   call is a conversion shape; the map key list is exact) — a forged classifier could smuggle
   behavior justified only for the proven instance.  The family is [Local] to GoSemDenote.v; the
   ONLY live instantiation is [ptype] (the closed wrappers).  This fixture exercises the composed
   [GoSem] export and asserts the ENGINE face ([reval_int_tc]) is uncallable there; the other
   four faces have their own fixtures (count / operand / exit / val). *)
From Fido Require Import GoSem.
Definition forge := reval_int_tc.
