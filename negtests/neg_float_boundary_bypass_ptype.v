(* EXPECT: eval_value_ptype_core was not found *)
(* THE FLOAT-BOUNDARY SEAL, ptype-core half: [eval_value_ptype_core]'s
   [PtFloatConst] arm runs only the PER-NODE [fsf_checked] — child-position float coverage lives in
   [eval_value]'s [floats_checked] boundary, so naming this helper directly is the same bypass.
   It is [Local] to GoSemDenote.v — invisible through EVERY public import path; this fixture
   exercises the composed [GoSem] export and asserts it is UNCALLABLE. *)
From Fido Require Import GoSem.
Definition bypass := eval_value_ptype_core.
