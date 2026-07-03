(* EXPECT: eval_value_core was not found *)
(* THE FLOAT-BOUNDARY SEAL: [eval_value_core] is the evaluator BODY
   UNDER the [floats_checked] boundary — if an importer could name it, it could compute values while
   SKIPPING the whole-expression float re-verification ([eval_value_floats_checked] holds only for
   [eval_value]).  It is [Local] to GoSemDenote.v — invisible through EVERY public import path; this fixture
   exercises the composed [GoSem] export and asserts the bypass is UNCALLABLE. *)
From Fido Require Import GoSem.
Definition bypass := eval_value_core.
