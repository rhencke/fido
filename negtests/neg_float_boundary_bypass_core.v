(* EXPECT: eval_value_core was not found *)
(* THE FLOAT-BOUNDARY SEAL (§3a split review, 2026-07-02): [eval_value_core] is the evaluator BODY
   UNDER the [floats_checked] boundary — if an importer could name it, it could compute values while
   SKIPPING the whole-expression float re-verification ([eval_value_floats_checked] holds only for
   [eval_value]).  It is [Local] to GoSem.v; this fixture asserts the bypass is UNCALLABLE. *)
From Fido Require Import GoSem.
Definition bypass := eval_value_core.
