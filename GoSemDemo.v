(** ============================================================================
    GoSemDemo.v — the GoSem behavioral DELIVERABLE about the certified [GoEmit.demo_prog].

    This file is DOWNSTREAM of BOTH GoSem (the behavioral semantics) and GoEmit (which owns
    [demo_prog]): it imports both.  Keeping the demo theorem HERE — rather than in core
    GoSem.v — is what lets core GoSem.v import ONLY [GoAst] + the semantic substrate
    ([cmd]/[builtins]), never the upper emission layers, so the spine dependency points the
    right way (GoAst -> GoPrint -> GoSem -> GoSafe -> GoEmit; GoSem sits BELOW GoSafe/GoEmit).
    It introduces no new semantics — it just runs [GoSem.gosem_run] on the emitted program.
    ============================================================================ *)
From Fido Require Import builtins GoAst GoSem GoEmit.
From Stdlib Require Import String List ZArith.
Import ListNotations.
Open Scope string_scope.

(** ---- THE DELIVERABLE (the first behavioral theorem) ----
    [GoEmit.demo_prog]'s body runs to a NORMAL outcome ([ORet tt], NOT a panic — the
    [return] terminates normally) emitting EXACTLY the four [println] lines, in order:
      [println(1)]          -> the int    value 1   (Go prints "1")
      [println(int64(3))]   -> the int64  value 3   (Go prints "3")
      [println(1 + 2)]      -> the int    value 3   (Go prints "3")
      [println("hi")]       -> the string value "hi" (Go prints "hi")
    The two [GsBlankAssign]s ([_ = []int(nil)], [_ = []int{1}]) emit NOTHING — their RHS is
    [GoSem.rhs_effect_free], so the value is discarded silently — and the trailing bare
    [return] terminates normally (it does NOT fall through to add output).  This is the
    genuinely-correct Go behaviour of [demo_prog].

    The [match]-Prop shape pins, in one [vm_compute; reflexivity], that the result is
    (a) [Some] (the program is within denotational scope), (b) [ORet] (normal, NOT
    [OPanic]), (c) returning [tt], AND (d) the EXACT 4-event output trace.  Were it [None]
    / [OPanic] / a different trace, the goal would not reduce to [reflexivity]. *)
Theorem gosem_demo_output :
  match gosem_run (prog_body demo_prog) with
  | Some (ORet tt w') =>
      w_output w' =
        [ (true, [anyt TInt64 (intwrap 1)]);
          (true, [anyt TI64   (i64wrap 3)]);
          (true, [anyt TInt64 (intwrap 3)]);
          (true, [anyt TString "hi"]) ]
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** GATE — keep the behavioral deliverable axiom-free ("Closed under the global context").
    [make gosem-verify] (local) + the Docker prover-stage axiom-manifest gate (canonical)
    FAIL the build on ANY axiom this would surface. *)
Print Assumptions gosem_demo_output.
