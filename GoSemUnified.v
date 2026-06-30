(** GoSemUnified.v — wires GoSem's denotation to unified.v's operational semantics, grounded in cmd.v's
    authoritative [run_cmd] (proof-only, no Go).

    Kept in its OWN small module (not grown into GoSem.v) so GoSem stays focused on denotation.  It consumes
    the PUBLIC, [run_cmd]-grounded bridge [cmd_unified.cmd_to_ucmd_run_agrees] (never the file-private projection
    plumbing) and discharges the [no_defer] side condition from [denote_body_no_defer], so callers get the bridge
    with NO obligation.  Certified public surface of THIS module = [denote_program_run_agrees]. *)

From Fido Require Import preamble cmd unified GoAst GoSem cmd_unified.
From Stdlib Require Import List String.
Import ListNotations.

(** COMPOSITION + run_cmd AGREEMENT: a program GoSem DENOTES runs under unified.v's [ustep], and that run AGREES
    with cmd.v's authoritative [run_cmd 1 c w].  If [denote_program p = Some c] then, from the single-goroutine
    start config, [usteps] drives goroutine 0 to completion, and its [uc_out] / [uc_panic] EQUAL [run_cmd]'s
    appended [w_output] / Outcome panic.  The [no_defer] side condition is DISCHARGED here from
    [denote_body_no_defer]; the conclusion's authority is [run_cmd], inherited from [cmd_to_ucmd_run_agrees]. *)
Theorem denote_program_run_agrees : forall p c ucap w,
  denote_program p = Some c ->
  exists (uc : UConfig) (oc : Outcome unit),
    usteps ucap (ustart (cmd_to_ucmd c)) uc                            (* the unified operational run *)
    /\ run_cmd 1 c w = Some oc                                         (* cmd.v's AUTHORITATIVE run *)
    /\ uc_live uc 0 = false                                           (* goroutine done *)
    /\ w_output (oc_world oc) = w_output w ++ map snd (uc_out uc)      (* OUTPUT agrees with run_cmd *)
    /\ uc_panic uc 0 = ocpanic oc.                                    (* PANIC agrees with run_cmd *)
Proof.
  intros p c ucap w Hden.
  assert (Hnd : no_defer c = true).
  { unfold denote_program in Hden.
    destruct (String.eqb (proj1_sig (prog_pkg p)) "main") eqn:E.
    - exact (denote_body_no_defer _ _ Hden).
    - discriminate Hden. }
  exact (cmd_to_ucmd_run_agrees c ucap w Hnd).
Qed.

(** Trust surface for this module (axiom-manifest gate captures its [Print Assumptions]). *)
Print Assumptions denote_program_run_agrees.
