(** GoSemUnified.v — wires GoSem's denotation to unified.v's operational semantics (proof-only, no Go).

    Kept in its OWN small module (not grown into GoSem.v) so GoSem stays focused on denotation.  It imports
    GoSem (for [denote_program]/[denote_body_no_defer]) and cmd_unified (for [cmd_to_ucmd]/[cmd_to_ucmd_runs]),
    and discharges the [no_defer] side condition so callers get the bridge with NO obligation.

    Certified public surface of THIS module = [denote_program_usteps] (its [Print Assumptions] below is captured
    by the axiom-manifest gate). *)

From Fido Require Import preamble concurrency cmd unified GoAst GoTypes GoSafe GoSem cmd_unified.
From Stdlib Require Import List String.
Import ListNotations.

(** The initial single-goroutine config running [u] on goroutine 0: live, empty defers, no panic, no output. *)
Definition ustart (u : UCmd) : UConfig :=
  mkUCfg (fun t => if Nat.eqb t 0 then u else URet)
         (fun _ => nil) (fun _ => 0) (fun t => Nat.eqb t 0) nil nil (fun _ => nil) (fun _ => None).

(** COMPOSITION: a program GoSem DENOTES runs under unified.v's [ustep].  If [denote_program p = Some c] then,
    from the single-goroutine start config, [usteps] drives goroutine 0 to completion ([uc_live 0]:=false),
    emitting EXACTLY [c]'s output events (println flag + payload) into [uc_out] and ending with [uc_panic 0]
    equal to [c]'s panic outcome.  The [no_defer] side condition is DISCHARGED here from [denote_body_no_defer].
    This is the CHECKED link from GoSem's denotation to the operational semantics on which race-freedom /
    liveness / deadlock are proved — not "can be composed", but composed. *)
Theorem denote_program_usteps : forall p c,
  denote_program p = Some c ->
  forall ucap,
  exists p' lv' pa',
    usteps ucap (ustart (cmd_to_ucmd c))
                (mkUCfg p' (fun _ => nil) (fun _ => 0) lv' nil
                        (map (fun e => (0, e)) (cmd_out_events c)) (fun _ => nil) pa')
    /\ lv' 0 = false
    /\ pa' 0 = cmd_panic c.
Proof.
  intros p c Hden ucap.
  assert (Hnd : no_defer c = true).
  { unfold denote_program in Hden.
    destruct (String.eqb (proj1_sig (prog_pkg p)) "main") eqn:E.
    - exact (denote_body_no_defer _ _ Hden).
    - discriminate Hden. }
  destruct (cmd_to_ucmd_runs c Hnd ucap
              (fun t => if Nat.eqb t 0 then cmd_to_ucmd c else URet)
              (fun _ => nil) (fun _ => 0) (fun t => Nat.eqb t 0) nil nil (fun _ => nil) (fun _ => None)
              eq_refl eq_refl eq_refl eq_refl) as [p' [lv' [pa' [Hus [Hd Hp]]]]].
  exists p', lv', pa'. unfold ustart. rewrite app_nil_l in Hus.
  split; [exact Hus | split; [exact Hd | exact Hp] ].
Qed.

(** Trust surface for this module (axiom-manifest gate captures its [Print Assumptions]). *)
Print Assumptions denote_program_usteps.
