(** GoSemUnified.v — wires GoSem's denotation to unified.v's operational semantics AND grounds it in cmd.v's
    authoritative [run_cmd] (proof-only, no Go).

    Kept in its OWN small module (not grown into GoSem.v) so GoSem stays focused on denotation.  It imports
    GoSem (for [denote_program]/[denote_body_no_defer]) and cmd_unified (for the bridge + its [run_cmd] seal),
    and discharges the [no_defer] side condition so callers get the bridge with NO obligation.

    The PUBLIC theorem ([denote_program_run_agrees]) states agreement between the unified [ustep] run and cmd.v's
    [run_cmd 1 c w] DIRECTLY — output and panic.  [cmd_out_events]/[cmd_panic] do NOT appear in its conclusion;
    they are private helpers, and [run_cmd_seals_events] (used in the proof) is what makes [run_cmd] the
    authority.  Certified public surface of THIS module = [denote_program_run_agrees] (its [Print Assumptions]
    below is captured by the axiom-manifest gate). *)

From Fido Require Import preamble cmd unified GoAst GoSem cmd_unified.
From Stdlib Require Import List String.
Import ListNotations.

(** The initial single-goroutine config running [u] on goroutine 0: live, empty defers, no panic, no output. *)
Definition ustart (u : UCmd) : UConfig :=
  mkUCfg (fun t => if Nat.eqb t 0 then u else URet)
         (fun _ => nil) (fun _ => 0) (fun t => Nat.eqb t 0) nil nil (fun _ => nil) (fun _ => None).

(** The panic value an [Outcome] carries, if any — the cmd.v-side observation the unified [uc_panic] agrees with. *)
Definition ocpanic (oc : Outcome unit) : option GoAny :=
  match oc with OPanic v _ => Some v | ORet _ _ => None end.

Lemma map_snd_pair0 : forall (l : list (bool * list GoAny)), map snd (map (fun e => (0, e)) l) = l.
Proof. induction l as [|a l IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

(** COMPOSITION + run_cmd AGREEMENT: a program GoSem DENOTES runs under unified.v's [ustep], and that run
    AGREES with cmd.v's authoritative [run_cmd 1 c w].  If [denote_program p = Some c] then, from the
    single-goroutine start config, [usteps] drives goroutine 0 to completion, and its observable [uc_out] /
    [uc_panic] EQUAL [run_cmd 1 c w]'s World output / Outcome panic — the unified output events (stripped of
    goroutine id) are EXACTLY [run_cmd]'s appended [w_output], and [uc_panic 0] is EXACTLY the Outcome's panic.
    The [no_defer] side condition is DISCHARGED here from [denote_body_no_defer]; [run_cmd] (not a projection)
    is the conclusion's authority, via [run_cmd_seals_events]. *)
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
  destruct (cmd_to_ucmd_runs c Hnd ucap
              (fun t => if Nat.eqb t 0 then cmd_to_ucmd c else URet)
              (fun _ => nil) (fun _ => 0) (fun t => Nat.eqb t 0) nil nil (fun _ => nil) (fun _ => None)
              eq_refl eq_refl eq_refl eq_refl) as [p' [lv' [pa' [Hus [Hdone Hpan]]]]].
  destruct (run_cmd_seals_events c w Hnd) as [w' [Hrun Hout]].
  exists (mkUCfg p' (fun _ => nil) (fun _ => 0) lv' nil
                 (nil ++ map (fun e => (0, e)) (cmd_out_events c)) (fun _ => nil) pa'),
         (match cmd_panic c with None => ORet tt w' | Some v => OPanic v w' end).
  unfold ustart.
  split; [exact Hus | ]. split; [exact Hrun | ]. split; [exact Hdone | ]. split.
  - cbn [uc_out]. rewrite app_nil_l, map_snd_pair0.
    destruct (cmd_panic c); cbn [oc_world]; exact Hout.
  - cbn [uc_panic]. rewrite Hpan. unfold ocpanic. destruct (cmd_panic c); reflexivity.
Qed.

(** Trust surface for this module (axiom-manifest gate captures its [Print Assumptions]). *)
Print Assumptions denote_program_run_agrees.
