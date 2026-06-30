(** cmd_unified.v — the FIRST bridge between Fido's two proof-only semantics universes.

    GoSem denotes the supported AST into [cmd.v]'s command tree [Cmd unit] (CRet / COut / CPan / CDfr).
    [unified.v] is the closed-world OPERATIONAL semantics ([UCmd] / [ustep]) on which race-freedom and
    liveness/deadlock are proved.  The charter (ARCHITECTURE.md) requires GoSem to BRIDGE that existing
    semantics, NOT fork a second universe.  The structural fact that makes the bridge concrete: [cmd.v]'s
    four constructors are EXACTLY [unified.v]'s output / panic / return / defer fragment —
        CRet -> URet,  COut b xs -> UOut b xs,  CPan v -> UPan v,  CDfr d -> UDfr d.
    So [cmd_to_ucmd] is a TOTAL translation of the whole command language into a subset of [UCmd].  The
    print/println flag on [COut] is PRESERVED ([unified.v]'s [UOut]/[uc_out] now carry it, exactly the
    model's [w_output : list (bool * list GoAny)]) — the bridge is EXACT on observable output, not payload-only.

    This first slice proves EXACT OUTPUT + EXACT PANIC + RUN-TO-DONE for the DEFER-FREE fragment ([no_defer],
    from cmd.v) — precisely the fragment GoSem slice 1 denotes: a single goroutine running [cmd_to_ucmd c]
    [usteps] to completion (its goroutine goes [uc_live]:=false) emitting EXACTLY [c]'s output EVENTS (println
    flag and payload), in order, into [uc_out], and ending with [uc_panic 0] equal to [c]'s panic outcome.
    (Defer is excluded here: cmd.v runs deferred actions at return via [run_defers], unified.v via the
    [UDfr]/[ustep_ret_defer] LIFO stack; relating those two defer disciplines is a later slice.  No
    concurrency/heap/channel ops occur in this fragment, so [uc_bufs]/[uc_heap]/[uc_trace] are untouched.)
    This is proof-only: it emits no Go and adds no axiom. *)

From Fido Require Import preamble concurrency cmd unified.
From Stdlib Require Import List.
Import ListNotations.

(** The total structural translation: cmd.v command tree -> the output/panic/return/defer fragment of UCmd.
    [COut]'s [bool] (println vs print) is PRESERVED into [UOut]'s flag. *)
Fixpoint cmd_to_ucmd (c : Cmd unit) : UCmd :=
  match c with
  | CRet _      => URet
  | COut b xs c' => UOut b xs (cmd_to_ucmd c')
  | CPan v      => UPan v
  | CDfr d c'   => UDfr (cmd_to_ucmd d) (cmd_to_ucmd c')
  end.

(** The output EVENTS [c] emits, in order — each is the FULL model event [(println?, payload)], not just the
    payload (the defer-free reading: [go]'s [w_output] sequence). *)
Fixpoint cmd_out_events (c : Cmd unit) : list (bool * list GoAny) :=
  match c with
  | CRet _      => []
  | COut b xs c' => (b, xs) :: cmd_out_events c'
  | CPan _      => []
  | CDfr _ c'   => cmd_out_events c'
  end.

(** [c]'s final panic outcome on the defer-free fragment: [Some v] if it reaches [CPan v], else [None]. *)
Fixpoint cmd_panic (c : Cmd unit) : option GoAny :=
  match c with
  | CRet _      => None
  | COut _ _ c' => cmd_panic c'
  | CPan v      => Some v
  | CDfr _ c'   => cmd_panic c'
  end.

(** EXACT OUTPUT + EXACT PANIC + RUN-TO-DONE.  From any config whose goroutine 0 runs [cmd_to_ucmd c]
    (defer-free, empty defer stack, no active panic), [ustep] advances goroutine 0 to completion
    ([uc_live 0]:=false), appending EXACTLY [c]'s output EVENTS (println flag + payload, tagged with
    goroutine 0) to [uc_out], and leaving [uc_panic 0] equal to [c]'s panic outcome.  Buffers/heap/trace/
    defers are unchanged. *)
Theorem cmd_to_ucmd_runs : forall c,
  no_defer c = true ->
  forall (ucap : nat -> option nat) p b h lv tr o df pa,
    lv 0 = true -> p 0 = cmd_to_ucmd c -> df 0 = [] -> pa 0 = None ->
    exists (p' : nat -> UCmd) (lv' : nat -> bool) (pa' : nat -> option GoAny),
      usteps ucap (mkUCfg p b h lv tr o df pa)
                  (mkUCfg p' b h lv' tr (o ++ map (fun e => (0, e)) (cmd_out_events c)) df pa')
      /\ lv' 0 = false
      /\ pa' 0 = cmd_panic c.
Proof.
  intros c.
  induction c as [a | bo xs c' IH | v | d c' IHc'] using Cmd_rect';
    intros Hnd ucap p b h lv tr o df pa Hlv Hp Hdf Hpa.
  - (* CRet a : URet -> ustep_ret_done -> goroutine done, no output, no panic *)
    cbn [cmd_to_ucmd cmd_out_events cmd_panic] in *.
    exists p, (upd lv 0 false), pa. rewrite app_nil_r. split; [ | split ].
    + eapply usteps_step; [ eapply ustep_ret_done; [exact Hlv | exact Hp | exact Hdf] | apply usteps_refl ].
    + apply upd_same.
    + exact Hpa.
  - (* COut bo xs c' : UOut bo xs (..) -> ustep_out appends (0,(bo,xs)), then IH on c' *)
    cbn [cmd_to_ucmd cmd_out_events cmd_panic no_defer] in *.
    destruct (IH Hnd ucap (upd p 0 (cmd_to_ucmd c')) b h lv tr (o ++ [(0, (bo, xs))]) df pa
                  Hlv (upd_same _ _ _) Hdf Hpa) as [p' [lv' [pa' [Hus [Hdone Hpan]]]]].
    exists p', lv', pa'. split; [ | split; [exact Hdone | exact Hpan] ].
    replace (o ++ map (fun e => (0, e)) ((bo, xs) :: cmd_out_events c'))
       with ((o ++ [(0, (bo, xs))]) ++ map (fun e => (0, e)) (cmd_out_events c'))
      by (cbn [map]; rewrite <- app_assoc; reflexivity).
    eapply usteps_step; [ eapply ustep_out; [exact Hlv | exact Hp] | exact Hus ].
  - (* CPan v : UPan v -> ustep_pan_done -> goroutine done (panicking with v), no output *)
    cbn [cmd_to_ucmd cmd_out_events cmd_panic] in *.
    exists p, (upd lv 0 false), (upd pa 0 (Some v)). rewrite app_nil_r. split; [ | split ].
    + eapply usteps_step; [ eapply ustep_pan_done; [exact Hlv | exact Hp | exact Hdf] | apply usteps_refl ].
    + apply upd_same.
    + apply upd_same.
  - (* CDfr d c' : excluded by no_defer *)
    cbn [no_defer] in Hnd. discriminate Hnd.
Qed.

(** REGRESSIONS (Codex review): the bridge keeps print and println DISTINGUISHABLE, and the events carry the
    flag — it does not collapse them. *)
Example bridge_print_println_distinct : forall (a : GoAny),
  cmd_to_ucmd (COut true (a :: nil) (CRet tt)) <> cmd_to_ucmd (COut false (a :: nil) (CRet tt)).
Proof. intros a H. cbn in H. discriminate H. Qed.

Example bridge_events_carry_flag : forall (a b : GoAny),
  cmd_out_events (COut true (a :: nil) (COut false (b :: nil) (CRet tt))) = (true, a :: nil) :: (false, b :: nil) :: nil.
Proof. reflexivity. Qed.

(** A concrete run: a [print] (flag=false) followed by [panic v] emits exactly that one [(false, a)] event
    AND ends with [uc_panic 0 = Some v] — both observable facts, from the strengthened theorem. *)
Example bridge_print_then_panic : forall (a v : GoAny),
  exists p' lv' pa',
    usteps (fun _ => None)
      (mkUCfg (fun _ => cmd_to_ucmd (COut false (a :: nil) (CPan v)))
              (fun _ => nil) (fun _ => 0) (fun _ => true) nil nil (fun _ => nil) (fun _ => None))
      (mkUCfg p' (fun _ => nil) (fun _ => 0) lv' nil
              (nil ++ map (fun e => (0, e)) (cmd_out_events (COut false (a :: nil) (CPan v)))) (fun _ => nil) pa')
    /\ lv' 0 = false
    /\ pa' 0 = Some v.
Proof.
  intros a v.
  destruct (cmd_to_ucmd_runs (COut false (a :: nil) (CPan v)) eq_refl
              (fun _ => None) (fun _ => cmd_to_ucmd (COut false (a :: nil) (CPan v)))
              (fun _ => nil) (fun _ => 0) (fun _ => true) nil nil (fun _ => nil) (fun _ => None)
              eq_refl eq_refl eq_refl eq_refl) as [p' [lv' [pa' [Hus [Hdone Hpan]]]]].
  exists p', lv', pa'. split; [exact Hus | split; [exact Hdone | exact Hpan] ].
Qed.

(** Trust surface for this module (axiom-manifest gate captures its [Print Assumptions]). *)
Print Assumptions cmd_to_ucmd_runs.
