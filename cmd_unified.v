(** cmd_unified.v — the FIRST bridge between Fido's two proof-only semantics universes.

    GoSem denotes the supported AST into [cmd.v]'s command tree [Cmd unit] (CRet / COut / CPan / CDfr).
    [unified.v] is the closed-world OPERATIONAL semantics ([UCmd] / [ustep]) on which race-freedom and
    liveness/deadlock are proved.  The charter (ARCHITECTURE.md) requires GoSem to BRIDGE that existing
    semantics, NOT fork a second universe.  The structural fact that makes the bridge concrete: [cmd.v]'s
    four constructors are EXACTLY [unified.v]'s output / panic / return / defer fragment —
        CRet -> URet,  COut _ xs -> UOut xs,  CPan v -> UPan v,  CDfr d -> UDfr d.
    So [cmd_to_ucmd] is a TOTAL translation of the whole command language into a subset of [UCmd].

    This first slice proves OUTPUT PRESERVATION + RUN-TO-DONE for the DEFER-FREE fragment ([no_defer], from
    cmd.v) — precisely the fragment GoSem slice 1 denotes: a single goroutine running [cmd_to_ucmd c]
    [usteps] to completion (its goroutine goes [uc_live]:=false) emitting EXACTLY [c]'s output payloads, in
    order, into [uc_out].  (Defer is excluded here: cmd.v runs deferred actions at return via [run_defers],
    unified.v via the [UDfr]/[ustep_ret_defer] LIFO stack; relating those two defer disciplines is a later
    slice.  No concurrency/heap/channel ops occur in this fragment, so [uc_bufs]/[uc_heap]/[uc_trace] are
    untouched.)  This is proof-only: it emits no Go and adds no axiom. *)

From Fido Require Import preamble concurrency cmd unified.
From Stdlib Require Import List.
Import ListNotations.

(** The total structural translation: cmd.v command tree -> the output/panic/return/defer fragment of UCmd.
    [COut]'s [bool] (println vs print — a newline-rendering detail) is dropped: unified.v's [uc_out] records
    the PAYLOAD [xs], which is what is observed; both COut flavours print the same payload. *)
Fixpoint cmd_to_ucmd (c : Cmd unit) : UCmd :=
  match c with
  | CRet _      => URet
  | COut _ xs c' => UOut xs (cmd_to_ucmd c')
  | CPan v      => UPan v
  | CDfr d c'   => UDfr (cmd_to_ucmd d) (cmd_to_ucmd c')
  end.

(** The output payloads [c] emits, in order (the defer-free reading: [go]'s [w_log] sequence). *)
Fixpoint cmd_out_payloads (c : Cmd unit) : list (list GoAny) :=
  match c with
  | CRet _      => []
  | COut _ xs c' => xs :: cmd_out_payloads c'
  | CPan _      => []
  | CDfr _ c'   => cmd_out_payloads c'
  end.

(** OUTPUT PRESERVATION + RUN-TO-DONE.  From any config whose goroutine 0 runs [cmd_to_ucmd c] (defer-free,
    empty defer stack), [ustep] advances goroutine 0 to completion ([uc_live 0]:=false), appending EXACTLY
    [c]'s output payloads (tagged with goroutine 0) to [uc_out].  Buffers/heap/trace/defers are unchanged. *)
Theorem cmd_to_ucmd_runs : forall c,
  no_defer c = true ->
  forall (ucap : nat -> option nat) p b h lv tr o df pa,
    lv 0 = true -> p 0 = cmd_to_ucmd c -> df 0 = [] ->
    exists (p' : nat -> UCmd) (lv' : nat -> bool) (pa' : nat -> option GoAny),
      usteps ucap (mkUCfg p b h lv tr o df pa)
                  (mkUCfg p' b h lv' tr (o ++ map (fun x => (0, x)) (cmd_out_payloads c)) df pa')
      /\ lv' 0 = false.
Proof.
  intros c.
  induction c as [a | bo xs c' IH | v | d c' IHc'] using Cmd_rect';
    intros Hnd ucap p b h lv tr o df pa Hlv Hp Hdf.
  - (* CRet a : URet -> ustep_ret_done -> goroutine done, no output *)
    cbn [cmd_to_ucmd cmd_out_payloads] in *.
    exists p, (upd lv 0 false), pa. rewrite app_nil_r. split.
    + eapply usteps_step; [ eapply ustep_ret_done; [exact Hlv | exact Hp | exact Hdf] | apply usteps_refl ].
    + apply upd_same.
  - (* COut bo xs c' : UOut xs (..) -> ustep_out appends (0,xs), then IH on c' *)
    cbn [cmd_to_ucmd cmd_out_payloads no_defer] in *.
    destruct (IH Hnd ucap (upd p 0 (cmd_to_ucmd c')) b h lv tr (o ++ [(0, xs)]) df pa
                  Hlv (upd_same _ _ _) Hdf) as [p' [lv' [pa' [Hus Hdone]]]].
    exists p', lv', pa'. split; [ | exact Hdone ].
    replace (o ++ map (fun x => (0, x)) (xs :: cmd_out_payloads c'))
       with ((o ++ [(0, xs)]) ++ map (fun x => (0, x)) (cmd_out_payloads c'))
      by (cbn [map]; rewrite <- app_assoc; reflexivity).
    eapply usteps_step; [ eapply ustep_out; [exact Hlv | exact Hp] | exact Hus ].
  - (* CPan v : UPan v -> ustep_pan_done -> goroutine done (panicking), no output *)
    cbn [cmd_to_ucmd cmd_out_payloads] in *.
    exists p, (upd lv 0 false), (upd pa 0 (Some v)). rewrite app_nil_r. split.
    + eapply usteps_step; [ eapply ustep_pan_done; [exact Hlv | exact Hp | exact Hdf] | apply usteps_refl ].
    + apply upd_same.
  - (* CDfr d c' : excluded by no_defer *)
    cbn [no_defer] in Hnd. discriminate Hnd.
Qed.

(** Concrete witness: two prints then return bridge to their two payloads, in order. *)
Example bridge_two_prints : forall (a b : GoAny),
  cmd_out_payloads (COut true [a] (COut false [b] (CRet tt))) = [[a]; [b]].
Proof. reflexivity. Qed.

Example bridge_two_prints_ucmd : forall (a b : GoAny),
  cmd_to_ucmd (COut true [a] (COut false [b] (CRet tt))) = UOut [a] (UOut [b] URet).
Proof. reflexivity. Qed.

(** Trust surface for this module (axiom-manifest gate captures its [Print Assumptions]). *)
Print Assumptions cmd_to_ucmd_runs.
