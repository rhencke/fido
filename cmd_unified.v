(** cmd_unified.v — the FIRST bridge between Fido's two proof-only semantics universes.

    GoSem denotes the supported AST into [cmd.v]'s command tree [Cmd unit] (CRet / COut / CPan / CDfr).
    [unified.v] is the closed-world OPERATIONAL semantics ([UCmd] / [ustep]) on which race-freedom and
    liveness/deadlock are proved.  The charter (ARCHITECTURE.md) requires GoSem to BRIDGE that existing
    semantics, NOT fork a second universe.  The structural fact that makes the bridge concrete: [cmd.v]'s
    four constructors are EXACTLY [unified.v]'s output / panic / return / defer fragment —
        CRet -> URet,  COut b xs -> UOut b xs,  CPan v -> UPan v,  CDfr d -> UDfr d.
    So [cmd_to_ucmd] is a TOTAL translation of cmd.v's [Cmd unit] command tree into a subset of [UCmd].  The
    print/println flag on [COut] is PRESERVED ([unified.v]'s [UOut]/[uc_out] carry it, exactly the model's
    [w_output : list (bool * list GoAny)]).

    PUBLIC surfaces = [cmd_to_ucmd_run_agrees] (a DEFER-FREE [c], [cmd.no_defer] — the fragment GoSem slice 1
    denotes), [bridge_one_defer_agrees] (ONE defer: any [CDfr d c'] with [d]/[c'] [no_defer], either may panic),
    [bridge_flat_np_agrees] (MULTIPLE flat defers, fully NON-PANICKING — [flat c] + [cmd_no_panic c]), and
    [bridge_flat_agrees] (MULTIPLE flat defers WITH panics — just [flat c]; the (prog, pa) 2-mode unwind, final
    panic = [flat_defers_panic] last-raised-wins).  For all, the single-goroutine [usteps] run AGREES with
    cmd.v's AUTHORITATIVE [run_cmd] — the unified output events EQUAL [run_cmd]'s appended [w_output], and
    [uc_panic 0] EQUALS the Outcome's panic.
    There is NO public projection-observer theorem: the [cmd_out_events]/[cmd_panic]/[cmd_defers] projections,
    their [run_cmd] seal ([go_chars]), and the unified-side run lemmas are LOCAL (file-private) proof plumbing —
    no exported theorem concludes with them, so a consumer cannot prove bridge facts against a free observer
    instead of [run_cmd].  (NESTED defers are a later slice: a deferred action that itself defers — [flat] is
    one-level.  No concurrency/heap ops in this fragment, so [uc_bufs]/[uc_heap]/[uc_trace] are untouched.)
    Proof-only: emits no Go, adds no axiom. *)

From Fido Require Import preamble concurrency cmd unified.
From Stdlib Require Import List.
Import ListNotations.

(** PUBLIC.  The total structural translation: cmd.v command tree -> the output/panic/return/defer fragment of
    UCmd, [COut]'s println flag PRESERVED into [UOut]'s flag. *)
Fixpoint cmd_to_ucmd (c : Cmd unit) : UCmd :=
  match c with
  | CRet _      => URet
  | COut b xs c' => UOut b xs (cmd_to_ucmd c')
  | CPan v      => UPan v
  | CDfr d c'   => UDfr (cmd_to_ucmd d) (cmd_to_ucmd c')
  end.

(** PUBLIC.  The single-goroutine start config running [u] on goroutine 0 (live, empty defers, no panic, no
    output), and the panic an [Outcome] carries — the cmd.v-side observation [uc_panic] agrees with. *)
Definition ustart (u : UCmd) : UConfig :=
  mkUCfg (fun t => if Nat.eqb t 0 then u else URet)
         (fun _ => nil) (fun _ => 0) (fun t => Nat.eqb t 0) nil nil (fun _ => nil) (fun _ => None).
Definition ocpanic (oc : Outcome unit) : option GoAny :=
  match oc with OPanic v _ => Some v | ORet _ _ => None end.

(** ---- LOCAL proof plumbing (file-private — not exported, not gated; no PUBLIC theorem concludes with these) ----
    The output EVENTS / final panic [c] emits on the defer-free fragment, and their SEAL to cmd.v's authority. *)
Local Fixpoint cmd_out_events (c : Cmd unit) : list (bool * list GoAny) :=
  match c with
  | CRet _      => []
  | COut b xs c' => (b, xs) :: cmd_out_events c'
  | CPan _      => []
  | CDfr _ c'   => cmd_out_events c'
  end.
Local Fixpoint cmd_panic (c : Cmd unit) : option GoAny :=
  match c with
  | CRet _      => None
  | COut _ _ c' => cmd_panic c'
  | CPan v      => Some v
  | CDfr _ c'   => cmd_panic c'
  end.
(** The deferred actions [go] accumulates from [c] — in [go]'s order (innermost-deferred = LIFO HEAD = runs
    first), exactly the order [ustep_defer] builds the [uc_defers] stack.  [no_defer c] iff this is [[]].  This
    is NOT a second authority: [go_chars] below proves it EQUALS [snd (go c w)] (cmd.v's own accumulation). *)
Local Fixpoint cmd_defers (c : Cmd unit) : list (Cmd unit) :=
  match c with
  | CRet _      => []
  | COut _ _ c' => cmd_defers c'
  | CPan _      => []
  | CDfr d c'   => cmd_defers c' ++ (d :: nil)
  end.
Local Lemma cmd_defers_no_defer : forall c, no_defer c = true -> cmd_defers c = [].
Proof.
  intros c. induction c as [a | bo xs c' IH | v | d c' IHc'] using Cmd_rect'; intros Hnd; cbn in *;
    [ reflexivity | exact (IH Hnd) | reflexivity | discriminate Hnd ].
Qed.

(** [flat c] — every deferred action is [no_defer] (a one-level defer list).  Feeds the fully-non-panicking
    multiple-defer theorem below together with cmd.v's [cmd_no_panic] (the SINGLE panic-freedom authority — no
    local copy); both being syntactic + public keep that theorem's statement free of the Local [cmd_panic]. *)
Fixpoint flat (c : Cmd unit) : bool :=
  match c with
  | CRet _ => true | COut _ _ c' => flat c' | CPan _ => true | CDfr d c' => no_defer d && flat c'
  end.
Local Lemma cmd_no_panic_cmd_panic : forall c, cmd_no_panic c = true -> cmd_panic c = None.
Proof.
  intros c. induction c as [a | bo xs c' IH | v | d c' IHc'] using Cmd_rect'; intros Hnp; cbn in *;
    [ reflexivity | exact (IH Hnp) | discriminate Hnp
    | apply andb_prop in Hnp; exact (IHc' (proj2 Hnp)) ].
Qed.
(** Under [flat] + [cmd_no_panic], every deferred action [go] accumulates is BOTH [no_defer] and [cmd_no_panic]. *)
Local Lemma flat_np_defers : forall c, flat c = true -> cmd_no_panic c = true ->
  Forall (fun d => no_defer d = true /\ cmd_no_panic d = true) (cmd_defers c).
Proof.
  intros c. induction c as [a | bo xs c' IH | v | d c' IHc'] using Cmd_rect'; intros Hf Hnp; cbn in *.
  - constructor.
  - exact (IH Hf Hnp).
  - constructor.
  - apply andb_prop in Hf as [Hfd Hfc']. apply andb_prop in Hnp as [Hnpd Hnpc'].
    apply Forall_app; split; [ exact (IHc' Hfc' Hnpc') | constructor; [ split; assumption | constructor ] ].
Qed.

Local Lemma w_output_w_log : forall b xs w, w_output (w_log b xs w) = w_output w ++ ((b, xs) :: nil).
Proof. reflexivity. Qed.

(** GROUNDING in cmd.v's authoritative [go]: the three projections ARE [go]'s own components — for ANY [c]
    (defers included), [go c w] returns exactly [(<outcome from cmd_panic c>, cmd_defers c)] with the body's
    world advanced by [cmd_out_events c].  So [cmd_panic]/[cmd_out_events]/[cmd_defers] are not a parallel
    authority that could drift from [go]; they are derived NAMES for [go]'s behaviour.  [run_cmd_seals_events]
    (the no_defer seal) and Phase A ([cmd_to_ucmd_body_runs]) build on this. *)
Local Lemma go_chars : forall c w, exists w',
  go c w = ((match cmd_panic c with None => ORet tt w' | Some v => OPanic v w' end), cmd_defers c)
  /\ w_output w' = w_output w ++ cmd_out_events c.
Proof.
  intros c. induction c as [a | bo xs c' IH | v | d c' IHc'] using Cmd_rect'; intros w.
  - destruct a. exists w. cbn [go cmd_panic cmd_defers cmd_out_events]. rewrite app_nil_r. split; reflexivity.
  - cbn [go cmd_panic cmd_defers cmd_out_events].
    destruct (IH (w_log bo xs w)) as [w' [Hgo Hout]]. exists w'. rewrite Hgo. split;
      [ reflexivity | rewrite Hout, w_output_w_log, <- app_assoc; reflexivity ].
  - exists w. cbn [go cmd_panic cmd_defers cmd_out_events]. rewrite app_nil_r. split; reflexivity.
  - cbn [go cmd_panic cmd_defers cmd_out_events].
    destruct (IHc' w) as [w' [Hgo Hout]]. exists w'. rewrite Hgo. cbn. split; [ reflexivity | exact Hout ].
Qed.

(** SEAL: on the defer-free fragment the projections ARE cmd.v's own [run_cmd]/[w_output]/[Outcome] — derived
    from [go_chars] ([run_cmd 1 c w] = [go]'s body outcome, since [no_defer ⇒ cmd_defers c = []] so [run_defers]
    runs nothing).  The public theorem's [run_cmd] conclusion is thus grounded, not a free observer. *)
Local Lemma run_cmd_seals_events : forall c w,
  no_defer c = true ->
  exists w',
    run_cmd 1 c w = Some (match cmd_panic c with None => ORet tt w' | Some v => OPanic v w' end)
    /\ w_output w' = w_output w ++ cmd_out_events c.
Proof.
  intros c w Hnd. destruct (go_chars c w) as [w' [Hgo Hout]]. exists w'. split; [ | exact Hout ].
  unfold run_cmd. rewrite Hgo, (cmd_defers_no_defer c Hnd). destruct (cmd_panic c); reflexivity.
Qed.

(** Phase A of the defer bridge (general — NO [no_defer]): [ustep] runs [cmd_to_ucmd c]'s BODY to its outcome,
    accumulating its deferred actions onto goroutine 0's [uc_defers] stack in [go]'s order — leaving [prog 0] at
    [URet] / [UPan v] (per [cmd_panic c]) and [df' 0] = [map cmd_to_ucmd (cmd_defers c) ++ df 0].  The goroutine
    is NOT yet finished ([lv], [pa] untouched); the stack-UNWINDING ([run_defers]) is Phase B (done for ONE defer
    in [bridge_one_defer_agrees], and MULTIPLE non-panicking defers in [bridge_flat_np_agrees]; the multiple-
    PANICKING / nested case is later).  This
    is the [ustep] analogue of cmd.v's [go] — and faithfully so: [go_chars] proves the [cmd_panic c] /
    [cmd_out_events c] / [cmd_defers c] this conclusion uses ARE exactly [go c w]'s outcome / body output / defer
    list, so the simulation is grounded in cmd.v's authority, not a parallel projection.  [cmd_to_ucmd_runs] below
    specialises it to the [no_defer] fragment (then a single [ret_done]/[pan_done] finishes goroutine 0). *)
Local Lemma cmd_to_ucmd_body_runs : forall c ucap p b h lv tr o df pa,
  lv 0 = true -> p 0 = cmd_to_ucmd c ->
  exists (p' : nat -> UCmd) (df' : nat -> list UCmd),
    usteps ucap (mkUCfg p b h lv tr o df pa)
                (mkUCfg p' b h lv tr (o ++ map (fun e => (0, e)) (cmd_out_events c)) df' pa)
    /\ p' 0 = (match cmd_panic c with None => URet | Some v => UPan v end)
    /\ df' 0 = map cmd_to_ucmd (cmd_defers c) ++ df 0.
Proof.
  intros c. induction c as [a | bo xs c' IH | v | d c' IHc'] using Cmd_rect';
    intros ucap p b h lv tr o df pa Hlv Hp.
  - cbn [cmd_to_ucmd cmd_out_events cmd_panic cmd_defers] in *.
    exists p, df. rewrite app_nil_r. split; [ apply usteps_refl | split; [ exact Hp | reflexivity ] ].
  - cbn [cmd_to_ucmd cmd_out_events cmd_panic cmd_defers] in *.
    destruct (IH ucap (upd p 0 (cmd_to_ucmd c')) b h lv tr (o ++ [(0, (bo, xs))]) df pa
                  Hlv (upd_same _ _ _)) as [p' [df' [Hus [Hprog Hdf]]]].
    exists p', df'. split; [ | split; [ exact Hprog | exact Hdf ] ].
    replace (o ++ map (fun e => (0, e)) ((bo, xs) :: cmd_out_events c'))
       with ((o ++ [(0, (bo, xs))]) ++ map (fun e => (0, e)) (cmd_out_events c'))
      by (cbn [map]; rewrite <- app_assoc; reflexivity).
    eapply usteps_step; [ eapply ustep_out; [exact Hlv | exact Hp] | exact Hus ].
  - cbn [cmd_to_ucmd cmd_out_events cmd_panic cmd_defers] in *.
    exists p, df. rewrite app_nil_r. split; [ apply usteps_refl | split; [ exact Hp | reflexivity ] ].
  - cbn [cmd_to_ucmd cmd_out_events cmd_panic cmd_defers] in *.
    destruct (IHc' ucap (upd p 0 (cmd_to_ucmd c')) b h lv tr o (upd df 0 (cmd_to_ucmd d :: df 0)) pa
                  Hlv (upd_same _ _ _)) as [p' [df' [Hus [Hprog Hdf]]]].
    exists p', df'. split; [ | split; [ exact Hprog | ] ].
    + eapply usteps_step; [ eapply ustep_defer; [exact Hlv | exact Hp] | exact Hus ].
    + rewrite Hdf, upd_same, map_app. cbn [map]. rewrite <- app_assoc. reflexivity.
Qed.

(** the unified-side run on the [no_defer] fragment — now a SPECIALISATION of [cmd_to_ucmd_body_runs]: the body
    leaves [df' 0 = []] (since [cmd_defers c = []] when [no_defer]), so a single [ret_done] / [pan_done] finishes
    goroutine 0.  [df'] is now an EXISTENTIAL threaded from the body run (the projections [uc_live]/[uc_out]/
    [uc_panic] never read it). *)
Local Lemma cmd_to_ucmd_runs : forall c,
  no_defer c = true ->
  forall (ucap : nat -> option nat) p b h lv tr o df pa,
    lv 0 = true -> p 0 = cmd_to_ucmd c -> df 0 = [] -> pa 0 = None ->
    exists (p' : nat -> UCmd) (lv' : nat -> bool) (pa' : nat -> option GoAny) (df' : nat -> list UCmd),
      usteps ucap (mkUCfg p b h lv tr o df pa)
                  (mkUCfg p' b h lv' tr (o ++ map (fun e => (0, e)) (cmd_out_events c)) df' pa')
      /\ lv' 0 = false
      /\ pa' 0 = cmd_panic c.
Proof.
  intros c Hnd ucap p b h lv tr o df pa Hlv Hp Hdf Hpa.
  destruct (cmd_to_ucmd_body_runs c ucap p b h lv tr o df pa Hlv Hp) as [p' [df' [Hus [Hprog Hdf']]]].
  assert (Hdf0 : df' 0 = []).
  { rewrite Hdf', (cmd_defers_no_defer c Hnd); simpl; exact Hdf. }
  destruct (cmd_panic c) as [g | ]; cbn in Hprog.
  - exists p', (upd lv 0 false), (upd pa 0 (Some g)), df'.
    split; [ | split; [ apply upd_same | apply upd_same ] ].
    eapply usteps_trans; [ exact Hus | ].
    eapply usteps_step; [ eapply ustep_pan_done; [ exact Hlv | exact Hprog | exact Hdf0 ] | apply usteps_refl ].
  - exists p', (upd lv 0 false), pa, df'.
    split; [ | split; [ apply upd_same | exact Hpa ] ].
    eapply usteps_trans; [ exact Hus | ].
    eapply usteps_step; [ eapply ustep_ret_done; [ exact Hlv | exact Hprog | exact Hdf0 ] | apply usteps_refl ].
Qed.

Local Lemma map_snd_pair0 : forall (l : list (bool * list GoAny)), map snd (map (fun e => (0, e)) l) = l.
Proof. induction l as [|a l IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

(** ---- PUBLIC bridge theorem — agreement with cmd.v's authoritative [run_cmd] (NO projection in the conclusion) ----
    For a defer-free [c], the single-goroutine [usteps] run drives goroutine 0 to completion, and its observable
    [uc_out] / [uc_panic] EQUAL [run_cmd 1 c w]'s appended [w_output] / Outcome panic.  [run_cmd] (via the seal),
    not a free observer, is the authority. *)
Theorem cmd_to_ucmd_run_agrees : forall c ucap w,
  no_defer c = true ->
  exists (uc : UConfig) (oc : Outcome unit),
    usteps ucap (ustart (cmd_to_ucmd c)) uc
    /\ run_cmd 1 c w = Some oc
    /\ uc_live uc 0 = false
    /\ w_output (oc_world oc) = w_output w ++ map snd (uc_out uc)
    /\ uc_panic uc 0 = ocpanic oc.
Proof.
  intros c ucap w Hnd.
  destruct (cmd_to_ucmd_runs c Hnd ucap
              (fun t => if Nat.eqb t 0 then cmd_to_ucmd c else URet)
              (fun _ => nil) (fun _ => 0) (fun t => Nat.eqb t 0) nil nil (fun _ => nil) (fun _ => None)
              eq_refl eq_refl eq_refl eq_refl) as [p' [lv' [pa' [df' [Hus [Hdone Hpan]]]]]].
  destruct (run_cmd_seals_events c w Hnd) as [w' [Hrun Hout]].
  exists (mkUCfg p' (fun _ => nil) (fun _ => 0) lv' nil
                 (nil ++ map (fun e => (0, e)) (cmd_out_events c)) df' pa'),
         (match cmd_panic c with None => ORet tt w' | Some v => OPanic v w' end).
  unfold ustart.
  split; [exact Hus | ]. split; [exact Hrun | ]. split; [exact Hdone | ]. split.
  - cbn [uc_out]. rewrite app_nil_l, map_snd_pair0.
    destruct (cmd_panic c); cbn [oc_world]; exact Hout.
  - cbn [uc_panic]. rewrite Hpan. unfold ocpanic. destruct (cmd_panic c); reflexivity.
Qed.

(** LOCAL regressions (file-private): print and println stay DISTINGUISHABLE through the translation. *)
Local Example bridge_print_println_distinct : forall (a : GoAny),
  cmd_to_ucmd (COut true (a :: nil) (CRet tt)) <> cmd_to_ucmd (COut false (a :: nil) (CRet tt)).
Proof. intros a H. cbn in H. discriminate H. Qed.

(** ---- DEFER bridge — a CONCRETE witness for the one case still NOT general ----
    [cmd_to_ucmd_run_agrees] handles [no_defer]; [bridge_one_defer_agrees] handles ANY ONE defer ([CDfr d c']
    with [d]/[c'] [no_defer], EITHER may panic — covering [ustep_ret_defer]/[ustep_pan_defer]/[ustep_ret_done]/
    [ustep_pan_done] and panic-replacement in its four leaves); [bridge_flat_np_agrees] handles MULTIPLE
    non-panicking FLAT defers; and [bridge_flat_agrees] (below) handles MULTIPLE FLAT defers WITH panics (the
    (prog, pa) 2-mode) — which SUBSUMES the earlier two-panic witness ([defer panic v1; defer panic v2; return]),
    now deleted.  The earlier single-defer + sibling-LIFO demos are likewise SUBSUMED and were removed.  ONE
    file-private EXAMPLE remains, for the case NO theorem yet covers — it AGREES with cmd.v's [run_cmd]:
      NESTING ([defer (defer println(a))]): a deferred action that ITSELF defers (NOT [flat]) — [ustep_defer]
              fires AGAIN DURING the unwinding (the stack never exceeds ONE entry, but a second defer is
              registered mid-unwind), the inner defer running before the goroutine finishes (output [a]).
    NESTED defers GENERALLY (then channel/heap/spawn) are the next Phase-B slice. *)
Local Example bridge_defer_nested_agrees : forall (a : GoAny) (ucap : nat -> option nat) w,
  exists uc oc,
    usteps ucap (ustart (cmd_to_ucmd (CDfr (CDfr (COut true (a :: nil) (CRet tt)) (CRet tt)) (CRet tt)))) uc
    /\ run_cmd 5 (CDfr (CDfr (COut true (a :: nil) (CRet tt)) (CRet tt)) (CRet tt)) w = Some oc
    /\ uc_live uc 0 = false
    /\ w_output (oc_world oc) = w_output w ++ map snd (uc_out uc)
    /\ uc_panic uc 0 = ocpanic oc.
Proof.
  intros a ucap w. eexists. exists (ORet tt (w_log true (a :: nil) w)).
  split.
  { eapply usteps_step. { eapply ustep_defer     with (tid := 0); rewrite ?upd_same; cbn; reflexivity. }
    eapply usteps_step. { eapply ustep_ret_defer with (tid := 0); rewrite ?upd_same; cbn; reflexivity. }
    eapply usteps_step. { eapply ustep_defer     with (tid := 0); rewrite ?upd_same; cbn; reflexivity. }
    eapply usteps_step. { eapply ustep_ret_defer with (tid := 0); rewrite ?upd_same; cbn; reflexivity. }
    eapply usteps_step. { eapply ustep_out        with (tid := 0); rewrite ?upd_same; cbn; reflexivity. }
    eapply usteps_step. { eapply ustep_ret_done   with (tid := 0); rewrite ?upd_same; cbn; reflexivity. }
    apply usteps_refl. }
  split. { vm_compute. reflexivity. }
  split. { reflexivity. }
  split. { cbn. reflexivity. } { reflexivity. }
Qed.

(** ---- First GENERAL defer-agreement THEOREM (not a demo): ONE no_defer defer ----
    cmd.v-side grounding: [run_cmd] of [CDfr d c'] (defer [d]; then body [c']), for [d]/[c'] both [no_defer],
    runs the body THEN the single deferred [d].  The world is advanced by the body's output THEN [d]'s; the
    OUTCOME is [d]'s panic if [d] panics (a deferred panic REPLACES the active one), else the body's
    ([cmd_panic c']).  Derived purely from [go_chars] (applied to [CDfr d c'] and to [d]) + the one-element
    [run_defers] reduction — so it stays grounded in cmd.v's authoritative [run_cmd].  Fuel [2] is the MINIMAL
    principled count (one [run_defers] step to run [d], one for its empty tail), paralleling [run_cmd 1] for the
    zero-defer public theorem — NOT the arbitrary [5] the concrete demos carry. *)
Local Lemma run_cmd_one_defer : forall d c' w,
  no_defer d = true -> no_defer c' = true ->
  exists w'',
    run_cmd 2 (CDfr d c') w
      = Some (match cmd_panic d with
              | Some vd => OPanic vd w''
              | None    => match cmd_panic c' with None => ORet tt w'' | Some v => OPanic v w'' end
              end)
    /\ w_output w'' = w_output w ++ cmd_out_events c' ++ cmd_out_events d.
Proof.
  intros d c' w Hd Hc'.
  destruct (go_chars (CDfr d c') w) as [w' [Hgo Hout]].
  destruct (go_chars d w') as [w'' [Hgod Houtd]].
  exists w''. split.
  - unfold run_cmd. rewrite Hgo. cbn [cmd_defers cmd_panic] in *.
    rewrite (cmd_defers_no_defer c' Hc'), (cmd_defers_no_defer d Hd) in *. cbn [app] in *.
    (* ds = [d]; oc_world (oc_unit oc) = w'; go d w' = (<outcome cmd_panic d> w'', []) *)
    destruct (cmd_panic c') as [vb | ]; destruct (cmd_panic d) as [vd | ];
      cbn [oc_unit oc_world run_defers]; rewrite Hgod;
      cbn [run_defers oc_set_world oc_world]; reflexivity.
  - rewrite Houtd, Hout. cbn [cmd_out_events] in *. rewrite <- app_assoc. reflexivity.
Qed.

(** The first GENERAL (not concrete-demo) defer agreement: for ANY [CDfr d c'] with [d]/[c'] both [no_defer], the
    single-goroutine [usteps] run AGREES with cmd.v's authoritative [run_cmd] — SAME shape as
    [cmd_to_ucmd_run_agrees], for a CLASS [no_defer] rejects (defer-bearing).  NO restriction on whether [d] or
    [c'] panics: the statement is grounded in the abstract Outcome [oc] ([= run_cmd]'s result), not the private
    [cmd_panic].  FOUR leaves (body returns/panics × [d] returns/panics): Phase A ([cmd_to_ucmd_body_runs], run
    the body leaving [d] stacked) + ONE pop ([ustep_ret_defer] / [ustep_pan_defer], absorbing the body's panic
    into [pa]) + Phase A on [d] + the finish ([ustep_ret_done] if [d] returned, [ustep_pan_done] if [d] panicked
    — its panic REPLACING any active one); [run_cmd] grounded by [run_cmd_one_defer].  Multiple NON-panicking
    defers are [bridge_flat_np_agrees] below; multiple PANICKING / nested defers are later Phase-B slices. *)
Theorem bridge_one_defer_agrees : forall d c' ucap w,
  no_defer d = true -> no_defer c' = true ->
  exists (uc : UConfig) (oc : Outcome unit),
    usteps ucap (ustart (cmd_to_ucmd (CDfr d c'))) uc
    /\ run_cmd 2 (CDfr d c') w = Some oc
    /\ uc_live uc 0 = false
    /\ w_output (oc_world oc) = w_output w ++ map snd (uc_out uc)
    /\ uc_panic uc 0 = ocpanic oc.
Proof.
  intros d c' ucap w Hd Hc'.
  destruct (run_cmd_one_defer d c' w Hd Hc') as [w'' [Hrun Hwout]].
  destruct (cmd_to_ucmd_body_runs (CDfr d c') ucap
              (fun t => if Nat.eqb t 0 then cmd_to_ucmd (CDfr d c') else URet)
              (fun _ => nil) (fun _ => 0) (fun t => Nat.eqb t 0) nil nil (fun _ => nil) (fun _ => None)
              eq_refl eq_refl) as [p' [df' [Hus1 [Hprog1 Hdf1]]]].
  cbn [cmd_panic cmd_defers cmd_out_events] in Hprog1, Hdf1.
  rewrite (cmd_defers_no_defer c' Hc') in Hdf1. cbn [map app] in Hdf1.
  pose (oB := nil ++ map (fun e => (0, e)) (cmd_out_events c')).
  (* The output-agreement and liveness goals are identical across all four leaves. *)
  assert (Hout_ag : forall (dfx : nat -> list UCmd) (px : nat -> UCmd) (lvx : nat -> bool) pax (ocx : Outcome unit),
    oc_world ocx = w'' ->
    w_output (oc_world ocx) = w_output w ++ map snd (uc_out
      (mkUCfg px (fun _ => nil) (fun _ => 0) lvx nil (oB ++ map (fun e => (0, e)) (cmd_out_events d)) dfx pax))).
  { intros dfx px lvx pax ocx Hocx. cbn [uc_out]. rewrite Hocx, Hwout. subst oB.
    rewrite !map_app. cbn [map app]. rewrite !map_snd_pair0. rewrite app_assoc. reflexivity. }
  destruct (cmd_panic c') as [vb | ]; cbn in Hprog1.
  - (* body PANICS vb: pan_defer absorbs vb into pa, then run d. *)
    destruct (cmd_to_ucmd_body_runs d ucap (upd p' 0 (cmd_to_ucmd d))
                (fun _ => nil) (fun _ => 0) (fun t => Nat.eqb t 0) nil oB (upd df' 0 nil)
                (upd (fun _ : nat => @None GoAny) 0 (Some vb)) eq_refl (upd_same _ _ _))
      as [p'' [df'' [Hus2 [Hprog2 Hdf2]]]].
    cbn [cmd_defers] in Hdf2. rewrite (cmd_defers_no_defer d Hd) in Hdf2. cbn [map] in Hdf2. rewrite upd_same in Hdf2.
    destruct (cmd_panic d) as [vd | ]; cbn in Hprog2.
    + (* d panics vd: pan_done REPLACES vb -> Some vd. *)
      eexists. exists (OPanic vd w''). split; [ | split; [ exact Hrun | split ] ].
      * eapply usteps_trans; [ exact Hus1 | ].
        eapply usteps_step. { eapply ustep_pan_defer with (tid := 0); [ reflexivity | rewrite Hprog1; reflexivity | rewrite Hdf1; reflexivity ]. }
        eapply usteps_trans; [ exact Hus2 | ].
        eapply usteps_step. { eapply ustep_pan_done with (tid := 0); [ reflexivity | exact Hprog2 | exact Hdf2 ]. }
        apply usteps_refl.
      * cbn [uc_live]. apply upd_same.
      * split; [ apply Hout_ag; reflexivity | cbn [uc_panic]; rewrite upd_same; reflexivity ].
    + (* d returns: ret_done keeps the active vb. *)
      eexists. exists (OPanic vb w''). split; [ | split; [ exact Hrun | split ] ].
      * eapply usteps_trans; [ exact Hus1 | ].
        eapply usteps_step. { eapply ustep_pan_defer with (tid := 0); [ reflexivity | rewrite Hprog1; reflexivity | rewrite Hdf1; reflexivity ]. }
        eapply usteps_trans; [ exact Hus2 | ].
        eapply usteps_step. { eapply ustep_ret_done with (tid := 0); [ reflexivity | exact Hprog2 | exact Hdf2 ]. }
        apply usteps_refl.
      * cbn [uc_live]. apply upd_same.
      * split; [ apply Hout_ag; reflexivity | cbn [uc_panic]; rewrite upd_same; reflexivity ].
  - (* body RETURNS: ret_defer, then run d (pa stays None until d). *)
    destruct (cmd_to_ucmd_body_runs d ucap (upd p' 0 (cmd_to_ucmd d))
                (fun _ => nil) (fun _ => 0) (fun t => Nat.eqb t 0) nil oB (upd df' 0 nil)
                (fun _ => None) eq_refl (upd_same _ _ _))
      as [p'' [df'' [Hus2 [Hprog2 Hdf2]]]].
    cbn [cmd_defers] in Hdf2. rewrite (cmd_defers_no_defer d Hd) in Hdf2. cbn [map] in Hdf2. rewrite upd_same in Hdf2.
    destruct (cmd_panic d) as [vd | ]; cbn in Hprog2.
    + (* d panics vd: pan_done -> Some vd. *)
      eexists. exists (OPanic vd w''). split; [ | split; [ exact Hrun | split ] ].
      * eapply usteps_trans; [ exact Hus1 | ].
        eapply usteps_step. { eapply ustep_ret_defer with (tid := 0); [ reflexivity | rewrite Hprog1; reflexivity | rewrite Hdf1; reflexivity ]. }
        eapply usteps_trans; [ exact Hus2 | ].
        eapply usteps_step. { eapply ustep_pan_done with (tid := 0); [ reflexivity | exact Hprog2 | exact Hdf2 ]. }
        apply usteps_refl.
      * cbn [uc_live]. apply upd_same.
      * split; [ apply Hout_ag; reflexivity | cbn [uc_panic]; rewrite upd_same; reflexivity ].
    + (* d returns: ret_done -> ORet, no panic. *)
      eexists. exists (ORet tt w''). split; [ | split; [ exact Hrun | split ] ].
      * eapply usteps_trans; [ exact Hus1 | ].
        eapply usteps_step. { eapply ustep_ret_defer with (tid := 0); [ reflexivity | rewrite Hprog1; reflexivity | rewrite Hdf1; reflexivity ]. }
        eapply usteps_trans; [ exact Hus2 | ].
        eapply usteps_step. { eapply ustep_ret_done with (tid := 0); [ reflexivity | exact Hprog2 | exact Hdf2 ]. }
        apply usteps_refl.
      * cbn [uc_live]. apply upd_same.
      * split; [ apply Hout_ag; reflexivity | cbn [uc_panic]; reflexivity ].
Qed.

(** ---- SECOND general defer theorem: MULTIPLE flat defers, fully NON-PANICKING ----
    For [flat c] (every deferred action [no_defer]) AND [cmd_no_panic c] (no [CPan] anywhere), the [usteps] run of
    [cmd_to_ucmd c] AGREES with cmd.v's [run_cmd].  This is the common cleanup pattern ([defer f(); defer g();
    body], nothing panics) — ANY NUMBER of defers, but no panic, so the unwind is pure [ustep_ret_defer] pops
    ending in [ustep_ret_done] (the panic-in-flight 2-mode invariant is NOT needed).  [bridge_one_defer_agrees]
    (above) is the ORTHOGONAL axis: exactly one defer but EITHER side may panic. *)

(** cmd.v-side: [run_defers] over a list of [no_defer]+[cmd_no_panic] actions from an [ORet] just runs each in
    order, threading the world — no panic, no nesting.  Fuel [S (length ds)] suffices (one level per defer). *)
Local Lemma run_defers_np : forall ds w0,
  Forall (fun d => no_defer d = true /\ cmd_no_panic d = true) ds ->
  exists w', run_defers (S (length ds)) ds (ORet tt w0) = Some (ORet tt w')
    /\ w_output w' = w_output w0 ++ concat (map cmd_out_events ds).
Proof.
  induction ds as [| d ds' IH]; intros w0 Hall.
  - exists w0. cbn [run_defers concat map]. rewrite app_nil_r. split; reflexivity.
  - inversion Hall as [| x l [Hnd Hnp] Hall' Heq]; subst.
    destruct (go_chars d w0) as [w_d [Hgo Hout]].
    rewrite (cmd_no_panic_cmd_panic d Hnp), (cmd_defers_no_defer d Hnd) in Hgo.
    destruct (IH w_d Hall') as [w' [Hrun Houtf]].
    exists w'. split.
    + cbn [run_defers length]. cbn [oc_world]. rewrite Hgo. cbn [run_defers oc_set_world]. exact Hrun.
    + rewrite Houtf, Hout. cbn [concat map]. rewrite <- app_assoc. reflexivity.
Qed.

(** ustep-side: from [prog 0 = URet], [pa 0 = None], [df 0 = map cmd_to_ucmd ds] (all [no_defer]+[cmd_no_panic]),
    the run pops each defer via [ustep_ret_defer] + runs it (Phase A, [cmd_no_panic] ⇒ back to [URet]) and finishes
    with [ustep_ret_done]; [pa] stays [None] throughout (nothing panics). *)
Local Lemma unwind_np : forall ds ucap p b h lv tr o df pa,
  Forall (fun d => no_defer d = true /\ cmd_no_panic d = true) ds ->
  lv 0 = true -> p 0 = URet -> df 0 = map cmd_to_ucmd ds -> pa 0 = None ->
  exists (p' : nat -> UCmd) (lv' : nat -> bool) (df' : nat -> list UCmd),
    usteps ucap (mkUCfg p b h lv tr o df pa)
                (mkUCfg p' b h lv' tr (o ++ map (fun e => (0, e)) (concat (map cmd_out_events ds))) df' pa)
    /\ lv' 0 = false.
Proof.
  induction ds as [| d ds' IH]; intros ucap p b h lv tr o df pa Hall Hlv Hp Hdf Hpa.
  - cbn [map concat] in *. exists p, (upd lv 0 false), df. rewrite app_nil_r.
    split; [ | apply upd_same ].
    eapply usteps_step; [ eapply ustep_ret_done; [ exact Hlv | exact Hp | exact Hdf ] | apply usteps_refl ].
  - inversion Hall as [| x l [Hnd Hnp] Hall' Heq]; subst. cbn [map] in Hdf.
    destruct (cmd_to_ucmd_body_runs d ucap (upd p 0 (cmd_to_ucmd d)) b h lv tr o
                (upd df 0 (map cmd_to_ucmd ds')) pa Hlv (upd_same _ _ _))
      as [p'' [df'' [Hus2 [Hprog2 Hdf2]]]].
    rewrite (cmd_no_panic_cmd_panic d Hnp) in Hprog2.
    cbn [cmd_defers] in Hdf2. rewrite (cmd_defers_no_defer d Hnd) in Hdf2. cbn [map] in Hdf2. rewrite upd_same in Hdf2.
    destruct (IH ucap p'' b h lv tr (o ++ map (fun e => (0, e)) (cmd_out_events d)) df'' pa
                Hall' Hlv Hprog2 Hdf2 Hpa) as [p' [lv' [df' [Hus3 Hdone]]]].
    exists p', lv', df'. split; [ | exact Hdone ].
    replace (o ++ map (fun e => (0, e)) (concat (map cmd_out_events (d :: ds'))))
       with ((o ++ map (fun e => (0, e)) (cmd_out_events d)) ++ map (fun e => (0, e)) (concat (map cmd_out_events ds')))
      by (cbn [concat map]; rewrite map_app, <- app_assoc; reflexivity).
    eapply usteps_step; [ eapply ustep_ret_defer; [ exact Hlv | exact Hp | exact Hdf ] | ].
    eapply usteps_trans; [ exact Hus2 | exact Hus3 ].
Qed.

(** cmd.v authority for the theorem: [run_cmd] of a [flat]+[cmd_no_panic] [c] reaches [ORet], world advanced by the
    body's output THEN every defer's (in [go]-accumulation order).  From [go_chars] + [run_defers_np]. *)
Local Lemma run_cmd_flat_np : forall c w,
  flat c = true -> cmd_no_panic c = true ->
  exists w', run_cmd (S (length (cmd_defers c))) c w = Some (ORet tt w')
    /\ w_output w' = w_output w ++ cmd_out_events c ++ concat (map cmd_out_events (cmd_defers c)).
Proof.
  intros c w Hf Hnp.
  destruct (go_chars c w) as [w_body [Hgo Hout]].
  rewrite (cmd_no_panic_cmd_panic c Hnp) in Hgo.
  destruct (run_defers_np (cmd_defers c) w_body (flat_np_defers c Hf Hnp)) as [w' [Hrun Houtf]].
  exists w'. split.
  - unfold run_cmd. rewrite Hgo. cbn [oc_unit]. rewrite Hrun. cbn [oc_set_world]. reflexivity.
  - rewrite Houtf, Hout. rewrite <- app_assoc. reflexivity.
Qed.

Theorem bridge_flat_np_agrees : forall c ucap w,
  flat c = true -> cmd_no_panic c = true ->
  exists (uc : UConfig) (w' : World) (fuel : nat),
    usteps ucap (ustart (cmd_to_ucmd c)) uc
    /\ run_cmd fuel c w = Some (ORet tt w')   (* cmd.v's AUTHORITATIVE run (some SUFFICIENT fuel) — grounds w' *)
    /\ uc_live uc 0 = false
    /\ uc_panic uc 0 = None
    /\ w_output w' = w_output w ++ map snd (uc_out uc).
Proof.
  intros c ucap w Hf Hnp.
  destruct (run_cmd_flat_np c w Hf Hnp) as [w' [Hrun Hwout]].
  destruct (cmd_to_ucmd_body_runs c ucap
              (fun t => if Nat.eqb t 0 then cmd_to_ucmd c else URet)
              (fun _ => nil) (fun _ => 0) (fun t => Nat.eqb t 0) nil nil (fun _ => nil) (fun _ => None)
              eq_refl eq_refl) as [p' [df' [Hus1 [Hprog1 Hdf1]]]].
  rewrite (cmd_no_panic_cmd_panic c Hnp) in Hprog1. cbn in Hprog1.
  cbn in Hdf1. rewrite app_nil_r in Hdf1.
  destruct (unwind_np (cmd_defers c) ucap p' (fun _ => nil) (fun _ => 0) (fun t => Nat.eqb t 0) nil
              (nil ++ map (fun e => (0, e)) (cmd_out_events c)) df' (fun _ => None)
              (flat_np_defers c Hf Hnp) eq_refl Hprog1 Hdf1 eq_refl) as [p'' [lv'' [df'' [Hus2 Hdone]]]].
  eexists. exists w'. exists (S (length (cmd_defers c))). split; [ | split; [ exact Hrun | split ] ].
  - unfold ustart. eapply usteps_trans; [ exact Hus1 | exact Hus2 ].
  - exact Hdone.
  - split.
    + cbn [uc_panic]. reflexivity.
    + cbn [oc_world uc_out]. rewrite Hwout. rewrite !map_app. cbn [map app]. rewrite !map_snd_pair0.
      rewrite app_assoc. reflexivity.
Qed.

(** ---- THIRD general defer theorem: MULTIPLE flat defers, PANICS ALLOWED (the (prog, pa) 2-mode) ----
    Drops [bridge_flat_np_agrees]'s [cmd_no_panic]: for ANY [flat c] (every deferred action [no_defer], but the
    body and defers MAY panic), the [usteps] run of [cmd_to_ucmd c] AGREES with [run_cmd].  The final panic is
    [flat_defers_panic (cmd_defers c) (cmd_panic c)] — the body's panic threaded through the defers, each
    panicking defer REPLACING the active one (Go's last-raised-wins; = cmd.v's [run_defers] semantics).  Under
    [ustep] this is the 2-mode unwind: a defer's panic rides in [prog] as [UPan v] until the NEXT pop moves it
    into [pa] ([ustep_pan_defer]), a later panic superseding it — so this SUBSUMES the two-panic witness.  The
    invariant threaded by [unwind_flat] is [current = match prog 0 with UPan v => Some v | URet => pa 0]. *)

(** The active panic after running flat defers [ds] (in [go]-accumulation / run order, head first) seeded with
    [p0]: last panic wins (a returning defer keeps the active panic).  = the fold [run_defers] performs. *)
Fixpoint flat_defers_panic (ds : list (Cmd unit)) (p0 : option GoAny) : option GoAny :=
  match ds with
  | nil => p0
  | d :: ds' => flat_defers_panic ds' (match cmd_panic d with Some v => Some v | None => p0 end)
  end.
Local Lemma flat_defers_panic_none : forall ds p0, flat_defers_panic ds p0 = None -> p0 = None.
Proof.
  induction ds as [| d ds' IH]; intros p0 H; cbn in H; [ exact H | ].
  apply IH in H. destruct (cmd_panic d); [ discriminate H | exact H ].
Qed.
(** Under [flat] every deferred action [go] accumulates is [no_defer] (the [cmd_no_panic]-free half of
    [flat_np_defers]) — the defer list is one-level, exactly what [run_defers_flat] / [unwind_flat] consume. *)
Local Lemma flat_defers_nd : forall c, flat c = true -> Forall (fun d => no_defer d = true) (cmd_defers c).
Proof.
  intros c. induction c as [a | bo xs c' IH | v | d c' IHc'] using Cmd_rect'; intros Hf; cbn in *.
  - constructor.
  - exact (IH Hf).
  - constructor.
  - apply andb_prop in Hf as [Hfd Hfc'].
    apply Forall_app; split; [ exact (IHc' Hfc') | constructor; [ exact Hfd | constructor ] ].
Qed.

(** [oc_set_world] only advances the world — it preserves the [Outcome]'s panic status (and sets its world). *)
Local Lemma ocpanic_set_world : forall (acc : Outcome unit) w, ocpanic (oc_set_world acc w) = ocpanic acc.
Proof. intros [[] w0 | v w0] w; reflexivity. Qed.
Local Lemma oc_world_set_world : forall (acc : Outcome unit) w, oc_world (oc_set_world acc w) = w.
Proof. intros [[] w0 | v w0] w; reflexivity. Qed.

(** One definitional unfolding of [run_defers] over a [cons] with fuel to spare — a controlled rewrite so the
    step lemma need not fight [cbn]'s aggressiveness on the (variable-list) tail recursion. *)
Local Lemma run_defers_unfold : forall n d ds acc,
  run_defers (S n) (d :: ds) acc
    = (let '(oc_d, ds_d) := go d (oc_world acc) in
       match run_defers n ds_d oc_d with
       | None => None
       | Some net_d =>
           run_defers n ds (match net_d with
                            | OPanic v' w' => OPanic v' w'
                            | ORet _ w' => oc_set_world acc w' end)
       end).
Proof. reflexivity. Qed.

(** Running ONE [no_defer] defer [d] (head of the list): [go d] is atomic ([cmd_defers d = []]), so [run_defers]
    over [d :: ds] reduces to [run_defers] over [ds] with the accumulator advanced — panic REPLACED if [d]
    panicked, else the world advanced (active panic kept).  Grounded in [go_chars]. *)
Local Lemma run_defers_step_nd : forall n d ds acc,
  no_defer d = true ->
  exists w_d,
    run_defers (S (S n)) (d :: ds) acc
      = run_defers (S n) ds (match cmd_panic d with
                             | Some v => OPanic v w_d
                             | None => oc_set_world acc w_d end)
    /\ w_output w_d = w_output (oc_world acc) ++ cmd_out_events d.
Proof.
  intros n d ds acc Hnd.
  destruct (go_chars d (oc_world acc)) as [w_d [Hgo Hout]].
  rewrite (cmd_defers_no_defer d Hnd) in Hgo.
  exists w_d. split; [ | exact Hout ].
  rewrite run_defers_unfold, Hgo. destruct (cmd_panic d) as [v|]; reflexivity.
Qed.

(** cmd.v-side: [run_defers] over a list of [no_defer] actions (panics allowed) from an arbitrary accumulator
    [acc] threads each in order, the final panic being [flat_defers_panic ds (ocpanic acc)].  Fuel
    [S (length ds)]. *)
Local Lemma run_defers_flat : forall ds acc,
  Forall (fun d => no_defer d = true) ds ->
  exists w', run_defers (S (length ds)) ds acc
      = Some (match flat_defers_panic ds (ocpanic acc) with
              | Some v => OPanic v w' | None => ORet tt w' end)
    /\ w_output w' = w_output (oc_world acc) ++ concat (map cmd_out_events ds).
Proof.
  induction ds as [| d ds' IH]; intros acc Hall.
  - exists (oc_world acc). split.
    + cbn [run_defers length flat_defers_panic]. destruct acc as [[] w | v w]; reflexivity.
    + cbn [concat map]. rewrite app_nil_r. reflexivity.
  - inversion Hall as [| x l Hnd Hall' Heq]; subst.
    destruct (run_defers_step_nd (length ds') d ds' acc Hnd) as [w_d [Hstep Hout]].
    destruct (IH (match cmd_panic d with Some v => OPanic v w_d | None => oc_set_world acc w_d end) Hall')
      as [w' [Hrun Houtf]].
    exists w'. split.
    + cbn [length]. rewrite Hstep, Hrun. cbn [flat_defers_panic].
      destruct (cmd_panic d) as [v|].
      * cbn [ocpanic]. reflexivity.
      * rewrite ocpanic_set_world. reflexivity.
    + rewrite Houtf. cbn [concat map].
      destruct (cmd_panic d) as [v|].
      * cbn [oc_world]. rewrite Hout, <- app_assoc. reflexivity.
      * rewrite oc_world_set_world, Hout, <- app_assoc. reflexivity.
Qed.

(** cmd.v authority for the theorem: [run_cmd] of a [flat] [c] reaches [flat_defers_panic (cmd_defers c)
    (cmd_panic c)] (the body's panic threaded through the defers), world advanced by the body's output THEN
    every defer's.  From [go_chars] + [run_defers_flat]; the [None] case forces [cmd_panic c = None] via
    [flat_defers_panic_none], so the body returned and the emitted world is [ORet]'s. *)
Local Lemma run_cmd_flat : forall c w,
  flat c = true ->
  exists w', run_cmd (S (length (cmd_defers c))) c w
      = Some (match flat_defers_panic (cmd_defers c) (cmd_panic c) with
              | Some v => OPanic v w' | None => ORet tt w' end)
    /\ w_output w' = w_output w ++ cmd_out_events c ++ concat (map cmd_out_events (cmd_defers c)).
Proof.
  intros c w Hf.
  destruct (go_chars c w) as [w_body [Hgo Hout]].
  destruct (run_defers_flat (cmd_defers c)
              (match cmd_panic c with None => ORet tt w_body | Some v => OPanic v w_body end)
              (flat_defers_nd c Hf)) as [w' [Hrun Houtf]].
  exists w'. split.
  - unfold run_cmd. rewrite Hgo.
    replace (oc_unit (match cmd_panic c with None => ORet tt w_body | Some v => OPanic v w_body end))
       with (match cmd_panic c with None => ORet tt w_body | Some v => OPanic v w_body end)
      by (destruct (cmd_panic c); reflexivity).
    replace (ocpanic (match cmd_panic c with None => ORet tt w_body | Some v => OPanic v w_body end))
       with (cmd_panic c) in Hrun by (destruct (cmd_panic c); reflexivity).
    rewrite Hrun.
    destruct (flat_defers_panic (cmd_defers c) (cmd_panic c)) as [v|] eqn:Efd.
    + reflexivity.
    + apply flat_defers_panic_none in Efd. rewrite Efd. reflexivity.
  - rewrite Houtf.
    replace (oc_world (match cmd_panic c with None => ORet tt w_body | Some v => OPanic v w_body end))
       with w_body by (destruct (cmd_panic c); reflexivity).
    rewrite Hout, <- app_assoc. reflexivity.
Qed.

(** ustep-side: the (prog, pa) 2-mode unwind.  From [prog 0 ∈ {URet, UPan v}] and [df 0 = map cmd_to_ucmd ds]
    (all [no_defer]), pop each defer — [ustep_ret_defer] if [prog = URet] (pa unchanged), [ustep_pan_defer] if
    [prog = UPan v] (RECORDING v into pa) — run it (Phase A), and finish with [ustep_ret_done] / [ustep_pan_done].
    The current in-flight panic is [match prog 0 with UPan v => Some v | URet => pa 0]; the run ends with [pa' 0]
    = that threaded through [ds] by [flat_defers_panic]. *)
Local Lemma unwind_flat : forall ds ucap p b h lv tr o df pa,
  Forall (fun d => no_defer d = true) ds ->
  lv 0 = true -> (p 0 = URet \/ exists v, p 0 = UPan v) -> df 0 = map cmd_to_ucmd ds ->
  exists (p' : nat -> UCmd) (lv' : nat -> bool) (df' : nat -> list UCmd) (pa' : nat -> option GoAny),
    usteps ucap (mkUCfg p b h lv tr o df pa)
                (mkUCfg p' b h lv' tr (o ++ map (fun e => (0, e)) (concat (map cmd_out_events ds))) df' pa')
    /\ lv' 0 = false
    /\ pa' 0 = flat_defers_panic ds (match p 0 with UPan v => Some v | _ => pa 0 end).
Proof.
  induction ds as [| d ds' IH]; intros ucap p b h lv tr o df pa Hall Hlv Hp Hdf.
  - cbn [map concat] in *. rewrite app_nil_r.
    destruct Hp as [Hret | [v Hpan]].
    + exists p, (upd lv 0 false), df, pa. split; [ | split; [ apply upd_same | ] ].
      * eapply usteps_step; [ eapply ustep_ret_done; [ exact Hlv | exact Hret | exact Hdf ] | apply usteps_refl ].
      * cbn [flat_defers_panic]. rewrite Hret. reflexivity.
    + exists p, (upd lv 0 false), df, (upd pa 0 (Some v)). split; [ | split; [ apply upd_same | ] ].
      * eapply usteps_step; [ eapply ustep_pan_done; [ exact Hlv | exact Hpan | exact Hdf ] | apply usteps_refl ].
      * cbn [flat_defers_panic]. rewrite Hpan. apply upd_same.
  - inversion Hall as [| x l Hnd Hall' Heq]; subst. cbn [map] in Hdf.
    destruct Hp as [Hret | [v Hpan]].
    + (* prog = URet: ret_defer pops d (pa unchanged), then Phase A runs d, then IH over ds' *)
      destruct (cmd_to_ucmd_body_runs d ucap (upd p 0 (cmd_to_ucmd d)) b h lv tr o
                  (upd df 0 (map cmd_to_ucmd ds')) pa Hlv (upd_same _ _ _))
        as [p'' [df'' [Hus2 [Hprog2 Hdf2]]]].
      cbn [cmd_defers] in Hdf2. rewrite (cmd_defers_no_defer d Hnd) in Hdf2. cbn [map app] in Hdf2. rewrite upd_same in Hdf2.
      assert (Hdisj2 : p'' 0 = URet \/ exists v0, p'' 0 = UPan v0)
        by (rewrite Hprog2; destruct (cmd_panic d) as [vd|]; [ right; exists vd; reflexivity | left; reflexivity ]).
      destruct (IH ucap p'' b h lv tr (o ++ map (fun e => (0, e)) (cmd_out_events d)) df'' pa
                  Hall' Hlv Hdisj2 Hdf2) as [p' [lv' [df' [pa' [Hus3 [Hdone Hpanic]]]]]].
      exists p', lv', df', pa'. split; [ | split; [ exact Hdone | ] ].
      * replace (o ++ map (fun e => (0, e)) (concat (map cmd_out_events (d :: ds'))))
           with ((o ++ map (fun e => (0, e)) (cmd_out_events d)) ++ map (fun e => (0, e)) (concat (map cmd_out_events ds')))
          by (cbn [concat map]; rewrite map_app, <- app_assoc; reflexivity).
        eapply usteps_step; [ eapply ustep_ret_defer; [ exact Hlv | exact Hret | rewrite Hdf; reflexivity ] | ].
        eapply usteps_trans; [ exact Hus2 | exact Hus3 ].
      * rewrite Hpanic, Hret. cbn [flat_defers_panic]. rewrite Hprog2. destruct (cmd_panic d) as [vd|]; reflexivity.
    + (* prog = UPan v: pan_defer pops d RECORDING v into pa, then Phase A runs d, then IH over ds' *)
      destruct (cmd_to_ucmd_body_runs d ucap (upd p 0 (cmd_to_ucmd d)) b h lv tr o
                  (upd df 0 (map cmd_to_ucmd ds')) (upd pa 0 (Some v)) Hlv (upd_same _ _ _))
        as [p'' [df'' [Hus2 [Hprog2 Hdf2]]]].
      cbn [cmd_defers] in Hdf2. rewrite (cmd_defers_no_defer d Hnd) in Hdf2. cbn [map app] in Hdf2. rewrite upd_same in Hdf2.
      assert (Hdisj2 : p'' 0 = URet \/ exists v0, p'' 0 = UPan v0)
        by (rewrite Hprog2; destruct (cmd_panic d) as [vd|]; [ right; exists vd; reflexivity | left; reflexivity ]).
      destruct (IH ucap p'' b h lv tr (o ++ map (fun e => (0, e)) (cmd_out_events d)) df'' (upd pa 0 (Some v))
                  Hall' Hlv Hdisj2 Hdf2) as [p' [lv' [df' [pa' [Hus3 [Hdone Hpanic]]]]]].
      exists p', lv', df', pa'. split; [ | split; [ exact Hdone | ] ].
      * replace (o ++ map (fun e => (0, e)) (concat (map cmd_out_events (d :: ds'))))
           with ((o ++ map (fun e => (0, e)) (cmd_out_events d)) ++ map (fun e => (0, e)) (concat (map cmd_out_events ds')))
          by (cbn [concat map]; rewrite map_app, <- app_assoc; reflexivity).
        eapply usteps_step; [ eapply ustep_pan_defer; [ exact Hlv | exact Hpan | rewrite Hdf; reflexivity ] | ].
        eapply usteps_trans; [ exact Hus2 | exact Hus3 ].
      * rewrite Hpanic, Hpan. cbn [flat_defers_panic]. rewrite Hprog2, upd_same. destruct (cmd_panic d) as [vd|]; reflexivity.
Qed.

(** THIRD general defer theorem: for ANY [flat c], the single-goroutine [usteps] run AGREES with [run_cmd] —
    same shape as [bridge_one_defer_agrees]/[bridge_flat_np_agrees] but for the full flat class (any number of
    defers, any panicking).  Phase A runs the body (leaving [prog 0] per [cmd_panic c], defers stacked), then
    [unwind_flat] does the 2-mode unwind; [run_cmd] grounded by [run_cmd_flat].  SUBSUMES the two-panic witness. *)
Theorem bridge_flat_agrees : forall c ucap w,
  flat c = true ->
  exists (uc : UConfig) (oc : Outcome unit) (fuel : nat),
    usteps ucap (ustart (cmd_to_ucmd c)) uc
    /\ run_cmd fuel c w = Some oc
    /\ uc_live uc 0 = false
    /\ uc_panic uc 0 = ocpanic oc
    /\ w_output (oc_world oc) = w_output w ++ map snd (uc_out uc).
Proof.
  intros c ucap w Hf.
  destruct (run_cmd_flat c w Hf) as [w' [Hrun Hwout]].
  destruct (cmd_to_ucmd_body_runs c ucap
              (fun t => if Nat.eqb t 0 then cmd_to_ucmd c else URet)
              (fun _ => nil) (fun _ => 0) (fun t => Nat.eqb t 0) nil nil (fun _ => nil) (fun _ => None)
              eq_refl eq_refl) as [p' [df' [Hus1 [Hprog1 Hdf1]]]].
  cbn in Hdf1. rewrite app_nil_r in Hdf1.
  assert (Hdisj1 : p' 0 = URet \/ exists v, p' 0 = UPan v)
    by (rewrite Hprog1; destruct (cmd_panic c) as [vb|]; [ right; exists vb; reflexivity | left; reflexivity ]).
  destruct (unwind_flat (cmd_defers c) ucap p' (fun _ => nil) (fun _ => 0) (fun t => Nat.eqb t 0) nil
              (nil ++ map (fun e => (0, e)) (cmd_out_events c)) df' (fun _ => None)
              (flat_defers_nd c Hf) eq_refl Hdisj1 Hdf1) as [p'' [lv'' [df'' [pa'' [Hus2 [Hdone Hpanic]]]]]].
  set (P := flat_defers_panic (cmd_defers c) (cmd_panic c)).
  assert (Hpa2 : pa'' 0 = P) by (rewrite Hpanic, Hprog1; unfold P; destruct (cmd_panic c); reflexivity).
  eexists. exists (match P with Some v => OPanic v w' | None => ORet tt w' end). exists (S (length (cmd_defers c))).
  split; [ | split; [ exact Hrun | split; [ | split ] ] ].
  - unfold ustart. eapply usteps_trans; [ exact Hus1 | exact Hus2 ].
  - exact Hdone.
  - cbn [uc_panic]. rewrite Hpa2. destruct P as [v|]; reflexivity.
  - destruct P as [v|]; cbn [oc_world uc_out]; rewrite Hwout, !map_app; cbn [map app];
      rewrite !map_snd_pair0, app_assoc; reflexivity.
Qed.

(** Public assumption surfaces for this module — the manifest gate captures these [Print Assumptions]: the
    no_defer [run_cmd]-grounded bridge AND its three defer-bearing generalisations (ONE defer either-panics;
    MULTIPLE non-panicking defers; MULTIPLE flat defers with panics — the 2-mode).  The projection plumbing
    ([cmd_out_events]/[cmd_panic]/[cmd_defers]/[go_chars]/[run_cmd_one_defer]/[run_defers_np]/[run_defers_flat]/
    [unwind_np]/[unwind_flat]/Phase A) is Local and covered TRANSITIVELY through these cones, not separately
    printed. *)
Print Assumptions cmd_to_ucmd_run_agrees.
Print Assumptions bridge_one_defer_agrees.
Print Assumptions bridge_flat_np_agrees.
Print Assumptions bridge_flat_agrees.
