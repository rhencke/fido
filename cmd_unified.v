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
    and [bridge_flat_np_agrees] (MULTIPLE flat defers, fully NON-PANICKING — [flat c] + [no_panic c]).  For all,
    the single-goroutine [usteps] run AGREES with cmd.v's AUTHORITATIVE [run_cmd] — the unified output events
    EQUAL [run_cmd]'s appended [w_output], and [uc_panic 0] EQUALS the Outcome's panic.
    There is NO public projection-observer theorem: the [cmd_out_events]/[cmd_panic]/[cmd_defers] projections,
    their [run_cmd] seal ([go_chars]), and the unified-side run lemmas are LOCAL (file-private) proof plumbing —
    no exported theorem concludes with them, so a consumer cannot prove bridge facts against a free observer
    instead of [run_cmd].  (MULTIPLE PANICKING or NESTED defers are a later slice: cmd.v runs deferred actions at
    return via [run_defers], unified.v via the [UDfr] LIFO stack.  No concurrency/heap ops in this fragment, so
    [uc_bufs]/[uc_heap]/[uc_trace] are untouched.)  Proof-only: emits no Go, adds no axiom. *)

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

(** [no_panic c] — [c] has NO [CPan] ANYWHERE (body OR any deferred action): it can never panic.  Public
    (syntactic, like [no_defer]).  [flat c] — every deferred action is [no_defer] (a one-level defer list).
    Both feed the fully-non-panicking multiple-defer theorem below; being syntactic + public, they let its
    statement avoid the Local [cmd_panic]. *)
Fixpoint no_panic (c : Cmd unit) : bool :=
  match c with
  | CRet _ => true | COut _ _ c' => no_panic c' | CPan _ => false | CDfr d c' => no_panic d && no_panic c'
  end.
Fixpoint flat (c : Cmd unit) : bool :=
  match c with
  | CRet _ => true | COut _ _ c' => flat c' | CPan _ => true | CDfr d c' => no_defer d && flat c'
  end.
Local Lemma no_panic_cmd_panic : forall c, no_panic c = true -> cmd_panic c = None.
Proof.
  intros c. induction c as [a | bo xs c' IH | v | d c' IHc'] using Cmd_rect'; intros Hnp; cbn in *;
    [ reflexivity | exact (IH Hnp) | discriminate Hnp
    | apply andb_prop in Hnp; exact (IHc' (proj2 Hnp)) ].
Qed.
(** Under [flat] + [no_panic], every deferred action [go] accumulates is BOTH [no_defer] and [no_panic]. *)
Local Lemma flat_np_defers : forall c, flat c = true -> no_panic c = true ->
  Forall (fun d => no_defer d = true /\ no_panic d = true) (cmd_defers c).
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

(** ---- DEFER bridge — CONCRETE witnesses for the NOT-YET-GENERAL cases ----
    [cmd_to_ucmd_run_agrees] handles [no_defer]; [bridge_one_defer_agrees] (proved below) handles ANY ONE defer
    ([CDfr d c'] with [d]/[c'] [no_defer], EITHER may panic — covering [ustep_ret_defer]/[ustep_pan_defer]/
    [ustep_ret_done]/[ustep_pan_done] and panic-replacement generally in its four leaves).  So the earlier
    single-defer demos (return / panic-propagation / panic-replacement) are now SUBSUMED by that theorem and were
    removed.  These TWO file-private EXAMPLES pin the behaviours the general theorem does NOT yet cover — MORE
    THAN ONE deferred action runs (whether NESTED or SIBLING); each pins that the [CDfr -> UDfr] translation RUNS
    correctly under [ustep] and AGREES with cmd.v's authoritative [run_cmd]:
      NESTING ([defer (defer println(a))]): a deferred action that ITSELF defers — [ustep_defer] fires AGAIN
              DURING the unwinding (the stack never exceeds ONE entry, but a second defer is registered
              mid-unwind), the inner defer running before the goroutine finishes (output [a]).
      SIBLING LIFO ([defer println(a); defer println(b); return]): TWO defers pushed by the body ([ustep_defer]
              twice BEFORE it returns, so the stack reaches DEPTH 2), popped LIFO — [b] deferred LAST runs FIRST,
              output [[b]; [a]] (two [ustep_ret_defer] pops in stack order, NO defer-during-unwind).
    Multiple NON-panicking flat defers are done ([bridge_flat_np_agrees]); multiple PANICKING (the 2-mode
    invariant) or NESTED defers are the next Phase-B slice. *)
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

(** SIBLING LIFO witness ([defer println(a); defer println(b); return]).  [b] is deferred
    LAST so it runs FIRST: the output is [[b]; [a]], NOT [[a]; [b]].  Exercises [ustep_ret_defer] TWICE, popping
    the [uc_defers] stack in the order [ustep_defer] built it — the LIFO discipline Phase B's list-unwinding
    must reproduce.  Agrees with cmd.v's [run_cmd] (whose [run_defers] runs the accumulated list head-first). *)
Local Example bridge_defer_lifo_agrees : forall (a : GoAny) (b : GoAny) (ucap : nat -> option nat) w,
  exists uc oc,
    usteps ucap (ustart (cmd_to_ucmd (CDfr (COut true (a :: nil) (CRet tt)) (CDfr (COut true (b :: nil) (CRet tt)) (CRet tt))))) uc
    /\ run_cmd 5 (CDfr (COut true (a :: nil) (CRet tt)) (CDfr (COut true (b :: nil) (CRet tt)) (CRet tt))) w = Some oc
    /\ uc_live uc 0 = false
    /\ w_output (oc_world oc) = w_output w ++ map snd (uc_out uc)
    /\ uc_panic uc 0 = ocpanic oc.
Proof.
  intros a b ucap w. eexists. exists (ORet tt (w_log true (a :: nil) (w_log true (b :: nil) w))).
  split.
  { eapply usteps_step. { eapply ustep_defer     with (tid := 0); rewrite ?upd_same; cbn; reflexivity. }
    eapply usteps_step. { eapply ustep_defer     with (tid := 0); rewrite ?upd_same; cbn; reflexivity. }
    eapply usteps_step. { eapply ustep_ret_defer with (tid := 0); rewrite ?upd_same; cbn; reflexivity. }
    eapply usteps_step. { eapply ustep_out        with (tid := 0); rewrite ?upd_same; cbn; reflexivity. }
    eapply usteps_step. { eapply ustep_ret_defer with (tid := 0); rewrite ?upd_same; cbn; reflexivity. }
    eapply usteps_step. { eapply ustep_out        with (tid := 0); rewrite ?upd_same; cbn; reflexivity. }
    eapply usteps_step. { eapply ustep_ret_done   with (tid := 0); rewrite ?upd_same; cbn; reflexivity. }
    apply usteps_refl. }
  split. { vm_compute. reflexivity. }
  split. { reflexivity. }
  split. { cbn. rewrite <- app_assoc. reflexivity. } { reflexivity. }
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
    For [flat c] (every deferred action [no_defer]) AND [no_panic c] (no [CPan] anywhere), the [usteps] run of
    [cmd_to_ucmd c] AGREES with cmd.v's [run_cmd].  This is the common cleanup pattern ([defer f(); defer g();
    body], nothing panics) — ANY NUMBER of defers, but no panic, so the unwind is pure [ustep_ret_defer] pops
    ending in [ustep_ret_done] (the panic-in-flight 2-mode invariant is NOT needed).  [bridge_one_defer_agrees]
    (above) is the ORTHOGONAL axis: exactly one defer but EITHER side may panic. *)

(** cmd.v-side: [run_defers] over a list of [no_defer]+[no_panic] actions from an [ORet] just runs each in
    order, threading the world — no panic, no nesting.  Fuel [S (length ds)] suffices (one level per defer). *)
Local Lemma run_defers_np : forall ds w0,
  Forall (fun d => no_defer d = true /\ no_panic d = true) ds ->
  exists w', run_defers (S (length ds)) ds (ORet tt w0) = Some (ORet tt w')
    /\ w_output w' = w_output w0 ++ concat (map cmd_out_events ds).
Proof.
  induction ds as [| d ds' IH]; intros w0 Hall.
  - exists w0. cbn [run_defers concat map]. rewrite app_nil_r. split; reflexivity.
  - inversion Hall as [| x l [Hnd Hnp] Hall' Heq]; subst.
    destruct (go_chars d w0) as [w_d [Hgo Hout]].
    rewrite (no_panic_cmd_panic d Hnp), (cmd_defers_no_defer d Hnd) in Hgo.
    destruct (IH w_d Hall') as [w' [Hrun Houtf]].
    exists w'. split.
    + cbn [run_defers length]. cbn [oc_world]. rewrite Hgo. cbn [run_defers oc_set_world]. exact Hrun.
    + rewrite Houtf, Hout. cbn [concat map]. rewrite <- app_assoc. reflexivity.
Qed.

(** ustep-side: from [prog 0 = URet], [pa 0 = None], [df 0 = map cmd_to_ucmd ds] (all [no_defer]+[no_panic]),
    the run pops each defer via [ustep_ret_defer] + runs it (Phase A, [no_panic] ⇒ back to [URet]) and finishes
    with [ustep_ret_done]; [pa] stays [None] throughout (nothing panics). *)
Local Lemma unwind_np : forall ds ucap p b h lv tr o df pa,
  Forall (fun d => no_defer d = true /\ no_panic d = true) ds ->
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
    rewrite (no_panic_cmd_panic d Hnp) in Hprog2.
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

(** cmd.v authority for the theorem: [run_cmd] of a [flat]+[no_panic] [c] reaches [ORet], world advanced by the
    body's output THEN every defer's (in [go]-accumulation order).  From [go_chars] + [run_defers_np]. *)
Local Lemma run_cmd_flat_np : forall c w,
  flat c = true -> no_panic c = true ->
  exists w', run_cmd (S (length (cmd_defers c))) c w = Some (ORet tt w')
    /\ w_output w' = w_output w ++ cmd_out_events c ++ concat (map cmd_out_events (cmd_defers c)).
Proof.
  intros c w Hf Hnp.
  destruct (go_chars c w) as [w_body [Hgo Hout]].
  rewrite (no_panic_cmd_panic c Hnp) in Hgo.
  destruct (run_defers_np (cmd_defers c) w_body (flat_np_defers c Hf Hnp)) as [w' [Hrun Houtf]].
  exists w'. split.
  - unfold run_cmd. rewrite Hgo. cbn [oc_unit]. rewrite Hrun. cbn [oc_set_world]. reflexivity.
  - rewrite Houtf, Hout. rewrite <- app_assoc. reflexivity.
Qed.

Theorem bridge_flat_np_agrees : forall c ucap w,
  flat c = true -> no_panic c = true ->
  exists (uc : UConfig) (w' : World),
    usteps ucap (ustart (cmd_to_ucmd c)) uc
    /\ run_cmd (S (length (cmd_defers c))) c w = Some (ORet tt w')   (* cmd.v's AUTHORITATIVE run — grounds w' *)
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
  rewrite (no_panic_cmd_panic c Hnp) in Hprog1. cbn in Hprog1.
  cbn in Hdf1. rewrite app_nil_r in Hdf1.
  destruct (unwind_np (cmd_defers c) ucap p' (fun _ => nil) (fun _ => 0) (fun t => Nat.eqb t 0) nil
              (nil ++ map (fun e => (0, e)) (cmd_out_events c)) df' (fun _ => None)
              (flat_np_defers c Hf Hnp) eq_refl Hprog1 Hdf1 eq_refl) as [p'' [lv'' [df'' [Hus2 Hdone]]]].
  eexists. exists w'. split; [ | split; [ exact Hrun | split ] ].
  - unfold ustart. eapply usteps_trans; [ exact Hus1 | exact Hus2 ].
  - exact Hdone.
  - split.
    + cbn [uc_panic]. reflexivity.
    + cbn [oc_world uc_out]. rewrite Hwout. rewrite !map_app. cbn [map app]. rewrite !map_snd_pair0.
      rewrite app_assoc. reflexivity.
Qed.

(** Public assumption surfaces for this module — the manifest gate captures these [Print Assumptions]: the
    no_defer [run_cmd]-grounded bridge AND its two defer-bearing generalisations (ONE defer either-panics;
    MULTIPLE non-panicking defers).  The projection plumbing ([cmd_out_events]/[cmd_panic]/[cmd_defers]/
    [go_chars]/[run_cmd_one_defer]/[run_defers_np]/[unwind_np]/Phase A) is Local and covered TRANSITIVELY
    through these cones, not separately printed. *)
Print Assumptions cmd_to_ucmd_run_agrees.
Print Assumptions bridge_one_defer_agrees.
Print Assumptions bridge_flat_np_agrees.
