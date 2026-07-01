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

    The module exposes single-goroutine [usteps] AGREEMENT bridges (the [usteps] run AGREES with cmd.v's
    AUTHORITATIVE [run_cmd] — the unified output events EQUAL [run_cmd]'s appended [w_output], and [uc_panic 0]
    EQUALS the Outcome's panic) over two ORTHOGONAL defer classes: [flat c] (one level of [no_defer] defers, any
    panicking) and NESTED but panic-free ([cmd_no_panic c], arbitrary depth — UNCONDITIONAL, [run_cmd] completion
    discharged internally by [run_cmd_terminates]) — the full nested+panicking case is later.  Plus cmd.v-side properties for ANY [c] (nested
    included): [run_cmd] TERMINATES for enough fuel (unconditional), and — for a COMPLETING [run_cmd] — its
    output only APPENDS (never retracts) and a panic-free such run returns [ORet].  The EXACT gated public-surface set is the
    [Print Assumptions] block at the end of this file (the single in-file authority); this header does not
    re-enumerate it.
    There is NO public projection-observer theorem: the [cmd_out_events]/[cmd_panic]/[cmd_defers] projections,
    their [run_cmd] seal ([go_chars]), and the unified-side run lemmas are LOCAL (file-private) proof plumbing —
    no exported theorem concludes with them, so a consumer cannot prove bridge facts against a free observer
    instead of [run_cmd].  (The full nested+PANICKING agreement is a later slice; no concurrency/heap ops in this
    fragment, so [uc_bufs]/[uc_heap]/[uc_trace] are untouched.)
    Proof-only: emits no Go, adds no axiom. *)

From Fido Require Import preamble concurrency cmd unified.
From Stdlib Require Import List Lia.
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

(** A structural node-count of a command, and of a defer list — the termination measure for [run_defers] over a
    NESTED defer forest ([go d] peels the head into strictly-smaller sub-forests). *)
Local Fixpoint cmd_sz (c : Cmd unit) : nat :=
  match c with
  | CRet _ => 1 | COut _ _ c' => S (cmd_sz c') | CPan _ => 1 | CDfr d c' => S (cmd_sz d + cmd_sz c')
  end.
Local Fixpoint defers_sz (ds : list (Cmd unit)) : nat :=
  match ds with [] => 0 | d :: ds' => cmd_sz d + defers_sz ds' end.
Local Lemma defers_sz_app : forall l1 l2, defers_sz (l1 ++ l2) = defers_sz l1 + defers_sz l2.
Proof. induction l1 as [|d l1 IH]; intro l2; cbn [defers_sz app]; [ reflexivity | rewrite IH; lia ]. Qed.
(** A command's accumulated defer forest is strictly SMALLER than the command (its own body node is dropped). *)
Local Lemma cmd_defers_sz_lt : forall c, defers_sz (cmd_defers c) < cmd_sz c.
Proof.
  intros c. induction c as [a | bo xs c' IH | v | d c' IHc'] using Cmd_rect'; cbn [cmd_sz cmd_defers].
  - cbn; lia.
  - lia.
  - cbn; lia.
  - rewrite defers_sz_app. cbn [defers_sz]. lia.
Qed.

(** [flat c] — every deferred action is [no_defer] (a one-level defer list, no NESTED defers).  Feeds the
    multiple-flat-defer theorem [bridge_flat_agrees] below (panics allowed); a syntactic + public predicate,
    so that theorem's statement stays free of the Local [cmd_panic]. *)
Fixpoint flat (c : Cmd unit) : bool :=
  match c with
  | CRet _ => true | COut _ _ c' => flat c' | CPan _ => true | CDfr d c' => no_defer d && flat c'
  end.

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
    is NOT yet finished ([lv], [pa] untouched); the stack-UNWINDING ([run_defers]) is Phase B (done for ANY
    [flat c] — panics allowed — in [bridge_flat_agrees], and for NESTED [cmd_no_panic c] in [bridge_nested_np]
    via [unwind_prefix_np]; the nested+panicking case is later).  This
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

(** ---- The GENERAL defer theorem: MULTIPLE flat defers, PANICS ALLOWED (the (prog, pa) 2-mode) ----
    For ANY [flat c] (every deferred action [no_defer], but the
    body and defers MAY panic), the [usteps] run of [cmd_to_ucmd c] AGREES with [run_cmd].  The final panic is
    [flat_defers_panic (cmd_defers c) (cmd_panic c)] — the body's panic threaded through the defers, each
    panicking defer REPLACING the active one (Go's last-raised-wins; = cmd.v's [run_defers] semantics).  Under
    [ustep] this is the 2-mode unwind: a defer's panic rides in [prog] as [UPan v] until the NEXT pop moves it
    into [pa] ([ustep_pan_defer]), a later panic superseding it.  The invariant threaded by [unwind_flat] is
    [current = match prog 0 with UPan v => Some v | URet => pa 0]. *)

(** The active panic after running flat defers [ds] (in [go]-accumulation / run order, head first) seeded with
    [p0]: last panic wins (a returning defer keeps the active panic).  = the fold [run_defers] performs. *)
Local Fixpoint flat_defers_panic (ds : list (Cmd unit)) (p0 : option GoAny) : option GoAny :=
  match ds with
  | nil => p0
  | d :: ds' => flat_defers_panic ds' (match cmd_panic d with Some v => Some v | None => p0 end)
  end.
Local Lemma flat_defers_panic_none : forall ds p0, flat_defers_panic ds p0 = None -> p0 = None.
Proof.
  induction ds as [| d ds' IH]; intros p0 H; cbn in H; [ exact H | ].
  apply IH in H. destruct (cmd_panic d); [ discriminate H | exact H ].
Qed.
(** Under [flat] every deferred action [go] accumulates is [no_defer] — the defer list is one-level (no
    nesting), exactly what [run_defers_flat] / [unwind_flat] consume. *)
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

(** run_defers is OUTPUT-MONOTONE for ARBITRARY nesting: unwinding a defer list only ever APPENDS to the
    world's output trace (each deferred body's [cmd_out_events] and, recursively, its own nested defers'),
    never RETRACTS.  Grounded in [go_chars] (each [go d] appends [cmd_out_events d]); induction on FUEL, the IH
    applied to the nested run ([cmd_defers d]) and the tail ([ds']).  Note [oc_world acc'] = [oc_world net_d]
    (a returning defer keeps [acc]'s panic but takes the run's advanced world; a panicking one carries its
    own), so the world only grows across both sub-runs. *)
Local Lemma run_defers_out : forall fuel ds acc result,
  run_defers fuel ds acc = Some result ->
  exists evs, w_output (oc_world result) = w_output (oc_world acc) ++ evs.
Proof.
  induction fuel as [| n IH]; intros ds acc result H; [ discriminate H | ].
  destruct ds as [| d ds'].
  - cbn in H. injection H as <-. exists nil. rewrite app_nil_r. reflexivity.
  - rewrite run_defers_unfold in H.
    destruct (go_chars d (oc_world acc)) as [w_d [Hgo Hout]]. rewrite Hgo in H. cbn zeta in H.
    destruct (run_defers n (cmd_defers d)
                (match cmd_panic d with None => ORet tt w_d | Some v => OPanic v w_d end)) as [net_d|] eqn:Enet;
      [ | discriminate H ].
    destruct (IH (cmd_defers d)
                (match cmd_panic d with None => ORet tt w_d | Some v => OPanic v w_d end) net_d Enet) as [evs1 Hevs1].
    destruct (IH ds' (match net_d with OPanic v' w' => OPanic v' w' | ORet _ w' => oc_set_world acc w' end)
                result H) as [evs2 Hevs2].
    exists (cmd_out_events d ++ evs1 ++ evs2).
    assert (Hw1 : w_output (oc_world net_d) = w_output w_d ++ evs1)
      by (rewrite Hevs1; destruct (cmd_panic d); reflexivity).
    assert (Hw2 : w_output (oc_world result) = w_output (oc_world net_d) ++ evs2)
      by (rewrite Hevs2; destruct net_d as [[] w' | v' w']; cbn [oc_world]; [ rewrite oc_world_set_world | ]; reflexivity).
    rewrite Hw2, Hw1, Hout, <- !app_assoc. reflexivity.
Qed.

(** [cmd_no_panic] (cmd.v's panic-freedom predicate) implies the body has no in-flight panic — relates it to the
    Local [cmd_panic]; feeds the panic-free run properties below. *)
Local Lemma cmd_no_panic_cmd_panic : forall c, cmd_no_panic c = true -> cmd_panic c = None.
Proof.
  intros c. induction c as [a | bo xs c' IH | v | d c' IHc'] using Cmd_rect'; intros Hnp; cbn in *;
    [ reflexivity | exact (IH Hnp) | discriminate Hnp | apply andb_prop in Hnp; exact (IHc' (proj2 Hnp)) ].
Qed.

(** Under [cmd_no_panic] every deferred action [go] accumulates is itself [cmd_no_panic] (the defer forest is
    panic-free too). *)
Local Lemma cmd_no_panic_defers : forall c,
  cmd_no_panic c = true -> Forall (fun d => cmd_no_panic d = true) (cmd_defers c).
Proof.
  intros c. induction c as [a | bo xs c' IH | v | d c' IHc'] using Cmd_rect'; intros Hnp; cbn in *.
  - constructor.
  - exact (IH Hnp).
  - discriminate Hnp.
  - apply andb_prop in Hnp as [Hnpd Hnpc'].
    apply Forall_app; split; [ exact (IHc' Hnpc') | constructor; [ exact Hnpd | constructor ] ].
Qed.

(** run_defers PRESERVES panic-freedom for ARBITRARY nesting: over [cmd_no_panic] defers (each recursively),
    from a panic-free accumulator, the net outcome is panic-free.  Induction on FUEL: [go d] is [ORet]
    ([cmd_no_panic d ⇒ cmd_panic d = None]), the nested run stays panic-free (IH), so [acc'] keeps [acc]'s
    absent panic ([oc_set_world]). *)
Local Lemma run_defers_no_panic : forall fuel ds acc result,
  run_defers fuel ds acc = Some result ->
  Forall (fun d => cmd_no_panic d = true) ds ->
  ocpanic acc = None -> ocpanic result = None.
Proof.
  induction fuel as [| n IH]; intros ds acc result H Hall Hacc; [ discriminate H | ].
  destruct ds as [| d ds'].
  - cbn in H. injection H as <-. exact Hacc.
  - inversion Hall as [| x l Hnp Hall' Heq]; subst.
    rewrite run_defers_unfold in H.
    destruct (go_chars d (oc_world acc)) as [w_d [Hgo Hout]]. rewrite Hgo in H. cbn zeta in H.
    replace (match cmd_panic d with None => ORet tt w_d | Some v => OPanic v w_d end)
       with (ORet tt w_d) in H by (rewrite (cmd_no_panic_cmd_panic d Hnp); reflexivity).
    destruct (run_defers n (cmd_defers d) (ORet tt w_d)) as [net_d|] eqn:Enet; [ | discriminate H ].
    assert (Hnet : ocpanic net_d = None)
      by exact (IH (cmd_defers d) (ORet tt w_d) net_d Enet (cmd_no_panic_defers d Hnp) eq_refl).
    destruct net_d as [[] w' | v' w']; cbn [ocpanic] in Hnet; [ | discriminate Hnet ].
    exact (IH ds' (oc_set_world acc w') result H Hall' (eq_trans (ocpanic_set_world acc w') Hacc)).
Qed.

(** [run_defers] is MONOTONE in fuel: extra fuel never changes a successful result (it only guards against
    exhaustion).  Induction on the fuel [f]. *)
Local Lemma run_defers_mono : forall f ds acc r,
  run_defers f ds acc = Some r -> forall f', f <= f' -> run_defers f' ds acc = Some r.
Proof.
  induction f as [| n IH]; intros ds acc r H f' Hle; [ discriminate H | ].
  destruct f' as [| n']; [ inversion Hle | ]. apply le_S_n in Hle.
  destruct ds as [| d ds']; [ cbn in H |- *; exact H | ].
  rewrite run_defers_unfold in H. rewrite run_defers_unfold.
  destruct (go d (oc_world acc)) as [oc_d ds_d].
  destruct (run_defers n ds_d oc_d) as [net_d|] eqn:Enet; [ | discriminate H ].
  rewrite (IH ds_d oc_d net_d Enet n' Hle). exact (IH ds' _ r H n' Hle).
Qed.

(** [run_defers] TERMINATES for enough fuel, over ARBITRARY nesting: bounded strong induction on the defer
    forest's node-count [defers_sz] (each [go d] peels [d] into the strictly-smaller [cmd_defers d] + [ds']),
    lifting the two sub-results to a common fuel via [run_defers_mono].  No well-founded machinery — plain [nat]
    induction on the [defers_sz] bound.  The tail [ds']'s seed depends on the nested run's RESULT, so the two
    sub-runs are resolved to concrete [net_d]/[r] before choosing the common fuel. *)
Local Lemma run_defers_terminates : forall ds acc, exists f, run_defers f ds acc <> None.
Proof.
  assert (aux : forall n ds acc, defers_sz ds <= n -> exists f, run_defers f ds acc <> None).
  { induction n as [| n IH]; intros ds acc Hle.
    - destruct ds as [| d ds']; [ exists 1; cbn; discriminate | ].
      cbn [defers_sz] in Hle. pose proof (cmd_defers_sz_lt d). lia.
    - destruct ds as [| d ds']; [ exists 1; cbn; discriminate | ].
      cbn [defers_sz] in Hle. pose proof (cmd_defers_sz_lt d) as Hlt.
      destruct (go_chars d (oc_world acc)) as [w_d [Hgo _]].
      destruct (IH (cmd_defers d)
                  (match cmd_panic d with None => ORet tt w_d | Some v => OPanic v w_d end)) as [f1 H1]; [ lia | ].
      destruct (run_defers f1 (cmd_defers d)
                  (match cmd_panic d with None => ORet tt w_d | Some v => OPanic v w_d end)) as [net_d|] eqn:Enet;
        [ | exfalso; apply H1; reflexivity ].
      destruct (IH ds' (match net_d with OPanic v' w' => OPanic v' w' | ORet _ w' => oc_set_world acc w' end))
        as [f2 H2]; [ lia | ].
      destruct (run_defers f2 ds' (match net_d with OPanic v' w' => OPanic v' w' | ORet _ w' => oc_set_world acc w' end))
        as [r|] eqn:Erest; [ | exfalso; apply H2; reflexivity ].
      exists (S (Nat.max f1 f2)).
      assert (Hfull : run_defers (S (Nat.max f1 f2)) (d :: ds') acc = Some r).
      { rewrite run_defers_unfold, Hgo. cbn zeta.
        rewrite (run_defers_mono _ _ _ _ Enet (Nat.max f1 f2) ltac:(lia)). cbn match.
        exact (run_defers_mono _ _ _ _ Erest (Nat.max f1 f2) ltac:(lia)). }
      rewrite Hfull. discriminate. }
  intros ds acc. exact (aux (defers_sz ds) ds acc (le_n _)).
Qed.

(** [run_cmd] TERMINATES for enough fuel, for ANY [c] (nested defers included): the body ([go]) plus the defer
    forest ([run_defers_terminates]).  A cmd.v-side property CONSUMED by [bridge_nested_np] below to discharge its
    [run_cmd]-completion obligation (making that bridge UNCONDITIONAL). *)
Theorem run_cmd_terminates : forall (c : Cmd unit) w, exists fuel oc, run_cmd fuel c w = Some oc.
Proof.
  intros c w. destruct (go_chars c w) as [w_body [Hgo _]].
  destruct (run_defers_terminates (cmd_defers c) (oc_unit (fst (go c w)))) as [fuel Hrd].
  destruct (run_defers fuel (cmd_defers c) (oc_unit (fst (go c w)))) as [result|] eqn:Erd;
    [ | exfalso; apply Hrd; reflexivity ].
  exists fuel.
  unfold run_cmd. rewrite Hgo. cbn [fst] in Erd. rewrite Hgo in Erd. cbn [fst] in Erd. cbn zeta. rewrite Erd.
  destruct result as [[] w' | v w']; eexists; reflexivity.
Qed.

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

(** ustep-side for NESTED non-panicking defers (arbitrary depth): given [run_defers fuel ds acc = Some result]
    over [cmd_no_panic] defers from a panic-free [acc], the ustep unwinds the FRONT [ds] of the stack
    [map ds ++ map ds_tail] down to [map ds_tail], keeping [prog 0 = URet] / [pa 0 = None] and advancing the
    output by EXACTLY [run_defers]'s world delta [evs].  Induction on FUEL, the [ds_tail] parameter carrying the
    not-yet-run frames: at a [cons], pop [d] ([ustep_ret_defer]), run its body ([cmd_to_ucmd_body_runs] pushes
    [cmd_defers d]), then the IH runs [d]'s nested defers (tail [ds' ++ ds_tail]) and the rest (tail [ds_tail]).
    NO (prog, pa) 2-mode: panic-freedom keeps [prog = URet], every pop is [ret_defer], never touching [pa]. *)
Local Lemma unwind_prefix_np : forall fuel ds acc result,
  run_defers fuel ds acc = Some result ->
  Forall (fun d => cmd_no_panic d = true) ds -> ocpanic acc = None ->
  forall ucap p b h lv tr o df pa ds_tail,
    lv 0 = true -> p 0 = URet -> pa 0 = None ->
    df 0 = map cmd_to_ucmd ds ++ map cmd_to_ucmd ds_tail ->
    exists (p' : nat -> UCmd) (df' : nat -> list UCmd) evs,
      usteps ucap (mkUCfg p b h lv tr o df pa)
                  (mkUCfg p' b h lv tr (o ++ map (fun e => (0, e)) evs) df' pa)
      /\ p' 0 = URet /\ df' 0 = map cmd_to_ucmd ds_tail
      /\ w_output (oc_world result) = w_output (oc_world acc) ++ evs.
Proof.
  induction fuel as [| n IH]; intros ds acc result H Hall Hacc ucap p b h lv tr o df pa ds_tail Hlv Hp Hpa Hdf;
    [ discriminate H | ].
  destruct ds as [| d ds'].
  - cbn in H. injection H as <-. exists p, df, nil.
    cbn [map] in Hdf. rewrite !app_nil_r.
    split; [ apply usteps_refl | split; [ exact Hp | split; [ exact Hdf | reflexivity ] ] ].
  - inversion Hall as [| x l Hnp Hall' Heq]; subst.
    rewrite run_defers_unfold in H.
    destruct (go_chars d (oc_world acc)) as [w_d [Hgo Hout]]. rewrite Hgo in H. cbn zeta in H.
    replace (match cmd_panic d with None => ORet tt w_d | Some v => OPanic v w_d end)
       with (ORet tt w_d) in H by (rewrite (cmd_no_panic_cmd_panic d Hnp); reflexivity).
    destruct (run_defers n (cmd_defers d) (ORet tt w_d)) as [net_d|] eqn:Enet; [ | discriminate H ].
    assert (Hnet : ocpanic net_d = None)
      by exact (run_defers_no_panic n (cmd_defers d) (ORet tt w_d) net_d Enet (cmd_no_panic_defers d Hnp) eq_refl).
    destruct net_d as [[] w_net | v' w_net]; cbn [ocpanic] in Hnet; [ | discriminate Hnet ].
    cbn [map] in Hdf.
    (* Phase A on d (pops via ret_defer first), pushing cmd_defers d onto the front of the residual stack *)
    destruct (cmd_to_ucmd_body_runs d ucap (upd p 0 (cmd_to_ucmd d)) b h lv tr o
                (upd df 0 (map cmd_to_ucmd ds' ++ map cmd_to_ucmd ds_tail)) pa Hlv (upd_same _ _ _))
      as [pA [dfA [HusA [HprogA HdfA]]]].
    rewrite (cmd_no_panic_cmd_panic d Hnp) in HprogA. cbn in HprogA.
    rewrite upd_same in HdfA.
    (* IH 1: run d's nested defers, tail = ds' ++ ds_tail *)
    assert (HdfA' : dfA 0 = map cmd_to_ucmd (cmd_defers d) ++ map cmd_to_ucmd (ds' ++ ds_tail))
      by (rewrite HdfA, map_app; reflexivity).
    destruct (IH (cmd_defers d) (ORet tt w_d) (ORet tt w_net) Enet (cmd_no_panic_defers d Hnp) eq_refl
                ucap pA b h lv tr (o ++ map (fun e => (0, e)) (cmd_out_events d)) dfA pa (ds' ++ ds_tail)
                Hlv HprogA Hpa HdfA')
      as [pB [dfB [evs1 [HusB [HprogB [HdfB Hw1]]]]]].
    (* IH 2: run the rest ds', tail = ds_tail *)
    assert (HdfB' : dfB 0 = map cmd_to_ucmd ds' ++ map cmd_to_ucmd ds_tail)
      by (rewrite HdfB, map_app; reflexivity).
    destruct (IH ds' (oc_set_world acc w_net) result H Hall'
                (eq_trans (ocpanic_set_world acc w_net) Hacc)
                ucap pB b h lv tr ((o ++ map (fun e => (0, e)) (cmd_out_events d)) ++ map (fun e => (0, e)) evs1)
                dfB pa ds_tail Hlv HprogB Hpa HdfB')
      as [pC [dfC [evs2 [HusC [HprogC [HdfC Hw2]]]]]].
    exists pC, dfC, (cmd_out_events d ++ evs1 ++ evs2).
    split; [ | split; [ exact HprogC | split; [ exact HdfC | ] ] ].
    + replace (o ++ map (fun e => (0, e)) (cmd_out_events d ++ evs1 ++ evs2))
         with (((o ++ map (fun e => (0, e)) (cmd_out_events d)) ++ map (fun e => (0, e)) evs1)
                 ++ map (fun e => (0, e)) evs2)
        by (rewrite !map_app, !app_assoc; reflexivity).
      eapply usteps_step; [ eapply ustep_ret_defer; [ exact Hlv | exact Hp | rewrite Hdf; reflexivity ] | ].
      eapply usteps_trans; [ exact HusA | ]. eapply usteps_trans; [ exact HusB | exact HusC ].
    + rewrite Hw2. cbn [oc_world] in Hw1 |- *. rewrite oc_world_set_world.
      rewrite Hw1, Hout, <- !app_assoc. reflexivity.
Qed.

(** The GENERAL defer theorem: for ANY [flat c], the single-goroutine [usteps] run AGREES with [run_cmd] — same
    shape as [cmd_to_ucmd_run_agrees] but for the full flat class (any number of [no_defer] defers, panicking or
    not).  Phase A runs the body (leaving [prog 0] per [cmd_panic c], defers stacked), then [unwind_flat] does the
    2-mode unwind; [run_cmd] grounded by [run_cmd_flat]. *)
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

(** LOCAL helper for the NESTED non-panicking bridge: GIVEN a completing [run_cmd fuel c w = Some oc] (supplied
    by [run_cmd_terminates] in the public theorem below), the [usteps] run AGREES with it — finishes
    ([uc_live 0 = false]), panic EQUALS the Outcome's ([uc_panic 0 = ocpanic oc], = [None] as [c] is panic-free),
    output EQUALS [run_cmd]'s appended [w_output].  Phase A runs the body (pushing [cmd_defers c]),
    [unwind_prefix_np] does the nested unwind (tail []), a final [ret_done] closes goroutine 0. *)
Local Lemma bridge_nested_np_complete : forall fuel (c : Cmd unit) ucap w oc,
  run_cmd fuel c w = Some oc -> cmd_no_panic c = true ->
  exists uc : UConfig,
    usteps ucap (ustart (cmd_to_ucmd c)) uc
    /\ uc_live uc 0 = false
    /\ uc_panic uc 0 = ocpanic oc
    /\ w_output (oc_world oc) = w_output w ++ map snd (uc_out uc).
Proof.
  intros fuel c ucap w oc H Hnp.
  destruct (go_chars c w) as [w_body [Hgo Hout]].
  unfold run_cmd in H. rewrite Hgo in H. rewrite (cmd_no_panic_cmd_panic c Hnp) in H. cbn [oc_unit] in H.
  destruct (run_defers fuel (cmd_defers c) (ORet tt w_body)) as [result|] eqn:Erd; [ | discriminate H ].
  assert (Hresnp : ocpanic result = None)
    by exact (run_defers_no_panic fuel (cmd_defers c) (ORet tt w_body) result Erd (cmd_no_panic_defers c Hnp) eq_refl).
  destruct result as [[] w_r | v w_r]; cbn [ocpanic] in Hresnp; [ | discriminate Hresnp ].
  cbn in H. injection H as <-.
  destruct (cmd_to_ucmd_body_runs c ucap
              (fun t => if Nat.eqb t 0 then cmd_to_ucmd c else URet)
              (fun _ => nil) (fun _ => 0) (fun t => Nat.eqb t 0) nil nil (fun _ => nil) (fun _ => None)
              eq_refl eq_refl) as [p' [df' [Hus1 [Hprog1 Hdf1]]]].
  rewrite (cmd_no_panic_cmd_panic c Hnp) in Hprog1. cbn in Hprog1.
  cbn in Hdf1. rewrite app_nil_r in Hdf1.
  assert (Hdf1' : df' 0 = map cmd_to_ucmd (cmd_defers c) ++ map cmd_to_ucmd nil)
    by (rewrite Hdf1; cbn [map]; rewrite app_nil_r; reflexivity).
  destruct (unwind_prefix_np fuel (cmd_defers c) (ORet tt w_body) (ORet tt w_r) Erd
              (cmd_no_panic_defers c Hnp) eq_refl ucap p' (fun _ => nil) (fun _ => 0) (fun t => Nat.eqb t 0) nil
              (nil ++ map (fun e => (0, e)) (cmd_out_events c)) df' (fun _ => None) nil
              eq_refl Hprog1 eq_refl Hdf1')
    as [p'' [df'' [evs [Hus2 [Hprog2 [Hdf2 Hw]]]]]].
  cbn [map] in Hdf2.
  eexists. split; [ | split; [ | split ] ].
  - unfold ustart. eapply usteps_trans; [ exact Hus1 | ].
    eapply usteps_trans; [ exact Hus2 | ].
    eapply usteps_step; [ eapply ustep_ret_done with (tid := 0); [ reflexivity | exact Hprog2 | exact Hdf2 ] | apply usteps_refl ].
  - cbn [uc_live]. apply upd_same.
  - cbn [uc_panic ocpanic]. reflexivity.
  - cbn [oc_world uc_out] in Hw |- *. rewrite Hw, Hout, !map_app. cbn [map app].
    rewrite !map_snd_pair0, app_assoc. reflexivity.
Qed.

(** The NESTED (arbitrary-depth) non-panicking defer bridge — UNCONDITIONAL, the first coverage PAST [flat]'s one
    level.  For ANY [cmd_no_panic c] (no completion premise — [run_cmd_terminates] discharges it), the
    single-goroutine [usteps] run AGREES with cmd.v's [run_cmd] for some sufficient [fuel]/[oc]: finishes, panic
    EQUALS the Outcome's, output EQUALS [run_cmd]'s appended [w_output] — the SAME agreement surface as
    [bridge_flat_agrees].  Composes [run_cmd_terminates] (some [fuel] completes) with the [bridge_nested_np_complete]
    helper.  Orthogonal to [bridge_flat_agrees] (panics but one level); the FULL nested+panicking theorem needs the
    2-level (prog, pa) panic invariant. *)
Theorem bridge_nested_np : forall (c : Cmd unit) ucap w,
  cmd_no_panic c = true ->
  exists (uc : UConfig) (oc : Outcome unit) (fuel : nat),
    usteps ucap (ustart (cmd_to_ucmd c)) uc
    /\ run_cmd fuel c w = Some oc
    /\ uc_live uc 0 = false
    /\ uc_panic uc 0 = ocpanic oc
    /\ w_output (oc_world oc) = w_output w ++ map snd (uc_out uc).
Proof.
  intros c ucap w Hnp.
  destruct (run_cmd_terminates c w) as [fuel [oc Hrun]].
  destruct (bridge_nested_np_complete fuel c ucap w oc Hrun Hnp) as [uc [Hus [Hlv [Hpan Hout]]]].
  exists uc, oc, fuel.
  split; [ exact Hus | split; [ exact Hrun | split; [ exact Hlv | split; [ exact Hpan | exact Hout ] ] ] ].
Qed.

(** OUTPUT-MONOTONICITY of [run_cmd], for ANY [c] (nested defers included — NOT restricted to [flat]): a
    COMPLETING run ([run_cmd fuel c w = Some oc]) only ever APPENDS to the world's output (the body's
    [cmd_out_events c] then, via [run_defers_out], every defer's, recursively), never RETRACTS.  A cmd.v-side
    faithfulness guarantee — Go's deferred actions and
    panics cannot un-print already-printed output.  A standalone cmd.v-side property (distinct from the ustep
    AGREEMENT bridges), via [run_defers_out].  The nested-defer bridge [bridge_nested_np] (for [cmd_no_panic c])
    establishes its output agreement independently through [unwind_prefix_np], so this theorem is a sibling, not a
    dependency, of the bridge. *)
Theorem run_cmd_out_monotone : forall fuel (c : Cmd unit) w oc,
  run_cmd fuel c w = Some oc ->
  exists evs, w_output (oc_world oc) = w_output w ++ evs.
Proof.
  intros fuel c w oc H.
  destruct (go_chars c w) as [w_body [Hgo Hout]].
  unfold run_cmd in H. rewrite Hgo in H. cbn zeta in H.
  destruct (run_defers fuel (cmd_defers c)
              (oc_unit (match cmd_panic c with None => ORet tt w_body | Some v => OPanic v w_body end))) as [result|] eqn:Erd;
    [ | discriminate H ].
  destruct (run_defers_out fuel (cmd_defers c) _ result Erd) as [evs Hevs].
  assert (Hseed : oc_world (oc_unit (match cmd_panic c with None => ORet tt w_body | Some v => OPanic v w_body end)) = w_body)
    by (destruct (cmd_panic c); reflexivity).
  rewrite Hseed in Hevs.
  exists (cmd_out_events c ++ evs).
  destruct result as [[] w' | v w']; cbn [oc_world] in Hevs; cbn in H; injection H as <-.
  - rewrite oc_world_set_world, Hevs, Hout, <- app_assoc. reflexivity.
  - cbn [oc_world]. rewrite Hevs, Hout, <- app_assoc. reflexivity.
Qed.

(** PANIC-FREEDOM of [run_cmd] for ANY [c] (nested defers included): a [cmd_no_panic c] run that COMPLETES
    returns [ORet] — Go's panic-free program cannot end in a panic.  Via [go_chars] (the body is [ORet], as
    [cmd_no_panic c ⇒ cmd_panic c = None]) + [run_defers_no_panic] (the defers preserve it).  A standalone
    cmd.v-side property, panic-free companion to [run_cmd_out_monotone]; the bridge [bridge_nested_np] proves the
    SAME [cmd_no_panic] fragment agrees with [ustep] (unconditionally), resting on the shared [run_defers_no_panic]
    (not on this theorem). *)
Theorem run_cmd_no_panic_ret : forall fuel (c : Cmd unit) w oc,
  run_cmd fuel c w = Some oc -> cmd_no_panic c = true ->
  exists w', oc = ORet tt w'.
Proof.
  intros fuel c w oc H Hnp.
  destruct (go_chars c w) as [w_body [Hgo Hout]].
  unfold run_cmd in H. rewrite Hgo in H. rewrite (cmd_no_panic_cmd_panic c Hnp) in H. cbn [oc_unit] in H.
  destruct (run_defers fuel (cmd_defers c) (ORet tt w_body)) as [result|] eqn:Erd; [ | discriminate H ].
  assert (Hres : ocpanic result = None)
    by exact (run_defers_no_panic fuel (cmd_defers c) (ORet tt w_body) result Erd (cmd_no_panic_defers c Hnp) eq_refl).
  destruct result as [[] w' | v w']; cbn [ocpanic] in Hres; [ | discriminate Hres ].
  cbn in H. injection H as <-. exists w'. reflexivity.
Qed.

(** The EXACT gated public-surface set for this module is the [Print Assumptions] lines below — the single
    in-file authority (the Docker manifest gate scrapes their [Axioms:] report, which must be empty).  Every
    OTHER definition here (the [cmd_out_events]/[cmd_panic]/[cmd_defers] projections, their [run_cmd] seal
    [go_chars], the [run_defers]/unwind plumbing, Phase A) is Local and covered TRANSITIVELY through these
    cones, not separately printed. *)
Print Assumptions cmd_to_ucmd_run_agrees.
Print Assumptions bridge_flat_agrees.
Print Assumptions bridge_nested_np.
Print Assumptions run_cmd_out_monotone.
Print Assumptions run_cmd_no_panic_ret.
Print Assumptions run_cmd_terminates.
