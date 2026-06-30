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

    PUBLIC surface = [cmd_to_ucmd_run_agrees]: for a DEFER-FREE [c] ([cmd.no_defer], the fragment GoSem slice 1
    denotes), the single-goroutine [usteps] run AGREES with cmd.v's AUTHORITATIVE [run_cmd 1 c w] — the unified
    output events EQUAL [run_cmd]'s appended [w_output], and [uc_panic 0] EQUALS the Outcome's panic.  There is
    NO public projection-observer theorem: the [cmd_out_events]/[cmd_panic] projections, their [run_cmd] seal,
    and the unified-side run lemma are LOCAL (file-private) proof plumbing — no exported theorem concludes with
    them, so a consumer cannot prove bridge facts against a free observer instead of [run_cmd].  (Defer is
    excluded: cmd.v runs deferred actions at return via [run_defers], unified.v via the [UDfr] LIFO stack —
    a later slice.  No concurrency/heap ops in this fragment, so [uc_bufs]/[uc_heap]/[uc_trace] are untouched.)
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
    is NOT yet finished ([lv], [pa] untouched); the stack-UNWINDING ([run_defers]) is the (future) Phase B.  This
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

(** ---- DEFER bridge — first CONCRETE slice (the general [no_defer]-free theorem is future work) ----
    [cmd_to_ucmd_run_agrees] is restricted to [no_defer c].  These FIVE file-private EXAMPLES show the SAME
    agreement shape holds for CONCRETE DEFERRED programs, and TOGETHER exercise every [ustep] defer rule a
    general theorem must drive: [ustep_defer] (push the LIFO stack; ALL five), [ustep_ret_defer] (pop + run at
    return; demos 1, 4, 5), [ustep_pan_defer] (pop + run mid-panic; demos 2, 3), [ustep_ret_done] (demos 1, 2, 4,
    5), and [ustep_pan_done] (panic with an EMPTY defer stack; demo 3) — PLUS the nested-defer INTERLEAVING
    (demo 4) and the sibling-defer LIFO ORDER (demo 5), the structurally-new behaviours Phase B's stack-unwinding
    must generalise.  They are CONCRETE WITNESSES, NOT a general defer theorem — each pins that the
    [CDfr -> UDfr] translation RUNS correctly under [ustep] and AGREES with cmd.v's authoritative [run_cmd]
    (same shape as the public theorem) for that program.
      Demo 1 ([defer println(a); return]):  the defer RUNS at return (output [a], no panic).
      Demo 2 ([defer println(a); panic v]): the defer STILL runs (output [a]) while the panic propagates
              ([uc_panic 0 = Some v]) — the review-P0 "remaining defers run during unwinding" discipline.
      Demo 3 ([defer panic v2; panic v1]):  the deferred PANIC runs with the stack now empty -> [ustep_pan_done],
              and v2 REPLACES the active v1 ([uc_panic 0 = Some v2]) — faithful panic-replacement across the bridge.
      Demo 4 ([defer (defer println(a))]):  a deferred action that ITSELF defers — [ustep_defer] fires AGAIN
              DURING the unwinding (NESTING), the inner defer running before the goroutine finishes (output [a]).
      Demo 5 ([defer println(a); defer println(b); return]): SIBLING defers run LIFO — [b] deferred LAST runs
              FIRST, so the output is [[b]; [a]] (two [ustep_ret_defer] pops in stack order). *)
Local Example bridge_defer_return_agrees : forall (a : GoAny) (ucap : nat -> option nat) w,
  exists uc oc,
    usteps ucap (ustart (cmd_to_ucmd (CDfr (COut true (a :: nil) (CRet tt)) (CRet tt)))) uc
    /\ run_cmd 5 (CDfr (COut true (a :: nil) (CRet tt)) (CRet tt)) w = Some oc
    /\ uc_live uc 0 = false
    /\ w_output (oc_world oc) = w_output w ++ map snd (uc_out uc)
    /\ uc_panic uc 0 = ocpanic oc.
Proof.
  intros a ucap w. eexists. exists (ORet tt (w_log true (a :: nil) w)).
  split.
  { eapply usteps_step. { eapply ustep_defer     with (tid := 0); rewrite ?upd_same; cbn; reflexivity. }
    eapply usteps_step. { eapply ustep_ret_defer with (tid := 0); rewrite ?upd_same; cbn; reflexivity. }
    eapply usteps_step. { eapply ustep_out        with (tid := 0); rewrite ?upd_same; cbn; reflexivity. }
    eapply usteps_step. { eapply ustep_ret_done   with (tid := 0); rewrite ?upd_same; cbn; reflexivity. }
    apply usteps_refl. }
  split. { vm_compute. reflexivity. }
  split. { reflexivity. }
  split. { cbn. reflexivity. } { reflexivity. }
Qed.

Local Example bridge_defer_panic_agrees : forall (a : GoAny) (v : GoAny) (ucap : nat -> option nat) w,
  exists uc oc,
    usteps ucap (ustart (cmd_to_ucmd (CDfr (COut true (a :: nil) (CRet tt)) (CPan v)))) uc
    /\ run_cmd 5 (CDfr (COut true (a :: nil) (CRet tt)) (CPan v)) w = Some oc
    /\ uc_live uc 0 = false
    /\ w_output (oc_world oc) = w_output w ++ map snd (uc_out uc)
    /\ uc_panic uc 0 = ocpanic oc.
Proof.
  intros a v ucap w. eexists. exists (OPanic v (w_log true (a :: nil) w)).
  split.
  { eapply usteps_step. { eapply ustep_defer     with (tid := 0); rewrite ?upd_same; cbn; reflexivity. }
    eapply usteps_step. { eapply ustep_pan_defer with (tid := 0); rewrite ?upd_same; cbn; reflexivity. }
    eapply usteps_step. { eapply ustep_out        with (tid := 0); rewrite ?upd_same; cbn; reflexivity. }
    eapply usteps_step. { eapply ustep_ret_done   with (tid := 0); rewrite ?upd_same; cbn; reflexivity. }
    apply usteps_refl. }
  split. { vm_compute. reflexivity. }
  split. { reflexivity. }
  split. { cbn. reflexivity. } { reflexivity. }
Qed.

Local Example bridge_defer_panic_replace_agrees : forall (v1 : GoAny) (v2 : GoAny) (ucap : nat -> option nat) w,
  exists uc oc,
    usteps ucap (ustart (cmd_to_ucmd (CDfr (CPan v2) (CPan v1)))) uc
    /\ run_cmd 5 (CDfr (CPan v2) (CPan v1)) w = Some oc
    /\ uc_live uc 0 = false
    /\ w_output (oc_world oc) = w_output w ++ map snd (uc_out uc)
    /\ uc_panic uc 0 = ocpanic oc.
Proof.
  intros v1 v2 ucap w. eexists. exists (OPanic v2 w).
  split.
  { eapply usteps_step. { eapply ustep_defer     with (tid := 0); rewrite ?upd_same; cbn; reflexivity. }
    eapply usteps_step. { eapply ustep_pan_defer with (tid := 0); rewrite ?upd_same; cbn; reflexivity. }
    eapply usteps_step. { eapply ustep_pan_done  with (tid := 0); rewrite ?upd_same; cbn; reflexivity. }
    apply usteps_refl. }
  split. { vm_compute. reflexivity. }
  split. { reflexivity. }
  split. { cbn. rewrite app_nil_r. reflexivity. } { reflexivity. }
Qed.

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

(** Demo 5 — LIFO ORDER across SIBLING defers ([defer println(a); defer println(b); return]).  [b] is deferred
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

(** Public assumption surface for this module — the manifest gate captures this ONE [Print Assumptions]:
    the [run_cmd]-grounded bridge.  The projection plumbing is Local and deliberately NOT printed/gated. *)
Print Assumptions cmd_to_ucmd_run_agrees.
