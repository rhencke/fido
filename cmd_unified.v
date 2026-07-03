(** cmd_unified.v — the FIRST bridge between Fido's two proof-only semantics universes.

    GoSem denotes the supported AST into [cmd.v]'s command tree [Cmd unit] (CRet / COut / CPan / CDfr,
    plus the heap pair CWrite / CRead — typed cells, ABSENT on unallocated access).
    [unified.v] is the closed-world OPERATIONAL semantics ([UCmd] / [ustep]) on which race-freedom and
    liveness/deadlock are proved.  The charter (ARCHITECTURE.md) requires GoSem to BRIDGE that existing
    semantics, NOT fork a second universe.  The structural fact that makes the bridge concrete: [cmd.v]'s
    constructors map 1-for-1 into [unified.v]'s fragment —
        CRet -> URet,  COut b xs -> UOut b xs,  CPan v -> UPan v,  CDfr d -> UDfr d,
        CWrite l v -> UWrite l v,  CRead l f -> URead l f.
    So [cmd_to_ucmd] is a TOTAL translation of cmd.v's [Cmd unit] command tree into a subset of [UCmd].  The
    print/println flag on [COut] is PRESERVED ([unified.v]'s [UOut]/[uc_out] carry it, exactly the model's
    [w_output : list (bool * list GoAny)]).

    The module exposes ONE single-goroutine [usteps] AGREEMENT bridge, [bridge_heap_agrees]:
    ANY [c] (heap reads/writes, arbitrary defer nesting, any panics) whose [run_cmd] COMPLETES
    agrees end to end INCLUDING final heaps, from the [ustart_w] mirrored-heap start (the
    completion premise is the well-formedness gate; for [no_heap] commands completion is a
    THEOREM — cmd.v's [run_cmd_terminates] — so consumers compose the two).  Plus cmd.v-side
    properties for a COMPLETING [run_cmd] on ANY [c] (heap ops included): output only APPENDS,
    and a panic-free completing run returns [ORet].
    The EXACT gated public-surface set is the [Print Assumptions] block at the end of this file (the single in-file
    authority); this header does not re-enumerate it.
    There is NO public projection-observer theorem: every unified-side run/unwind lemma is LOCAL
    (file-private) proof plumbing grounded directly in cmd.v's [go]/[run_defers] — no exported
    theorem concludes with a private observer, so a consumer cannot prove bridge facts against
    anything but [run_cmd].  (No concurrency ops in this fragment, so [uc_bufs] is untouched;
    [uc_heap] carries the heap commands' effects and heap steps append [KWrite]/[KRead] to [uc_trace] —
    the trace is existential in the heap bridge's statement.)
    Proof-only: emits no Go, adds no axiom. *)

From Fido Require Import preamble concurrency cmd unified.
From Stdlib Require Import List Lia.
Import ListNotations.

(** PUBLIC.  The total structural translation: cmd.v command tree -> [UCmd]'s
    output/panic/return/defer + heap fragment, [COut]'s println flag PRESERVED into [UOut]'s flag. *)
(** The bridge instantiates the value-parametric calculus at [V := GoAny]: the fragment's
    payloads ([UOut]/[UPan] values) are the model's own [GoAny], no erasure. *)
Notation UCmdG := (@UCmd GoAny).

Fixpoint cmd_to_ucmd (c : Cmd unit) : UCmdG :=
  match c with
  | CRet _      => URet
  | COut b xs c' => UOut b xs (cmd_to_ucmd c')
  | CPan v      => UPan v
  | CDfr d c'   => UDfr (cmd_to_ucmd d) (cmd_to_ucmd c')
  | CWrite l v c' => UWrite l v (cmd_to_ucmd c')
  | CRead l f   => URead l (fun x => cmd_to_ucmd (f x))
  end.

(** PUBLIC + GATED: the IMAGE seal — [cmd_to_ucmd] lands in the TRANSLATED fragment BY
    CONSTRUCTION: output/panic/defer plus the heap pair, and NO channel/spawn form ever
    ([USend]/[URecv]/[USelect]/[UClose]/[USpawn] all excluded).  ⚠ This image ALONE no
    longer bounds the calculus' closed-recv value: [URead] binds from the heap, whose
    START default is [vz] — the no-[vz] license is the SEPARATE, STRONGER seal
    [cmd_to_ucmd_novz] below, on the [no_heap] fragment the bridge is quarantined to. *)
Inductive UFrag {V : Type} : @UCmd V -> Prop :=
  | UF_ret : UFrag URet
  | UF_out : forall pb xs k, UFrag k -> UFrag (UOut pb xs k)
  | UF_pan : forall v, UFrag (UPan v)
  | UF_dfr : forall d k, UFrag d -> UFrag k -> UFrag (UDfr d k)
  | UF_wr  : forall l v k, UFrag k -> UFrag (UWrite l v k)
  | UF_rd  : forall l f, (forall x, UFrag (f x)) -> UFrag (URead l f).
Theorem cmd_to_ucmd_fragment : forall c : Cmd unit, UFrag (cmd_to_ucmd c).
Proof.
  fix IH 1. intros [u | pb xs c' | v | d c' | l v c' | l f]; cbn [cmd_to_ucmd].
  - constructor.
  - constructor. exact (IH c').
  - constructor.
  - constructor; [exact (IH d) | exact (IH c')].
  - constructor. exact (IH c').
  - constructor. intro x. exact (IH (f x)).
Qed.

(** PUBLIC + GATED: the NO-[vz] seal — on the [no_heap] fragment (exactly where
    completion is a theorem), [cmd_to_ucmd]'s image contains NOTHING that can bind the
    calculus' [vzero] parameter or the [vz]-defaulted start heap: no [URead] (the start
    heap defaults to [vz]), no [URecv]/[USelect] (the closed-recv rules bind [vzero]), no
    channel/spawn forms.  THIS licenses the quantified [vz] for the [no_heap] statements
    (historically the no-heap lane; the bridge [bridge_heap_agrees] carries
    its OWN license — see the [vz] banner); the CHANNEL slice must replace the parameter
    with a STRUCTURAL per-element-type zero (the element tag at the [URecv] boundary) —
    Go's closed-recv zero is typed, and no single [GoAny] can stand for all of them
    (plans/bridge-effects.md). *)
Inductive UNoVz {V : Type} : @UCmd V -> Prop :=
  | UV_ret : UNoVz URet
  | UV_out : forall pb xs k, UNoVz k -> UNoVz (UOut pb xs k)
  | UV_pan : forall v, UNoVz (UPan v)
  | UV_dfr : forall d k, UNoVz d -> UNoVz k -> UNoVz (UDfr d k).
Theorem cmd_to_ucmd_novz : forall c : Cmd unit,
  no_heap c = true -> UNoVz (cmd_to_ucmd c).
Proof.
  fix IH 1. intros [a | pb xs c' | v | d c' | l v c' | l f]; cbn [cmd_to_ucmd no_heap]; intro H.
  - constructor.
  - constructor. exact (IH c' H).
  - constructor.
  - destruct (no_heap d) eqn:Hd; [ | discriminate H ]. cbn in H.
    constructor; [ exact (IH d Hd) | exact (IH c' H) ].
  - discriminate H.
  - discriminate H.
Qed.

(** [vz] — the calculus' closed-recv parameter and the start configs' initial-heap default at
    this instance.  It is an ARBITRARY [GoAny], NOT a Go zero value, and every public statement
    below that MENTIONS the unified [GoAny] configuration ([usteps]/[ustart]/[ustart_w])
    UNIVERSALLY QUANTIFIES it (section generalization; the pure [run_cmd]-side theorems in
    this section never involve it), each with its OWN license:
    a [no_heap] image never reaches a [vz]-consulting rule ([cmd_to_ucmd_novz] — the seal the
    CHANNEL slice extends); [bridge_heap_agrees] starts from the [ustart_w] heap that MIRRORS
    the World's allocated cells and its [go]-completion premise keeps the run inside them, so the
    [vz] defaults on unallocated locations are never consulted. *)
Section BridgeVal.
Variable vz : GoAny.

(** PUBLIC.  The single-goroutine start config running [u] on goroutine 0 (live, empty defers, no panic, no
    output), and the panic an [Outcome] carries — the cmd.v-side observation [uc_panic] agrees with. *)
(** ---- Part ii of the heap slice: the AGREEMENT kit (plans/bridge-effects.md 2c) ----
    [heap_agrees h rh]: the calculus heap [h] holds each ALLOCATED cell's boxed value
    ([any_of_cell]); unallocated locations are UNCONSTRAINED (a completing run never touches
    them — [go] is [None] there).  [heap_of_world w] is the CANONICAL start heap — every
    allocated cell boxed, [vz] elsewhere. *)
Definition heap_agrees (h : nat -> GoAny) (rh : RefHeap) : Prop :=
  forall l cell, rh l = Some cell -> h l = any_of_cell cell.
Definition heap_of_world (w : World) : nat -> GoAny :=
  fun l => match w_refs w l with Some cell => any_of_cell cell | None => vz end.
Local Lemma heap_of_world_agrees : forall w, heap_agrees (heap_of_world w) (w_refs w).
Proof. intros w l cell H. unfold heap_of_world. rewrite H. reflexivity. Qed.

(** PUBLIC.  The start config whose heap MIRRORS a [World]'s allocated cells ([heap_of_world]
    below) — the heap-bridging theorems start here, so their statements need no side
    agreement premise. *)
Definition ustart_w (w : World) (u : UCmdG) : UConfig :=
  mkUCfg (fun t => if Nat.eqb t 0 then u else URet)
         (fun _ => nil) (heap_of_world w) (fun t => Nat.eqb t 0) nil nil (fun _ => nil) (fun _ => None).
Definition ocpanic (oc : Outcome unit) : option GoAny :=
  match oc with OPanic v _ => Some v | ORet _ _ => None end.

(** a tag-preserving write keeps the agreement: the new cell's box IS the written value *)
Local Lemma heap_write_agrees : forall h w l v w',
  heap_agrees h (w_refs w) ->
  heap_write l v w = Some w' ->
  heap_agrees (upd h l v) (w_refs w').
Proof.
  intros h w l v w' Ha Hw l' cell' H'.
  unfold heap_write in Hw.
  destruct (w_refs w l) as [[T [tc y]]|] eqn:Hl; [ | discriminate Hw ].
  destruct v as [A [x ta]].
  destruct (tag_eq ta tc); [ | discriminate Hw ].
  injection Hw as <-.
  cbn [w_refs] in H'.
  destruct (Nat.eqb l' l) eqn:El.
  - apply PeanoNat.Nat.eqb_eq in El. subst l'.
    injection H' as <-. rewrite upd_same. reflexivity.
  - apply PeanoNat.Nat.eqb_neq in El.
    rewrite (upd_other h l (existT _ A (x, ta)) l' El).
    exact (Ha l' cell' H').
Qed.

(** Phase A, SEMANTIC (heap ops included): grounded directly in [go]'s RESULT — given a
    successful body run and a calculus heap agreeing with [w]'s allocated cells, the [ustep]
    run mirrors it: program per [oc], defers = [ds] (in [go]'s order), output advanced by
    exactly [go]'s delta, final heaps AGREE.  The trace is EXISTENTIAL (heap steps emit
    [KWrite]/[KRead] events — the race substrate, not part of this agreement). *)
Local Lemma body_runs_sem : forall c w oc ds ucap p b h lv tr o df pa,
  go c w = Some (oc, ds) ->
  heap_agrees h (w_refs w) ->
  lv 0 = true -> p 0 = cmd_to_ucmd c ->
  exists p' h' tr' df' evs,
    usteps vz ucap (mkUCfg p b h lv tr o df pa)
                (mkUCfg p' b h' lv tr' (o ++ map (fun e => (0, e)) evs) df' pa)
    /\ p' 0 = (match oc with ORet _ _ => URet | OPanic v _ => UPan v end)
    /\ df' 0 = map cmd_to_ucmd ds ++ df 0
    /\ heap_agrees h' (w_refs (oc_world oc))
    /\ w_output (oc_world oc) = w_output w ++ evs.
Proof.
  intros c.
  induction c as [a | bo xs c' IH | v | d c' IHc' | l v c' IH | l f IH] using Cmd_rect';
    intros w oc ds ucap p b h lv tr o df pa Hgo Hha Hlv Hp;
    cbn [go] in Hgo; cbn [cmd_to_ucmd] in Hp.
  - (* CRet *)
    injection Hgo as <- <-.
    exists p, h, tr, df, nil. cbn [map]. rewrite !app_nil_r.
    split; [ apply usteps_refl | split; [ exact Hp | split; [ reflexivity | split; [ exact Hha | reflexivity ] ] ] ].
  - (* COut *)
    destruct (IH (w_log bo xs w) oc ds ucap (upd p 0 (cmd_to_ucmd c')) b h lv tr
                 (o ++ ((0, (bo, xs)) :: nil)) df pa Hgo Hha Hlv (upd_same _ _ _))
      as [p' [h' [tr' [df' [evs [Hus [Hprog [Hdf [Hha2 Hout]]]]]]]]].
    exists p', h', tr', df', ((bo, xs) :: evs).
    split; [ | split; [ exact Hprog | split; [ exact Hdf | split; [ exact Hha2 | ] ] ] ].
    + replace (o ++ map (fun e => (0, e)) ((bo, xs) :: evs))
         with ((o ++ ((0, (bo, xs)) :: nil)) ++ map (fun e => (0, e)) evs)
        by (cbn [map]; rewrite <- app_assoc; reflexivity).
      eapply usteps_step; [ eapply ustep_out; [ exact Hlv | exact Hp ] | exact Hus ].
    + rewrite Hout. cbn [w_log w_output]. rewrite <- app_assoc. reflexivity.
  - (* CPan *)
    injection Hgo as <- <-.
    exists p, h, tr, df, nil. cbn [map]. rewrite !app_nil_r.
    split; [ apply usteps_refl | split; [ exact Hp | split; [ reflexivity | split; [ exact Hha | reflexivity ] ] ] ].
  - (* CDfr *)
    destruct (go c' w) as [[oc0 ds0]|] eqn:E; [ | discriminate Hgo ].
    injection Hgo as H1 H2. subst oc ds.
    destruct (IHc' w oc0 ds0 ucap (upd p 0 (cmd_to_ucmd c')) b h lv tr o
                  (upd df 0 (cmd_to_ucmd d :: df 0)) pa E Hha Hlv (upd_same _ _ _))
      as [p' [h' [tr' [df' [evs [Hus [Hprog [Hdf [Hha2 Hout]]]]]]]]].
    exists p', h', tr', df', evs.
    split; [ | split; [ exact Hprog | split; [ | split; [ exact Hha2 | exact Hout ] ] ] ].
    + eapply usteps_step; [ eapply ustep_defer; [ exact Hlv | exact Hp ] | exact Hus ].
    + rewrite Hdf, upd_same, map_app. cbn [map]. rewrite <- app_assoc. reflexivity.
  - (* CWrite *)
    destruct (heap_write l v w) as [w'|] eqn:Hw; [ | discriminate Hgo ].
    destruct (IH w' oc ds ucap (upd p 0 (cmd_to_ucmd c')) b (upd h l v) lv
                 (tr ++ (mkEv 0 (KWrite l) :: nil)) o df pa Hgo
                 (heap_write_agrees h w l v w' Hha Hw) Hlv (upd_same _ _ _))
      as [p' [h' [tr' [df' [evs [Hus [Hprog [Hdf [Hha2 Hout]]]]]]]]].
    exists p', h', tr', df', evs.
    split; [ | split; [ exact Hprog | split; [ exact Hdf | split; [ exact Hha2 | ] ] ] ].
    + eapply usteps_step; [ eapply ustep_write; [ exact Hlv | exact Hp ] | exact Hus ].
    + rewrite Hout, (heap_write_output l v w w' Hw). reflexivity.
  - (* CRead *)
    destruct (w_refs w l) as [cell|] eqn:Hl; [ | discriminate Hgo ].
    pose proof (Hha l cell Hl) as Hhl.
    destruct (IH (any_of_cell cell) w oc ds ucap
                 (upd p 0 (cmd_to_ucmd (f (any_of_cell cell)))) b h lv
                 (tr ++ (mkEv 0 (KRead l) :: nil)) o df pa Hgo Hha Hlv (upd_same _ _ _))
      as [p' [h' [tr' [df' [evs [Hus [Hprog [Hdf [Hha2 Hout]]]]]]]]].
    exists p', h', tr', df', evs.
    split; [ | split; [ exact Hprog | split; [ exact Hdf | split; [ exact Hha2 | exact Hout ] ] ] ].
    eapply usteps_step; [ eapply ustep_read; [ exact Hlv | exact Hp ] | ].
    rewrite Hhl. exact Hus.
Qed.


Local Lemma w_output_w_log : forall b xs w, w_output (w_log b xs w) = w_output w ++ ((b, xs) :: nil).
Proof. reflexivity. Qed.



Local Lemma map_snd_pair0 : forall (l : list (bool * list GoAny)), map snd (map (fun e => (0, e)) l) = l.
Proof. induction l as [|a l IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

(** LOCAL regressions (file-private): print and println stay DISTINGUISHABLE through the translation. *)
Local Example bridge_print_println_distinct : forall (a : GoAny),
  cmd_to_ucmd (COut true (a :: nil) (CRet tt)) <> cmd_to_ucmd (COut false (a :: nil) (CRet tt)).
Proof. intros a H. cbn in H. discriminate H. Qed.

(** [oc_set_world] only advances the world — it preserves the [Outcome]'s panic status (and sets its world). *)
Local Lemma ocpanic_set_world : forall (acc : Outcome unit) w, ocpanic (oc_set_world acc w) = ocpanic acc.
Proof. intros [[] w0 | v w0] w; reflexivity. Qed.
Local Lemma oc_world_set_world : forall (acc : Outcome unit) w, oc_world (oc_set_world acc w) = w.
Proof. intros [[] w0 | v w0] w; reflexivity. Qed.

(** run_defers is OUTPUT-MONOTONE for ARBITRARY nesting: unwinding a defer list only ever APPENDS to the
    world's output trace (each deferred body's [go] delta and, recursively, its own nested defers'),
    never RETRACTS.  Grounded in [go_out_monotone]; induction on FUEL, the IH
    applied to the nested run and the tail.  Note [oc_world acc'] = [oc_world net_d]
    (a returning defer keeps [acc]'s panic but takes the run's advanced world; a panicking one carries its
    own), so the world only grows across both sub-runs. *)
(** The BODY's output-append law, grounded directly in [go] — premise-FREE (heap ops included: a
    write never touches [w_output], a read never writes), by tree induction with the binder case. *)
Local Lemma go_out_monotone : forall (c : Cmd unit) w oc ds,
  go c w = Some (oc, ds) ->
  exists evs, w_output (oc_world oc) = w_output w ++ evs.
Proof.
  intros c; induction c as [a | b xs c' IH | v | d c' IH | l v c' IH | l f IH] using Cmd_rect';
    intros w oc ds H; cbn [go] in H.
  - injection H as <- <-. exists nil. cbn [oc_world]. rewrite app_nil_r. reflexivity.
  - destruct (IH (w_log b xs w) oc ds H) as [evs Hevs].
    exists ((b, xs) :: evs). rewrite Hevs, w_output_w_log, <- app_assoc. reflexivity.
  - injection H as <- <-. exists nil. cbn [oc_world]. rewrite app_nil_r. reflexivity.
  - destruct (go c' w) as [[oc0 ds0]|] eqn:E; [ | discriminate H ].
    injection H as H1 H2. subst oc. exact (IH w oc0 ds0 E).
  - destruct (heap_write l v w) as [w'|] eqn:E; [ | discriminate H ].
    destruct (IH w' oc ds H) as [evs Hevs].
    exists evs. rewrite Hevs, (heap_write_output l v w w' E). reflexivity.
  - destruct (w_refs w l) as [cell|]; [ | discriminate H ].
    exact (IH (any_of_cell cell) w oc ds H).
Qed.

Local Lemma run_defers_out : forall fuel ds acc result,
  run_defers fuel ds acc = Some result ->
  exists evs, w_output (oc_world result) = w_output (oc_world acc) ++ evs.
Proof.
  induction fuel as [| n IH]; intros ds acc result H; [ discriminate H | ].
  destruct ds as [| d ds'].
  - cbn in H. injection H as <-. exists nil. rewrite app_nil_r. reflexivity.
  - rewrite run_defers_unfold in H.
    destruct (go d (oc_world acc)) as [[oc_d ds_d]|] eqn:Hgo; [ | discriminate H ].
    destruct (run_defers n ds_d oc_d) as [net_d|] eqn:Enet; [ | discriminate H ].
    destruct (go_out_monotone d (oc_world acc) oc_d ds_d Hgo) as [evs0 Hevs0].
    destruct (IH ds_d oc_d net_d Enet) as [evs1 Hevs1].
    destruct (IH ds' (match net_d with OPanic v' w' => OPanic v' w' | ORet _ w' => oc_set_world acc w' end)
                result H) as [evs2 Hevs2].
    exists (evs0 ++ evs1 ++ evs2).
    assert (Hw2 : w_output (oc_world result) = w_output (oc_world net_d) ++ evs2)
      by (rewrite Hevs2; destruct net_d as [[] w' | v' w']; cbn [oc_world]; [ rewrite oc_world_set_world | ]; reflexivity).
    rewrite Hw2, Hevs1, Hevs0, <- !app_assoc. reflexivity.
Qed.







(** SEMANTIC no-panic law for the body: a [cmd_no_panic] command's successful [go] returns
    (never panics) and every deferred action it accumulated is itself [cmd_no_panic] —
    grounded in [go]'s result by tree induction (the heap arms of [cmd_no_panic] are [false],
    so those cases are vacuous). *)
Local Lemma go_no_panic : forall (c : Cmd unit) w oc ds,
  cmd_no_panic c = true -> go c w = Some (oc, ds) ->
  (exists w', oc = ORet tt w') /\ Forall (fun d => cmd_no_panic d = true) ds.
Proof.
  intros c; induction c as [a | b xs c' IH | v | d c' IHc' | l v c' IH | l f IH] using Cmd_rect';
    intros w oc ds Hnp Hgo; cbn [cmd_no_panic] in Hnp; cbn [go] in Hgo.
  - destruct a. injection Hgo as <- <-. split; [ exists w; reflexivity | constructor ].
  - exact (IH (w_log b xs w) oc ds Hnp Hgo).
  - discriminate Hnp.
  - apply andb_prop in Hnp. destruct Hnp as [Hd Hc'].
    destruct (go c' w) as [[oc0 ds0]|] eqn:E; [ | discriminate Hgo ].
    injection Hgo as H1 H2. subst oc ds.
    destruct (IHc' w oc0 ds0 Hc' E) as [Hret Hall].
    split; [ exact Hret | ].
    apply Forall_app. split; [ exact Hall | constructor; [ exact Hd | constructor ] ].
  - discriminate Hnp.
  - discriminate Hnp.
Qed.

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
    destruct (go d (oc_world acc)) as [[oc_d ds_d]|] eqn:Hgo; [ | discriminate H ].
    destruct (go_no_panic d (oc_world acc) oc_d ds_d Hnp Hgo) as [[w_d ->] Hall_d].
    destruct (run_defers n ds_d (ORet tt w_d)) as [net_d|] eqn:Enet; [ | discriminate H ].
    assert (Hnet : ocpanic net_d = None)
      by exact (IH ds_d (ORet tt w_d) net_d Enet Hall_d eq_refl).
    destruct net_d as [[] w' | v' w']; cbn [ocpanic] in Hnet; [ | discriminate Hnet ].
    exact (IH ds' (oc_set_world acc w') result H Hall' (eq_trans (ocpanic_set_world acc w') Hacc)).
Qed.

(** Pop ONE defer off goroutine 0's stack, uniformly across the 2-mode: [ustep_ret_defer] if [prog = URet]
    (leaving [pa] alone) or [ustep_pan_defer] if [prog = UPan v] (recording [v] into [pa]).  Either way the
    post-pop [pa 0] equals the pre-pop in-flight panic [q0], so the caller need not case-split. *)
Local Lemma pop_defer_step : forall ucap p b h lv tr o df pa d rest q0,
  lv 0 = true -> (p 0 = URet \/ exists v, p 0 = UPan v) ->
  (match p 0 with UPan v => Some v | _ => pa 0 end) = q0 ->
  df 0 = cmd_to_ucmd d :: rest ->
  exists paP, paP 0 = q0 /\
    usteps vz ucap (mkUCfg p b h lv tr o df pa)
                (mkUCfg (upd p 0 (cmd_to_ucmd d)) b h lv tr o (upd df 0 rest) paP).
Proof.
  intros ucap p b h lv tr o df pa d rest q0 Hlv Hp Hq0 Hdf.
  destruct Hp as [Hret | [v Hpan]].
  - exists pa. rewrite Hret in Hq0. cbn in Hq0. split; [ exact Hq0 | ].
    eapply usteps_step; [ eapply ustep_ret_defer; [ exact Hlv | exact Hret | exact Hdf ] | apply usteps_refl ].
  - exists (upd pa 0 (Some v)). rewrite Hpan in Hq0. cbn in Hq0. split; [ rewrite upd_same; exact Hq0 | ].
    eapply usteps_step; [ eapply ustep_pan_defer; [ exact Hlv | exact Hpan | exact Hdf ] | apply usteps_refl ].
Qed.

(** A panic in flight is NEVER lost, semantically: a completing [run_defers] from a
    panic-seeded accumulator ends in a panic (a returning defer KEEPS the seed via
    [oc_set_world]; a panicking one replaces it with another panic). *)
Local Lemma run_defers_panic_stays : forall fuel ds v w r,
  run_defers fuel ds (OPanic v w) = Some r ->
  exists v' w', r = OPanic v' w'.
Proof.
  induction fuel as [| n IH]; intros ds v w r H; [ discriminate H | ].
  destruct ds as [| d ds'].
  - cbn in H. injection H as <-. exists v, w. reflexivity.
  - rewrite run_defers_unfold in H. cbn [oc_world] in H.
    destruct (go d w) as [[oc_d ds_d]|] eqn:Hgo; [ | discriminate H ].
    destruct (run_defers n ds_d oc_d) as [net_d|] eqn:Enet; [ | discriminate H ].
    destruct net_d as [[] w_n | v_n w_n]; cbn [oc_set_world] in H.
    + exact (IH ds' v w_n r H).
    + exact (IH ds' v_n w_n r H).
Qed.

(** SEED-LINEARITY of [run_defers] at the OUTCOME level (semantic — no syntactic flatten):
    re-seeding a completing unwind with an in-flight panic [v] (same world) completes
    IDENTICALLY — same worlds throughout — and the seed survives exactly when the
    return-seeded run returns.  This is the reconciliation the deferred-heap unwind's IH
    composition needs: the ustep threads the enclosing panic CARRIED-IN through each
    nested run, while [run_defers] seeds fresh and re-applies at the level boundary. *)
Local Lemma run_defers_seed_linear : forall fuel ds w r0,
  run_defers fuel ds (ORet tt w) = Some r0 ->
  forall v, run_defers fuel ds (OPanic v w)
    = Some (match r0 with ORet _ w' => OPanic v w' | OPanic v' w' => OPanic v' w' end).
Proof.
  induction fuel as [| n IH]; intros ds w r0 H v; [ discriminate H | ].
  destruct ds as [| d ds'].
  - cbn in H |- *. injection H as <-. reflexivity.
  - rewrite run_defers_unfold in H. rewrite run_defers_unfold. cbn [oc_world] in H |- *.
    destruct (go d w) as [[oc_d ds_d]|] eqn:Hgo; [ | discriminate H ].
    destruct (run_defers n ds_d oc_d) as [net_d|] eqn:Enet; [ | discriminate H ].
    destruct net_d as [[] w_n | v_n w_n]; cbn [oc_set_world] in H |- *.
    + (* the nested run RETURNS: the accumulator keeps its seed, world advanced *)
      exact (IH ds' w_n r0 H v).
    + (* the nested run PANICS: both seeds converge on the same accumulator *)
      rewrite H.
      destruct (run_defers_panic_stays n ds' v_n w_n r0 H) as [v' [w' ->]].
      reflexivity.
Qed.

(** The DEFERRED-HEAP unwind (semantic 2-mode): given a completing [run_defers] and a ustep
    state whose in-flight panic ((prog, pa) 2-mode) and heap AGREE with the accumulator, the
    ustep pops and runs the whole LIFO front [ds] down to [ds_tail], landing on [result]'s
    panic, world-output delta, and ALLOCATED heap.  Each popped defer's body runs via
    [body_runs_sem]; the carried-vs-fresh panic threading is reconciled by
    [run_defers_seed_linear] at each nesting boundary (no syntactic flatten). *)
Local Lemma unwind_heap : forall fuel ds acc result,
  run_defers fuel ds acc = Some result ->
  forall ucap p b h lv tr o df pa ds_tail,
    lv 0 = true ->
    (p 0 = URet \/ exists v, p 0 = UPan v) ->
    (match p 0 with UPan v => Some v | _ => pa 0 end) = ocpanic acc ->
    heap_agrees h (w_refs (oc_world acc)) ->
    df 0 = map cmd_to_ucmd ds ++ ds_tail ->
    exists p' h' tr' df' pa' evs,
      usteps vz ucap (mkUCfg p b h lv tr o df pa)
                  (mkUCfg p' b h' lv tr' (o ++ map (fun e => (0, e)) evs) df' pa')
      /\ (p' 0 = URet \/ exists v, p' 0 = UPan v)
      /\ (match p' 0 with UPan v => Some v | _ => pa' 0 end) = ocpanic result
      /\ df' 0 = ds_tail
      /\ heap_agrees h' (w_refs (oc_world result))
      /\ w_output (oc_world result) = w_output (oc_world acc) ++ evs.
Proof.
  induction fuel as [| n IH]; intros ds acc result Hrd
    ucap p b h lv tr o df pa ds_tail Hlv Hp Hq0 Hha Hdf; [ discriminate Hrd | ].
  destruct ds as [| d ds'].
  - cbn in Hrd. injection Hrd as <-.
    cbn [map] in Hdf. rewrite app_nil_l in Hdf.
    exists p, h, tr, df, pa, nil. cbn [map]. rewrite !app_nil_r.
    split; [ apply usteps_refl | ].
    split; [ exact Hp | split; [ exact Hq0 | split; [ exact Hdf | split; [ exact Hha | reflexivity ] ] ] ].
  - rewrite run_defers_unfold in Hrd.
    destruct (go d (oc_world acc)) as [[oc_d ds_d]|] eqn:Hgo; [ | discriminate Hrd ].
    destruct (run_defers n ds_d oc_d) as [net_d|] eqn:Enet; [ | discriminate Hrd ].
    cbn [map] in Hdf.
    destruct (pop_defer_step ucap p b h lv tr o df pa d
                (map cmd_to_ucmd ds' ++ ds_tail) (ocpanic acc) Hlv Hp Hq0 Hdf)
      as [paP [HpaP Hpop]].
    destruct (body_runs_sem d (oc_world acc) oc_d ds_d ucap
                (upd p 0 (cmd_to_ucmd d)) b h lv tr o
                (upd df 0 (map cmd_to_ucmd ds' ++ ds_tail)) paP
                Hgo Hha Hlv (upd_same _ _ _))
      as [pA [hA [trA [dfA [evs0 [HusA [HprogA [HdfA [HhaA Hout0]]]]]]]]].
    rewrite upd_same in HdfA.
    (* the CARRIED-seed nested run and its result [net'] *)
    set (qmid := match oc_d with OPanic v _ => Some v | ORet _ _ => ocpanic acc end).
    assert (Hqmid : (match pA 0 with UPan v => Some v | _ => paP 0 end) = qmid)
      by (rewrite HprogA; unfold qmid; destruct oc_d as [[] ?|? ?]; [ exact HpaP | reflexivity ]).
    assert (HprogA' : pA 0 = URet \/ exists v, pA 0 = UPan v)
      by (rewrite HprogA; destruct oc_d as [[] ?|vd ?]; [ left; reflexivity | right; exists vd; reflexivity ]).
    (* choose the carried seed + its completing run via seed-linearity *)
    set (seed := match qmid with Some v => OPanic v (oc_world oc_d) | None => ORet tt (oc_world oc_d) end).
    assert (Hseed_run : exists net',
              run_defers n ds_d seed = Some net'
              /\ ocpanic net'
                 = ocpanic (match net_d with
                            | OPanic v' w' => OPanic v' w'
                            | ORet _ w' => oc_set_world acc w' end)
              /\ oc_world net'
                 = oc_world (match net_d with
                             | OPanic v' w' => OPanic v' w'
                             | ORet _ w' => oc_set_world acc w' end)
              /\ w_output (oc_world net') = w_output (oc_world net_d)).
    { destruct oc_d as [[] w_d | v_d w_d]; unfold qmid, seed; cbn [ocpanic].
      - (* body RETURNS *)
        destruct acc as [[] w_a | v_a w_a]; cbn [ocpanic].
        + (* carried None: the fresh run IS the carried run *)
          exists net_d. split; [ exact Enet | ].
          destruct net_d as [[] w_n | v_n w_n]; cbn [ocpanic oc_world];
            rewrite ?ocpanic_set_world, ?oc_world_set_world; cbn [ocpanic oc_world];
            repeat split; reflexivity.
        + (* carried Some v_a: seed-linearity converts the fresh run *)
          exists (match net_d with ORet _ w' => OPanic v_a w' | OPanic v' w' => OPanic v' w' end).
          split; [ exact (run_defers_seed_linear n ds_d w_d net_d Enet v_a) | ].
          destruct net_d as [[] w_n | v_n w_n]; cbn [ocpanic oc_world];
            rewrite ?ocpanic_set_world, ?oc_world_set_world; cbn [ocpanic oc_world];
            repeat split; reflexivity.
      - (* body PANICS: the fresh seed IS the carried seed; net_d stays a panic *)
        exists net_d. split; [ exact Enet | ].
        destruct (run_defers_panic_stays n ds_d v_d w_d net_d Enet) as [v_n [w_n ->]].
        cbn [ocpanic oc_world]. repeat split; reflexivity. }
    destruct Hseed_run as [net' [Enet' [Hpan' [Hw' Hwo']]]].
    assert (Hqseed : (match pA 0 with UPan v => Some v | _ => paP 0 end) = ocpanic seed)
      by (rewrite Hqmid; unfold seed; destruct qmid; reflexivity).
    assert (Hhaseed : heap_agrees hA (w_refs (oc_world seed)))
      by (unfold seed; destruct qmid; exact HhaA).
    destruct (IH ds_d seed net' Enet' ucap pA b hA lv trA
                 (o ++ map (fun e => (0, e)) evs0) dfA paP
                 (map cmd_to_ucmd ds' ++ ds_tail)
                 Hlv HprogA' Hqseed Hhaseed HdfA)
      as [pB [hB [trB [dfB [paB [evs1 [HusB [HprogB [HqB [HdfB [HhaB Hout1]]]]]]]]]]].
    (* the tail at [acc']: the IH#1 landing state matches by [Hpan']/[Hw'] *)
    assert (HqB' : (match pB 0 with UPan v => Some v | _ => paB 0 end)
                   = ocpanic (match net_d with
                              | OPanic v' w' => OPanic v' w'
                              | ORet _ w' => oc_set_world acc w' end))
      by (rewrite HqB; exact Hpan').
    assert (HhaB' : heap_agrees hB (w_refs (oc_world (match net_d with
                              | OPanic v' w' => OPanic v' w'
                              | ORet _ w' => oc_set_world acc w' end))))
      by (rewrite <- Hw'; exact HhaB).
    destruct (IH ds' (match net_d with
                      | OPanic v' w' => OPanic v' w'
                      | ORet _ w' => oc_set_world acc w' end) result Hrd
                 ucap pB b hB lv trB
                 ((o ++ map (fun e => (0, e)) evs0) ++ map (fun e => (0, e)) evs1)
                 dfB paB ds_tail Hlv HprogB HqB' HhaB' HdfB)
      as [pC [hC [trC [dfC [paC [evs2 [HusC [HprogC [HqC [HdfC [HhaC Hout2]]]]]]]]]]].
    exists pC, hC, trC, dfC, paC, (evs0 ++ evs1 ++ evs2).
    split; [ | split; [ exact HprogC | split; [ exact HqC | split; [ exact HdfC | split; [ exact HhaC | ] ] ] ] ].
    + replace (o ++ map (fun e => (0, e)) (evs0 ++ evs1 ++ evs2))
         with (((o ++ map (fun e => (0, e)) evs0) ++ map (fun e => (0, e)) evs1)
                 ++ map (fun e => (0, e)) evs2)
        by (rewrite !map_app, !app_assoc; reflexivity).
      eapply usteps_trans; [ exact Hpop | ].
      eapply usteps_trans; [ exact HusA | ].
      eapply usteps_trans; [ exact HusB | exact HusC ].
    + rewrite Hout2.
      assert (Hwacc' : w_output (oc_world (match net_d with
                                            | OPanic v' w' => OPanic v' w'
                                            | ORet _ w' => oc_set_world acc w' end))
                       = w_output (oc_world net')).
      { rewrite Hw'. reflexivity. }
      rewrite Hwacc', Hout1.
      assert (Hwseed : w_output (oc_world seed) = w_output (oc_world oc_d))
        by (unfold seed; destruct qmid; reflexivity).
      rewrite Hwseed, Hout0, <- !app_assoc. reflexivity.
Qed.


(** OUTPUT-MONOTONICITY of [run_cmd], for ANY [c] (arbitrary defer nesting, heap ops included —
    a write never touches [w_output]): a
    COMPLETING run ([run_cmd fuel c w = Some oc]) only ever APPENDS to the world's output (the body's
    body's [go] delta then, via [run_defers_out], every defer's, recursively), never RETRACTS.  A cmd.v-side
    faithfulness guarantee — Go's deferred actions and
    panics cannot un-print already-printed output.  A standalone cmd.v-side property (distinct from the ustep
    AGREEMENT bridge), via [run_defers_out].  The bridge [bridge_heap_agrees] establishes its output agreement
    independently through [unwind_heap], so this theorem is a sibling, not a dependency, of the bridge. *)
Theorem run_cmd_out_monotone : forall fuel (c : Cmd unit) w oc,
  run_cmd fuel c w = Some oc ->
  exists evs, w_output (oc_world oc) = w_output w ++ evs.
Proof.
  intros fuel c w oc H.
  unfold run_cmd in H.
  destruct (go c w) as [[oc0 ds]|] eqn:Hgo; [ | discriminate H ].
  destruct (go_out_monotone c w oc0 ds Hgo) as [evs0 Hevs0].
  destruct (run_defers fuel ds (oc_unit oc0)) as [result|] eqn:Erd; [ | discriminate H ].
  destruct (run_defers_out fuel ds (oc_unit oc0) result Erd) as [evs Hevs].
  assert (Hseed : oc_world (oc_unit oc0) = oc_world oc0) by (destruct oc0; reflexivity).
  rewrite Hseed, Hevs0 in Hevs.
  exists (evs0 ++ evs).
  destruct result as [[] w' | v w']; cbn [oc_world] in Hevs; cbn in H; injection H as <-.
  - rewrite oc_world_set_world, Hevs, <- app_assoc. reflexivity.
  - cbn [oc_world]. rewrite Hevs, <- app_assoc. reflexivity.
Qed.

(** PANIC-FREEDOM of [run_cmd] for ANY [c] (nested defers included): a [cmd_no_panic c] run that COMPLETES
    returns [ORet] — Go's panic-free program cannot end in a panic.  Via [go_no_panic] (the body returns and
    its defer forest is panic-free) + [run_defers_no_panic] (the unwind preserves it).  A standalone
    cmd.v-side property, panic-free companion to [run_cmd_out_monotone]; the bridge [bridge_heap_agrees]
    separately proves agreement for completing runs, not resting on this theorem. *)
Theorem run_cmd_no_panic_ret : forall fuel (c : Cmd unit) w oc,
  run_cmd fuel c w = Some oc -> cmd_no_panic c = true ->
  exists w', oc = ORet tt w'.
Proof.
  intros fuel c w oc H Hnp.
  unfold run_cmd in H.
  destruct (go c w) as [[oc0 ds]|] eqn:Hgo; [ | discriminate H ].
  destruct (go_no_panic c w oc0 ds Hnp Hgo) as [[w_b ->] Hall].
  destruct (run_defers fuel ds (oc_unit (ORet tt w_b))) as [result|] eqn:Erd; [ | discriminate H ].
  assert (Hres : ocpanic result = None)
    by exact (run_defers_no_panic fuel ds (oc_unit (ORet tt w_b)) result Erd Hall eq_refl).
  destruct result as [[] w' | v w']; cbn [ocpanic] in Hres; [ | discriminate Hres ].
  cbn in H. injection H as <-. exists w'. reflexivity.
Qed.




(** ★ The GENERAL heap bridge (PUBLIC + GATED): for ANY [c] — heap reads/writes, arbitrary
    defer nesting, any panics — whose [run_cmd] COMPLETES, the [usteps] run from the
    [ustart_w w] config (heap = [w]'s allocated cells, boxed) AGREES end to end, INCLUDING
    the final heaps ([heap_agrees] against the result world's allocated cells).  Assembly:
    [body_runs_sem] (Phase A, semantic) + [unwind_heap] (the deferred-heap unwind, its
    carried-vs-fresh panic threading reconciled by [run_defers_seed_linear]) + the 2-mode
    final done.  The completion premise is the well-formedness gate (an unallocated access
    never completes — [cread_unallocated_absent] below). *)
Theorem bridge_heap_agrees : forall (c : Cmd unit) ucap w fuel oc,
  run_cmd fuel c w = Some oc ->
  exists uc : UConfig,
    usteps vz ucap (ustart_w w (cmd_to_ucmd c)) uc
    /\ uc_live uc 0 = false
    /\ uc_panic uc 0 = ocpanic oc
    /\ w_output (oc_world oc) = w_output w ++ map snd (uc_out uc)
    /\ heap_agrees (uc_heap uc) (w_refs (oc_world oc)).
Proof.
  intros c ucap w fuel oc H.
  unfold run_cmd in H.
  destruct (go c w) as [[oc0 ds]|] eqn:Hgo; [ | discriminate H ].
  destruct (run_defers fuel ds (oc_unit oc0)) as [result|] eqn:Erd; [ | discriminate H ].
  destruct (body_runs_sem c w oc0 ds ucap
              (fun t => if Nat.eqb t 0 then cmd_to_ucmd c else URet)
              (fun _ => nil) (heap_of_world w) (fun t => Nat.eqb t 0) nil nil
              (fun _ => nil) (fun _ => None)
              Hgo (heap_of_world_agrees w) eq_refl eq_refl)
    as [pA [hA [trA [dfA [evs0 [HusA [HprogA [HdfA [HhaA Hout0]]]]]]]]].
  rewrite app_nil_r in HdfA.
  assert (HdfA' : dfA 0 = map cmd_to_ucmd ds ++ nil) by (rewrite HdfA, app_nil_r; reflexivity).
  assert (HprogA' : pA 0 = URet \/ exists v, pA 0 = UPan v)
    by (rewrite HprogA; destruct oc0 as [[] ?|v0 ?]; [ left; reflexivity | right; exists v0; reflexivity ]).
  assert (Hq0 : (match pA 0 with UPan v => Some v | _ => (fun _ : nat => @None GoAny) 0 end)
                = ocpanic (oc_unit oc0))
    by (rewrite HprogA; destruct oc0 as [[] ?|? ?]; reflexivity).
  assert (Hha0 : heap_agrees hA (w_refs (oc_world (oc_unit oc0))))
    by (destruct oc0 as [[] ?|? ?]; exact HhaA).
  destruct (unwind_heap fuel ds (oc_unit oc0) result Erd ucap pA
              (fun _ => nil) hA (fun t => Nat.eqb t 0) trA
              (nil ++ map (fun e => (0, e)) evs0) dfA (fun _ => None) nil
              eq_refl HprogA' Hq0 Hha0 HdfA')
    as [pB [hB [trB [dfB [paB [evs1 [HusB [HprogB [HqB [HdfB [HhaB Hout1]]]]]]]]]]].
  (* relate [result] to run_cmd's [oc] *)
  assert (Hoc : ocpanic oc = ocpanic result
                /\ oc_world oc = oc_world result).
  { destruct result as [[] w' | v w']; cbn in H; injection H as <-.
    - (* result returns: the body cannot have panicked (a panic seed never returns) *)
      destruct oc0 as [[] w0 | v0 w0].
      + split; reflexivity.
      + exfalso.
        destruct (run_defers_panic_stays fuel ds v0 w0 (ORet tt w') Erd) as [? [? Hcontra]].
        discriminate Hcontra.
    - cbn [ocpanic oc_world]. split; reflexivity. }
  destruct Hoc as [Hocp Hocw].
  (* the final done step per the 2-mode *)
  destruct HprogB as [HretB | [v HpanB]].
  - exists (mkUCfg pB (fun _ => nil) hB (upd (fun t => Nat.eqb t 0) 0 false) trB
                   ((nil ++ map (fun e => (0, e)) evs0) ++ map (fun e => (0, e)) evs1) dfB paB).
    split; [ | split; [ apply upd_same | split; [ | split ] ] ].
    + unfold ustart_w. eapply usteps_trans; [ exact HusA | ].
      eapply usteps_trans; [ exact HusB | ].
      eapply usteps_step;
        [ eapply ustep_ret_done with (tid := 0); [ reflexivity | exact HretB | exact HdfB ] | apply usteps_refl ].
    + cbn [uc_panic]. rewrite Hocp, <- HqB, HretB. reflexivity.
    + cbn [uc_out]. rewrite Hocw, Hout1.
      assert (Hw0 : oc_world (oc_unit oc0) = oc_world oc0) by (destruct oc0; reflexivity).
      rewrite Hw0, Hout0, !map_app, map_snd_pair0. cbn [app map].
      rewrite map_snd_pair0, <- app_assoc. reflexivity.
    + cbn [uc_heap]. rewrite Hocw. exact HhaB.
  - exists (mkUCfg pB (fun _ => nil) hB (upd (fun t => Nat.eqb t 0) 0 false) trB
                   ((nil ++ map (fun e => (0, e)) evs0) ++ map (fun e => (0, e)) evs1) dfB
                   (upd paB 0 (Some v))).
    split; [ | split; [ apply upd_same | split; [ | split ] ] ].
    + unfold ustart_w. eapply usteps_trans; [ exact HusA | ].
      eapply usteps_trans; [ exact HusB | ].
      eapply usteps_step;
        [ eapply ustep_pan_done with (tid := 0); [ reflexivity | exact HpanB | exact HdfB ] | apply usteps_refl ].
    + cbn [uc_panic]. rewrite upd_same, Hocp, <- HqB, HpanB. reflexivity.
    + cbn [uc_out]. rewrite Hocw, Hout1.
      assert (Hw0 : oc_world (oc_unit oc0) = oc_world oc0) by (destruct oc0; reflexivity).
      rewrite Hw0, Hout0, !map_app, map_snd_pair0. cbn [app map].
      rewrite map_snd_pair0, <- app_assoc. reflexivity.
    + cbn [uc_heap]. rewrite Hocw. exact HhaB.
Qed.

(** The NEGATIVE witness for the quarantine: an unallocated read has NO completing run at ANY
    fuel — so no unconditional (premise-free) bridge over heap commands can exist; the agreement
    for heap programs must carry allocation/completion premises, as [bridge_heap_agrees]'s
    [run_cmd]-completion premise does. *)
Example cread_unallocated_absent : forall fuel w,
  w_refs w 0 = None ->
  run_cmd fuel (CRead 0 (fun _ => CRet tt)) w = None.
Proof. intros fuel w H. unfold run_cmd. cbn [go]. rewrite H. reflexivity. Qed.

End BridgeVal.

(** The EXACT gated public-surface set for this module is the [Print Assumptions] lines below — the SINGLE
    zero-axiom authority (the Docker manifest gate scrapes their [Axioms:] report, which must be empty).  A
    [Print Assumptions] audits its whole dependency CONE, so EVERY Local definition here is covered TRANSITIVELY
    through some public theorem's cone, not separately printed: the [go]-grounded [run_defers] plumbing feeds
    the [run_cmd_*] properties, and the semantic Phase A + seed-linearity + unwind machinery ([body_runs_sem] /
    [run_defers_seed_linear] / [unwind_heap] / [pop_defer_step]) is CONSUMED by the bridge
    [bridge_heap_agrees]. *)
Print Assumptions cmd_to_ucmd_fragment.
Print Assumptions cmd_to_ucmd_novz.
Print Assumptions bridge_heap_agrees.
Print Assumptions run_cmd_out_monotone.
Print Assumptions run_cmd_no_panic_ret.
