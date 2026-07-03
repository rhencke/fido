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

    The module exposes TWO single-goroutine [usteps] AGREEMENT bridges: [bridge_agrees] — every
    [no_heap] [c] (arbitrary defer nesting, any panics) agrees with cmd.v's AUTHORITATIVE
    [run_cmd] (output appended, [uc_panic 0] = the Outcome's panic; the LIFO defer forest
    unwinds under the (prog, pa) 2-mode; completion discharged by [run_cmd_terminates]) — and
    [bridge_heap_body_agrees] — DEFER-FREE heap commands agree end to end INCLUDING final heaps,
    from the [ustart_w] mirrored-heap start.  DEFERRED heap commands are translated but not yet
    under an agreement (the unwind, then the general conditional heap bridge, remain —
    plans/bridge-effects.md).  Plus cmd.v-side properties for a COMPLETING [run_cmd] on ANY [c]
    (heap ops included): output only APPENDS, and a panic-free completing run returns [ORet].
    The EXACT gated public-surface set is the [Print Assumptions] block at the end of this file (the single in-file
    authority); this header does not re-enumerate it.
    There is NO public projection-observer theorem: the [cmd_out_events]/[cmd_panic]/[cmd_defers] projections,
    their [run_cmd] seal ([go_chars]), and the unified-side run/unwind lemmas are LOCAL (file-private) proof
    plumbing — no exported theorem concludes with them, so a consumer cannot prove bridge facts against a free
    observer instead of [run_cmd].  (No concurrency ops in this fragment, so [uc_bufs]/[uc_trace] are
    untouched; [uc_heap] carries the heap commands' effects, bridged on the defer-free fragment.)
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
    [bridge_agrees] lives), [cmd_to_ucmd]'s image contains NOTHING that can bind the
    calculus' [vzero] parameter or the [vz]-defaulted start heap: no [URead] (the start
    heap defaults to [vz]), no [URecv]/[USelect] (the closed-recv rules bind [vzero]), no
    channel/spawn forms.  THIS licenses the quantified [vz] for the [no_heap] statements
    ([bridge_agrees] and its consumers; the heap bridge [bridge_heap_body_agrees] carries
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
    below UNIVERSALLY QUANTIFIES it (section generalization), each with its OWN license:
    [bridge_agrees] (and the other [no_heap] statements) never reach a [vz]-consulting rule
    ([cmd_to_ucmd_novz]); [bridge_heap_body_agrees] starts from the [ustart_w] heap that MIRRORS
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

Definition ustart (u : UCmdG) : UConfig :=
  mkUCfg (fun t => if Nat.eqb t 0 then u else URet)
         (fun _ => nil) (fun _ => vz) (fun t => Nat.eqb t 0) nil nil (fun _ => nil) (fun _ => None).
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

(** ---- LOCAL proof plumbing (file-private — not exported, not gated; no PUBLIC theorem concludes with these) ----
    The output EVENTS / final panic [c] emits on the defer-free fragment, and their SEAL to cmd.v's authority. *)
Local Fixpoint cmd_out_events (c : Cmd unit) : list (bool * list GoAny) :=
  match c with
  | CRet _      => []
  | COut b xs c' => (b, xs) :: cmd_out_events c'
  | CPan _      => []
  | CDfr _ c'   => cmd_out_events c'
  | CWrite _ _ c' => cmd_out_events c'   (* dead: every consumer carries a [no_heap]-entailing premise *)
  | CRead _ _   => []                    (* dead: no syntactic projection exists under the binder *)
  end.
Local Fixpoint cmd_panic (c : Cmd unit) : option GoAny :=
  match c with
  | CRet _      => None
  | COut _ _ c' => cmd_panic c'
  | CPan v      => Some v
  | CDfr _ c'   => cmd_panic c'
  | CWrite _ _ c' => cmd_panic c'        (* dead: see [cmd_out_events] *)
  | CRead _ _   => None                  (* dead: see [cmd_out_events] *)
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
  | CWrite _ _ c' => cmd_defers c'       (* dead: see [cmd_out_events] *)
  | CRead _ _   => []                    (* dead: see [cmd_out_events] *)
  end.
Local Lemma cmd_defers_no_defer : forall c, no_defer c = true -> cmd_defers c = [].
Proof.
  intros c.
  induction c as [a | bo xs c' IH | v | d c' IHc' | l v c' IH | l f IH] using Cmd_rect';
    intros Hnd; cbn in *;
    [ reflexivity | exact (IH Hnd) | reflexivity | discriminate Hnd
    | discriminate Hnd | discriminate Hnd ].
Qed.

Local Lemma cmd_defers_no_heap : forall c, no_heap c = true -> no_heap_all (cmd_defers c) = true.
Proof.
  intros c.
  induction c as [a | bo xs c' IH | v | d c' IHc' | l v c' IH | l f IH] using Cmd_rect';
    intro Hnh; cbn [no_heap cmd_defers no_heap_all] in *;
    try reflexivity; try exact (IH Hnh); try discriminate Hnh.
  apply Bool.andb_true_iff in Hnh. destruct Hnh as [Hd Hc'].
  rewrite no_heap_all_app. cbn [no_heap_all]. rewrite (IHc' Hc'), Hd. reflexivity.
Qed.

Local Lemma w_output_w_log : forall b xs w, w_output (w_log b xs w) = w_output w ++ ((b, xs) :: nil).
Proof. reflexivity. Qed.

(** GROUNDING in cmd.v's authoritative [go]: the three projections ARE [go]'s own components — for any [no_heap] [c]
    (defers included), [go c w] returns exactly [(<outcome from cmd_panic c>, cmd_defers c)] with the body's
    world advanced by [cmd_out_events c].  So [cmd_panic]/[cmd_out_events]/[cmd_defers] are not a parallel
    authority that could drift from [go]; they are derived NAMES for [go]'s behaviour.  [run_cmd_seals_events]
    (the no_defer seal) and Phase A ([cmd_to_ucmd_body_runs]) build on this. *)
Local Lemma go_chars : forall c w, no_heap c = true -> exists w',
  go c w = Some ((match cmd_panic c with None => ORet tt w' | Some v => OPanic v w' end), cmd_defers c)
  /\ w_output w' = w_output w ++ cmd_out_events c.
Proof.
  intros c. induction c as [a | bo xs c' IH | v | d c' IHc' | l v c' IH | l f IH] using Cmd_rect';
    intros w Hnh; cbn [no_heap] in Hnh.
  - destruct a. exists w. cbn [go cmd_panic cmd_defers cmd_out_events]. rewrite app_nil_r. split; reflexivity.
  - cbn [go cmd_panic cmd_defers cmd_out_events].
    destruct (IH (w_log bo xs w) Hnh) as [w' [Hgo Hout]]. exists w'. rewrite Hgo. split;
      [ reflexivity | rewrite Hout, w_output_w_log, <- app_assoc; reflexivity ].
  - exists w. cbn [go cmd_panic cmd_defers cmd_out_events]. rewrite app_nil_r. split; reflexivity.
  - apply Bool.andb_true_iff in Hnh. destruct Hnh as [_ Hnh].
    cbn [go cmd_panic cmd_defers cmd_out_events].
    destruct (IHc' w Hnh) as [w' [Hgo Hout]]. exists w'. rewrite Hgo. cbn. split; [ reflexivity | exact Hout ].
  - discriminate Hnh.
  - discriminate Hnh.
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
  intros c w Hnd. destruct (go_chars c w (no_defer_no_heap c Hnd)) as [w' [Hgo Hout]].
  exists w'. split; [ | exact Hout ].
  unfold run_cmd. rewrite Hgo, (cmd_defers_no_defer c Hnd). destruct (cmd_panic c); reflexivity.
Qed.

(** Phase A of the defer bridge (general — NO [no_defer]): [ustep] runs [cmd_to_ucmd c]'s BODY to its outcome,
    accumulating its deferred actions onto goroutine 0's [uc_defers] stack in [go]'s order — leaving [prog 0] at
    [URet] / [UPan v] (per [cmd_panic c]) and [df' 0] = [map cmd_to_ucmd (cmd_defers c) ++ df 0].  The goroutine
    is NOT yet finished ([lv], [pa] untouched); the stack-UNWINDING ([run_defers]) is Phase B (done for any [no_heap] [c] —
    arbitrary nesting, any panics — in [bridge_agrees] via [unwind_prefix_panic]).  This
    is the [ustep] analogue of cmd.v's [go] — and faithfully so: [go_chars] proves the [cmd_panic c] /
    [cmd_out_events c] / [cmd_defers c] this conclusion uses ARE exactly [go c w]'s outcome / body output / defer
    list, so the simulation is grounded in cmd.v's authority, not a parallel projection.  [cmd_to_ucmd_runs] below
    specialises it to the [no_defer] fragment (then a single [ret_done]/[pan_done] finishes goroutine 0). *)
Local Lemma cmd_to_ucmd_body_runs : forall c ucap p b h lv tr o df pa,
  no_heap c = true ->
  lv 0 = true -> p 0 = cmd_to_ucmd c ->
  exists (p' : nat -> UCmdG) (df' : nat -> list UCmdG),
    usteps vz ucap (mkUCfg p b h lv tr o df pa)
                (mkUCfg p' b h lv tr (o ++ map (fun e => (0, e)) (cmd_out_events c)) df' pa)
    /\ p' 0 = (match cmd_panic c with None => URet | Some v => UPan v end)
    /\ df' 0 = map cmd_to_ucmd (cmd_defers c) ++ df 0.
Proof.
  intros c. induction c as [a | bo xs c' IH | v | d c' IHc' | l v c' IH | l f IH] using Cmd_rect';
    intros ucap p b h lv tr o df pa Hnh Hlv Hp; cbn [no_heap] in Hnh.
  - cbn [cmd_to_ucmd cmd_out_events cmd_panic cmd_defers] in *.
    exists p, df. rewrite app_nil_r. split; [ apply usteps_refl | split; [ exact Hp | reflexivity ] ].
  - cbn [cmd_to_ucmd cmd_out_events cmd_panic cmd_defers] in *.
    destruct (IH ucap (upd p 0 (cmd_to_ucmd c')) b h lv tr (o ++ [(0, (bo, xs))]) df pa
                  Hnh Hlv (upd_same _ _ _)) as [p' [df' [Hus [Hprog Hdf]]]].
    exists p', df'. split; [ | split; [ exact Hprog | exact Hdf ] ].
    replace (o ++ map (fun e => (0, e)) ((bo, xs) :: cmd_out_events c'))
       with ((o ++ [(0, (bo, xs))]) ++ map (fun e => (0, e)) (cmd_out_events c'))
      by (cbn [map]; rewrite <- app_assoc; reflexivity).
    eapply usteps_step; [ eapply ustep_out; [exact Hlv | exact Hp] | exact Hus ].
  - cbn [cmd_to_ucmd cmd_out_events cmd_panic cmd_defers] in *.
    exists p, df. rewrite app_nil_r. split; [ apply usteps_refl | split; [ exact Hp | reflexivity ] ].
  - apply Bool.andb_true_iff in Hnh. destruct Hnh as [_ Hnh].
    cbn [cmd_to_ucmd cmd_out_events cmd_panic cmd_defers] in *.
    destruct (IHc' ucap (upd p 0 (cmd_to_ucmd c')) b h lv tr o (upd df 0 (cmd_to_ucmd d :: df 0)) pa
                  Hnh Hlv (upd_same _ _ _)) as [p' [df' [Hus [Hprog Hdf]]]].
    exists p', df'. split; [ | split; [ exact Hprog | ] ].
    + eapply usteps_step; [ eapply ustep_defer; [exact Hlv | exact Hp] | exact Hus ].
    + rewrite Hdf, upd_same, map_app. cbn [map]. rewrite <- app_assoc. reflexivity.
  - discriminate Hnh.
  - discriminate Hnh.
Qed.

(** the unified-side run on the [no_defer] fragment — now a SPECIALISATION of [cmd_to_ucmd_body_runs]: the body
    leaves [df' 0 = []] (since [cmd_defers c = []] when [no_defer]), so a single [ret_done] / [pan_done] finishes
    goroutine 0.  [df'] is now an EXISTENTIAL threaded from the body run (the projections [uc_live]/[uc_out]/
    [uc_panic] never read it). *)
Local Lemma cmd_to_ucmd_runs : forall c,
  no_defer c = true ->
  forall (ucap : nat -> option nat) p b h lv tr o df pa,
    lv 0 = true -> p 0 = cmd_to_ucmd c -> df 0 = [] -> pa 0 = None ->
    exists (p' : nat -> UCmdG) (lv' : nat -> bool) (pa' : nat -> option GoAny) (df' : nat -> list UCmdG),
      usteps vz ucap (mkUCfg p b h lv tr o df pa)
                  (mkUCfg p' b h lv' tr (o ++ map (fun e => (0, e)) (cmd_out_events c)) df' pa')
      /\ lv' 0 = false
      /\ pa' 0 = cmd_panic c.
Proof.
  intros c Hnd ucap p b h lv tr o df pa Hlv Hp Hdf Hpa.
  destruct (cmd_to_ucmd_body_runs c ucap p b h lv tr o df pa (no_defer_no_heap c Hnd) Hlv Hp) as [p' [df' [Hus [Hprog Hdf']]]].
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
    usteps vz ucap (ustart (cmd_to_ucmd c)) uc
    /\ run_cmd 1 c w = Some oc
    /\ uc_live uc 0 = false
    /\ w_output (oc_world oc) = w_output w ++ map snd (uc_out uc)
    /\ uc_panic uc 0 = ocpanic oc.
Proof.
  intros c ucap w Hnd.
  destruct (cmd_to_ucmd_runs c Hnd ucap
              (fun t => if Nat.eqb t 0 then cmd_to_ucmd c else URet)
              (fun _ => nil) (fun _ => vz) (fun t => Nat.eqb t 0) nil nil (fun _ => nil) (fun _ => None)
              eq_refl eq_refl eq_refl eq_refl) as [p' [lv' [pa' [df' [Hus [Hdone Hpan]]]]]].
  destruct (run_cmd_seals_events c w Hnd) as [w' [Hrun Hout]].
  exists (mkUCfg p' (fun _ => nil) (fun _ => vz) lv' nil
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

(** [oc_set_world] only advances the world — it preserves the [Outcome]'s panic status (and sets its world). *)
Local Lemma ocpanic_set_world : forall (acc : Outcome unit) w, ocpanic (oc_set_world acc w) = ocpanic acc.
Proof. intros [[] w0 | v w0] w; reflexivity. Qed.
Local Lemma oc_world_set_world : forall (acc : Outcome unit) w, oc_world (oc_set_world acc w) = w.
Proof. intros [[] w0 | v w0] w; reflexivity. Qed.

(** run_defers is OUTPUT-MONOTONE for ARBITRARY nesting: unwinding a defer list only ever APPENDS to the
    world's output trace (each deferred body's [cmd_out_events] and, recursively, its own nested defers'),
    never RETRACTS.  Grounded in [go_chars] (each [go d] appends [cmd_out_events d]); induction on FUEL, the IH
    applied to the nested run ([cmd_defers d]) and the tail ([ds']).  Note [oc_world acc'] = [oc_world net_d]
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

(** ---- The PANIC characterization (the panic-side analog of [run_defers_out]'s output-APPEND law).  Where
    output only grows, the active PANIC is THREADED: unwinding the LIFO defer forest, a (nested) defer whose net
    outcome PANICS REPLACES the active panic, one that RETURNS KEEPS it — so the final panic is the LAST one
    raised.  [nested_defers_panic] is that single-accumulator threading, recursing into each defer's OWN
    [cmd_defers].  It is NOT a second authority:
    [run_defers_panic_eq] proves [run_defers] REALIZES it at the SAME fuel, so it merely NAMES which panic wins. *)
Local Fixpoint nested_defers_panic (fuel : nat) (ds : list (Cmd unit)) (p0 : option GoAny) : option (option GoAny) :=
  match fuel with
  | O => None
  | S n =>
    match ds with
    | nil => Some p0
    | d :: ds' =>
        match nested_defers_panic n (cmd_defers d) (cmd_panic d) with   (* d's NET panic, seeded by its body's *)
        | None => None
        | Some pd => nested_defers_panic n ds' (match pd with Some v => Some v | None => p0 end)
        end                                                             (* d panicked -> REPLACE [p0]; else KEEP *)
    end
  end.

(** A Some-seed yields a Some-result: a panic in flight is never LOST (a returning defer keeps it, a panicking
    one replaces it with another Some) — the forward companion to [run_defers_no_panic]. *)
Local Lemma nested_defers_panic_some : forall f ds v r,
  nested_defers_panic f ds (Some v) = Some r -> exists v', r = Some v'.
Proof.
  induction f as [| n IH]; intros ds v r H; [ discriminate H | ].
  destruct ds as [| d ds']; cbn [nested_defers_panic] in H.
  - injection H as <-. exists v. reflexivity.
  - destruct (nested_defers_panic n (cmd_defers d) (cmd_panic d)) as [pd|]; [ | discriminate H ].
    destruct pd as [v'|]; [ exact (IH ds' v' r H) | exact (IH ds' v r H) ].
Qed.

(** [run_defers] REALIZES [nested_defers_panic] at the SAME fuel: its final panic is exactly the flattened
    last-raised panic.  Induction on FUEL, mirroring [run_defers_out] — IH on the nested run ([cmd_defers d],
    seeded [cmd_panic d]) and the tail ([ds']); the tail's seed [acc']'s panic is [Some (panic net_d)] if [d]
    panicked else [ocpanic acc], exactly [nested_defers_panic]'s [match pd ...] step. *)
Local Lemma run_defers_panic_eq : forall fuel ds acc result,
  no_heap_all ds = true ->
  run_defers fuel ds acc = Some result ->
  nested_defers_panic fuel ds (ocpanic acc) = Some (ocpanic result).
Proof.
  induction fuel as [| n IH]; intros ds acc result Hnh H; [ discriminate H | ].
  destruct ds as [| d ds'].
  - cbn in H |- *. injection H as <-. reflexivity.
  - cbn [no_heap_all] in Hnh. apply Bool.andb_true_iff in Hnh. destruct Hnh as [Hd Hds'].
    rewrite run_defers_unfold in H.
    destruct (go_chars d (oc_world acc) Hd) as [w_d [Hgo _]]. rewrite Hgo in H. cbn zeta in H.
    destruct (run_defers n (cmd_defers d)
                (match cmd_panic d with None => ORet tt w_d | Some v => OPanic v w_d end)) as [net_d|] eqn:Enet;
      [ | discriminate H ].
    assert (Hseed : ocpanic (match cmd_panic d with None => ORet tt w_d | Some v => OPanic v w_d end) = cmd_panic d)
      by (destruct (cmd_panic d); reflexivity).
    pose proof (IH (cmd_defers d) _ net_d (cmd_defers_no_heap d Hd) Enet) as Hnest.
    rewrite Hseed in Hnest.
    pose proof (IH ds' _ result Hds' H) as Htail.
    cbn [nested_defers_panic]. rewrite Hnest.
    replace (match ocpanic net_d with Some v => Some v | None => ocpanic acc end)
       with (ocpanic (match net_d with OPanic v' w' => OPanic v' w' | ORet _ w' => oc_set_world acc w' end));
      [ exact Htail | destruct net_d as [[] w' | v' w']; cbn [ocpanic]; [ rewrite ocpanic_set_world | ]; reflexivity ].
Qed.

(** SEED-LINEARITY for [nested_defers_panic]: the flatten from ANY seed [p0] = the flatten from [None] (the panic
    PURELY from the defers), or [p0] if the defers raise none.  This is the bridge the nested-panic unwind needs:
    the ustep threads the ENCLOSING panic CARRIED-IN through each nested run, whereas [run_defers] /
    [nested_defers_panic] seed each nested run FRESH then re-apply — seed-linearity reconciles the two.  Induction
    on fuel; the [cons] step uses the IH TWICE on the tail (seeds [pd or p0] and [pd]) and the associativity
    [r or (pd or p0) = (r or pd) or p0] of the last-panic-wins combine. *)
Local Lemma nested_defers_panic_seed : forall f ds p0,
  nested_defers_panic f ds p0
    = match nested_defers_panic f ds None with
      | None => None
      | Some q => Some (match q with Some v => Some v | None => p0 end)
      end.
Proof.
  induction f as [| n IH]; intros ds p0; [ reflexivity | ].
  destruct ds as [| d ds']; [ reflexivity | ].
  cbn [nested_defers_panic].
  destruct (nested_defers_panic n (cmd_defers d) (cmd_panic d)) as [pd|] eqn:Ecd; [ | reflexivity ].
  replace (match pd with Some v => Some v | None => None end) with pd by (destruct pd; reflexivity).
  rewrite (IH ds' (match pd with Some v => Some v | None => p0 end)), (IH ds' pd).
  destruct (nested_defers_panic n ds' None) as [r|]; [ | reflexivity ].
  destruct r as [rv|]; destruct pd as [pv|]; reflexivity.
Qed.

(** [cmd_no_panic] (cmd.v's panic-freedom predicate) implies the body has no in-flight panic — relates it to the
    Local [cmd_panic]; feeds the panic-free run properties below. *)
Local Lemma cmd_no_panic_cmd_panic : forall c, cmd_no_panic c = true -> cmd_panic c = None.
Proof.
  intros c.
  induction c as [a | bo xs c' IH | v | d c' IHc' | l v c' IH | l f IH] using Cmd_rect';
    intros Hnp; cbn in *;
    [ reflexivity | exact (IH Hnp) | discriminate Hnp
    | apply andb_prop in Hnp; exact (IHc' (proj2 Hnp))
    | discriminate Hnp | discriminate Hnp ].
Qed.

(** Under [cmd_no_panic] every deferred action [go] accumulates is itself [cmd_no_panic] (the defer forest is
    panic-free too). *)
Local Lemma cmd_no_panic_defers : forall c,
  cmd_no_panic c = true -> Forall (fun d => cmd_no_panic d = true) (cmd_defers c).
Proof.
  intros c.
  induction c as [a | bo xs c' IH | v | d c' IHc' | l v c' IH | l f IH] using Cmd_rect';
    intros Hnp; cbn in *.
  - constructor.
  - exact (IH Hnp).
  - discriminate Hnp.
  - apply andb_prop in Hnp as [Hnpd Hnpc'].
    apply Forall_app; split; [ exact (IHc' Hnpc') | constructor; [ exact Hnpd | constructor ] ].
  - discriminate Hnp.
  - discriminate Hnp.
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
    destruct (go_chars d (oc_world acc) (cmd_no_panic_no_heap d Hnp)) as [w_d [Hgo Hout]].
    rewrite Hgo in H. cbn zeta in H.
    replace (match cmd_panic d with None => ORet tt w_d | Some v => OPanic v w_d end)
       with (ORet tt w_d) in H by (rewrite (cmd_no_panic_cmd_panic d Hnp); reflexivity).
    destruct (run_defers n (cmd_defers d) (ORet tt w_d)) as [net_d|] eqn:Enet; [ | discriminate H ].
    assert (Hnet : ocpanic net_d = None)
      by exact (IH (cmd_defers d) (ORet tt w_d) net_d Enet (cmd_no_panic_defers d Hnp) eq_refl).
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

(** ustep-side for NESTED defers WITH PANICS (arbitrary depth) — the general unwind combining a (prog, pa) 2-mode
    (a defer's panic rides in [prog] as [UPan v] until the next pop moves it into [pa], a later panic superseding
    it) with a fuel/[ds_tail] recursion over the nested defer forest.  Given [run_defers fuel ds acc = Some
    result] (world delta + fuel) and [nested_defers_panic fuel ds q0 = Some val] (the flattened panic from the
    current in-flight [q0]), the ustep unwinds the FRONT [ds] down to [ds_tail], threading the in-flight panic to
    [val] and advancing output by [run_defers]'s delta.  CRUX: the ustep threads [q0] CARRIED-IN through each
    nested run, whereas [nested_defers_panic] seeds nested runs FRESH — reconciled by [nested_defers_panic_seed]
    (the post-body in-flight [cmd_panic d or q0] and the tail seed [pd or q0] agree via combine-associativity). *)
Local Lemma unwind_prefix_panic : forall fuel ds acc result q0 val,
  no_heap_all ds = true ->
  run_defers fuel ds acc = Some result ->
  nested_defers_panic fuel ds q0 = Some val ->
  forall ucap p b h lv tr o df pa ds_tail,
    lv 0 = true ->
    (p 0 = URet \/ exists v, p 0 = UPan v) ->
    (match p 0 with UPan v => Some v | _ => pa 0 end) = q0 ->
    df 0 = map cmd_to_ucmd ds ++ map cmd_to_ucmd ds_tail ->
    exists (p' : nat -> UCmdG) (df' : nat -> list UCmdG) (pa' : nat -> option GoAny) evs,
      usteps vz ucap (mkUCfg p b h lv tr o df pa)
                  (mkUCfg p' b h lv tr (o ++ map (fun e => (0, e)) evs) df' pa')
      /\ (p' 0 = URet \/ exists v, p' 0 = UPan v)
      /\ (match p' 0 with UPan v => Some v | _ => pa' 0 end) = val
      /\ df' 0 = map cmd_to_ucmd ds_tail
      /\ w_output (oc_world result) = w_output (oc_world acc) ++ evs.
Proof.
  induction fuel as [| n IH]; intros ds acc result q0 val Hnhds Hrd Hnp
    ucap p b h lv tr o df pa ds_tail Hlv Hp Hq0 Hdf; [ discriminate Hrd | ].
  destruct ds as [| d ds'].
  - cbn in Hrd. injection Hrd as <-. cbn [nested_defers_panic] in Hnp. injection Hnp as <-.
    cbn [map] in Hdf. rewrite app_nil_l in Hdf.
    exists p, df, pa, nil. cbn [map]. rewrite !app_nil_r.
    split; [ apply usteps_refl | split; [ exact Hp | split; [ exact Hq0 | split; [ exact Hdf | reflexivity ] ] ] ].
  - cbn [no_heap_all] in Hnhds. apply Bool.andb_true_iff in Hnhds. destruct Hnhds as [Hd Hds'].
    rewrite run_defers_unfold in Hrd.
    destruct (go_chars d (oc_world acc) Hd) as [w_d [Hgo Hout]]. rewrite Hgo in Hrd. cbn zeta in Hrd.
    destruct (run_defers n (cmd_defers d)
                (match cmd_panic d with None => ORet tt w_d | Some v => OPanic v w_d end)) as [net_d|] eqn:Enet;
      [ | discriminate Hrd ].
    cbn [nested_defers_panic] in Hnp.
    destruct (nested_defers_panic n (cmd_defers d) (cmd_panic d)) as [pd|] eqn:Ecd; [ | discriminate Hnp ].
    rewrite (nested_defers_panic_seed n (cmd_defers d) (cmd_panic d)) in Ecd.
    destruct (nested_defers_panic n (cmd_defers d) None) as [q_cd|] eqn:ENd; [ | discriminate Ecd ].
    injection Ecd as Hpd.
    cbn [map] in Hdf.
    destruct (pop_defer_step ucap p b h lv tr o df pa d
                (map cmd_to_ucmd ds' ++ map cmd_to_ucmd ds_tail) q0 Hlv Hp Hq0 Hdf) as [paP [HpaP Hpop]].
    destruct (cmd_to_ucmd_body_runs d ucap (upd p 0 (cmd_to_ucmd d)) b h lv tr o
                (upd df 0 (map cmd_to_ucmd ds' ++ map cmd_to_ucmd ds_tail)) paP Hd Hlv (upd_same _ _ _))
      as [pA [dfA [HusA [HprogA HdfA]]]].
    rewrite upd_same in HdfA.
    assert (Hq1 : (match pA 0 with UPan v => Some v | _ => paP 0 end)
                  = match cmd_panic d with Some v => Some v | None => q0 end)
      by (rewrite HprogA, HpaP; destruct (cmd_panic d); reflexivity).
    assert (HprogA' : pA 0 = URet \/ exists v, pA 0 = UPan v)
      by (rewrite HprogA; destruct (cmd_panic d) as [vd|]; [ right; exists vd; reflexivity | left; reflexivity ]).
    assert (HdfA' : dfA 0 = map cmd_to_ucmd (cmd_defers d) ++ map cmd_to_ucmd (ds' ++ ds_tail))
      by (rewrite HdfA, map_app; reflexivity).
    assert (Hnp1 : nested_defers_panic n (cmd_defers d)
                     (match cmd_panic d with Some v => Some v | None => q0 end)
                   = Some (match q_cd with Some v => Some v
                           | None => match cmd_panic d with Some v => Some v | None => q0 end end)).
    { rewrite (nested_defers_panic_seed n (cmd_defers d)
                (match cmd_panic d with Some v => Some v | None => q0 end)), ENd. reflexivity. }
    destruct (IH (cmd_defers d)
                 (match cmd_panic d with None => ORet tt w_d | Some v => OPanic v w_d end) net_d
                 (match cmd_panic d with Some v => Some v | None => q0 end)
                 (match q_cd with Some v => Some v
                  | None => match cmd_panic d with Some v => Some v | None => q0 end end)
                 (cmd_defers_no_heap d Hd) Enet Hnp1
                 ucap pA b h lv tr (o ++ map (fun e => (0, e)) (cmd_out_events d)) dfA paP (ds' ++ ds_tail)
                 Hlv HprogA' Hq1 HdfA')
      as [pB [dfB [paB [evs1 [HusB [HprogB [Hval1 [HdfB Hw1]]]]]]]].
    assert (Hq2 : (match q_cd with Some v => Some v
                   | None => match cmd_panic d with Some v => Some v | None => q0 end end)
                  = match pd with Some v => Some v | None => q0 end)
      by (rewrite <- Hpd; destruct q_cd as [qv|]; reflexivity).
    rewrite Hq2 in Hval1.
    assert (HdfB' : dfB 0 = map cmd_to_ucmd ds' ++ map cmd_to_ucmd ds_tail)
      by (rewrite HdfB, map_app; reflexivity).
    destruct (IH ds'
                 (match net_d with OPanic v' w' => OPanic v' w' | ORet _ w' => oc_set_world acc w' end) result
                 (match pd with Some v => Some v | None => q0 end) val
                 Hds' Hrd Hnp
                 ucap pB b h lv tr ((o ++ map (fun e => (0, e)) (cmd_out_events d)) ++ map (fun e => (0, e)) evs1)
                 dfB paB ds_tail Hlv HprogB Hval1 HdfB')
      as [pC [dfC [paC [evs2 [HusC [HprogC [Hval2 [HdfC Hw2]]]]]]]].
    exists pC, dfC, paC, (cmd_out_events d ++ evs1 ++ evs2).
    split; [ | split; [ exact HprogC | split; [ exact Hval2 | split; [ exact HdfC | ] ] ] ].
    + replace (o ++ map (fun e => (0, e)) (cmd_out_events d ++ evs1 ++ evs2))
         with (((o ++ map (fun e => (0, e)) (cmd_out_events d)) ++ map (fun e => (0, e)) evs1)
                 ++ map (fun e => (0, e)) evs2)
        by (rewrite !map_app, !app_assoc; reflexivity).
      eapply usteps_trans; [ exact Hpop | ].
      eapply usteps_trans; [ exact HusA | ].
      eapply usteps_trans; [ exact HusB | exact HusC ].
    + rewrite Hw2.
      assert (Hwacc' : w_output (oc_world (match net_d with OPanic v' w' => OPanic v' w'
                                            | ORet _ w' => oc_set_world acc w' end)) = w_output (oc_world net_d))
        by (destruct net_d as [[] w_net | v' w_net]; cbn [oc_world]; [ rewrite oc_world_set_world | ]; reflexivity).
      rewrite Hwacc', Hw1.
      assert (Hwd : oc_world (match cmd_panic d with None => ORet tt w_d | Some v => OPanic v w_d end) = w_d)
        by (destruct (cmd_panic d); reflexivity).
      rewrite Hwd, Hout, <- !app_assoc. reflexivity.
Qed.

(** OUTPUT-MONOTONICITY of [run_cmd], for ANY [c] (arbitrary defer nesting, heap ops included —
    a write never touches [w_output]): a
    COMPLETING run ([run_cmd fuel c w = Some oc]) only ever APPENDS to the world's output (the body's
    [cmd_out_events c] then, via [run_defers_out], every defer's, recursively), never RETRACTS.  A cmd.v-side
    faithfulness guarantee — Go's deferred actions and
    panics cannot un-print already-printed output.  A standalone cmd.v-side property (distinct from the ustep
    AGREEMENT bridges), via [run_defers_out].  The general bridge [bridge_agrees] establishes its output agreement
    independently through [unwind_prefix_panic], so this theorem is a sibling, not a dependency, of the bridge. *)
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
    returns [ORet] — Go's panic-free program cannot end in a panic.  Via [go_chars] (the body is [ORet], as
    [cmd_no_panic c ⇒ cmd_panic c = None]) + [run_defers_no_panic] (the defers preserve it).  A standalone
    cmd.v-side property, panic-free companion to [run_cmd_out_monotone] (via [run_defers_no_panic]); the general
    bridge [bridge_agrees] separately proves every [no_heap] [c] agrees with [ustep] (this panic-free case included), not
    resting on this theorem. *)
Theorem run_cmd_no_panic_ret : forall fuel (c : Cmd unit) w oc,
  run_cmd fuel c w = Some oc -> cmd_no_panic c = true ->
  exists w', oc = ORet tt w'.
Proof.
  intros fuel c w oc H Hnp.
  destruct (go_chars c w (cmd_no_panic_no_heap c Hnp)) as [w_body [Hgo Hout]].
  unfold run_cmd in H. rewrite Hgo in H. rewrite (cmd_no_panic_cmd_panic c Hnp) in H. cbn [oc_unit] in H.
  destruct (run_defers fuel (cmd_defers c) (ORet tt w_body)) as [result|] eqn:Erd; [ | discriminate H ].
  assert (Hres : ocpanic result = None)
    by exact (run_defers_no_panic fuel (cmd_defers c) (ORet tt w_body) result Erd (cmd_no_panic_defers c Hnp) eq_refl).
  destruct result as [[] w' | v w']; cbn [ocpanic] in Hres; [ | discriminate Hres ].
  cbn in H. injection H as <-. exists w'. reflexivity.
Qed.

(** LOCAL plumbing (NOT a public surface — its statement names the Local projections [nested_defers_panic] /
    [cmd_defers] / [cmd_panic], so it is Local; CONSUMED by [bridge_agrees], which ties the ustep's
    flatten-threading to [run_cmd]'s Outcome): a COMPLETED [run_cmd] ends with EXACTLY the flattened last-raised
    panic of [c]'s defer forest ([cmd_defers c]) seeded by the body's own panic [cmd_panic c].  Consumes
    [run_defers_panic_eq]; the [ORet]-result case needs [cmd_panic c = None] (else the body's in-flight panic
    would survive to the result, by [nested_defers_panic_some]). *)
Local Lemma run_cmd_panic_char : forall fuel (c : Cmd unit) w oc,
  no_heap c = true ->
  run_cmd fuel c w = Some oc ->
  nested_defers_panic fuel (cmd_defers c) (cmd_panic c) = Some (ocpanic oc).
Proof.
  intros fuel c w oc Hnh H.
  destruct (go_chars c w Hnh) as [w_body [Hgo _]].
  unfold run_cmd in H. rewrite Hgo in H. cbn zeta in H.
  destruct (run_defers fuel (cmd_defers c)
              (oc_unit (match cmd_panic c with None => ORet tt w_body | Some v => OPanic v w_body end))) as [result|] eqn:Erd;
    [ | discriminate H ].
  assert (Hseed : ocpanic (oc_unit (match cmd_panic c with None => ORet tt w_body | Some v => OPanic v w_body end)) = cmd_panic c)
    by (destruct (cmd_panic c); reflexivity).
  pose proof (run_defers_panic_eq fuel (cmd_defers c) _ result (cmd_defers_no_heap c Hnh) Erd) as Heq.
  rewrite Hseed in Heq.
  rewrite Heq. f_equal.
  destruct result as [[] w' | v' w']; cbn [ocpanic] in *; cbn in H; injection H as <-.
  - (* result RETURNS: the body could not have panicked, else the in-flight panic would survive to the result *)
    destruct (cmd_panic c) as [v0|] eqn:Ecp; [ | rewrite ocpanic_set_world; reflexivity ].
    (* [cmd_panic c = Some v0] contradicts [ocpanic result = None] via [nested_defers_panic_some] *)
    apply nested_defers_panic_some in Heq. destruct Heq as [? Hcontra]. discriminate Hcontra.
  - reflexivity.
Qed.

(** LOCAL helper for the GENERAL bridge: GIVEN a completing [run_cmd fuel c w = Some oc], the [usteps] run AGREES
    with it for ARBITRARY [c] (any nesting, any panics).  Phase A runs the body (pushing [cmd_defers c], leaving
    [prog 0] per [cmd_panic c]), [unwind_prefix_panic] does the 2-mode nested unwind (tail []) threading the panic
    to [ocpanic oc] (the flattened value, from [run_cmd_panic_char]), and a final [ret_done] / [pan_done] closes
    goroutine 0. *)
Local Lemma bridge_agrees_complete : forall fuel (c : Cmd unit) ucap w oc,
  no_heap c = true ->
  run_cmd fuel c w = Some oc ->
  exists uc : UConfig,
    usteps vz ucap (ustart (cmd_to_ucmd c)) uc
    /\ uc_live uc 0 = false
    /\ uc_panic uc 0 = ocpanic oc
    /\ w_output (oc_world oc) = w_output w ++ map snd (uc_out uc).
Proof.
  intros fuel c ucap w oc Hnh H.
  pose proof (run_cmd_panic_char fuel c w oc Hnh H) as Hchar.
  destruct (go_chars c w Hnh) as [w_body [Hgo Hout]].
  unfold run_cmd in H. rewrite Hgo in H. cbn zeta in H.
  destruct (run_defers fuel (cmd_defers c)
              (oc_unit (match cmd_panic c with None => ORet tt w_body | Some v => OPanic v w_body end))) as [result|] eqn:Erd;
    [ | discriminate H ].
  destruct (cmd_to_ucmd_body_runs c ucap
              (fun t => if Nat.eqb t 0 then cmd_to_ucmd c else URet)
              (fun _ => nil) (fun _ => vz) (fun t => Nat.eqb t 0) nil nil (fun _ => nil) (fun _ => None)
              Hnh eq_refl eq_refl) as [p' [df' [Hus1 [Hprog1 Hdf1]]]].
  cbn in Hdf1. rewrite app_nil_r in Hdf1.
  assert (Hdf1' : df' 0 = map cmd_to_ucmd (cmd_defers c) ++ map cmd_to_ucmd nil)
    by (rewrite Hdf1; cbn [map]; rewrite app_nil_r; reflexivity).
  assert (Hdisj1 : p' 0 = URet \/ exists v, p' 0 = UPan v)
    by (rewrite Hprog1; destruct (cmd_panic c) as [vb|]; [ right; exists vb; reflexivity | left; reflexivity ]).
  assert (Hq0 : (match p' 0 with UPan v => Some v | _ => (fun _ : nat => @None GoAny) 0 end) = cmd_panic c)
    by (rewrite Hprog1; destruct (cmd_panic c); reflexivity).
  destruct (unwind_prefix_panic fuel (cmd_defers c)
              (oc_unit (match cmd_panic c with None => ORet tt w_body | Some v => OPanic v w_body end)) result
              (cmd_panic c) (ocpanic oc) (cmd_defers_no_heap c Hnh) Erd Hchar
              ucap p' (fun _ => nil) (fun _ => vz) (fun t => Nat.eqb t 0) nil
              (nil ++ map (fun e => (0, e)) (cmd_out_events c)) df' (fun _ => None) nil
              eq_refl Hdisj1 Hq0 Hdf1')
    as [p'' [df'' [pa'' [evs [Hus2 [Hdisj2 [Hval2 [Hdf2 Hw]]]]]]]].
  cbn [map] in Hdf2.
  (* [oc_world oc = oc_world result], from peeling [run_cmd] *)
  assert (Hocw : w_output (oc_world oc) = w_output (oc_world result)).
  { destruct result as [[] w_r | v_r w_r]; cbn in H; injection H as <-; cbn [oc_world]; [ rewrite oc_world_set_world | ]; reflexivity. }
  (* final done — [ret_done] if [p'' 0 = URet], else [pan_done] *)
  assert (Hfin : exists (lvF : nat -> bool) (paF : nat -> option GoAny),
             usteps vz ucap (mkUCfg p'' (fun _ => nil) (fun _ => vz) (fun t => Nat.eqb t 0) nil
                            ((nil ++ map (fun e => (0, e)) (cmd_out_events c)) ++ map (fun e => (0, e)) evs) df'' pa'')
                         (mkUCfg p'' (fun _ => nil) (fun _ => vz) lvF nil
                            ((nil ++ map (fun e => (0, e)) (cmd_out_events c)) ++ map (fun e => (0, e)) evs) df'' paF)
             /\ lvF 0 = false /\ paF 0 = ocpanic oc).
  { destruct Hdisj2 as [Hr | [v Hp]].
    - exists (upd (fun t => Nat.eqb t 0) 0 false), pa''.
      split; [ | split; [ apply upd_same | ] ].
      + eapply usteps_step; [ eapply ustep_ret_done with (tid := 0); [ reflexivity | exact Hr | exact Hdf2 ] | apply usteps_refl ].
      + rewrite <- Hval2, Hr. reflexivity.
    - exists (upd (fun t => Nat.eqb t 0) 0 false), (upd pa'' 0 (Some v)).
      split; [ | split; [ apply upd_same | ] ].
      + eapply usteps_step; [ eapply ustep_pan_done with (tid := 0); [ reflexivity | exact Hp | exact Hdf2 ] | apply usteps_refl ].
      + rewrite upd_same, <- Hval2, Hp. reflexivity. }
  destruct Hfin as [lvF [paF [HusF [HlvF HpaF]]]].
  eexists. split; [ | split; [ | split ] ].
  - unfold ustart. eapply usteps_trans; [ exact Hus1 | ].
    eapply usteps_trans; [ exact Hus2 | exact HusF ].
  - cbn [uc_live]. exact HlvF.
  - cbn [uc_panic]. exact HpaF.
  - assert (Haccw : oc_world (oc_unit (match cmd_panic c with None => ORet tt w_body | Some v => OPanic v w_body end)) = w_body)
      by (destruct (cmd_panic c); reflexivity).
    cbn [uc_out]. rewrite Hocw, Hw, Haccw, Hout, !map_app. cbn [map app].
    rewrite !map_snd_pair0, app_assoc. reflexivity.
Qed.

(** ★ The cmd↔unified defer bridge — for every [no_heap] [c] (arbitrary defer nesting, any panics), the
    single-goroutine [usteps] run AGREES with cmd.v's authoritative [run_cmd]: finishes ([uc_live 0 = false]),
    panic EQUALS the Outcome's ([uc_panic 0 = ocpanic oc]), output EQUALS [run_cmd]'s appended [w_output].  The
    SINGLE public defer bridge.  Composes cmd.v's [run_cmd_terminates] (some [fuel] completes) with
    [bridge_agrees_complete] (which threads the panic through [unwind_prefix_panic], grounded on
    [run_cmd_panic_char]).
    ⚠ THE [no_heap] QUARANTINE of THIS theorem: heap commands are covered by the DEFER-FREE
    heap bridge [bridge_heap_body_agrees] below, not by this one — and no heap agreement can be
    UNCONDITIONAL: cmd.v gives an unallocated access NO behavior ([run_cmd] is [None] at every
    fuel — [cread_unallocated_absent] below) while the calculus' total [uc_heap] default-binds, so
    the two sides genuinely diverge outside allocated memory.  The DEFERRED-heap unwind and the
    general conditional heap bridge remain — plans/bridge-effects.md. *)
Theorem bridge_agrees : forall (c : Cmd unit) ucap w,
  no_heap c = true ->
  exists (uc : UConfig) (oc : Outcome unit) (fuel : nat),
    usteps vz ucap (ustart (cmd_to_ucmd c)) uc
    /\ run_cmd fuel c w = Some oc
    /\ uc_live uc 0 = false
    /\ uc_panic uc 0 = ocpanic oc
    /\ w_output (oc_world oc) = w_output w ++ map snd (uc_out uc).
Proof.
  intros c ucap w Hnh.
  destruct (run_cmd_terminates c w Hnh) as [fuel [oc Hrun]].
  destruct (bridge_agrees_complete fuel c ucap w oc Hnh Hrun) as [uc [Hus [Hlv [Hpan Hout]]]].
  exists uc, oc, fuel.
  split; [ exact Hus | split; [ exact Hrun | split; [ exact Hlv | split; [ exact Hpan | exact Hout ] ] ] ].
Qed.

(** ★ The FIRST heap-bridging agreement (PUBLIC + GATED) — the DEFER-FREE heap fragment: for
    any [c] whose body run COMPLETES accumulating no defers ([go c w = Some (oc, nil)] — heap
    reads/writes included), the [usteps] run from the [ustart_w w] config (heap = [w]'s
    allocated cells, boxed) AGREES with [run_cmd] end to end, INCLUDING the final heaps
    ([heap_agrees] against the result world's allocated cells).  Consumes [body_runs_sem]
    (Phase A, semantic — grounded in [go]'s result, not syntactic projections, which cannot
    exist under [CRead]'s binder).  DEFERRED-heap commands await the unwind threading the heap
    invariant — plans/bridge-effects.md. *)
Theorem bridge_heap_body_agrees : forall (c : Cmd unit) ucap w oc,
  go c w = Some (oc, nil) ->
  exists (uc : UConfig) (fuel : nat),
    usteps vz ucap (ustart_w w (cmd_to_ucmd c)) uc
    /\ run_cmd fuel c w = Some oc
    /\ uc_live uc 0 = false
    /\ uc_panic uc 0 = ocpanic oc
    /\ w_output (oc_world oc) = w_output w ++ map snd (uc_out uc)
    /\ heap_agrees (uc_heap uc) (w_refs (oc_world oc)).
Proof.
  intros c ucap w oc Hgo.
  destruct (body_runs_sem c w oc nil ucap
              (fun t => if Nat.eqb t 0 then cmd_to_ucmd c else URet)
              (fun _ => nil) (heap_of_world w) (fun t => Nat.eqb t 0) nil nil
              (fun _ => nil) (fun _ => None)
              Hgo (heap_of_world_agrees w) eq_refl eq_refl)
    as [p' [h' [tr' [df' [evs [Hus [Hprog [Hdf [Hha Hout]]]]]]]]].
  cbn [map] in Hdf. rewrite app_nil_r in Hdf.
  destruct oc as [[] w_r | v w_r]; cbn [ocpanic oc_world] in *.
  - (* body returns *)
    exists (mkUCfg p' (fun _ => nil) h' (upd (fun t => Nat.eqb t 0) 0 false) tr'
                   (nil ++ map (fun e => (0, e)) evs) df' (fun _ => None)), 1.
    split; [ | split; [ | split; [ apply upd_same | split; [ reflexivity | split ] ] ] ].
    + unfold ustart_w. eapply usteps_trans; [ exact Hus | ].
      eapply usteps_step;
        [ eapply ustep_ret_done with (tid := 0); [ reflexivity | exact Hprog | exact Hdf ] | apply usteps_refl ].
    + unfold run_cmd. rewrite Hgo. cbn. reflexivity.
    + cbn [uc_out]. rewrite Hout. cbn [app]. rewrite map_snd_pair0. reflexivity.
    + cbn [uc_heap]. exact Hha.
  - (* body panics *)
    exists (mkUCfg p' (fun _ => nil) h' (upd (fun t => Nat.eqb t 0) 0 false) tr'
                   (nil ++ map (fun e => (0, e)) evs) df' (upd (fun _ : nat => @None GoAny) 0 (Some v))), 1.
    split; [ | split; [ | split; [ apply upd_same | split; [ apply upd_same | split ] ] ] ].
    + unfold ustart_w. eapply usteps_trans; [ exact Hus | ].
      eapply usteps_step;
        [ eapply ustep_pan_done with (tid := 0); [ reflexivity | exact Hprog | exact Hdf ] | apply usteps_refl ].
    + unfold run_cmd. rewrite Hgo. cbn. reflexivity.
    + cbn [uc_out]. rewrite Hout. cbn [app]. rewrite map_snd_pair0. reflexivity.
    + cbn [uc_heap]. exact Hha.
Qed.

(** The NEGATIVE witness for the quarantine: an unallocated read has NO completing run at ANY
    fuel — so no unconditional (premise-free) bridge over heap commands can exist; the agreement
    for heap programs must carry allocation/completion premises, as [bridge_heap_body_agrees]'s
    [go]-completion premise does. *)
Example cread_unallocated_absent : forall fuel w,
  w_refs w 0 = None ->
  run_cmd fuel (CRead 0 (fun _ => CRet tt)) w = None.
Proof. intros fuel w H. unfold run_cmd. cbn [go]. rewrite H. reflexivity. Qed.

End BridgeVal.

(** The EXACT gated public-surface set for this module is the [Print Assumptions] lines below — the SINGLE
    zero-axiom authority (the Docker manifest gate scrapes their [Axioms:] report, which must be empty).  A
    [Print Assumptions] audits its whole dependency CONE, so EVERY Local definition here is covered TRANSITIVELY
    through some public theorem's cone, not separately printed: the projections
    ([cmd_out_events]/[cmd_panic]/[cmd_defers]/[go_chars]) and the [run_defers]/unwind plumbing feed the [run_cmd_*]
    properties, and the panic-characterization + nested-unwind machinery ([nested_defers_panic] /
    [nested_defers_panic_seed] / [run_defers_panic_eq] / [run_cmd_panic_char] / [unwind_prefix_panic] /
    [pop_defer_step]) is CONSUMED by the general bridge [bridge_agrees]. *)
Print Assumptions cmd_to_ucmd_fragment.
Print Assumptions cmd_to_ucmd_novz.
Print Assumptions bridge_heap_body_agrees.
Print Assumptions cmd_to_ucmd_run_agrees.
Print Assumptions bridge_agrees.
Print Assumptions run_cmd_out_monotone.
Print Assumptions run_cmd_no_panic_ret.
