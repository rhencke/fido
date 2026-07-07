(** cmd_unified.v — the FIRST bridge between Fido's two proof-only semantics universes.

    GoSem denotes the supported AST into [cmd.v]'s command tree [Cmd unit] (CRet / COut / CPan / CDfr,
    plus the heap TRIO CWrite / CRead / CAlloc — typed cells, ABSENT on unallocated access,
    DETERMINISTIC allocation at exactly [w_next]).
    [unified.v] is the closed-world OPERATIONAL semantics ([UCmd] / [ustep]) on which race-freedom and
    liveness/deadlock are proved.  The charter (ARCHITECTURE.md) requires GoSem to BRIDGE that existing
    semantics, NOT fork a second universe.  The structural fact that makes the bridge concrete: [cmd.v]'s
    constructors map 1-for-1 into [unified.v]'s fragment —
        CRet -> URet,  COut b xs -> UOut b xs,  CPan v -> UPan v,  CDfr d -> UDfr d,
        CWrite l v -> UWrite l v,  CRead l f -> URead l f,  CAlloc v f -> UAlloc v f.
    So [cmd_to_ucmd] is a TOTAL translation of cmd.v's [Cmd unit] command tree into a subset of [UCmd].  The
    print/println flag on [COut] is PRESERVED ([unified.v]'s [UOut]/[uc_out] carry it, exactly the model's
    [w_output : list (bool * list GoAny)]).

    The module exposes ONE single-goroutine [usteps] AGREEMENT bridge, [bridge_heap_agrees]:
    ANY [c] (heap reads/writes/ALLOCATIONS, arbitrary defer nesting, any panics) whose [run_cmd] COMPLETES
    agrees end to end INCLUDING final heaps, from the [ustart_w] mirrored-heap start (the
    completion premise is the well-formedness gate; for [no_heap] commands completion is a
    THEOREM — cmd.v's [run_cmd_terminates] — so consumers compose the two).  Plus cmd.v-side
    properties for a COMPLETING [run_cmd] on ANY [c] (heap ops included): output only APPENDS,
    and a panic-free completing run returns [ORet].
    The EXACT gated public-surface set is the [Print Assumptions] block at the end of this file (the single in-file
    authority); this header does not re-enumerate it.
    There is NO public projection-observer theorem: every unified-side run/unwind lemma is LOCAL
    (file-private) proof plumbing grounded directly in cmd.v's [go]/[unwind_defers] — no exported
    theorem concludes with a private observer, so a consumer cannot prove bridge facts against
    anything but [run_cmd].  (No concurrency ops in this fragment, so [uc_bufs] is untouched;
    [uc_heap] carries the heap commands' effects and heap steps append [KWrite]/[KRead] to [uc_trace] —
    the trace is existential in the heap bridge's statement.)
    Proof-only: emits no Go, adds no axiom. *)

From Fido Require Import preamble concurrency cmd unified.
From Fido Require Import GoRuntimeTypes.
From Fido Require Import GoEffects.
From Fido Require Import GoSlice.
From Fido Require Import GoHeap.   (* ValidWorld — the CAlloc gate lemmas live where alloc_world meets it *)
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
  | CAlloc v f  => UAlloc v (fun l => cmd_to_ucmd (f l))
  end.

(** PUBLIC + GATED: the IMAGE seal — [cmd_to_ucmd] lands in the TRANSLATED fragment BY
    CONSTRUCTION: output/panic/defer plus the heap trio (write/read/alloc), and NO channel/spawn form ever
    ([USend]/[URecv]/[USelect]/[UClose]/[USpawn] all excluded) — so no bridged run can reach
    a closed-recv rule; the CHANNEL slice must land its own structural seal before that
    changes (plans/bridge-effects.md). *)
Inductive UFrag {V : Type} : @UCmd V -> Prop :=
  | UF_ret : UFrag URet
  | UF_out : forall pb xs k, UFrag k -> UFrag (UOut pb xs k)
  | UF_pan : forall v, UFrag (UPan v)
  | UF_dfr : forall d k, UFrag d -> UFrag k -> UFrag (UDfr d k)
  | UF_wr  : forall l v k, UFrag k -> UFrag (UWrite l v k)
  | UF_rd  : forall l f, (forall x, UFrag (f x)) -> UFrag (URead l f)
  | UF_al  : forall v f, (forall l, UFrag (f l)) -> UFrag (UAlloc v f).
Theorem cmd_to_ucmd_fragment : forall c : Cmd unit, UFrag (cmd_to_ucmd c).
Proof.
  fix IH 1. intros [u | pb xs c' | v | d c' | l v c' | l f | v f]; cbn [cmd_to_ucmd].
  - constructor.
  - constructor. exact (IH c').
  - constructor.
  - constructor; [exact (IH d) | exact (IH c')].
  - constructor. exact (IH c').
  - constructor. intro x. exact (IH (f x)).
  - constructor. intro l. exact (IH (f l)).
Qed.


(** [vz] — the start configs' UNALLOCATED-HEAP default at this instance, and nothing more
    (the calculus has NO global closed-recv zero any more: [URecv]/[USelect] carry the zero
    PER SITE).  It is an ARBITRARY [GoAny], NOT a Go zero value, and every public statement
    below that MENTIONS the unified [GoAny] configuration ([ustart_w]) UNIVERSALLY
    QUANTIFIES it (section generalization; the pure [run_cmd]-side theorems in this section
    never involve it).  The license: [bridge_heap_agrees] starts from the [ustart_w] heap
    that MIRRORS the World's allocated cells and the [go]-completion premise keeps the run
    inside allocated memory — so the [vz] heap defaults are never consulted. *)
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
         (fun _ => nil) (heap_of_world w) (fun t => Nat.eqb t 0) nil nil (fun _ => nil) (fun _ => None)
         (w_next w).   (* the allocator agreement: the config's pointer MIRRORS the World's *)
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

(** the deterministic allocation keeps the agreement: both sides install [v] at the SAME
    location ([w_next w] — the mirrored allocator), and [any_of_cell (cell_of_any v) = v]. *)
Local Lemma heap_alloc_agrees : forall h w v,
  heap_agrees h (w_refs w) ->
  heap_agrees (upd h (w_next w) v) (w_refs (alloc_world v w)).
Proof.
  intros h w v Ha l' cell' H'. cbn [alloc_world w_refs] in H'.
  destruct (Nat.eqb l' (w_next w)) eqn:El.
  - apply PeanoNat.Nat.eqb_eq in El. subst l'.
    injection H' as <-. rewrite upd_same. symmetry. apply any_cell_roundtrip.
  - apply PeanoNat.Nat.eqb_neq in El.
    rewrite (upd_other h (w_next w) v l' El).
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
    usteps ucap (mkUCfg p b h lv tr o df pa (w_next w))
                (mkUCfg p' b h' lv tr' (o ++ map (fun e => (0, e)) evs) df' pa
                        (w_next (oc_world oc)))
    /\ p' 0 = (match oc with ORet _ _ => URet | OPanic v _ => UPan v end)
    /\ df' 0 = map cmd_to_ucmd ds ++ df 0
    /\ heap_agrees h' (w_refs (oc_world oc))
    /\ w_output (oc_world oc) = w_output w ++ evs.
Proof.
  intros c.
  induction c as [a | bo xs c' IH | v | d c' IHc' | l v c' IH | l f IH | v f IH] using Cmd_rect';
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
    + eapply usteps_step; [ eapply ustep_write; [ exact Hlv | exact Hp ]
        | rewrite (heap_write_next l v w w' Hw) in Hus; exact Hus ].
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
  - (* CAlloc: both sides allocate at the SAME location — the mirrored pointer — and bump *)
    destruct (IH (w_next w) (alloc_world v w) oc ds ucap
                 (upd p 0 (cmd_to_ucmd (f (w_next w)))) b (upd h (w_next w) v) lv
                 (tr ++ (mkEv 0 (KWrite (w_next w)) :: nil)) o df pa Hgo
                 (heap_alloc_agrees h w v Hha) Hlv (upd_same _ _ _))
      as [p' [h' [tr' [df' [evs [Hus [Hprog [Hdf [Hha2 Hout]]]]]]]]].
    exists p', h', tr', df', evs.
    split; [ | split; [ exact Hprog | split; [ exact Hdf | split; [ exact Hha2 | exact Hout ] ] ] ].
    eapply usteps_step; [ eapply ustep_alloc; [ exact Hlv | exact Hp ] | exact Hus ].
Qed.


Local Lemma w_output_w_log : forall b xs w, w_output (w_log b xs w) = w_output w ++ ((b, xs) :: nil).
Proof. reflexivity. Qed.



Local Lemma map_snd_pair0 : forall (l : list (bool * list GoAny)), map snd (map (fun e => (0, e)) l) = l.
Proof. induction l as [|a l IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

(** [oc_set_world] only advances the world — it preserves the [Outcome]'s panic status (and sets its world). *)
Local Lemma ocpanic_set_world : forall (acc : Outcome unit) w, ocpanic (oc_set_world acc w) = ocpanic acc.
Proof. intros [[] w0 | v w0] w; reflexivity. Qed.
Local Lemma oc_world_set_world : forall (acc : Outcome unit) w, oc_world (oc_set_world acc w) = w.
Proof. intros [[] w0 | v w0] w; reflexivity. Qed.







(** Pop ONE defer off goroutine 0's stack, uniformly across the 2-mode: [ustep_ret_defer] if [prog = URet]
    (leaving [pa] alone) or [ustep_pan_defer] if [prog = UPan v] (recording [v] into [pa]).  Either way the
    post-pop [pa 0] equals the pre-pop in-flight panic [q0], so the caller need not case-split. *)
Local Lemma pop_defer_step : forall ucap p b h lv tr o df pa nx d rest q0,
  lv 0 = true -> (p 0 = URet \/ exists v, p 0 = UPan v) ->
  (match p 0 with UPan v => Some v | _ => pa 0 end) = q0 ->
  df 0 = cmd_to_ucmd d :: rest ->
  exists paP, paP 0 = q0 /\
    usteps ucap (mkUCfg p b h lv tr o df pa nx)
                (mkUCfg (upd p 0 (cmd_to_ucmd d)) b h lv tr o (upd df 0 rest) paP nx).
Proof.
  intros ucap p b h lv tr o df pa nx d rest q0 Hlv Hp Hq0 Hdf.
  destruct Hp as [Hret | [v Hpan]].
  - exists pa. rewrite Hret in Hq0. cbn in Hq0. split; [ exact Hq0 | ].
    eapply usteps_step; [ eapply ustep_ret_defer; [ exact Hlv | exact Hret | exact Hdf ] | apply usteps_refl ].
  - exists (upd pa 0 (Some v)). rewrite Hpan in Hq0. cbn in Hq0. split; [ rewrite upd_same; exact Hq0 | ].
    eapply usteps_step; [ eapply ustep_pan_defer; [ exact Hlv | exact Hpan | exact Hdf ] | apply usteps_refl ].
Qed.

(** The machine's in-flight panic MODE, relative to a base [qb]: the derivation's accumulator
    panic when one is recorded, else the base carried in from the enclosing scope.  Quantifying
    [qb] in [unwind_heap]'s motive lets the nested-scope IH instantiate it at the CARRIED mode —
    no seed-linearity reconciliation is needed. *)
Local Definition mode_or (o q : option GoAny) : option GoAny :=
  match o with Some v => Some v | None => q end.

(** The DEFERRED-HEAP unwind (semantic 2-mode): given an unwind DERIVATION and a ustep state
    whose in-flight panic ((prog, pa) 2-mode) and heap AGREE with the accumulator (mode relative
    to any base [qb]), the ustep pops and runs the whole LIFO front [ds] down to [ds_tail],
    landing on [result]'s panic (relative to the same base), world-output delta, and ALLOCATED
    heap.  Induction on the derivation: the nested forest is a SUB-DERIVATION, instantiated at
    base [mode_or (ocpanic acc) qb]. *)
Local Lemma unwind_heap : forall ds acc result,
  unwind_defers ds acc result ->
  forall ucap p b h lv tr o df pa ds_tail qb,
    lv 0 = true ->
    (p 0 = URet \/ exists v, p 0 = UPan v) ->
    (match p 0 with UPan v => Some v | _ => pa 0 end) = mode_or (ocpanic acc) qb ->
    heap_agrees h (w_refs (oc_world acc)) ->
    df 0 = map cmd_to_ucmd ds ++ ds_tail ->
    exists p' h' tr' df' pa' evs,
      usteps ucap (mkUCfg p b h lv tr o df pa (w_next (oc_world acc)))
                  (mkUCfg p' b h' lv tr' (o ++ map (fun e => (0, e)) evs) df' pa'
                          (w_next (oc_world result)))
      /\ (p' 0 = URet \/ exists v, p' 0 = UPan v)
      /\ (match p' 0 with UPan v => Some v | _ => pa' 0 end) = mode_or (ocpanic result) qb
      /\ df' 0 = ds_tail
      /\ heap_agrees h' (w_refs (oc_world result))
      /\ w_output (oc_world result) = w_output (oc_world acc) ++ evs.
Proof.
  intros ds acc result Hun.
  induction Hun as [acc | d ds acc oc_d ds_d net r Hgo Hnest IHnest Hrest IHrest];
    intros ucap p b h lv tr o df pa ds_tail qb Hlv Hp Hq0 Hha Hdf.
  - cbn [map] in Hdf. rewrite app_nil_l in Hdf.
    exists p, h, tr, df, pa, nil. cbn [map]. rewrite !app_nil_r.
    split; [ apply usteps_refl | ].
    split; [ exact Hp | split; [ exact Hq0 | split; [ exact Hdf | split; [ exact Hha | reflexivity ] ] ] ].
  - cbn [map] in Hdf.
    destruct (pop_defer_step ucap p b h lv tr o df pa (w_next (oc_world acc)) d
                (map cmd_to_ucmd ds ++ ds_tail) (mode_or (ocpanic acc) qb) Hlv Hp Hq0 Hdf)
      as [paP [HpaP Hpop]].
    destruct (body_runs_sem d (oc_world acc) oc_d ds_d ucap
                (upd p 0 (cmd_to_ucmd d)) b h lv tr o
                (upd df 0 (map cmd_to_ucmd ds ++ ds_tail)) paP
                Hgo Hha Hlv (upd_same _ _ _))
      as [pA [hA [trA [dfA [evs0 [HusA [HprogA [HdfA [HhaA Hout0]]]]]]]]].
    rewrite upd_same in HdfA.
    assert (HprogA' : pA 0 = URet \/ exists v, pA 0 = UPan v)
      by (rewrite HprogA; destruct oc_d as [[] ?|vd ?]; [ left; reflexivity | right; exists vd; reflexivity ]).
    (* the nested scope's mode: the sub-derivation runs at base [mode_or (ocpanic acc) qb] *)
    assert (HqA : (match pA 0 with UPan v => Some v | _ => paP 0 end)
                  = mode_or (ocpanic (oc_unit oc_d)) (mode_or (ocpanic acc) qb)).
    { rewrite HprogA. destruct oc_d as [[] ?|vd ?]; cbn [oc_unit ocpanic mode_or]; [ exact HpaP | reflexivity ]. }
    assert (HhaA' : heap_agrees hA (w_refs (oc_world (oc_unit oc_d))))
      by (destruct oc_d; exact HhaA).
    destruct (IHnest ucap pA b hA lv trA (o ++ map (fun e => (0, e)) evs0) dfA paP
                 (map cmd_to_ucmd ds ++ ds_tail) (mode_or (ocpanic acc) qb)
                 Hlv HprogA' HqA HhaA' HdfA)
      as [pB [hB [trB [dfB [paB [evs1 [HusB [HprogB [HqB [HdfB [HhaB Hout1]]]]]]]]]]].
    (* the tail continues at the combined accumulator, same base [qb] *)
    assert (HqB' : (match pB 0 with UPan v => Some v | _ => paB 0 end)
                   = mode_or (ocpanic (match net with
                                       | OPanic v' w' => OPanic v' w'
                                       | ORet _ w' => oc_set_world acc w' end)) qb).
    { rewrite HqB. destruct net as [[] wn | vn wn]; cbn [ocpanic mode_or].
      - rewrite ocpanic_set_world. reflexivity.
      - reflexivity. }
    assert (HhaB' : heap_agrees hB (w_refs (oc_world (match net with
                                       | OPanic v' w' => OPanic v' w'
                                       | ORet _ w' => oc_set_world acc w' end)))).
    { destruct net as [[] wn | vn wn]; cbn [oc_world] in HhaB |- *;
        [ rewrite oc_world_set_world; exact HhaB | exact HhaB ]. }
    destruct (IHrest ucap pB b hB lv trB
                 ((o ++ map (fun e => (0, e)) evs0) ++ map (fun e => (0, e)) evs1)
                 dfB paB ds_tail qb Hlv HprogB HqB' HhaB' HdfB)
      as [pC [hC [trC [dfC [paC [evs2 [HusC [HprogC [HqC [HdfC [HhaC Hout2]]]]]]]]]]].
    exists pC, hC, trC, dfC, paC, (evs0 ++ evs1 ++ evs2).
    split; [ | split; [ exact HprogC | split; [ exact HqC | split; [ exact HdfC | split; [ exact HhaC | ] ] ] ] ].
    + replace (o ++ map (fun e => (0, e)) (evs0 ++ evs1 ++ evs2))
         with (((o ++ map (fun e => (0, e)) evs0) ++ map (fun e => (0, e)) evs1)
                 ++ map (fun e => (0, e)) evs2)
        by (rewrite !map_app, !app_assoc; reflexivity).
      rewrite oc_unit_world in HusB.
      assert (HnextC : oc_world (match net with
                                 | OPanic v' w' => OPanic v' w'
                                 | ORet _ w' => oc_set_world acc w' end) = oc_world net)
        by (destruct net as [[] wn | vn wn]; cbn [oc_world]; [ rewrite oc_world_set_world | ]; reflexivity).
      rewrite HnextC in HusC.
      eapply usteps_trans; [ exact Hpop | ].
      eapply usteps_trans; [ exact HusA | ].
      eapply usteps_trans; [ exact HusB | exact HusC ].
    + rewrite Hout2.
      assert (Hwacc' : w_output (oc_world (match net with
                                            | OPanic v' w' => OPanic v' w'
                                            | ORet _ w' => oc_set_world acc w' end))
                       = w_output (oc_world net))
        by (destruct net as [[] wn | vn wn]; cbn [oc_world]; [ rewrite oc_world_set_world | ]; reflexivity).
      assert (Hwseed : w_output (oc_world (oc_unit oc_d)) = w_output (oc_world oc_d))
        by (destruct oc_d; reflexivity).
      rewrite Hwacc', Hout1, Hwseed, Hout0, <- !app_assoc. reflexivity.
Qed.


(** OUTPUT-MONOTONICITY of [run_cmd], for ANY [c] (arbitrary defer nesting, heap ops included —
    a write never touches [w_output]): a COMPLETING run only ever APPENDS to the world's output,
    never RETRACTS — Go's deferred actions and panics cannot un-print already-printed output.
    Structural on the tree — the [CDfr] case composes the continuation's delta with the deferred
    scope's (whose final world is the result's world in BOTH combine arms).  A standalone
    cmd.v-side property; the bridge [bridge_heap_agrees] establishes its output agreement
    independently, so this theorem is a sibling, not a dependency, of the bridge. *)
Theorem run_cmd_out_monotone : forall (c : Cmd unit) w oc,
  run_cmd c w = Some oc ->
  exists evs, w_output (oc_world oc) = w_output w ++ evs.
Proof.
  fix IH 1. intros [a | b xs c' | v | d c' | l v c' | l f | v f] w oc H; cbn [run_cmd] in H.
  - injection H as <-. exists nil. cbn [oc_world]. rewrite app_nil_r. reflexivity.
  - destruct (IH c' (w_log b xs w) oc H) as [evs Hevs].
    exists ((b, xs) :: evs). rewrite Hevs, w_output_w_log, <- app_assoc. reflexivity.
  - injection H as <-. exists nil. cbn [oc_world]. rewrite app_nil_r. reflexivity.
  - destruct (run_cmd c' w) as [oc0|] eqn:E0; [ | discriminate H ].
    destruct (run_cmd d (oc_world oc0)) as [[[] w'|vd w']|] eqn:Ed; try discriminate H.
    + injection H as <-.
      destruct (IH c' w oc0 E0) as [evs0 Hevs0].
      destruct (IH d (oc_world oc0) (ORet tt w') Ed) as [evs1 Hevs1].
      exists (evs0 ++ evs1). rewrite oc_world_set_world.
      cbn [oc_world] in Hevs1. rewrite Hevs1, Hevs0, <- app_assoc. reflexivity.
    + injection H as <-.
      destruct (IH c' w oc0 E0) as [evs0 Hevs0].
      destruct (IH d (oc_world oc0) (OPanic vd w') Ed) as [evs1 Hevs1].
      exists (evs0 ++ evs1). cbn [oc_world] in Hevs1 |- *.
      rewrite Hevs1, Hevs0, <- app_assoc. reflexivity.
  - destruct (heap_write l v w) as [w'|] eqn:E; [ | discriminate H ].
    destruct (IH c' w' oc H) as [evs Hevs].
    exists evs. rewrite Hevs, (heap_write_output l v w w' E). reflexivity.
  - destruct (w_refs w l) as [cell|]; [ | discriminate H ].
    exact (IH (f (any_of_cell cell)) w oc H).
  - exact (IH (f (w_next w)) (alloc_world v w) oc H).
Qed.

(** PANIC-FREEDOM of [run_cmd] for ANY [c] (nested defers included): a [cmd_no_panic c] run that
    COMPLETES returns [ORet] — Go's panic-free program cannot end in a panic.  Structural; the
    [CDfr] case threads both conjuncts.  A standalone cmd.v-side property, panic-free companion to
    [run_cmd_out_monotone]. *)
Theorem run_cmd_no_panic_ret : forall (c : Cmd unit) w oc,
  run_cmd c w = Some oc -> cmd_no_panic c = true ->
  exists w', oc = ORet tt w'.
Proof.
  fix IH 1. intros [a | b xs c' | v | d c' | l v c' | l f | v f] w oc H Hnp;
    cbn [cmd_no_panic] in Hnp; cbn [run_cmd] in H.
  - destruct a. injection H as <-. exists w. reflexivity.
  - exact (IH c' (w_log b xs w) oc H Hnp).
  - discriminate Hnp.
  - apply andb_prop in Hnp. destruct Hnp as [Hd Hc'].
    destruct (run_cmd c' w) as [oc0|] eqn:E0; [ | discriminate H ].
    destruct (run_cmd d (oc_world oc0)) as [ocd|] eqn:Ed; [ | discriminate H ].
    destruct (IH d (oc_world oc0) ocd Ed Hd) as [wd ->].
    injection H as <-.
    destruct (IH c' w oc0 E0 Hc') as [w0 ->].
    exists wd. reflexivity.
  - discriminate Hnp.
  - discriminate Hnp.
  - discriminate Hnp.
Qed.




(** ★ The GENERAL heap bridge (PUBLIC + GATED): for ANY [c] — heap reads/writes/ALLOCATIONS, arbitrary
    defer nesting, any panics — whose [run_cmd] COMPLETES, the [usteps] run from the
    [ustart_w w] config (heap = [w]'s allocated cells, boxed) AGREES end to end, INCLUDING
    the final heaps ([heap_agrees] against the result world's allocated cells).  Assembly:
    [body_runs_sem] (Phase A, semantic) + [unwind_heap] (the deferred-heap unwind, by
    induction on the [unwind_defers] derivation obtained from [run_cmd_eval]) + the 2-mode
    final done.  The completion premise is the well-formedness gate (an unallocated access
    never completes — [cread_unallocated_absent] below). *)
Theorem bridge_heap_agrees : forall (c : Cmd unit) ucap w oc,
  run_cmd c w = Some oc ->
  exists uc : UConfig,
    usteps ucap (ustart_w w (cmd_to_ucmd c)) uc
    /\ uc_live uc 0 = false
    /\ uc_panic uc 0 = ocpanic oc
    /\ w_output (oc_world oc) = w_output w ++ map snd (uc_out uc)
    /\ heap_agrees (uc_heap uc) (w_refs (oc_world oc))
    /\ uc_next uc = w_next (oc_world oc).   (* the allocator agreement, end to end *)
Proof.
  intros c ucap w oc H.
  destruct (run_cmd_eval c w oc H) as [oc0 [ds [result [Hgo [Hun Hcomb]]]]].
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
                = mode_or (ocpanic (oc_unit oc0)) None)
    by (rewrite HprogA; destruct oc0 as [[] ?|? ?]; reflexivity).
  assert (Hha0 : heap_agrees hA (w_refs (oc_world (oc_unit oc0))))
    by (destruct oc0 as [[] ?|? ?]; exact HhaA).
  destruct (unwind_heap ds (oc_unit oc0) result Hun ucap pA
              (fun _ => nil) hA (fun t => Nat.eqb t 0) trA
              (nil ++ map (fun e => (0, e)) evs0) dfA (fun _ => None) nil None
              eq_refl HprogA' Hq0 Hha0 HdfA')
    as [pB [hB [trB [dfB [paB [evs1 [HusB [HprogB [HqB [HdfB [HhaB Hout1]]]]]]]]]]].
  rewrite oc_unit_world in HusB.
  assert (HqB0 : (match pB 0 with UPan v => Some v | _ => paB 0 end) = ocpanic result)
    by (rewrite HqB; destruct result as [[] ?|? ?]; reflexivity).
  (* relate [result] to run_cmd's [oc] *)
  assert (Hoc : ocpanic oc = ocpanic result
                /\ oc_world oc = oc_world result).
  { destruct result as [[] w' | v w']; subst oc.
    - (* result returns: the body cannot have panicked (a panic seed never returns) *)
      destruct oc0 as [[] w0 | v0 w0].
      + split; reflexivity.
      + exfalso.
        destruct (unwind_panic_stays ds (oc_unit (OPanic v0 w0)) (ORet tt w') Hun v0 w0 eq_refl)
          as [? [? Hcontra]].
        discriminate Hcontra.
    - cbn [ocpanic oc_world]. split; reflexivity. }
  destruct Hoc as [Hocp Hocw].
  (* the final done step per the 2-mode *)
  destruct HprogB as [HretB | [v HpanB]].
  - exists (mkUCfg pB (fun _ => nil) hB (upd (fun t => Nat.eqb t 0) 0 false) trB
                   ((nil ++ map (fun e => (0, e)) evs0) ++ map (fun e => (0, e)) evs1) dfB paB
                   (w_next (oc_world result))).
    split; [ | split; [ apply upd_same | split; [ | split; [ | split ] ] ] ].
    + unfold ustart_w. eapply usteps_trans; [ exact HusA | ].
      eapply usteps_trans; [ exact HusB | ].
      eapply usteps_step;
        [ eapply ustep_ret_done with (tid := 0); [ reflexivity | exact HretB | exact HdfB ] | apply usteps_refl ].
    + cbn [uc_panic]. rewrite Hocp, <- HqB0, HretB. reflexivity.
    + cbn [uc_out]. rewrite Hocw, Hout1.
      assert (Hw0 : oc_world (oc_unit oc0) = oc_world oc0) by (destruct oc0; reflexivity).
      rewrite Hw0, Hout0, !map_app, map_snd_pair0. cbn [app map].
      rewrite map_snd_pair0, <- app_assoc. reflexivity.
    + cbn [uc_heap]. rewrite Hocw. exact HhaB.
    + cbn [uc_next]. rewrite Hocw. reflexivity.
  - exists (mkUCfg pB (fun _ => nil) hB (upd (fun t => Nat.eqb t 0) 0 false) trB
                   ((nil ++ map (fun e => (0, e)) evs0) ++ map (fun e => (0, e)) evs1) dfB
                   (upd paB 0 (Some v)) (w_next (oc_world result))).
    split; [ | split; [ apply upd_same | split; [ | split; [ | split ] ] ] ].
    + unfold ustart_w. eapply usteps_trans; [ exact HusA | ].
      eapply usteps_trans; [ exact HusB | ].
      eapply usteps_step;
        [ eapply ustep_pan_done with (tid := 0); [ reflexivity | exact HpanB | exact HdfB ] | apply usteps_refl ].
    + cbn [uc_panic]. rewrite upd_same, Hocp, <- HqB0, HpanB. reflexivity.
    + cbn [uc_out]. rewrite Hocw, Hout1.
      assert (Hw0 : oc_world (oc_unit oc0) = oc_world oc0) by (destruct oc0; reflexivity).
      rewrite Hw0, Hout0, !map_app, map_snd_pair0. cbn [app map].
      rewrite map_snd_pair0, <- app_assoc. reflexivity.
    + cbn [uc_heap]. rewrite Hocw. exact HhaB.
    + cbn [uc_next]. rewrite Hocw. reflexivity.
Qed.

(** The NEGATIVE witness for the quarantine: an unallocated read has NO completing run at
    all — so no unconditional (premise-free) bridge over heap commands can exist; the agreement
    for heap programs must carry allocation/completion premises, as [bridge_heap_agrees]'s
    [run_cmd]-completion premise does. *)
Example cread_unallocated_absent : forall w,
  w_refs w 0 = None ->
  run_cmd (CRead 0 (fun _ => CRet tt)) w = None.
Proof. intros w H. cbn [run_cmd]. rewrite H. reflexivity. Qed.

End BridgeVal.

(** PUBLIC SURFACE — this module's gated results bundled into ONE constant (the module-standard
    surface shape), so a SINGLE [Print Assumptions] covers all their transitive cones (the Docker
    manifest gate scrapes the [Axioms:] report, which must be empty).  THE CLAIM IS THE CONES,
    exactly: the audit covers what the four bundled theorems consume — the [go]-grounded
    derivation plumbing feeds the [run_cmd_*] properties, and the semantic Phase A +
    unwind machinery ([body_runs_sem] / [unwind_heap]
    / [pop_defer_step]) is CONSUMED by [bridge_heap_agrees].  The one always-dead-by-convention
    artifact shape — a LOCAL [Example], vernacular or #[local] attribute spelling (an Example
    nothing consumes — compiled but outside every printed cone) — is mechanically rejected
    repo-wide by smart-ctor-gate.sh check 6 (token-aware; exact boundary documented at the
    detector); a general Local lemma's audit is membership in a consumer's cone. *)
(** ---- The CAlloc regression obligations (design v2's gate lemmas): under GoHeap's
    [ValidWorld] the deterministic allocator is SAFE — the minted location is never 0
    (Go's nil is unreachable from a continuation branching on it), never a clobber of
    an allocated cell, and validity is PRESERVED by [alloc_world] (so the obligations
    compose down a run).  cmd.v owns [alloc_world], GoHeap owns [ValidWorld]; the
    bridge is where the two meet. *)
Theorem calloc_loc_nonzero : forall w, ValidWorld w -> Nat.eqb (w_next w) 0 = false.
Proof.
  intros w [Hpos _]. destruct (w_next w); [ discriminate Hpos | reflexivity ].
Qed.
Theorem calloc_no_clobber : forall w, ValidWorld w -> w_refs w (w_next w) = None.
Proof.
  intros w [_ Hbound].
  exact (proj1 (Hbound (w_next w) (PeanoNat.Nat.leb_refl _))).
Qed.
Theorem alloc_world_valid : forall v w, ValidWorld w -> ValidWorld (alloc_world v w).
Proof.
  intros v w [Hpos Hbound]. split.
  - reflexivity.
  - intros l Hl. cbn [alloc_world w_next] in Hl.
    apply PeanoNat.Nat.leb_le in Hl.
    assert (Hgt : w_next w <= l) by lia.
    assert (El : Nat.eqb l (w_next w) = false)
      by (apply PeanoNat.Nat.eqb_neq; lia).
    cbn [alloc_world w_refs w_chans w_maps]. rewrite El.
    apply Hbound. apply PeanoNat.Nat.leb_le. exact Hgt.
Qed.

Definition cmd_unified_surface :=
  (cmd_to_ucmd_fragment, bridge_heap_agrees, run_cmd_out_monotone, run_cmd_no_panic_ret,
   calloc_loc_nonzero, calloc_no_clobber, alloc_world_valid).
Print Assumptions cmd_unified_surface.
