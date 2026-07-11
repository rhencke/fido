(** cmd_unified.v — the FIRST bridge between Fido's two proof-only semantics universes.

    GoSem denotes the supported AST into [cmd.v]'s command tree [Cmd unit] (CRet / COut / CPan / CDfr,
    the heap TRIO CWrite / CRead / CAlloc — typed cells, ABSENT on unallocated access,
    DETERMINISTIC allocation at exactly [w_next] — and the CHANNEL trio CChSend / CChRecv /
    CChClose, the recv sites carrying their element tags).
    [unified.v] is the closed-world OPERATIONAL semantics ([UCmd] / [ustep]) on which race-freedom and
    liveness/deadlock are proved.  The charter (ARCHITECTURE.md) requires GoSem to BRIDGE that existing
    semantics, NOT fork a second universe.  The structural fact that makes the bridge concrete: [cmd.v]'s
    constructors map 1-for-1 into [unified.v]'s fragment —
        CRet -> URet,  COut b xs -> UOut b xs,  CPan v -> UPan v,  CDfr d -> UDfr d,
        CWrite l v -> UWrite l v,  CRead l f -> URead l f,  CAlloc v f -> UAlloc v f,
        CChSend c v -> USend c v,  CChRecv c tg f -> URecv c (anyt tg (zero_val tg)) f,
        CChClose c -> UClose c.
    So [cmd_to_ucmd] is a TOTAL translation of cmd.v's [Cmd unit] command tree into a subset of [UCmd].  The
    print/println flag on [COut] is PRESERVED ([unified.v]'s [UOut]/[uc_out] carry it, exactly the model's
    [w_output : list (bool * list GoAny)]).

    The module exposes ONE single-goroutine [usteps] AGREEMENT bridge, [bridge_effects_agree]:
    ANY [c] — heap reads/writes/ALLOCATIONS, the CHANNEL trio (send/recv/close), arbitrary
    defer nesting, any panics — whose [run_cmd] COMPLETES agrees end to end INCLUDING the
    final heaps, BUFFERS ([bufs_agree], boxed through each cell's own tag), CLOSEDNESS
    ([closed_agree] — a trace property, hence the [chans_open] start premise), the allocator
    pointer, and capacities pinned to the world's ([ucap_of_world]) — from the [ustart_w]
    mirrored start (the completion premise is the well-formedness gate; for [structurally_total_cmd]
    commands completion is a THEOREM — cmd.v's [run_cmd_terminates] — so consumers compose
    the two).  Plus cmd.v-side properties for a COMPLETING [run_cmd] on ANY [c]: output only
    APPENDS, and a panic-free completing run returns [ORet].
    The EXACT gated public-surface set is the [Print Assumptions] block at the end of this file (the single in-file
    authority); this header does not re-enumerate it.
    There is NO public projection-observer theorem: every unified-side run/unwind lemma is LOCAL
    (file-private) proof plumbing grounded directly in cmd.v's [go]/[unwind_defers] — no exported
    theorem concludes with a private observer, so a consumer cannot prove bridge facts against
    anything but [run_cmd].  (No SPAWN/SELECT in this fragment — [uc_bufs] carries the
    channel trio's effects, [uc_heap] the heap commands'; steps append [KWrite]/[KRead]/
    [KSend]/[KRecv]/[KClose] to [uc_trace], which stays existential in the bridge's statement
    beyond the [closed_agree] conclusion.)
    Proof-only: emits no Go, adds no axiom. *)

From Fido Require Import preamble concurrency cmd unified.
From Fido Require Import GoRuntimeTypes.
From Fido Require Import GoEffects.
From Fido Require Import GoSlice.
From Fido Require Import GoHeap.   (* AllocFrontierOk — the CAlloc gate lemmas live where alloc_world meets it *)
From Fido Require Import GoPanic.  (* the channel trio's Go-faithful CLOSED-channel panics (send/close on closed); the would-block markers are NOT faithful — see GoPanic's header *)
From Fido Require Import GoNumeric.  (* GoI64/TI64 — the closed-recv typed-zero instance obligations *)
From Stdlib Require Import List Lia.
Import ListNotations.

(** PUBLIC.  The total structural translation: cmd.v command tree -> [UCmd]'s
    output/panic/return/defer + heap + channel fragment (no spawn/select; defer is func-scoped
    WITHOUT recover), [COut]'s println flag PRESERVED into [UOut]'s flag and every [URecv] zero the
    TYPED [zero_val]. *)
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
  (* the channel trio.  [CChRecv]'s closed-recv zero is the TYPED [zero_val] through the
     syntax tag — Go's per-element-type zero, never a global fallback (the ⛔ obligation). *)
  | CChSend c v k => USend c v (cmd_to_ucmd k)
  | CChRecv c tg f =>
      URecv c (match tg with existT _ _ tgt => anyt tgt (zero_val tgt) end)
              (fun x => cmd_to_ucmd (f x))
  | CChClose c k => UClose c (cmd_to_ucmd k)
  end.

(** PUBLIC + GATED: the IMAGE seal — [cmd_to_ucmd] lands in the TRANSLATED fragment BY
    CONSTRUCTION: output/panic/defer, the heap trio (write/read/alloc), and the channel trio
    (send/recv/close — the recv zeros are the TYPED [zero_val]s the translation supplies);
    NO spawn/select form ever ([USelect]/[USpawn] excluded) — the single-goroutine
    deterministic fragment (plans/bridge-effects.md). *)
Inductive UFrag {V : Type} : @UCmd V -> Prop :=
  | UF_ret : UFrag URet
  | UF_out : forall pb xs k, UFrag k -> UFrag (UOut pb xs k)
  | UF_pan : forall v, UFrag (UPan v)
  | UF_dfr : forall d k, UFrag d -> UFrag k -> UFrag (UDfr d k)
  | UF_wr  : forall l v k, UFrag k -> UFrag (UWrite l v k)
  | UF_rd  : forall l f, (forall x, UFrag (f x)) -> UFrag (URead l f)
  | UF_al  : forall v f, (forall l, UFrag (f l)) -> UFrag (UAlloc v f)
  | UF_sn  : forall c v k, UFrag k -> UFrag (USend c v k)
  | UF_rc  : forall c z f, (forall x, UFrag (f x)) -> UFrag (URecv c z f)
  | UF_cl  : forall c k, UFrag k -> UFrag (UClose c k).
Theorem cmd_to_ucmd_fragment : forall c : Cmd unit, UFrag (cmd_to_ucmd c).
Proof.
  fix IH 1. intros [u | pb xs c' | v | d c' | l v c' | l f | v f | ch v c' | ch tg f | ch c']; cbn [cmd_to_ucmd].
  - constructor.
  - constructor. exact (IH c').
  - constructor.
  - constructor; [exact (IH d) | exact (IH c')].
  - constructor. exact (IH c').
  - constructor. intro x. exact (IH (f x)).
  - constructor. intro l. exact (IH (f l)).
  - constructor. exact (IH c').
  - constructor. intro x. exact (IH (f x)).
  - constructor. exact (IH c').
Qed.


(** [vz] — the start configs' UNALLOCATED-HEAP default at this instance, and nothing more
    (the calculus has NO global closed-recv zero any more: [URecv]/[USelect] carry the zero
    PER SITE).  It is an ARBITRARY [GoAny], NOT a Go zero value, and every public statement
    below that MENTIONS the unified [GoAny] configuration ([ustart_w]) UNIVERSALLY
    QUANTIFIES it (section generalization; the pure [run_cmd]-side theorems in this section
    never involve it).  The license: [bridge_effects_agree] starts from the [ustart_w] heap
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

(** ---- The CHANNEL mirroring kit ----
    [bufs_of_world w c]: the cell's buffer BOXED through the cell's own tag (synthetic
    position 0 — the agreements ignore positions; they exist for happens-before, which the
    single-goroutine bridge does not consult).
    ⚠ WfTrace / HAPPENS-BEFORE BOUNDARY: that synthetic position 0 on an INITIAL buffered
    value has NO producing [KSend] in the (empty) start trace, so a buffered recv can emit
    [KRecv c 0] with no earlier [KSend c 0].  [bridge_effects_agree] concludes [bufs_agree]
    and [closed_agree] ONLY — it does NOT conclude [WfTrace] and MUST NOT be composed with
    [concurrency.v]'s happens-before / race-freedom ([WfTrace] requires every [KRecv]'s
    source to point at an earlier [KSend]/[KClose]) without an extra invariant: empty initial
    buffers, or a buffer-origin invariant giving each initial value a real producer event.
    [ucap_of_world w c]: the cell's capacity —
    sound to FIX at the start world because the trio has NO make-channel, so the chan-heap
    DOMAIN (and every cap) is invariant across a bridged run.  [chans_open w]: every
    allocated cell OPEN — the bridge's start premise (unified closedness is a TRACE
    property, so a pre-closed START cell is unrepresentable in an empty trace; closure
    during the run emits the KClose on both sides consistently). *)
Definition bufs_of_world (w : World) : nat -> list (GoAny * nat) :=
  fun c => match w_chans w c with
           | Some (existT _ E (tag, (buf, _))) => map (fun v => (existT _ E (v, tag), 0)) buf
           | None => nil
           end.
Definition ucap_of_world (w : World) : nat -> option nat :=
  fun c => match w_chans w c with
           | Some (existT _ _ (_, (_, (_, cap)))) => cap
           | None => None
           end.
Definition chans_open (w : World) : Prop :=
  forall c E tag buf closed cap,
    w_chans w c = Some (existT _ E (tag, (buf, (closed, cap)))) -> closed = false.
(** the two run-time agreements the invariant threads *)
Definition bufs_agree (b : nat -> list (GoAny * nat)) (ch : ChanHeap) : Prop :=
  forall c, map fst (b c) = match ch c with
                            | Some (existT _ E (tag, (buf, _))) =>
                                map (fun v => existT _ E (v, tag)) buf
                            | None => nil
                            end.
Definition closed_agree (tr : Trace) (ch : ChanHeap) : Prop :=
  forall c, closedb tr c = match ch c with
                           | Some (existT _ _ (_, (_, (closed, _)))) => closed
                           | None => false
                           end.

(** [ucap_agree]: the relation's capacity parameter matches every allocated cell's cap
    (and is [None] on absent cells).  Preserved down a run — the trio has no make-channel
    and no op changes a cap. *)
Definition ucap_agree (ucap : nat -> option nat) (ch : ChanHeap) : Prop :=
  forall c, ucap c = match ch c with
                     | Some (existT _ _ (_, (_, (_, cap)))) => cap
                     | None => None
                     end.

(** PUBLIC.  The start config whose heap MIRRORS a [World]'s allocated cells ([heap_of_world]
    below) — the heap-bridging theorems start here, so their statements need no side
    agreement premise. *)
Definition ustart_w (w : World) (u : UCmdG) : UConfig :=
  mkUCfg (fun t => if Nat.eqb t 0 then u else URet)
         (bufs_of_world w) (heap_of_world w) (fun t => Nat.eqb t 0) nil nil (fun _ => nil) (fun _ => None)
         (w_next w).   (* pointer + buffers MIRROR the World's *)
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

(** channel-agreement preservation helpers *)
Local Lemma heap_write_chans : forall l v w w',
  heap_write l v w = Some w' -> w_chans w' = w_chans w.
Proof.
  intros l v w w' H. unfold heap_write in H.
  destruct (w_refs w l) as [[T [tc y]]|]; [ | discriminate H ].
  destruct v as [A [x ta]].
  destruct (tag_eq ta tc); [ | discriminate H ].
  injection H as <-. reflexivity.
Qed.
(** appending a NON-CLOSE event never closes anything *)
Local Lemma closed_agree_ev : forall tr (ch : ChanHeap) ev,
  closed_agree tr ch -> (forall c, closedb (ev :: nil) c = false) ->
  closed_agree (tr ++ ev :: nil) ch.
Proof.
  intros tr ch ev H He c. rewrite closedb_app, He, Bool.orb_false_r. apply H.
Qed.
(** a channel-cell update at [c0] leaves every OTHER channel's view alone; agreements
    step by re-checking [c0] and delegating the rest *)
Local Lemma chan_cell_upd_other : forall c0 cell w c,
  c <> c0 -> w_chans (chan_cell_upd c0 cell w) c = w_chans w c.
Proof.
  intros c0 cell w c Hne. cbn [chan_cell_upd w_chans].
  destruct (Nat.eqb c c0) eqn:E; [ apply PeanoNat.Nat.eqb_eq in E; contradiction | reflexivity ].
Qed.
Local Lemma chan_cell_upd_same : forall c0 cell w,
  w_chans (chan_cell_upd c0 cell w) c0 = Some cell.
Proof.
  intros c0 cell w. cbn [chan_cell_upd w_chans]. rewrite PeanoNat.Nat.eqb_refl. reflexivity.
Qed.
Local Lemma heap_write_next_chans_refs : forall v w,
  w_chans (alloc_world v w) = w_chans w.
Proof. reflexivity. Qed.

(** a successful coercion cannot cross tags: the sent box and the stored box are ONE GoAny
    (the send agreement's key; stands on [tag_eq_sound]) *)
Local Lemma tag_coerce_box : forall {A B} (want : GoTypeTag A) (have : GoTypeTag B) (x : B) (y : A),
  tag_coerce want have x = Some y ->
  existT (fun T => (T * GoTypeTag T)%type) B (x, have)
  = existT (fun T => (T * GoTypeTag T)%type) A (y, want).
Proof.
  intros A B want have x y H. unfold tag_coerce in H.
  destruct (tag_eq want have) as [p|] eqn:Hq; [ | discriminate H ].
  injection H as <-.
  pose proof (tag_eq_sound want have p Hq) as Hs.
  destruct p. cbn in Hs |- *. subst have. reflexivity.
Qed.
(** room transfers from the cell's capacity check to the calculus' [uroom] *)
Local Lemma room_from_agree : forall b (ch : ChanHeap) ucap c E tag buf closed cap,
  bufs_agree b ch -> ucap_agree ucap ch ->
  ch c = Some (existT _ E (tag, (buf, (closed, cap)))) ->
  chan_room_cap (length buf) cap = true ->
  uroom ucap b c = true.
Proof.
  intros b ch ucap c E tag buf closed cap Hba Hua Hc Hr.
  unfold uroom. rewrite (Hua c), Hc.
  destruct cap as [n|]; [ | reflexivity ].
  cbn [chan_room_cap] in Hr.
  assert (Hlen : length (b c) = length buf).
  { pose proof (Hba c) as Hb. rewrite Hc in Hb.
    rewrite <- (map_length fst (b c)), Hb, map_length. reflexivity. }
  rewrite Hlen. exact Hr.
Qed.

(** Phase A, SEMANTIC (heap AND channel ops included): grounded directly in [go]'s RESULT —
    given a successful body run and a calculus state agreeing with [w] (heap, buffers,
    trace-closedness, capacities), the [ustep] run mirrors it: program per [oc], defers =
    [ds] (in [go]'s order), output advanced by exactly [go]'s delta, final heaps AND
    buffers/closedness AGREE with the result world, capacities invariant.  The trace is
    EXISTENTIAL beyond its closedness view (steps emit [KWrite]/[KRead]/[KSend]/[KRecv]/
    [KClose] events — the race substrate). *)
Local Lemma body_runs_sem : forall c w oc ds ucap p b h lv tr o df pa,
  go c w = Some (oc, ds) ->
  heap_agrees h (w_refs w) ->
  bufs_agree b (w_chans w) ->
  closed_agree tr (w_chans w) ->
  ucap_agree ucap (w_chans w) ->
  lv 0 = true -> p 0 = cmd_to_ucmd c ->
  exists p' b' h' tr' df' evs,
    usteps ucap (mkUCfg p b h lv tr o df pa (w_next w))
                (mkUCfg p' b' h' lv tr' (o ++ map (fun e => (0, e)) evs) df' pa
                        (w_next (outcome_world oc)))
    /\ p' 0 = (match oc with ORet _ _ => URet | OPanic v _ => UPan v end)
    /\ df' 0 = map cmd_to_ucmd ds ++ df 0
    /\ heap_agrees h' (w_refs (outcome_world oc))
    /\ bufs_agree b' (w_chans (outcome_world oc))
    /\ closed_agree tr' (w_chans (outcome_world oc))
    /\ ucap_agree ucap (w_chans (outcome_world oc))
    /\ w_output (outcome_world oc) = w_output w ++ evs.
Proof.
  intros c.
  induction c as [a | bo xs c' IH | v | d c' IHc' | l v c' IH | l f IH | v f IH
                 | ch v c' IH | ch tg f IH | ch c' IH] using Cmd_rect';
    intros w oc ds ucap p b h lv tr o df pa Hgo Hha Hba Hca Hua Hlv Hp;
    cbn [go] in Hgo; cbn [cmd_to_ucmd] in Hp.
  - (* CRet *)
    injection Hgo as <- <-.
    exists p, b, h, tr, df, nil. cbn [map]. rewrite !app_nil_r.
    repeat split; try assumption. apply usteps_refl.
  - (* COut *)
    destruct (IH (w_log bo xs w) oc ds ucap (upd p 0 (cmd_to_ucmd c')) b h lv tr
                 (o ++ ((0, (bo, xs)) :: nil)) df pa Hgo Hha Hba Hca Hua Hlv (upd_same _ _ _))
      as [p' [b' [h' [tr' [df' [evs [Hus [Hprog [Hdf [Hha2 [Hba2 [Hca2 [Hua2 Hout]]]]]]]]]]]]].
    exists p', b', h', tr', df', ((bo, xs) :: evs).
    split; [ | split; [ exact Hprog | split; [ exact Hdf | split; [ exact Hha2 | split; [ exact Hba2 | split; [ exact Hca2 | split; [ exact Hua2 | ] ] ] ] ] ] ].
    + replace (o ++ map (fun e => (0, e)) ((bo, xs) :: evs))
         with ((o ++ ((0, (bo, xs)) :: nil)) ++ map (fun e => (0, e)) evs)
        by (cbn [map]; rewrite <- app_assoc; reflexivity).
      eapply usteps_step; [ eapply ustep_out; [ exact Hlv | exact Hp ] | exact Hus ].
    + rewrite Hout. cbn [w_log w_output]. rewrite <- app_assoc. reflexivity.
  - (* CPan *)
    injection Hgo as <- <-.
    exists p, b, h, tr, df, nil. cbn [map]. rewrite !app_nil_r.
    repeat split; try assumption. apply usteps_refl.
  - (* CDfr *)
    destruct (go c' w) as [[oc0 ds0]|] eqn:E; [ | discriminate Hgo ].
    injection Hgo as H1 H2. subst oc ds.
    destruct (IHc' w oc0 ds0 ucap (upd p 0 (cmd_to_ucmd c')) b h lv tr o
                  (upd df 0 (cmd_to_ucmd d :: df 0)) pa E Hha Hba Hca Hua Hlv (upd_same _ _ _))
      as [p' [b' [h' [tr' [df' [evs [Hus [Hprog [Hdf [Hha2 [Hba2 [Hca2 [Hua2 Hout]]]]]]]]]]]]].
    exists p', b', h', tr', df', evs.
    split; [ | split; [ exact Hprog | split; [ | split; [ exact Hha2 | split; [ exact Hba2 | split; [ exact Hca2 | split; [ exact Hua2 | exact Hout ] ] ] ] ] ] ].
    + eapply usteps_step; [ eapply ustep_defer; [ exact Hlv | exact Hp ] | exact Hus ].
    + rewrite Hdf, upd_same, map_app. cbn [map]. rewrite <- app_assoc. reflexivity.
  - (* CWrite *)
    destruct (heap_write l v w) as [w'|] eqn:Hw; [ | discriminate Hgo ].
    assert (Hba' : bufs_agree b (w_chans w'))
      by (rewrite (heap_write_chans l v w w' Hw); exact Hba).
    assert (Hca' : closed_agree (tr ++ (mkEv 0 (KWrite l) :: nil)) (w_chans w'))
      by (rewrite (heap_write_chans l v w w' Hw);
          apply closed_agree_ev; [ exact Hca | intro c0; reflexivity ]).
    assert (Hua' : ucap_agree ucap (w_chans w'))
      by (rewrite (heap_write_chans l v w w' Hw); exact Hua).
    destruct (IH w' oc ds ucap (upd p 0 (cmd_to_ucmd c')) b (upd h l v) lv
                 (tr ++ (mkEv 0 (KWrite l) :: nil)) o df pa Hgo
                 (heap_write_agrees h w l v w' Hha Hw) Hba' Hca' Hua' Hlv (upd_same _ _ _))
      as [p' [b' [h' [tr' [df' [evs [Hus [Hprog [Hdf [Hha2 [Hba2 [Hca2 [Hua2 Hout]]]]]]]]]]]]].
    exists p', b', h', tr', df', evs.
    split; [ | split; [ exact Hprog | split; [ exact Hdf | split; [ exact Hha2 | split; [ exact Hba2 | split; [ exact Hca2 | split; [ exact Hua2 | ] ] ] ] ] ] ].
    + eapply usteps_step; [ eapply ustep_write; [ exact Hlv | exact Hp ]
        | rewrite (heap_write_next l v w w' Hw) in Hus; exact Hus ].
    + rewrite Hout, (heap_write_output l v w w' Hw). reflexivity.
  - (* CRead *)
    destruct (w_refs w l) as [cell|] eqn:Hl; [ | discriminate Hgo ].
    pose proof (Hha l cell Hl) as Hhl.
    assert (Hca' : closed_agree (tr ++ (mkEv 0 (KRead l) :: nil)) (w_chans w))
      by (apply closed_agree_ev; [ exact Hca | intro c0; reflexivity ]).
    destruct (IH (any_of_cell cell) w oc ds ucap
                 (upd p 0 (cmd_to_ucmd (f (any_of_cell cell)))) b h lv
                 (tr ++ (mkEv 0 (KRead l) :: nil)) o df pa Hgo Hha Hba Hca' Hua Hlv (upd_same _ _ _))
      as [p' [b' [h' [tr' [df' [evs [Hus [Hprog [Hdf [Hha2 [Hba2 [Hca2 [Hua2 Hout]]]]]]]]]]]]].
    exists p', b', h', tr', df', evs.
    split; [ | split; [ exact Hprog | split; [ exact Hdf | split; [ exact Hha2 | split; [ exact Hba2 | split; [ exact Hca2 | split; [ exact Hua2 | exact Hout ] ] ] ] ] ] ].
    eapply usteps_step; [ eapply ustep_read; [ exact Hlv | exact Hp ] | ].
    rewrite Hhl. exact Hus.
  - (* CAlloc *)
    assert (Hca' : closed_agree (tr ++ (mkEv 0 (KWrite (w_next w)) :: nil)) (w_chans (alloc_world v w)))
      by (apply closed_agree_ev; [ exact Hca | intro c0; reflexivity ]).
    destruct (IH (w_next w) (alloc_world v w) oc ds ucap
                 (upd p 0 (cmd_to_ucmd (f (w_next w)))) b (upd h (w_next w) v) lv
                 (tr ++ (mkEv 0 (KWrite (w_next w)) :: nil)) o df pa Hgo
                 (heap_alloc_agrees h w v Hha) Hba Hca' Hua Hlv (upd_same _ _ _))
      as [p' [b' [h' [tr' [df' [evs [Hus [Hprog [Hdf [Hha2 [Hba2 [Hca2 [Hua2 Hout]]]]]]]]]]]]].
    exists p', b', h', tr', df', evs.
    split; [ | split; [ exact Hprog | split; [ exact Hdf | split; [ exact Hha2 | split; [ exact Hba2 | split; [ exact Hca2 | split; [ exact Hua2 | exact Hout ] ] ] ] ] ] ].
    eapply usteps_step; [ eapply ustep_alloc; [ exact Hlv | exact Hp ] | exact Hus ].
  - (* CChSend *)
    destruct (w_chans w ch) as [[E [tag [buf [closed cap]]]]|] eqn:Ec; [ | discriminate Hgo ].
    destruct v as [A0 [x ta]].
    destruct (tag_coerce tag ta x) as [xe|] eqn:Etc; [ | discriminate Hgo ].
    destruct closed eqn:Ecl.
    + (* send-on-closed: one panic step, both sides *)
      injection Hgo as <- <-.
      exists (upd p 0 (UPan rt_send_closed)), b, h, tr, df, nil.
      cbn [map]. rewrite !app_nil_r.
      split; [ | split; [ apply upd_same | repeat split; try assumption; reflexivity ] ].
      eapply usteps_step;
        [ eapply ustep_send_closed;
            [ exact Hlv | exact Hp | rewrite (Hca ch), Ec; reflexivity ]
        | apply usteps_refl ].
    + destruct (chan_room_cap (length buf) cap) eqn:Er; [ | discriminate Hgo ].
      set (w2 := chan_cell_upd ch (existT _ E (tag, (buf ++ xe :: nil, (false, cap)))) w).
      set (b2 := upd b ch (b ch ++ (existT (fun T => (T * GoTypeTag T)%type) A0 (x, ta), length tr) :: nil)).
      assert (Hba' : bufs_agree b2 (w_chans w2)).
      { intro c0. unfold b2. destruct (PeanoNat.Nat.eq_dec c0 ch) as [-> | Hne].
        - rewrite upd_same. unfold w2. rewrite chan_cell_upd_same.
          rewrite map_app, map_app. cbn [map fst].
          pose proof (Hba ch) as Hb. rewrite Ec in Hb. rewrite Hb.
          rewrite (tag_coerce_box tag ta x xe Etc). reflexivity.
        - rewrite (upd_other _ _ _ _ Hne). unfold w2.
          rewrite (chan_cell_upd_other _ _ _ _ Hne).
          pose proof (Hba c0) as Hb. exact Hb. }
      assert (Hca' : closed_agree (tr ++ (mkEv 0 (KSend ch) :: nil)) (w_chans w2)).
      { intro c0. destruct (PeanoNat.Nat.eq_dec c0 ch) as [-> | Hne].
        - unfold w2. rewrite chan_cell_upd_same, closedb_app. cbn.
          rewrite Bool.orb_false_r, (Hca ch), Ec. reflexivity.
        - unfold w2. rewrite (chan_cell_upd_other _ _ _ _ Hne), closedb_app. cbn.
          rewrite Bool.orb_false_r. apply Hca. }
      assert (Hua' : ucap_agree ucap (w_chans w2)).
      { intro c0. destruct (PeanoNat.Nat.eq_dec c0 ch) as [-> | Hne].
        - unfold w2. rewrite chan_cell_upd_same. rewrite (Hua ch), Ec. reflexivity.
        - unfold w2. rewrite (chan_cell_upd_other _ _ _ _ Hne). apply Hua. }
      destruct (IH w2 oc ds ucap (upd p 0 (cmd_to_ucmd c')) b2 h lv
                   (tr ++ (mkEv 0 (KSend ch) :: nil)) o df pa Hgo Hha Hba' Hca' Hua' Hlv (upd_same _ _ _))
        as [p' [b' [h' [tr' [df' [evs [Hus [Hprog [Hdf [Hha2 [Hba2 [Hca2 [Hua2 Hout]]]]]]]]]]]]].
      exists p', b', h', tr', df', evs.
      split; [ | split; [ exact Hprog | split; [ exact Hdf | split; [ exact Hha2 | split; [ exact Hba2 | split; [ exact Hca2 | split; [ exact Hua2 | exact Hout ] ] ] ] ] ] ].
      eapply usteps_step;
        [ eapply ustep_send;
            [ exact Hlv | exact Hp
            | rewrite (Hca ch), Ec; reflexivity
            | exact (room_from_agree b (w_chans w) ucap ch E tag buf false cap Hba Hua Ec Er) ]
        | exact Hus ].
  - (* CChRecv *)
    destruct (w_chans w ch) as [[E [tag [buf [closed cap]]]]|] eqn:Ec; [ | discriminate Hgo ].
    destruct tg as [T tgt].
    destruct (tag_eq tgt tag) as [pf|] eqn:Ete; [ | discriminate Hgo ].
    destruct buf as [|v0 rest].
    + (* closed + drained: the TYPED zero fires on both sides *)
      destruct closed eqn:Ecl; [ | discriminate Hgo ].
      assert (Hclosed : closedb tr ch = true) by (rewrite (Hca ch), Ec; reflexivity).
      destruct (closedb_true_witness _ _ Hclosed) as [pos [e [Hpos Hek]]].
      assert (Hbnil : b ch = nil).
      { pose proof (Hba ch) as Hb. rewrite Ec in Hb. cbn in Hb.
        destruct (b ch); [ reflexivity | discriminate Hb ]. }
      assert (Hca' : closed_agree (tr ++ (mkEv 0 (KRecv ch pos) :: nil)) (w_chans w))
        by (apply closed_agree_ev; [ exact Hca | intro c0; reflexivity ]).
      destruct (IH (anyt tgt (zero_val tgt)) w oc ds ucap
                   (upd p 0 (cmd_to_ucmd (f (anyt tgt (zero_val tgt))))) b h lv
                   (tr ++ (mkEv 0 (KRecv ch pos) :: nil)) o df pa Hgo Hha Hba Hca' Hua Hlv (upd_same _ _ _))
        as [p' [b' [h' [tr' [df' [evs [Hus [Hprog [Hdf [Hha2 [Hba2 [Hca2 [Hua2 Hout]]]]]]]]]]]]].
      exists p', b', h', tr', df', evs.
      split; [ | split; [ exact Hprog | split; [ exact Hdf | split; [ exact Hha2 | split; [ exact Hba2 | split; [ exact Hca2 | split; [ exact Hua2 | exact Hout ] ] ] ] ] ] ].
      eapply usteps_step;
        [ eapply ustep_recv_closed;
            [ exact Hlv | exact Hp | exact Hbnil | exact Hpos | exact Hek ]
        | exact Hus ].
    + (* buffered pop: the SAME box flows to both continuations *)
      pose proof (Hba ch) as Hb. rewrite Ec in Hb. cbn [map] in Hb.
      destruct (b ch) as [|[g s] brest] eqn:Ebch; [ discriminate Hb | ].
      cbn [map fst] in Hb. injection Hb as Hg Hbrest.
      set (w2 := chan_cell_upd ch (existT _ E (tag, (rest, (closed, cap)))) w).
      set (b2 := upd b ch brest).
      assert (Hba' : bufs_agree b2 (w_chans w2)).
      { intro c0. unfold b2. destruct (PeanoNat.Nat.eq_dec c0 ch) as [-> | Hne].
        - rewrite upd_same. unfold w2. rewrite chan_cell_upd_same. exact Hbrest.
        - rewrite (upd_other _ _ _ _ Hne). unfold w2.
          rewrite (chan_cell_upd_other _ _ _ _ Hne). apply Hba. }
      assert (Hca' : closed_agree (tr ++ (mkEv 0 (KRecv ch s) :: nil)) (w_chans w2)).
      { intro c0. destruct (PeanoNat.Nat.eq_dec c0 ch) as [-> | Hne].
        - unfold w2. rewrite chan_cell_upd_same, closedb_app. cbn.
          rewrite Bool.orb_false_r, (Hca ch), Ec. reflexivity.
        - unfold w2. rewrite (chan_cell_upd_other _ _ _ _ Hne), closedb_app. cbn.
          rewrite Bool.orb_false_r. apply Hca. }
      assert (Hua' : ucap_agree ucap (w_chans w2)).
      { intro c0. destruct (PeanoNat.Nat.eq_dec c0 ch) as [-> | Hne].
        - unfold w2. rewrite chan_cell_upd_same. rewrite (Hua ch), Ec. reflexivity.
        - unfold w2. rewrite (chan_cell_upd_other _ _ _ _ Hne). apply Hua. }
      destruct (IH (existT _ E (v0, tag)) w2 oc ds ucap
                   (upd p 0 (cmd_to_ucmd (f (existT _ E (v0, tag))))) b2 h lv
                   (tr ++ (mkEv 0 (KRecv ch s) :: nil)) o df pa Hgo Hha Hba' Hca' Hua' Hlv (upd_same _ _ _))
        as [p' [b' [h' [tr' [df' [evs [Hus [Hprog [Hdf [Hha2 [Hba2 [Hca2 [Hua2 Hout]]]]]]]]]]]]].
      exists p', b', h', tr', df', evs.
      split; [ | split; [ exact Hprog | split; [ exact Hdf | split; [ exact Hha2 | split; [ exact Hba2 | split; [ exact Hca2 | split; [ exact Hua2 | exact Hout ] ] ] ] ] ] ].
      eapply usteps_step;
        [ eapply ustep_recv; [ exact Hlv | exact Hp | exact Ebch ]
        | rewrite Hg; exact Hus ].
  - (* CChClose *)
    destruct (w_chans w ch) as [[E [tag [buf [closed cap]]]]|] eqn:Ec; [ | discriminate Hgo ].
    destruct closed eqn:Ecl.
    + (* close-on-closed: one panic step, both sides *)
      injection Hgo as <- <-.
      exists (upd p 0 (UPan rt_close_closed)), b, h, tr, df, nil.
      cbn [map]. rewrite !app_nil_r.
      split; [ | split; [ apply upd_same | repeat split; try assumption; reflexivity ] ].
      eapply usteps_step;
        [ eapply ustep_close_closed;
            [ exact Hlv | exact Hp | rewrite (Hca ch), Ec; reflexivity ]
        | apply usteps_refl ].
    + set (w2 := chan_cell_upd ch (existT _ E (tag, (buf, (true, cap)))) w).
      assert (Hba' : bufs_agree b (w_chans w2)).
      { intro c0. destruct (PeanoNat.Nat.eq_dec c0 ch) as [-> | Hne].
        - unfold w2. rewrite chan_cell_upd_same.
          pose proof (Hba ch) as Hb. rewrite Ec in Hb. exact Hb.
        - unfold w2. rewrite (chan_cell_upd_other _ _ _ _ Hne). apply Hba. }
      assert (Hca' : closed_agree (tr ++ (mkEv 0 (KClose ch) :: nil)) (w_chans w2)).
      { intro c0. destruct (PeanoNat.Nat.eq_dec c0 ch) as [-> | Hne].
        - unfold w2. rewrite chan_cell_upd_same, closedb_app. cbn.
          rewrite PeanoNat.Nat.eqb_refl, Bool.orb_true_r. reflexivity.
        - unfold w2. rewrite (chan_cell_upd_other _ _ _ _ Hne), closedb_app. cbn.
          assert (Eeq : Nat.eqb ch c0 = false)
            by (apply PeanoNat.Nat.eqb_neq; intro; subst; apply Hne; reflexivity).
          rewrite Eeq, Bool.orb_false_r. apply Hca. }
      assert (Hua' : ucap_agree ucap (w_chans w2)).
      { intro c0. destruct (PeanoNat.Nat.eq_dec c0 ch) as [-> | Hne].
        - unfold w2. rewrite chan_cell_upd_same. rewrite (Hua ch), Ec. reflexivity.
        - unfold w2. rewrite (chan_cell_upd_other _ _ _ _ Hne). apply Hua. }
      destruct (IH w2 oc ds ucap (upd p 0 (cmd_to_ucmd c')) b h lv
                   (tr ++ (mkEv 0 (KClose ch) :: nil)) o df pa Hgo Hha Hba' Hca' Hua' Hlv (upd_same _ _ _))
        as [p' [b' [h' [tr' [df' [evs [Hus [Hprog [Hdf [Hha2 [Hba2 [Hca2 [Hua2 Hout]]]]]]]]]]]]].
      exists p', b', h', tr', df', evs.
      split; [ | split; [ exact Hprog | split; [ exact Hdf | split; [ exact Hha2 | split; [ exact Hba2 | split; [ exact Hca2 | split; [ exact Hua2 | exact Hout ] ] ] ] ] ] ].
      eapply usteps_step;
        [ eapply ustep_close;
            [ exact Hlv | exact Hp | rewrite (Hca ch), Ec; reflexivity ]
        | exact Hus ].
Qed.


Local Lemma w_output_w_log : forall b xs w, w_output (w_log b xs w) = w_output w ++ ((b, xs) :: nil).
Proof. reflexivity. Qed.



Local Lemma map_snd_pair0 : forall (l : list (bool * list GoAny)), map snd (map (fun e => (0, e)) l) = l.
Proof. induction l as [|a l IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

(** [oc_set_world] only advances the world — it preserves the [Outcome]'s panic status (and sets its world). *)
Local Lemma ocpanic_set_world : forall (acc : Outcome unit) w, ocpanic (oc_set_world acc w) = ocpanic acc.
Proof. intros [[] w0 | v w0] w; reflexivity. Qed.
Local Lemma outcome_world_set_world : forall (acc : Outcome unit) w, outcome_world (oc_set_world acc w) = w.
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
    heap_agrees h (w_refs (outcome_world acc)) ->
    bufs_agree b (w_chans (outcome_world acc)) ->
    closed_agree tr (w_chans (outcome_world acc)) ->
    ucap_agree ucap (w_chans (outcome_world acc)) ->
    df 0 = map cmd_to_ucmd ds ++ ds_tail ->
    exists p' b' h' tr' df' pa' evs,
      usteps ucap (mkUCfg p b h lv tr o df pa (w_next (outcome_world acc)))
                  (mkUCfg p' b' h' lv tr' (o ++ map (fun e => (0, e)) evs) df' pa'
                          (w_next (outcome_world result)))
      /\ (p' 0 = URet \/ exists v, p' 0 = UPan v)
      /\ (match p' 0 with UPan v => Some v | _ => pa' 0 end) = mode_or (ocpanic result) qb
      /\ df' 0 = ds_tail
      /\ heap_agrees h' (w_refs (outcome_world result))
      /\ bufs_agree b' (w_chans (outcome_world result))
      /\ closed_agree tr' (w_chans (outcome_world result))
      /\ ucap_agree ucap (w_chans (outcome_world result))
      /\ w_output (outcome_world result) = w_output (outcome_world acc) ++ evs.
Proof.
  intros ds acc result Hun.
  induction Hun as [acc | d ds acc oc_d ds_d net r Hgo Hnest IHnest Hrest IHrest];
    intros ucap p b h lv tr o df pa ds_tail qb Hlv Hp Hq0 Hha Hba Hca Hua Hdf.
  - cbn [map] in Hdf. rewrite app_nil_l in Hdf.
    exists p, b, h, tr, df, pa, nil. cbn [map]. rewrite !app_nil_r.
    repeat split; try assumption. apply usteps_refl.
  - cbn [map] in Hdf.
    destruct (pop_defer_step ucap p b h lv tr o df pa (w_next (outcome_world acc)) d
                (map cmd_to_ucmd ds ++ ds_tail) (mode_or (ocpanic acc) qb) Hlv Hp Hq0 Hdf)
      as [paP [HpaP Hpop]].
    destruct (body_runs_sem d (outcome_world acc) oc_d ds_d ucap
                (upd p 0 (cmd_to_ucmd d)) b h lv tr o
                (upd df 0 (map cmd_to_ucmd ds ++ ds_tail)) paP
                Hgo Hha Hba Hca Hua Hlv (upd_same _ _ _))
      as [pA [bA [hA [trA [dfA [evs0 [HusA [HprogA [HdfA [HhaA [HbaA [HcaA [HuaA Hout0]]]]]]]]]]]]].
    rewrite upd_same in HdfA.
    assert (HprogA' : pA 0 = URet \/ exists v, pA 0 = UPan v)
      by (rewrite HprogA; destruct oc_d as [[] ?|vd ?]; [ left; reflexivity | right; exists vd; reflexivity ]).
    (* the nested scope's mode: the sub-derivation runs at base [mode_or (ocpanic acc) qb] *)
    assert (HqA : (match pA 0 with UPan v => Some v | _ => paP 0 end)
                  = mode_or (ocpanic (oc_unit oc_d)) (mode_or (ocpanic acc) qb)).
    { rewrite HprogA. destruct oc_d as [[] ?|vd ?]; cbn [oc_unit ocpanic mode_or]; [ exact HpaP | reflexivity ]. }
    assert (HhaA' : heap_agrees hA (w_refs (outcome_world (oc_unit oc_d))))
      by (destruct oc_d; exact HhaA).
    assert (HbaA' : bufs_agree bA (w_chans (outcome_world (oc_unit oc_d))))
      by (destruct oc_d; exact HbaA).
    assert (HcaA' : closed_agree trA (w_chans (outcome_world (oc_unit oc_d))))
      by (destruct oc_d; exact HcaA).
    assert (HuaA' : ucap_agree ucap (w_chans (outcome_world (oc_unit oc_d))))
      by (destruct oc_d; exact HuaA).
    destruct (IHnest ucap pA bA hA lv trA (o ++ map (fun e => (0, e)) evs0) dfA paP
                 (map cmd_to_ucmd ds ++ ds_tail) (mode_or (ocpanic acc) qb)
                 Hlv HprogA' HqA HhaA' HbaA' HcaA' HuaA' HdfA)
      as [pB [bB [hB [trB [dfB [paB [evs1 [HusB [HprogB [HqB [HdfB [HhaB [HbaB [HcaB [HuaB Hout1]]]]]]]]]]]]]]].
    (* the tail continues at the combined accumulator, same base [qb] *)
    assert (HqB' : (match pB 0 with UPan v => Some v | _ => paB 0 end)
                   = mode_or (ocpanic (match net with
                                       | OPanic v' w' => OPanic v' w'
                                       | ORet _ w' => oc_set_world acc w' end)) qb).
    { rewrite HqB. destruct net as [[] wn | vn wn]; cbn [ocpanic mode_or].
      - rewrite ocpanic_set_world. reflexivity.
      - reflexivity. }
    assert (HhaB' : heap_agrees hB (w_refs (outcome_world (match net with
                                       | OPanic v' w' => OPanic v' w'
                                       | ORet _ w' => oc_set_world acc w' end)))).
    { destruct net as [[] wn | vn wn]; cbn [outcome_world] in HhaB |- *;
        [ rewrite outcome_world_set_world; exact HhaB | exact HhaB ]. }
    assert (HbaB' : bufs_agree bB (w_chans (outcome_world (match net with
                                       | OPanic v' w' => OPanic v' w'
                                       | ORet _ w' => oc_set_world acc w' end)))).
    { destruct net as [[] wn | vn wn]; cbn [outcome_world] in HbaB |- *;
        [ rewrite outcome_world_set_world; exact HbaB | exact HbaB ]. }
    assert (HcaB' : closed_agree trB (w_chans (outcome_world (match net with
                                       | OPanic v' w' => OPanic v' w'
                                       | ORet _ w' => oc_set_world acc w' end)))).
    { destruct net as [[] wn | vn wn]; cbn [outcome_world] in HcaB |- *;
        [ rewrite outcome_world_set_world; exact HcaB | exact HcaB ]. }
    assert (HuaB' : ucap_agree ucap (w_chans (outcome_world (match net with
                                       | OPanic v' w' => OPanic v' w'
                                       | ORet _ w' => oc_set_world acc w' end)))).
    { destruct net as [[] wn | vn wn]; cbn [outcome_world] in HuaB |- *;
        [ rewrite outcome_world_set_world; exact HuaB | exact HuaB ]. }
    destruct (IHrest ucap pB bB hB lv trB
                 ((o ++ map (fun e => (0, e)) evs0) ++ map (fun e => (0, e)) evs1)
                 dfB paB ds_tail qb Hlv HprogB HqB' HhaB' HbaB' HcaB' HuaB' HdfB)
      as [pC [bC [hC [trC [dfC [paC [evs2 [HusC [HprogC [HqC [HdfC [HhaC [HbaC [HcaC [HuaC Hout2]]]]]]]]]]]]]]].
    exists pC, bC, hC, trC, dfC, paC, (evs0 ++ evs1 ++ evs2).
    split; [ | split; [ exact HprogC | split; [ exact HqC | split; [ exact HdfC | split; [ exact HhaC | split; [ exact HbaC | split; [ exact HcaC | split; [ exact HuaC | ] ] ] ] ] ] ] ].
    + replace (o ++ map (fun e => (0, e)) (evs0 ++ evs1 ++ evs2))
         with (((o ++ map (fun e => (0, e)) evs0) ++ map (fun e => (0, e)) evs1)
                 ++ map (fun e => (0, e)) evs2)
        by (rewrite !map_app, !app_assoc; reflexivity).
      rewrite oc_unit_world in HusB.
      assert (HnextC : outcome_world (match net with
                                 | OPanic v' w' => OPanic v' w'
                                 | ORet _ w' => oc_set_world acc w' end) = outcome_world net)
        by (destruct net as [[] wn | vn wn]; cbn [outcome_world]; [ rewrite outcome_world_set_world | ]; reflexivity).
      rewrite HnextC in HusC.
      eapply usteps_trans; [ exact Hpop | ].
      eapply usteps_trans; [ exact HusA | ].
      eapply usteps_trans; [ exact HusB | exact HusC ].
    + rewrite Hout2.
      assert (Hwacc' : w_output (outcome_world (match net with
                                            | OPanic v' w' => OPanic v' w'
                                            | ORet _ w' => oc_set_world acc w' end))
                       = w_output (outcome_world net))
        by (destruct net as [[] wn | vn wn]; cbn [outcome_world]; [ rewrite outcome_world_set_world | ]; reflexivity).
      assert (Hwseed : w_output (outcome_world (oc_unit oc_d)) = w_output (outcome_world oc_d))
        by (destruct oc_d; reflexivity).
      rewrite Hwacc', Hout1, Hwseed, Hout0, <- !app_assoc. reflexivity.
Qed.


(** OUTPUT-MONOTONICITY of [run_cmd], for ANY [c] (arbitrary defer nesting, heap AND channel
    ops included — no write, allocation, send, recv, or close touches [w_output]): a
    COMPLETING run only ever APPENDS to the world's output,
    never RETRACTS — Go's deferred actions and panics cannot un-print already-printed output.
    Structural on the tree — the [CDfr] case composes the continuation's delta with the deferred
    scope's (whose final world is the result's world in BOTH combine arms).  A standalone
    cmd.v-side property; the bridge [bridge_effects_agree] establishes its output agreement
    independently, so this theorem is a sibling, not a dependency, of the bridge. *)
Theorem run_cmd_out_monotone : forall (c : Cmd unit) w oc,
  run_cmd c w = Some oc ->
  exists evs, w_output (outcome_world oc) = w_output w ++ evs.
Proof.
  fix IH 1. intros [a | b xs c' | v | d c' | l v c' | l f | v f | ch v c' | ch tg f | ch c'] w oc H; cbn [run_cmd] in H.
  - injection H as <-. exists nil. cbn [outcome_world]. rewrite app_nil_r. reflexivity.
  - destruct (IH c' (w_log b xs w) oc H) as [evs Hevs].
    exists ((b, xs) :: evs). rewrite Hevs, w_output_w_log, <- app_assoc. reflexivity.
  - injection H as <-. exists nil. cbn [outcome_world]. rewrite app_nil_r. reflexivity.
  - destruct (run_cmd c' w) as [oc0|] eqn:E0; [ | discriminate H ].
    destruct (run_cmd d (outcome_world oc0)) as [[[] w'|vd w']|] eqn:Ed; try discriminate H.
    + injection H as <-.
      destruct (IH c' w oc0 E0) as [evs0 Hevs0].
      destruct (IH d (outcome_world oc0) (ORet tt w') Ed) as [evs1 Hevs1].
      exists (evs0 ++ evs1). rewrite outcome_world_set_world.
      cbn [outcome_world] in Hevs1. rewrite Hevs1, Hevs0, <- app_assoc. reflexivity.
    + injection H as <-.
      destruct (IH c' w oc0 E0) as [evs0 Hevs0].
      destruct (IH d (outcome_world oc0) (OPanic vd w') Ed) as [evs1 Hevs1].
      exists (evs0 ++ evs1). cbn [outcome_world] in Hevs1 |- *.
      rewrite Hevs1, Hevs0, <- app_assoc. reflexivity.
  - destruct (heap_write l v w) as [w'|] eqn:E; [ | discriminate H ].
    destruct (IH c' w' oc H) as [evs Hevs].
    exists evs. rewrite Hevs, (heap_write_output l v w w' E). reflexivity.
  - destruct (w_refs w l) as [cell|]; [ | discriminate H ].
    exact (IH (f (any_of_cell cell)) w oc H).
  - exact (IH (f (w_next w)) (alloc_world v w) oc H).
  - (* CChSend — TAG-FIRST: match cell, then v, then tag_coerce, THEN closed *)
    destruct (w_chans w ch) as [[E [tag [buf [closed cap]]]]|]; [ | discriminate H ].
    destruct v as [A0 [x ta]].
    destruct (tag_coerce tag ta x) as [xe|]; [ | discriminate H ].
    destruct closed.
    + injection H as <-. exists nil. cbn [outcome_world]. rewrite app_nil_r. reflexivity.
    + destruct (chan_room_cap (length buf) cap); [ | discriminate H ].
      exact (IH c' _ oc H).
  - (* CChRecv *)
    destruct (w_chans w ch) as [[E [tag [buf [closed cap]]]]|]; [ | discriminate H ].
    destruct tg as [T tgt].
    destruct (tag_eq tgt tag); [ | discriminate H ].
    destruct buf as [|v0 rest].
    + destruct closed; [ | discriminate H ].
      exact (IH (f (anyt tgt (zero_val tgt))) w oc H).
    + exact (IH (f (existT _ E (v0, tag))) _ oc H).
  - (* CChClose *)
    destruct (w_chans w ch) as [[E [tag [buf [closed cap]]]]|]; [ | discriminate H ].
    destruct closed.
    + injection H as <-. exists nil. cbn [outcome_world]. rewrite app_nil_r. reflexivity.
    + exact (IH c' _ oc H).
Qed.

(** PANIC-FREEDOM of [run_cmd] for ANY [c] (nested defers included): a [cmd_no_panic c] run that
    COMPLETES returns [ORet] — Go's panic-free program cannot end in a panic.  Structural; the
    [CDfr] case threads both conjuncts.  A standalone cmd.v-side property, panic-free companion to
    [run_cmd_out_monotone]. *)
Theorem run_cmd_no_panic_ret : forall (c : Cmd unit) w oc,
  run_cmd c w = Some oc -> cmd_no_panic c = true ->
  exists w', oc = ORet tt w'.
Proof.
  fix IH 1. intros [a | b xs c' | v | d c' | l v c' | l f | v f | ch v c' | ch tg f | ch c'] w oc H Hnp;
    cbn [cmd_no_panic] in Hnp; cbn [run_cmd] in H.
  - destruct a. injection H as <-. exists w. reflexivity.
  - exact (IH c' (w_log b xs w) oc H Hnp).
  - discriminate Hnp.
  - apply andb_prop in Hnp. destruct Hnp as [Hd Hc'].
    destruct (run_cmd c' w) as [oc0|] eqn:E0; [ | discriminate H ].
    destruct (run_cmd d (outcome_world oc0)) as [ocd|] eqn:Ed; [ | discriminate H ].
    destruct (IH d (outcome_world oc0) ocd Ed Hd) as [wd ->].
    injection H as <-.
    destruct (IH c' w oc0 E0 Hc') as [w0 ->].
    exists wd. reflexivity.
  - discriminate Hnp.
  - discriminate Hnp.
  - discriminate Hnp.
  - discriminate Hnp.
  - discriminate Hnp.
  - discriminate Hnp.
Qed.




(** the mirrored start satisfies all three channel agreements *)
Local Lemma bufs_of_world_agrees : forall w, bufs_agree (bufs_of_world w) (w_chans w).
Proof.
  intros w c. unfold bufs_of_world.
  destruct (w_chans w c) as [[E [tag [buf [cl cap]]]]|]; [ | reflexivity ].
  induction buf as [|v0 rest IHb]; cbn; [ reflexivity | rewrite IHb; reflexivity ].
Qed.
Local Lemma closed_agree_start : forall w, chans_open w -> closed_agree nil (w_chans w).
Proof.
  intros w Hop c. cbn.
  destruct (w_chans w c) as [[E [tag [buf [cl cap]]]]|] eqn:Ec; [ | reflexivity ].
  symmetry. exact (Hop c E tag buf cl cap Ec).
Qed.
Local Lemma ucap_of_world_agrees : forall w, ucap_agree (ucap_of_world w) (w_chans w).
Proof. intros w c. reflexivity. Qed.

(** ★ The GENERAL bridge (PUBLIC + GATED): for ANY [c] — heap reads/writes/ALLOCATIONS, the
    CHANNEL trio, arbitrary defer nesting, any panics — whose [run_cmd] COMPLETES (given the
    [chans_open] start), the [usteps] run at [ucap_of_world w] from the [ustart_w w] config
    (heap + buffers mirrored, boxed) AGREES end to end, INCLUDING
    the final heaps ([heap_agrees] against the result world's allocated cells).  Assembly:
    [body_runs_sem] (Phase A, semantic) + [unwind_heap] (the deferred-heap unwind, by
    induction on the [unwind_defers] derivation obtained from [run_cmd_eval]) + the 2-mode
    final done.  The completion premise is the well-formedness gate (an unallocated access
    never completes — [cread_unallocated_absent] below). *)
Theorem bridge_effects_agree : forall (c : Cmd unit) w oc,
  run_cmd c w = Some oc ->
  chans_open w ->
  exists uc : UConfig,
    usteps (ucap_of_world w) (ustart_w w (cmd_to_ucmd c)) uc
    /\ uc_live uc 0 = false
    /\ uc_panic uc 0 = ocpanic oc
    /\ w_output (outcome_world oc) = w_output w ++ map snd (uc_out uc)
    /\ heap_agrees (uc_heap uc) (w_refs (outcome_world oc))
    /\ bufs_agree (uc_bufs uc) (w_chans (outcome_world oc))       (* the channel agreements, *)
    /\ closed_agree (uc_trace uc) (w_chans (outcome_world oc))    (* end to end, *)
    /\ ucap_agree (ucap_of_world w) (w_chans (outcome_world oc))  (* capacities pinned to the world's, *)
    /\ uc_next uc = w_next (outcome_world oc).   (* and the allocator agreement, end to end *)
Proof.
  intros c w oc H Hopen.
  set (ucap := ucap_of_world w).
  destruct (run_cmd_eval c w oc H) as [oc0 [ds [result [Hgo [Hun Hcomb]]]]].
  destruct (body_runs_sem c w oc0 ds ucap
              (fun t => if Nat.eqb t 0 then cmd_to_ucmd c else URet)
              (bufs_of_world w) (heap_of_world w) (fun t => Nat.eqb t 0) nil nil
              (fun _ => nil) (fun _ => None)
              Hgo (heap_of_world_agrees w) (bufs_of_world_agrees w)
              (closed_agree_start w Hopen) (ucap_of_world_agrees w) eq_refl eq_refl)
    as [pA [bA [hA [trA [dfA [evs0 [HusA [HprogA [HdfA [HhaA [HbaA [HcaA [HuaA Hout0]]]]]]]]]]]]].
  rewrite app_nil_r in HdfA.
  assert (HdfA' : dfA 0 = map cmd_to_ucmd ds ++ nil) by (rewrite HdfA, app_nil_r; reflexivity).
  assert (HprogA' : pA 0 = URet \/ exists v, pA 0 = UPan v)
    by (rewrite HprogA; destruct oc0 as [[] ?|v0 ?]; [ left; reflexivity | right; exists v0; reflexivity ]).
  assert (Hq0 : (match pA 0 with UPan v => Some v | _ => (fun _ : nat => @None GoAny) 0 end)
                = mode_or (ocpanic (oc_unit oc0)) None)
    by (rewrite HprogA; destruct oc0 as [[] ?|? ?]; reflexivity).
  assert (Hha0 : heap_agrees hA (w_refs (outcome_world (oc_unit oc0))))
    by (destruct oc0 as [[] ?|? ?]; exact HhaA).
  assert (Hba0 : bufs_agree bA (w_chans (outcome_world (oc_unit oc0))))
    by (destruct oc0 as [[] ?|? ?]; exact HbaA).
  assert (Hca0 : closed_agree trA (w_chans (outcome_world (oc_unit oc0))))
    by (destruct oc0 as [[] ?|? ?]; exact HcaA).
  assert (Hua0 : ucap_agree ucap (w_chans (outcome_world (oc_unit oc0))))
    by (destruct oc0 as [[] ?|? ?]; exact HuaA).
  destruct (unwind_heap ds (oc_unit oc0) result Hun ucap pA
              bA hA (fun t => Nat.eqb t 0) trA
              (nil ++ map (fun e => (0, e)) evs0) dfA (fun _ => None) nil None
              eq_refl HprogA' Hq0 Hha0 Hba0 Hca0 Hua0 HdfA')
    as [pB [bB [hB [trB [dfB [paB [evs1 [HusB [HprogB [HqB [HdfB [HhaB [HbaB [HcaB [HuaB Hout1]]]]]]]]]]]]]]].
  rewrite oc_unit_world in HusB.
  assert (HqB0 : (match pB 0 with UPan v => Some v | _ => paB 0 end) = ocpanic result)
    by (rewrite HqB; destruct result as [[] ?|? ?]; reflexivity).
  (* relate [result] to run_cmd's [oc] *)
  assert (Hoc : ocpanic oc = ocpanic result
                /\ outcome_world oc = outcome_world result).
  { destruct result as [[] w' | v w']; subst oc.
    - (* result returns: the body cannot have panicked (a panic seed never returns) *)
      destruct oc0 as [[] w0 | v0 w0].
      + split; reflexivity.
      + exfalso.
        destruct (unwind_panic_stays ds (oc_unit (OPanic v0 w0)) (ORet tt w') Hun v0 w0 eq_refl)
          as [? [? Hcontra]].
        discriminate Hcontra.
    - cbn [ocpanic outcome_world]. split; reflexivity. }
  destruct Hoc as [Hocp Hocw].
  (* the final done step per the 2-mode *)
  destruct HprogB as [HretB | [v HpanB]].
  - exists (mkUCfg pB bB hB (upd (fun t => Nat.eqb t 0) 0 false) trB
                   ((nil ++ map (fun e => (0, e)) evs0) ++ map (fun e => (0, e)) evs1) dfB paB
                   (w_next (outcome_world result))).
    split; [ | split; [ apply upd_same | split; [ | split; [ | split; [ | split; [ | split; [ | split ] ] ] ] ] ] ].
    + unfold ustart_w. eapply usteps_trans; [ exact HusA | ].
      eapply usteps_trans; [ exact HusB | ].
      eapply usteps_step;
        [ eapply ustep_ret_done with (tid := 0); [ reflexivity | exact HretB | exact HdfB ] | apply usteps_refl ].
    + cbn [uc_panic]. rewrite Hocp, <- HqB0, HretB. reflexivity.
    + cbn [uc_out]. rewrite Hocw, Hout1.
      assert (Hw0 : outcome_world (oc_unit oc0) = outcome_world oc0) by (destruct oc0; reflexivity).
      rewrite Hw0, Hout0, !map_app, map_snd_pair0. cbn [app map].
      rewrite map_snd_pair0, <- app_assoc. reflexivity.
    + cbn [uc_heap]. rewrite Hocw. exact HhaB.
    + cbn [uc_bufs]. rewrite Hocw. exact HbaB.
    + cbn [uc_trace]. rewrite Hocw. exact HcaB.
    + rewrite Hocw. exact HuaB.
    + cbn [uc_next]. rewrite Hocw. reflexivity.
  - exists (mkUCfg pB bB hB (upd (fun t => Nat.eqb t 0) 0 false) trB
                   ((nil ++ map (fun e => (0, e)) evs0) ++ map (fun e => (0, e)) evs1) dfB
                   (upd paB 0 (Some v)) (w_next (outcome_world result))).
    split; [ | split; [ apply upd_same | split; [ | split; [ | split; [ | split; [ | split; [ | split ] ] ] ] ] ] ].
    + unfold ustart_w. eapply usteps_trans; [ exact HusA | ].
      eapply usteps_trans; [ exact HusB | ].
      eapply usteps_step;
        [ eapply ustep_pan_done with (tid := 0); [ reflexivity | exact HpanB | exact HdfB ] | apply usteps_refl ].
    + cbn [uc_panic]. rewrite upd_same, Hocp, <- HqB0, HpanB. reflexivity.
    + cbn [uc_out]. rewrite Hocw, Hout1.
      assert (Hw0 : outcome_world (oc_unit oc0) = outcome_world oc0) by (destruct oc0; reflexivity).
      rewrite Hw0, Hout0, !map_app, map_snd_pair0. cbn [app map].
      rewrite map_snd_pair0, <- app_assoc. reflexivity.
    + cbn [uc_heap]. rewrite Hocw. exact HhaB.
    + cbn [uc_bufs]. rewrite Hocw. exact HbaB.
    + cbn [uc_trace]. rewrite Hocw. exact HcaB.
    + rewrite Hocw. exact HuaB.
    + cbn [uc_next]. rewrite Hocw. reflexivity.
Qed.

(** The NEGATIVE witness for the quarantine: an unallocated read has NO completing run at
    all — so no unconditional (premise-free) bridge over heap commands can exist; the agreement
    for heap programs must carry allocation/completion premises, as [bridge_effects_agree]'s
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
    / [pop_defer_step]) is CONSUMED by [bridge_effects_agree].  The one always-dead-by-convention
    artifact shape — a LOCAL [Example], vernacular or #[local] attribute spelling (an Example
    nothing consumes — compiled but outside every printed cone) — is mechanically rejected
    repo-wide by smart-ctor-gate.sh check 6 (token-aware; exact boundary documented at the
    detector); a general Local lemma's audit is membership in a consumer's cone. *)
(** ---- The CAlloc regression obligations (design v2's gate lemmas): under GoHeap's
    [AllocFrontierOk] the deterministic allocator is SAFE — the minted location is never 0
    (Go's nil is unreachable from a continuation branching on it), never a clobber of
    an allocated cell, and validity is PRESERVED by [alloc_world] (so the obligations
    compose down a run).  cmd.v owns [alloc_world], GoHeap owns [AllocFrontierOk]; the
    bridge is where the two meet. *)
Theorem calloc_loc_nonzero : forall w, AllocFrontierOk w -> Nat.eqb (w_next w) 0 = false.
Proof.
  intros w [Hpos _]. destruct (w_next w); [ discriminate Hpos | reflexivity ].
Qed.
Theorem calloc_no_clobber : forall w, AllocFrontierOk w -> w_refs w (w_next w) = None.
Proof.
  intros w [_ [_ Hbound]].
  exact (proj1 (Hbound (w_next w) (PeanoNat.Nat.leb_refl _))).
Qed.
Theorem alloc_world_valid : forall v w, AllocFrontierOk w -> AllocFrontierOk (alloc_world v w).
Proof.
  intros v w [Hpos [Hloc0 Hbound]]. split; [ | split ].
  - reflexivity.
  - (* WorldOk: [alloc_world] writes at [w_next] (nonzero), so loc 0 stays empty *)
    destruct Hloc0 as [Hr0 [Hc0 Hm0]].
    assert (El0 : Nat.eqb 0 (w_next w) = false)
      by (apply PeanoNat.Nat.eqb_neq; apply PeanoNat.Nat.ltb_lt in Hpos; lia).
    cbn [alloc_world w_refs w_chans w_maps]. rewrite El0. repeat split; assumption.
  - intros l Hl. cbn [alloc_world w_next] in Hl.
    apply PeanoNat.Nat.leb_le in Hl.
    assert (Hgt : w_next w <= l) by lia.
    assert (El : Nat.eqb l (w_next w) = false)
      by (apply PeanoNat.Nat.eqb_neq; lia).
    cbn [alloc_world w_refs w_chans w_maps]. rewrite El.
    apply Hbound. apply PeanoNat.Nat.leb_le. exact Hgt.
Qed.

(** ---- The CHANNEL landing obligations (theorem-shaped, per plans/bridge-effects.md):
    the typed-zero MECHANISM pinned as theorems — the closed-drained recv binds EXACTLY
    [anyt tgt (zero_val tgt)] (general + the two required element-type instances), the
    closed-send/close panics, the would-block ABSENCES (the deterministic-fragment gate),
    tag-mismatch REJECTION (never a coercion), and the admissibility pin the calculus
    cannot provide alone: the certified translation puts the TYPED zero in [URecv]'s
    field, so "URecv carries z" composes with "z IS the typed zero" — never an arbitrary
    [GoAny] zero through the public path. *)
Theorem cchrecv_closed_typed_zero : forall {T} (tgt : GoTypeTag T) ch (f : GoAny -> Cmd unit) w E tag cap,
  w_chans w ch = Some (existT _ E (tag, (nil, (true, cap)))) ->
  (exists p, tag_eq tgt tag = Some p) ->
  run_cmd (CChRecv ch (existT _ T tgt) f) w = run_cmd (f (anyt tgt (zero_val tgt))) w.
Proof.
  intros T tgt ch f w E tag cap Hc [p Hp].
  cbn [run_cmd]. rewrite Hc, Hp. reflexivity.
Qed.
Corollary cchrecv_closed_zero_i64 : forall ch (f : GoAny -> Cmd unit) w cap,
  w_chans w ch
    = Some (existT (fun E : Type => (GoTypeTag E * (list E * (bool * option nat)))%type)
                   GoI64 (TI64, (nil, (true, cap)))) ->
  run_cmd (CChRecv ch (existT (fun T : Type => GoTypeTag T) GoI64 TI64) f) w = run_cmd (f (anyt TI64 (zero_val TI64))) w.
Proof.
  intros ch f w cap Hc.
  exact (cchrecv_closed_typed_zero TI64 ch f w GoI64 TI64 cap Hc
           (ex_intro _ eq_refl (tag_eq_refl TI64))).
Qed.
Corollary cchrecv_closed_zero_string : forall ch (f : GoAny -> Cmd unit) w cap,
  w_chans w ch
    = Some (existT (fun E : Type => (GoTypeTag E * (list E * (bool * option nat)))%type)
                   GoString (TString, (nil, (true, cap)))) ->
  run_cmd (CChRecv ch (existT (fun T : Type => GoTypeTag T) GoString TString) f) w = run_cmd (f (anyt TString (zero_val TString))) w.
Proof.
  intros ch f w cap Hc.
  exact (cchrecv_closed_typed_zero TString ch f w GoString TString cap Hc
           (ex_intro _ eq_refl (tag_eq_refl TString))).
Qed.
(** Send on a CLOSED channel panics ([rt_send_closed]) — Go-faithful, but ONLY for a TAG-CORRECT value
    ([anyt tag x], the sent value tagged with the cell's own [tag]).  Checkpoint-58: [run_cmd]'s [CChSend] is
    tag-first, so a MISTYPED send on a closed cell is STUCK ([None]), NOT a panic — a forged wrong-tag value
    never observes the cell's closedness (mirrors [GoChan.send]'s [chan_cell_ok]-first guard). *)
Theorem cchsend_closed_panics : forall ch (k : Cmd unit) w E (tag : GoTypeTag E) (x : E) buf cap,
  w_chans w ch = Some (existT _ E (tag, (buf, (true, cap)))) ->
  run_cmd (CChSend ch (anyt tag x) k) w = Some (OPanic rt_send_closed w).
Proof.
  intros ch k w E tag x buf cap Hc. cbn [run_cmd]. rewrite Hc. cbn beta iota.
  rewrite tag_coerce_refl. reflexivity.
Qed.
Theorem cchclose_closed_panics : forall ch (k : Cmd unit) w E tag buf cap,
  w_chans w ch = Some (existT _ E (tag, (buf, (true, cap)))) ->
  run_cmd (CChClose ch k) w = Some (OPanic rt_close_closed w).
Proof. intros ch k w E tag buf cap Hc. cbn [run_cmd]. rewrite Hc. reflexivity. Qed.
Theorem cchrecv_open_empty_absent : forall {T} (tgt : GoTypeTag T) ch (f : GoAny -> Cmd unit) w E tag cap,
  w_chans w ch = Some (existT _ E (tag, (nil, (false, cap)))) ->
  run_cmd (CChRecv ch (existT _ T tgt) f) w = None.
Proof.
  intros T tgt ch f w E tag cap Hc. cbn [run_cmd]. rewrite Hc.
  destruct (tag_eq tgt tag); reflexivity.
Qed.
Theorem cchsend_no_room_absent : forall ch v (k : Cmd unit) w E tag buf cap,
  w_chans w ch = Some (existT _ E (tag, (buf, (false, cap)))) ->
  chan_room_cap (length buf) cap = false ->
  run_cmd (CChSend ch v k) w = None.
Proof.
  intros ch v k w E tag buf cap Hc Hr. cbn [run_cmd]. rewrite Hc.
  destruct v as [A0 [x ta]].
  destruct (tag_coerce tag ta x); [ rewrite Hr | ]; reflexivity.
Qed.
Corollary cchsend_unbuffered_absent : forall ch v (k : Cmd unit) w E tag,
  w_chans w ch = Some (existT _ E (tag, (nil, (false, Some 0)))) ->
  run_cmd (CChSend ch v k) w = None.
Proof.
  intros ch v k w E tag Hc.
  exact (cchsend_no_room_absent ch v k w E tag nil (Some 0) Hc eq_refl).
Qed.
Theorem cchrecv_tag_mismatch_absent : forall {T} (tgt : GoTypeTag T) ch (f : GoAny -> Cmd unit) w E tag buf closed cap,
  w_chans w ch = Some (existT _ E (tag, (buf, (closed, cap)))) ->
  tag_eq tgt tag = None ->
  run_cmd (CChRecv ch (existT _ T tgt) f) w = None.
Proof.
  intros T tgt ch f w E tag buf closed cap Hc Hne. cbn [run_cmd]. rewrite Hc, Hne. reflexivity.
Qed.
(** A WRONG-TAG send is STUCK ([None]) for ANY [closed] state of the cell (checkpoint-58: [CChSend] is
    tag-first, so a mistyped send never reaches the [closed] check).  Generalised from the open case so it
    ALSO covers a CLOSED cell — see [cchsend_closed_wrong_tag_stuck] for the explicitly-named closed corollary. *)
Theorem cchsend_tag_mismatch_absent : forall ch {A0} (x : A0) (ta : GoTypeTag A0) (k : Cmd unit) w E tag buf closed cap,
  w_chans w ch = Some (existT _ E (tag, (buf, (closed, cap)))) ->
  tag_coerce tag ta x = None ->
  run_cmd (CChSend ch (existT _ A0 (x, ta)) k) w = None.
Proof.
  intros ch A0 x ta k w E tag buf closed cap Hc Hne. cbn [run_cmd]. rewrite Hc, Hne. reflexivity.
Qed.
(** THE CLOSED WRONG-TAG PIN (checkpoint-58, manifest-gated below): a wrong-tag send on a CLOSED cell is STUCK
    ([None]) — it does NOT fabricate [rt_send_closed] off the foreign cell.  The exact anti-forgery counterpart
    to [cchsend_closed_panics] (which needs a TAG-CORRECT value). *)
Corollary cchsend_closed_wrong_tag_stuck : forall ch {A0} (x : A0) (ta : GoTypeTag A0) (k : Cmd unit) w E tag buf cap,
  w_chans w ch = Some (existT _ E (tag, (buf, (true, cap)))) ->
  tag_coerce tag ta x = None ->
  run_cmd (CChSend ch (existT _ A0 (x, ta)) k) w = None.
Proof. intros ch A0 x ta k w E tag buf cap Hc Hne. exact (cchsend_tag_mismatch_absent ch x ta k w E tag buf true cap Hc Hne). Qed.
(** the ADMISSIBILITY pin: the certified translation puts the TYPED zero in URecv's field *)
Theorem cmd_to_ucmd_recv_zero : forall ch T (tgt : GoTypeTag T) (f : GoAny -> Cmd unit),
  cmd_to_ucmd (CChRecv ch (existT _ T tgt) f)
  = URecv ch (anyt tgt (zero_val tgt)) (fun x => cmd_to_ucmd (f x)).
Proof. reflexivity. Qed.

Definition cmd_unified_surface :=
  (cmd_to_ucmd_fragment, bridge_effects_agree, run_cmd_out_monotone, run_cmd_no_panic_ret,
   calloc_loc_nonzero, calloc_no_clobber, alloc_world_valid,
   @cchrecv_closed_typed_zero, cchrecv_closed_zero_i64, cchrecv_closed_zero_string,
   cchsend_closed_panics, cchclose_closed_panics,
   @cchrecv_open_empty_absent, cchsend_no_room_absent, cchsend_unbuffered_absent,
   @cchrecv_tag_mismatch_absent, @cchsend_tag_mismatch_absent, @cchsend_closed_wrong_tag_stuck,
   cmd_to_ucmd_recv_zero).
Print Assumptions cmd_unified_surface.
