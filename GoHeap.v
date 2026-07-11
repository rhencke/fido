(** ==================================================================================================
    GoHeap — the world's REF HEAP as Go's mutable memory: mutable local variables ([Ref]/[ref_new]/
    [ref_get]/[ref_set]), the [AllocFrontierOk] allocation-freshness invariant (location 0 IS Go's nil,
    freshness/disjointness are THEOREMS), pointers ([Ptr]/[ptr_new]/[ptr_get]/[ptr_set]) and the
    address-of operator ([&x]), the CLOSED-WORLD nil-safety proofs (modeled nil panics are UNREACHABLE
    for allocated handles), slices as ALIASING HANDLES ([SliceH]: shared backing cells, [subslice] —
    the representation where Go aliasing is REAL, unlike GoSlice's pure single-goroutine lists), and
    heap-backed structs ([HStruct] field-cell bundles; the generic [StructRep]/[GSPtr] typed struct
    heap).  ONE module owns the ref-heap story; the map and channel heaps live in GoMap/GoChan.
    ================================================================================================ *)

Require Import Coq.Lists.List.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.
From Fido Require Import GoNumeric.
From Fido Require Import GoRuntimeTypes.
From Fido Require Import GoEffects.
From Fido Require Import GoPanic.
From Fido Require Import GoMap.
From Fido Require Import GoChan.

(** ---- Mutable local variables (Go spec "Variables" / "Assignment statements") ----

    [Ref A] is a mutable cell holding an [A] — Go's mutable local variable.
    Pure [let]-binding is single-assignment and cannot express a value that
    *changes* (a loop counter, an accumulator updated in place); a [Ref] can.
    [ref_new tag v] declares the variable ([x := v]); [ref_get] reads it;
    [ref_set] assigns ([x = v]).  A local cell extracts to a plain Go variable;
    cross-function sharing (pointers, [*T]) is a later, separate step.

    [Ref A] is a CONCRETE typed-cell HANDLE: a location
    [r_loc] into the world's [w_refs] heap, plus the element [GoTypeTag] [r_tag]
    (so a read can coerce the stored cell back to [A]).  The OPERATIONS are
    DEFINITIONS over the heap and [ref_sel_upd_same] (read-after-write) is a
    THEOREM.  At extraction a [Ref A] is a plain Go variable — [ref_new] lowers to
    [x := v], [ref_get] to a read, [ref_set] to [x = v] — and the [r_loc]/[r_tag]
    fields and the heap are proof-only (erased). *)
Record Ref (A : Type) : Type := mkRef { r_loc : nat ; r_tag : GoTypeTag A }.
Arguments mkRef {A} _ _.
Arguments r_loc {A} _.
Arguments r_tag {A} _.

(** [ref_sel r w]: read [r]'s cell from [w_refs] and coerce it to [A] via the
    ref's tag.  A well-typed program always reads the cell it wrote, so the stored
    tag matches [r_tag] and the coercion succeeds; the mismatch / empty-cell cases
    default to the type's zero value (totality). *)
Definition ref_sel {A : Type} (r : Ref A) (w : World) : A :=
  match w_refs w (r_loc r) with
  | Some (existT _ _ (tag0, x0)) =>
      match tag_coerce (r_tag r) tag0 x0 with
      | Some a => a
      | None   => zero_val (r_tag r)
      end
  | None => zero_val (r_tag r)
  end.

(** [ref_sel_opt r w]: the CHECKED (tag-aware) selector — [Some v] iff [r]'s cell EXISTS at [r_loc r] AND its
    stored tag coerces to [r_tag] (a LIVE, correctly-typed cell); [None] on a missing / dangling / WRONG-TAG
    handle.  (A SAME-TAG forged alias reads [Some] from the aliased cell — typed liveness is not origin, so
    "[None] on forged" would be FALSE for same-tag aliases.)  A ref is LIVE at [r] iff [ref_sel_opt r w = Some _].  [ref_sel] (above) is the TOTAL companion
    that fabricates a [zero_val] in those cases; [ref_sel_opt] is what the safe ops and the [ref_upd] root
    guard branch on.  (Lives here — AHEAD of [ref_upd] — because the guard reads it.) *)
Definition ref_sel_opt {A : Type} (r : Ref A) (w : World) : option A :=
  match w_refs w (r_loc r) with
  | Some (existT _ _ (tag0, x0)) => tag_coerce (r_tag r) tag0 x0
  | None => None
  end.

(** [ref_install r v w]: the ALLOCATOR's RAW cell install — unconditionally writes [v] (tagged with [r]'s own
    tag) at [r]'s location, CREATING the cell if absent.  It is NOT a public mutation: it is the installer the
    allocators own ([ref_upd]'s live branch below, and the struct-field initialiser [wr_fields] that
    [gsptr_new] runs).  Public writes go through the GUARDED [ref_upd] / [ref_set] / [ptr_set] / [hfield_set],
    which install ONLY through an already-live cell — so a forged handle can never fabricate / retype via them. *)
Definition ref_install {A : Type} (r : Ref A) (v : A) (w : World) : World :=
  mkWorld (fun l => if Nat.eqb l (r_loc r)
                    then Some (existT _ A (r_tag r, v))
                    else w_refs w l)
          (w_chans w) (w_maps w) (w_next w) (w_output w).

Lemma ref_sel_opt_install_same : forall {A} (r : Ref A) (v : A) (w : World),
  ref_sel_opt r (ref_install r v w) = Some v.
Proof.
  intros A r v w. unfold ref_sel_opt, ref_install; cbn.
  rewrite (Nat.eqb_refl (r_loc r)); cbn. apply tag_coerce_refl.
Qed.
Lemma ref_sel_opt_install_diff : forall {A B} (r : Ref A) (r' : Ref B) (v : B) (w : World),
  r_loc r <> r_loc r' -> ref_sel_opt r (ref_install r' v w) = ref_sel_opt r w.
Proof.
  intros A B r r' v w Hne. unfold ref_sel_opt, ref_install; cbn.
  rewrite (proj2 (Nat.eqb_neq (r_loc r) (r_loc r')) Hne). reflexivity.
Qed.
Lemma ref_sel_install_same : forall {A} (r : Ref A) (v : A) (w : World),
  ref_sel r (ref_install r v w) = v.
Proof.
  intros A r v w. unfold ref_sel, ref_install. cbn.
  rewrite (Nat.eqb_refl (r_loc r)). rewrite tag_coerce_refl. reflexivity.
Qed.
Lemma ref_sel_install_diff : forall {A B} (r : Ref A) (r' : Ref B) (v : A) (w : World),
  r_loc r <> r_loc r' -> ref_sel r' (ref_install r v w) = ref_sel r' w.
Proof.
  intros A B r r' v w Hne. unfold ref_sel, ref_install. cbn.
  destruct (Nat.eqb (r_loc r') (r_loc r)) eqn:E; [|reflexivity].
  apply Nat.eqb_eq in E. congruence.
Qed.

(** [ref_upd r v w]: the ROOT-GUARDED ref write (checkpoint-58, the ref dual of [chan_write] / [map_write]).
    It writes [v] at [r]'s location ONLY when [r] is LIVE ([ref_sel_opt r w = Some _]); on a handle with NO
    LIVE cell it is the IDENTITY ([ref_upd_dead_noop]).  This covers, at ANY location, an ABSENT / dangling
    handle and a WRONG-TAG alias ([ref_upd_wrong_tag_noop] — [tag_coerce] fails).  ⚠ NIL is subtler: unlike
    [chan_buf] / [map_get_fn], [ref_sel_opt] carries NO loc-0 guard, so in an arbitrary public-[mkWorld] world a
    forged loc-0 cell of the MATCHING tag would read live and be written; the NIL-ref seal therefore relies on
    [WorldOk] ([AllocFrontierOk] forces [w_refs w 0 = None] — [ref_upd_nil_noop_valid]), NOT on the [ref_upd] guard
    alone.  So a forged [Ref] (constructible via the public [mkRef]) can no longer FABRICATE a cell at an
    unallocated location NOR RETYPE an aliased cell of another type through the raw write.  The seal is the
    GUARD (+ [WorldOk] for loc-0): a WRONG-TAG or ABSENT/dangling forged handle is representable but INERT.
    ⚠ A SAME-TAG forged handle aliasing a real live same-tag cell is NOT inert — it reads/writes that cell as
    an alias (typed liveness does not prove origin); ruling that out needs allocation ORIGIN evidence, open.
    Cell CREATION is [ref_install]
    (allocators) / [ref_new]; every
    [ref_upd] rides an already-live, tag-correct ref, on which it is IDENTICAL to the unconditional install
    ([ref_upd_live_eq]) — so [ref_set] / [ptr_set] / [hfield_set] (which guard on [ref_sel_opt = Some] BEFORE
    calling [ref_upd]) are behaviour-preserving on every live ref. *)
Definition ref_upd {A : Type} (r : Ref A) (v : A) (w : World) : World :=
  match ref_sel_opt r w with
  | Some _ => ref_install r v w
  | None   => w
  end.

(** RAW ANTI-FORGERY WITNESS (the ref dual of [chan_write_cellko_noop] / [map_write_absent_noop]): a
    [ref_upd] through a handle with NO live cell ([ref_sel_opt = None] — an absent / dangling / WRONG-TAG handle
    at any location, or a NIL handle under [WorldOk]; [ref_sel_opt] has no loc-0 guard, so an arbitrary forged
    loc-0 cell would read live) is the IDENTITY.  So the raw ref write never fabricates or retypes a cell. *)
Lemma ref_upd_dead_noop : forall {A} (r : Ref A) (v : A) (w : World),
  ref_sel_opt r w = None -> ref_upd r v w = w.
Proof. intros A r v w H. unfold ref_upd. rewrite H. reflexivity. Qed.

(** On a LIVE ref the guarded write is IDENTICAL to the unconditional install — so every read-back / aliasing
    law reduces to the [ref_install] algebra once liveness is in hand (and public writes, which guard first,
    are unchanged). *)
Lemma ref_upd_live_eq : forall {A} (r : Ref A) (v a : A) (w : World),
  ref_sel_opt r w = Some a -> ref_upd r v w = ref_install r v w.
Proof. intros A r v a w H. unfold ref_upd. rewrite H. reflexivity. Qed.

(** WRONG-TAG ANTI-FORGERY: a forged [Ref A] whose location ALIASES a live cell of a
    DIFFERENT type [B] (stored tag [tb], [tag_eq (r_tag r) tb = None]) does NOT mutate — [ref_upd] is the
    IDENTITY.  A wrong-tag handle reads [ref_sel_opt = None] (its [tag_coerce] fails), so [ref_upd_dead_noop]
    applies.  (No [r_loc r <> 0] premise is needed, unlike [chan] / [map]: [ref_sel_opt] carries no loc-0
    guard, so the tag mismatch ALONE seals the write, at ANY location.) *)
Lemma ref_upd_wrong_tag_noop : forall {A B} (r : Ref A) (v : A) (w : World) (tb : GoTypeTag B) (x0 : B),
  w_refs w (r_loc r) = Some (existT _ B (tb, x0)) ->
  tag_eq (r_tag r) tb = None ->
  ref_upd r v w = w.
Proof.
  intros A B r v w tb x0 Hcell Htag. apply ref_upd_dead_noop.
  unfold ref_sel_opt. rewrite Hcell.
  change (tag_coerce (r_tag r) tb x0 = None).
  unfold tag_coerce. rewrite Htag. reflexivity.
Qed.

(** ROOT-GUARD ANTI-FORGERY: the two location-agnostic ref anti-forgery witnesses
    ([ref_upd_dead_noop] / [ref_upd_wrong_tag_noop]) are proved above; the NIL case needs [WorldOk], so
    [ref_upd_nil_noop_valid] and the gated [ref_wrong_tag_antiforgery_surface] live just after [valid_loc0_empty] below. *)

(** [ref_new tag v]: allocate the fresh location [w_next], seed [r_tag := tag],
    write [v], bump the allocator.  Carries the [GoTypeTag] so the cell is tagged
    (lowers to [x := v]; the tag and location are erased). *)
Definition ref_new {A : Type} (tag : GoTypeTag A) (v : A) : IO (Ref A) :=
  fun w => let l := w_next w in
           ORet (mkRef l tag)
                (mkWorld (fun k => if Nat.eqb k l
                                   then Some (existT _ A (tag, v))
                                   else w_refs w k)
                         (w_chans w) (w_maps w) (S l) (w_output w)).

(** ---- [AllocFrontierOk]: allocation freshness as a MACHINE-CHECKED invariant ----

    Every allocator ([map_make_typed]/[make_chan]/[ref_new]) mints [l := w_next w] and bumps
    [w_next] to [l+1].  For "fresh" / "nonzero" / "disjoint" to be THEOREMS rather than comments we carry an
    invariant [AllocFrontierOk]: the allocator pointer is positive (so location 0 is RESERVED — it is Go's [nil]),
    location 0 is EMPTY in all three heaps (the WorldOk property — no forged cell can hide at [nil]), AND it
    bounds the live region (every heap is [None] at and above [w_next]).  Three payoffs follow from the
    invariant ALONE (no side conditions): the next location is nonzero ([valid_fresh_nonzero] — a fresh
    pointer/chan/map is never nil), is currently unallocated in all three heaps ([valid_fresh_disjoint] — a
    fresh allocation overwrites nothing), and location 0 is empty ([valid_loc0_empty] — the accessors' loc-0
    read guards are provably redundant on the certified path).  The invariant holds at the initial world
    ([valid_w_init]) and is PRESERVED by every allocator ([valid_alloc_*]) UNCONDITIONALLY — allocators write
    at the nonzero [w_next], so loc 0 stays empty and [nat] locations never overflow.
    ⚠ SCOPE (checkpoint-61): this predicate proves ONLY the allocation-frontier
    facts above — NOT complete semantic world validity (no object-representation invariants, no
    value-well-typedness).  The real [WorldWellFormed Σ w := AllocFrontierOk w /\ WorldRealizes Σ w /\ rep
    invariants] awaits the StoreTyping authority (plans/result-control-split.md order #4); do not read this
    name as more than a frontier guard. *)
Definition AllocFrontierOk (w : World) : Prop :=
  (0 <? w_next w)%nat = true /\
  (w_refs w 0 = None /\ w_chans w 0 = None /\ w_maps w 0 = None) /\   (* WorldOk: loc 0 (Go's [nil]) empty in ALL heaps *)
  (forall l, (w_next w <=? l)%nat = true ->
     w_refs w l = None /\ w_chans w l = None /\ w_maps w l = None).

Lemma valid_w_init : AllocFrontierOk w_init.
Proof.
  split; [ | split ].
  - now vm_compute.
  - unfold w_init; cbn. repeat split; reflexivity.
  - intros l _. unfold w_init; cbn. repeat split; reflexivity.
Qed.

(** PAYOFF 1: the freshly minted location [w_next w] is nonzero — a fresh pointer/chan/map is never [nil]. *)
Lemma valid_fresh_nonzero : forall w, AllocFrontierOk w -> (0 <? w_next w)%nat = true.
Proof. intros w [Hpos _]. exact Hpos. Qed.

(** PAYOFF 2: the freshly minted location is currently unallocated in ALL three heaps — so installing a
    cell there (what every allocator does) overwrites nothing; allocations never alias a live object. *)
Lemma valid_fresh_disjoint : forall w, AllocFrontierOk w ->
  w_refs w (w_next w) = None /\ w_chans w (w_next w) = None /\ w_maps w (w_next w) = None.
Proof.
  intros w [_ [_ Hfresh]]. apply Hfresh. apply Nat.leb_le. lia.
Qed.

(** PAYOFF 3 (WorldOk): location 0 — Go's [nil] — is empty in ALL three heaps.  So a [AllocFrontierOk] cannot
    carry a forged cell at the reserved nil location.  For the accessors that DO carry a loc-0 read guard
    ([chan_buf] / [map_get_fn] / [ptr_get]/[ptr_set]) this makes the guard provably redundant on the certified
    path (it remains for the open-world / public-[mkWorld] case).  For [ref_sel_opt], which has NO loc-0 guard,
    [WorldOk] is instead LOAD-BEARING: it is the sole reason a NIL [Ref] cannot alias a forged loc-0 cell
    ([ref_upd_nil_noop_valid]). *)
Lemma valid_loc0_empty : forall w, AllocFrontierOk w ->
  w_refs w 0 = None /\ w_chans w 0 = None /\ w_maps w 0 = None.
Proof. intros w [_ [Hloc0 _]]. exact Hloc0. Qed.

(** NIL-REF ANTI-FORGERY under [WorldOk]: since [ref_sel_opt] has no loc-0 guard (unlike [chan_buf] /
    [map_get_fn]), the nil-ref seal needs the invariant — [AllocFrontierOk] forces [w_refs w 0 = None]
    ([valid_loc0_empty]), so a NIL [Ref] ([r_loc = 0]) reads [ref_sel_opt = None] and [ref_upd] is the IDENTITY.
    (In an arbitrary forged [mkWorld] a loc-0 cell of the MATCHING tag is representable and WOULD be written;
    [WorldOk] excludes it from every reachable world.) *)
Lemma ref_upd_nil_noop_valid : forall {A} (r : Ref A) (v : A) (w : World),
  AllocFrontierOk w -> r_loc r = 0 -> ref_upd r v w = w.
Proof.
  intros A r v w HV Hnil. apply ref_upd_dead_noop.
  unfold ref_sel_opt. rewrite Hnil.
  destruct (valid_loc0_empty w HV) as [Hr0 _]. rewrite Hr0. reflexivity.
Qed.
(** WRONG-TAG ANTI-FORGERY SURFACE: the ref anti-forgery witnesses as MANIFEST-GATED, zero-axiom PUBLIC
    evidence — the ref analogue of [GoChan.chan_wrong_tag_antiforgery_surface] /
    [GoMap.map_wrong_tag_antiforgery_surface].  These are TYPED-LIVENESS negatives (an invalid handle cannot
    mutate), NOT origin PROVENANCE: a forged / absent / dangling / WRONG-TAG [Ref] (constructible via public
    [mkRef]; WRONG-TAG or ABSENT ones INERT) cannot fabricate OR retype a cell through the raw [ref_upd] root at ANY location
    ([ref_upd_dead_noop] / [ref_upd_wrong_tag_noop]); the NIL case ([r_loc = 0]) is sealed under [WorldOk]
    ([ref_upd_nil_noop_valid]).  (A SAME-TAG forged handle aliasing a real same-tag cell is NOT stopped here —
    that needs allocation origin evidence, still open.)  Every public write ([ref_set] / [ptr_set] /
    [hfield_set]) already guards on [ref_sel_opt = Some] before reaching it.  The [Print Assumptions] below
    certifies the cone axiom-free — gated public evidence, not ungated internal lemmas. *)
Definition ref_wrong_tag_antiforgery_surface :=
  (@ref_upd_dead_noop, @ref_upd_wrong_tag_noop, @ref_upd_nil_noop_valid).
Print Assumptions ref_wrong_tag_antiforgery_surface.

(** Consequences of bumping the allocator past [l']: the OLD pointer is still [<= l'], and [l'] is
    distinct from the freshly minted location (so the install's [eqb] guard is [false] at [l']).
    With [nat] locations these are pure arithmetic — no no-wrap side condition. *)
Lemma bump_le : forall w l',
  (S (w_next w) <=? l')%nat = true -> (w_next w <=? l')%nat = true.
Proof.
  intros w l' Hle. apply Nat.leb_le. apply Nat.leb_le in Hle. lia.
Qed.

Lemma bump_neq : forall w l',
  (S (w_next w) <=? l')%nat = true -> Nat.eqb l' (w_next w) = false.
Proof.
  intros w l' Hle. apply Nat.leb_le in Hle. apply Nat.eqb_neq. lia.
Qed.

(** PRESERVATION: each allocator carries [AllocFrontierOk] to the post-allocation world (unconditionally —
    [nat] locations never overflow, so no [HasRoom] side condition). *)
Lemma valid_alloc_ref : forall {A} (tag : GoTypeTag A) (v : A) (w : World),
  AllocFrontierOk w ->
  AllocFrontierOk (mkWorld
    (fun k => if Nat.eqb k (w_next w) then Some (existT _ A (tag, v)) else w_refs w k)
    (w_chans w) (w_maps w) (S (w_next w)) (w_output w)).
Proof.
  intros A tag v w HV. destruct HV as [Hpos [Hloc0 Hfresh]]. split; [ | split ].
  - cbn [w_next]. apply Nat.ltb_lt. lia.
  - cbn [w_refs w_chans w_maps]. destruct Hloc0 as [Hr0 [Hc0 Hm0]].
    assert (Hne0 : Nat.eqb 0 (w_next w) = false) by (apply Nat.eqb_neq; apply Nat.ltb_lt in Hpos; lia).
    rewrite Hne0. repeat split; assumption.
  - intros l' Hle. cbn [w_next w_refs w_chans w_maps] in *.
    assert (Hle0 : (w_next w <=? l')%nat = true) by (apply (bump_le w l' Hle)).
    assert (Hneq : Nat.eqb l' (w_next w) = false) by (apply (bump_neq w l' Hle)).
    destruct (Hfresh l' Hle0) as [Hr [Hc Hm]].
    rewrite Hneq. repeat split; assumption.
Qed.

Lemma valid_alloc_chan : forall {A} (tag : GoTypeTag A) (cap : option nat) (w : World),
  AllocFrontierOk w ->
  AllocFrontierOk (mkWorld (w_refs w)
    (fun k => if Nat.eqb k (w_next w) then Some (existT _ A (tag, (nil, (false, cap)))) else w_chans w k)
    (w_maps w) (S (w_next w)) (w_output w)).
Proof.
  intros A tag cap w HV. destruct HV as [Hpos [Hloc0 Hfresh]]. split; [ | split ].
  - cbn [w_next]. apply Nat.ltb_lt. lia.
  - cbn [w_refs w_chans w_maps]. destruct Hloc0 as [Hr0 [Hc0 Hm0]].
    assert (Hne0 : Nat.eqb 0 (w_next w) = false) by (apply Nat.eqb_neq; apply Nat.ltb_lt in Hpos; lia).
    rewrite Hne0. repeat split; assumption.
  - intros l' Hle. cbn [w_next w_refs w_chans w_maps] in *.
    assert (Hle0 : (w_next w <=? l')%nat = true) by (apply (bump_le w l' Hle)).
    assert (Hneq : Nat.eqb l' (w_next w) = false) by (apply (bump_neq w l' Hle)).
    destruct (Hfresh l' Hle0) as [Hr [Hc Hm]].
    rewrite Hneq. repeat split; assumption.
Qed.

Lemma valid_alloc_map_typed : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (w : World),
  AllocFrontierOk w ->
  AllocFrontierOk (mkWorld (w_refs w) (w_chans w)
    (fun k => if Nat.eqb k (w_next w)
              then Some (0, existT _ K (kt, existT _ V (vt, fun _ => None))) else w_maps w k)
    (S (w_next w)) (w_output w)).
Proof.
  intros K V kt vt w HV. destruct HV as [Hpos [Hloc0 Hfresh]]. split; [ | split ].
  - cbn [w_next]. apply Nat.ltb_lt. lia.
  - cbn [w_refs w_chans w_maps]. destruct Hloc0 as [Hr0 [Hc0 Hm0]].
    assert (Hne0 : Nat.eqb 0 (w_next w) = false) by (apply Nat.eqb_neq; apply Nat.ltb_lt in Hpos; lia).
    rewrite Hne0. repeat split; assumption.
  - intros l' Hle. cbn [w_next w_refs w_chans w_maps] in *.
    assert (Hle0 : (w_next w <=? l')%nat = true) by (apply (bump_le w l' Hle)).
    assert (Hneq : Nat.eqb l' (w_next w) = false) by (apply (bump_neq w l' Hle)).
    destruct (Hfresh l' Hle0) as [Hr [Hc Hm]].
    rewrite Hneq. repeat split; assumption.
Qed.

(** Bumping [w_next] FORWARD (reserving a block of fresh cells without filling them yet) preserves validity —
    the same-or-larger frontier keeps loc 0 empty and shrinks the "fresh" region.  The multi-cell allocators
    ([gsptr_new]'s [wr_fields], the slice makes) reserve a block this way, then fill it. *)
Lemma valid_bump : forall (w : World) (n : nat),
  AllocFrontierOk w -> AllocFrontierOk (mkWorld (w_refs w) (w_chans w) (w_maps w) (w_next w + n) (w_output w)).
Proof.
  intros w n [Hpos [Hloc0 Hfresh]]. split; [ | split ].
  - cbn [w_next]. apply Nat.ltb_lt. apply Nat.ltb_lt in Hpos. lia.
  - cbn [w_refs w_chans w_maps]. exact Hloc0.
  - intros l Hle. cbn [w_next w_refs w_chans w_maps] in *.
    apply Hfresh. apply Nat.leb_le. apply Nat.leb_le in Hle. lia.
Qed.

(** Installing a ref cell at an INTERIOR location [0 < loc < w_next] preserves validity — it is neither loc 0
    (Go's nil) nor a fresh location [>= w_next], and [ref_install] leaves [w_next] and the chan/map heaps
    untouched.  This is the per-cell step the multi-cell struct allocator repeats. *)
Lemma valid_ref_install_interior : forall {A} (r : Ref A) (v : A) (w : World),
  AllocFrontierOk w -> (0 < r_loc r)%nat -> (r_loc r < w_next w)%nat -> AllocFrontierOk (ref_install r v w).
Proof.
  intros A r v w [Hpos [Hloc0 Hfresh]] Hlo Hhi. unfold ref_install. split; [ | split ].
  - cbn [w_next]. exact Hpos.
  - cbn [w_refs w_chans w_maps]. destruct Hloc0 as [Hr0 [Hc0 Hm0]].
    assert (Hne : Nat.eqb 0 (r_loc r) = false) by (apply Nat.eqb_neq; lia).
    rewrite Hne. repeat split; assumption.
  - intros l Hle. cbn [w_next w_refs w_chans w_maps] in *.
    assert (Hne : Nat.eqb l (r_loc r) = false) by (apply Nat.eqb_neq; apply Nat.leb_le in Hle; lia).
    rewrite Hne. exact (Hfresh l Hle).
Qed.

(** A LIVE cell is INTERIOR — under [AllocFrontierOk] a handle that reads [Some] sits at [0 < loc < w_next]: loc 0
    (Go's nil) and every fresh location are empty, so a readable cell is neither. *)
Lemma valid_live_interior : forall {A} (r : Ref A) (a : A) (w : World),
  AllocFrontierOk w -> ref_sel_opt r w = Some a -> (0 < r_loc r)%nat /\ (r_loc r < w_next w)%nat.
Proof.
  intros A r a w [Hpos [[Hr0 _] Hfresh]] Hs. unfold ref_sel_opt in Hs.
  destruct (w_refs w (r_loc r)) as [c|] eqn:Hw; [ | discriminate Hs ]. split.
  - assert (Hne : r_loc r <> 0) by (intro E; rewrite E, Hr0 in Hw; discriminate Hw). lia.
  - destruct (Nat.ltb (r_loc r) (w_next w)) eqn:Hlt; [ apply Nat.ltb_lt; exact Hlt | ].
    apply Nat.ltb_ge in Hlt. destruct (Hfresh (r_loc r) (proj2 (Nat.leb_le _ _) Hlt)) as [Hrn _].
    rewrite Hrn in Hw; discriminate Hw.
Qed.

(** [ref_upd] preserves [AllocFrontierOk] UNCONDITIONALLY — it is guarded (a no-op on a non-live handle, so it never
    fabricates a cell at loc 0 or a fresh location) and leaves [w_next] fixed; on a live handle the target is
    interior ([valid_live_interior]).  This covers every in-place write ([ref_set]/[ptr_set]/append-in-cap). *)
Lemma valid_ref_upd : forall {A} (r : Ref A) (v : A) (w : World),
  AllocFrontierOk w -> AllocFrontierOk (ref_upd r v w).
Proof.
  intros A r v w HV. unfold ref_upd. destruct (ref_sel_opt r w) as [a|] eqn:Hs; [ | exact HV ].
  destruct (valid_live_interior r a w HV Hs) as [Hlo Hhi].
  exact (valid_ref_install_interior r v w HV Hlo Hhi).
Qed.

(** A bulk ref-heap rewrite preserves [AllocFrontierOk] as long as it never turns an EMPTY cell into a live one —
    i.e. it agrees with the old heap ([= None]) wherever the old heap was [None].  Loc 0 and every fresh
    location are [None] in a valid world, so such a rewrite cannot fabricate a cell there.  This is the
    AllocFrontierOk obligation for the GUARDED bulk slice writes ([slice_clear_h]/[slice_copy]): each only rewrites a
    cell it read LIVE, so an absent cell stays [None]. *)
Lemma valid_guarded_refs : forall (newrefs : RefHeap) (w : World),
  AllocFrontierOk w -> (forall k, w_refs w k = None -> newrefs k = None) ->
  AllocFrontierOk (mkWorld newrefs (w_chans w) (w_maps w) (w_next w) (w_output w)).
Proof.
  intros newrefs w [Hpos [[Hr0 [Hc0 Hm0]] Hfresh]] Hkeep. split; [ | split ].
  - cbn [w_next]. exact Hpos.
  - cbn [w_refs w_chans w_maps]. split; [ exact (Hkeep 0 Hr0) | split; [ exact Hc0 | exact Hm0 ] ].
  - intros l Hle. cbn [w_next w_refs w_chans w_maps] in *. destruct (Hfresh l Hle) as [Hr [Hc Hm]].
    split; [ exact (Hkeep l Hr) | split; [ exact Hc | exact Hm ] ].
Qed.

(** A RANGE install — the shape the slice ops produce when they mint a fresh backing (both slice makes with the
    zero value; [slice_append]'s realloc with the copied/appended values).  Validity holds directly (no
    induction) and is INDIFFERENT to the installed values [g]: loc 0 is below the range (base [= w_next w > 0]),
    every fresh location [>= w_next w + cp] is above it, and only those out-of-range cells matter to the
    invariant. *)
Lemma valid_alloc_range : forall (g : RefHeap) (cp : nat) (w : World),
  AllocFrontierOk w ->
  AllocFrontierOk (mkWorld
    (fun k => if (Nat.leb (w_next w) k && Nat.ltb k (w_next w + cp))%bool then g k else w_refs w k)
    (w_chans w) (w_maps w) (w_next w + cp) (w_output w)).
Proof.
  intros g cp w [Hpos [Hloc0 Hfresh]]. apply Nat.ltb_lt in Hpos. split; [ | split ].
  - cbn [w_next]. apply Nat.ltb_lt. lia.
  - cbn [w_refs w_chans w_maps]. destruct Hloc0 as [Hr0 [Hc0 Hm0]].
    assert (Ha : Nat.leb (w_next w) 0 = false) by (apply Nat.leb_gt; lia).
    rewrite Ha. repeat split; assumption.
  - intros l Hle. cbn [w_next w_refs w_chans w_maps] in *. apply Nat.leb_le in Hle.
    assert (Hb : Nat.ltb l (w_next w + cp) = false) by (apply Nat.ltb_ge; lia).
    rewrite Hb. destruct (Hfresh l ltac:(apply Nat.leb_le; lia)) as [Hr [Hc Hm]].
    destruct (Nat.leb (w_next w) l); repeat split; assumption.
Qed.

(** AllocFrontierOk is preserved by every op that BUMPS [w_next] — proven BY NAME: the single-cell allocators
    [valid_run_ref_new] / [valid_run_ptr_new] / [valid_run_make_chan] / [valid_run_make_chan_buf] /
    [valid_run_map_typed], the multi-cell allocators [valid_run_slice_make_lc] / [valid_run_slice_make_h] /
    [valid_run_gsptr_new], and [valid_run_slice_append] ([append] is not an allocator, but its realloc branch
    mints a fresh backing; the latter three sit next to their later definitions).  It is ALSO preserved by the
    in-place REF-heap writes — every [ref_set] / [ptr_set] / [slice_idx_set] / append-in-cap funnels through the
    guarded [ref_upd] ([valid_ref_upd]) — and by the bulk slice writes [slice_clear_h] / [slice_copy] (guarded
    per cell, [valid_run_slice_clear_h] / [valid_run_slice_copy]).  With [valid_w_init], a program of allocations
    and these ref/slice writes keeps AllocFrontierOk at every step, so [valid_fresh_nonzero] / [valid_fresh_disjoint]
    apply at each allocation — which [ptr_new_nonzero] / [make_chan_nonzero] / [gsptr_new_live] &c. need for
    their nonzero location/base.  SCOPE: the MAP-heap and CHAN-heap edits ([map_set]/[send]/… ) touch their own
    heaps under their own guards; their AllocFrontierOk preservation is the analogous per-heap fact, proven beside
    those ops if a chain ever needs it — NOT asserted by this ref/slice cone. *)
Corollary valid_run_ref_new : forall {A} (tag : GoTypeTag A) (v : A) (w : World) r w',
  AllocFrontierOk w -> run_io (ref_new tag v) w = ORet r w' -> AllocFrontierOk w'.
Proof.
  intros A tag v w r w' HV Hrun. unfold run_io, ref_new in Hrun. cbv zeta in Hrun.
  injection Hrun as _ Hw. subst w'. apply valid_alloc_ref; assumption.
Qed.

Corollary valid_run_make_chan : forall {A} (tag : GoTypeTag A) (w : World) r w',
  AllocFrontierOk w -> run_io (make_chan tag) w = ORet r w' -> AllocFrontierOk w'.
Proof.
  intros A tag w r w' HV Hrun. unfold run_io, make_chan, make_chan_cap in Hrun. cbv zeta in Hrun.
  injection Hrun as _ Hw. subst w'. apply valid_alloc_chan; assumption.
Qed.

Corollary valid_run_make_chan_buf : forall {A} (tag : GoTypeTag A) (n : GoInt) (w : World) r w',
  AllocFrontierOk w -> run_io (make_chan_buf tag n) w = ORet r w' -> AllocFrontierOk w'.
Proof.
  intros A tag n w r w' HV Hrun. unfold run_io, make_chan_buf in Hrun.
  destruct (intraw n <? 0)%Z eqn:Hn; [ discriminate Hrun | ].
  unfold make_chan_cap in Hrun. cbv zeta in Hrun.
  injection Hrun as _ Hw. subst w'. apply valid_alloc_chan; assumption.
Qed.

Corollary valid_run_map_typed : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (w : World) r w',
  AllocFrontierOk w -> run_io (map_make_typed kt vt) w = ORet r w' -> AllocFrontierOk w'.
Proof.
  intros K V kt vt w r w' HV Hrun. unfold run_io, map_make_typed in Hrun. cbv zeta in Hrun.
  injection Hrun as _ Hw. subst w'. apply valid_alloc_map_typed; assumption.
Qed.

(* [ref_get] carries a [GoTypeTag] so that, when a read is bound inside a loop
   block, the lowering knows the Go type to hoist its declaration. *)
(** Read-after-write for the GUARDED [ref_upd] — now carrying a LIVENESS premise ([ref_sel_opt r w = Some a]):
    since [ref_upd] no-ops on a non-live handle, the round-trip holds precisely for a ref whose cell is already
    live, on which the write is the unconditional [ref_install] ([ref_upd_live_eq]).  ([ref_sel_opt] itself is
    defined AHEAD of [ref_upd], with [ref_sel], since the root guard reads it.) *)
Lemma ref_sel_opt_upd_same : forall {A} (r : Ref A) (v a : A) (w : World),
  ref_sel_opt r w = Some a -> ref_sel_opt r (ref_upd r v w) = Some v.
Proof.
  intros A r v a w H. rewrite (ref_upd_live_eq r v a w H). apply ref_sel_opt_install_same.
Qed.
Lemma ref_sel_opt_upd_diff : forall {A B} (r : Ref A) (r' : Ref B) (v : B) (w : World),
  r_loc r <> r_loc r' -> ref_sel_opt r (ref_upd r' v w) = ref_sel_opt r w.
Proof.
  intros A B r r' v w Hne. unfold ref_upd.
  destruct (ref_sel_opt r' w) as [a|]; [ apply ref_sel_opt_install_diff; exact Hne | reflexivity ].
Qed.
(** When the CHECKED read succeeds, the TOTAL read agrees — a live, correctly-typed cell has a real value.
    Bridges [ref_sel_opt = Some a] (cell-existence, the [ref_set] write premise) to the [ref_sel]-valued
    [WHMatchC] heap match. *)
Lemma ref_sel_of_opt : forall {A} (r : Ref A) (a : A) (w : World),
  ref_sel_opt r w = Some a -> ref_sel r w = a.
Proof.
  intros A r a w H. unfold ref_sel. unfold ref_sel_opt in H.
  destruct (w_refs w (r_loc r)) as [[T [tag0 x0]]|].
  - rewrite H. reflexivity.
  - discriminate H.
Qed.

(** [ref_get] — FAILS LOUD on a missing/retyped cell: dereferencing an absent / dangling / WRONG-TAG
    [Ref] (e.g. [mkRef 5 …] at an unallocated location) panics with the Go nil-pointer/invalid-address
    message instead of fabricating a zero.  ([ref_sel_opt] has no loc-0 guard, so a NIL [Ref] over a forged
    matching-tag loc-0 cell would READ it — dead only under [WorldOk].)  A [Ref] is a plain Go VARIABLE, so
    [ref_get] lowers to a bare variable read [x] (NOT a pointer deref [*r] — that is [ptr_get]); the loud check
    is proof-only and never reaches the emitted Go (a variable the generator emits is always in scope).  It
    only rules out the MODEL accepting a WRONG-TAG or ABSENT forged read (a SAME-TAG forged alias still reads
    the aliased cell — the origin frontier, not sealed here). *)
Definition ref_get {A} (tag : GoTypeTag A) (r : Ref A) : IO A :=
  fun w => match ref_sel_opt r w with
           | Some a => ORet a w
           | None   => OPanic rt_nil_deref w
           end.
(** ┌─ HEAP-WRITE ANTI-FORGERY: SCOPE AND FRONTIER ────────────────────────────────────────────────────┐
    Every heap-write op ([ref_set]/[ptr_set]/[slice_idx_set]/[hfield_set]/[slice_append] in-place) now
    writes ONLY through a cell that is LIVE ([ref_sel_opt = Some]), and FAILS LOUD ([rt_nil_deref]) on an
    absent / dangling / retyped handle (at ANY location) — so a forged handle can no longer FABRICATE a cell
    at an unallocated location, symmetric with the reads.  ([ptr_set] additionally guards [p_loc = 0]
    explicitly; [ref_set] has NO loc-0 guard, so a NIL [Ref] is dead only under [WorldOk] — [valid_loc0_empty]
    — a forged loc-0 cell of the matching tag being the loc-0 instance of the frontier below.)
    ⚠ FRONTIER (shared with [chan]/[map]'s forged-non-nil
    case): this does NOT stop a forged handle whose location COINCIDES with an ALREADY-LIVE cell of another
    object — the location-based model then ALIASES that cell (as [ptr_alias]/[subslice_alias]/[hstruct_alias]
    are theorems, aliasing is intrinsic).  Preventing forged ALIASING needs allocation PROVENANCE on the
    handle types ([Ref]/[Ptr]/[SliceH]/[HStruct] carrying an unforgeable allocation witness) — a deliberate
    architectural extension, out of the current location-based scope, NOT claimed as solved here.
    └───────────────────────────────────────────────────────────────────────────────────────────────────┘ *)
(** [ref_set] — the WRITE side, now SYMMETRIC with [ref_get]: it writes only through an allocated,
    correctly-typed cell ([ref_sel_opt r w = Some _]), and FAILS LOUD ([rt_nil_deref]) on an absent / dangling
    / retyped [r] (at any location) — exactly as [ref_get] does, instead of fabricating a cell.  (A NIL [r]
    ([r_loc = 0]) is dead only under [WorldOk]: [ref_set] has no explicit loc-0 guard, so an arbitrary forged
    loc-0 cell of the matching tag would be written — excluded from reachable worlds by [WorldOk].)  On the
    loud branch the world is UNCHANGED ([OPanic w]) — no mutation (see [ref_set_dangling]).  Body plugin-lowered
    to [r = v], so the check never reaches the emitted Go (a real [r] is allocated). *)
Definition ref_set {A} (r : Ref A) (v : A) : IO unit :=
  fun w => match ref_sel_opt r w with
           | Some _ => ORet tt (ref_upd r v w)
           | None   => OPanic rt_nil_deref w
           end.
Lemma run_ref_get : forall {A} (tag : GoTypeTag A) (r : Ref A) (w : World),
  run_io (ref_get tag r) w =
    match ref_sel_opt r w with
    | Some a => ORet a w
    | None   => OPanic rt_nil_deref w
    end.
Proof. reflexivity. Qed.
(** On an allocated, correctly-typed cell (the only case a valid program hits) the read delivers the value. *)
Lemma run_ref_get_some : forall {A} (tag : GoTypeTag A) (r : Ref A) (a : A) (w : World),
  ref_sel_opt r w = Some a -> run_io (ref_get tag r) w = ORet a w.
Proof. intros A tag r a w H. unfold run_io, ref_get. rewrite H. reflexivity. Qed.
Lemma run_ref_set : forall {A} (r : Ref A) (v : A) (w : World),
  run_io (ref_set r v) w =
    match ref_sel_opt r w with
    | Some _ => ORet tt (ref_upd r v w)
    | None   => OPanic rt_nil_deref w
    end.
Proof. reflexivity. Qed.
(** On an allocated, correctly-typed cell (the only case a valid program hits) the write proceeds. *)
Lemma run_ref_set_some : forall {A} (r : Ref A) (v a : A) (w : World),
  ref_sel_opt r w = Some a -> run_io (ref_set r v) w = ORet tt (ref_upd r v w).
Proof. intros A r v a w H. unfold run_io, ref_set. rewrite H. reflexivity. Qed.
(** FAIL-LOUD, NO-MUTATION witness: a write through a handle that reads DEAD ([ref_sel_opt r w = None] —
    missing / dangling / wrong-tag; NIL only under [WorldOk]) PANICS and leaves the world UNCHANGED — the raw
    [ref_upd] can never be reached to fabricate a cell. *)
Lemma ref_set_dangling : forall {A} (r : Ref A) (v : A) (w : World),
  ref_sel_opt r w = None -> run_io (ref_set r v) w = OPanic rt_nil_deref w.
Proof. intros A r v w H. unfold run_io, ref_set. rewrite H. reflexivity. Qed.

(** Read-after-write at the STATE level (with the LIVENESS premise [ref_sel_opt r w = Some a]): on a live ref
    the guarded [ref_upd] is the [ref_install], which tags the cell with [r]'s own tag, so the subsequent
    [ref_sel]'s [tag_coerce] is reflexive ([tag_coerce_refl]) and the location lookup hits ([eqb_refl]). *)
Lemma ref_sel_upd_same : forall {A} (r : Ref A) (v a : A) (w : World),
  ref_sel_opt r w = Some a -> ref_sel r (ref_upd r v w) = v.
Proof.
  intros A r v a w H. rewrite (ref_upd_live_eq r v a w H). apply ref_sel_install_same.
Qed.

(** Read-after-write — a THEOREM: after [ref_set r v], [ref_get] returns [v]. *)
Lemma ref_get_set_same : forall {A} (tag : GoTypeTag A) (r : Ref A) (v : A),
  bind (ref_set r v) (fun _ => ref_get tag r) =io=
  bind (ref_set r v) (fun _ => ret v).
Proof.
  intros. intro w.
  rewrite !run_bind, !run_ref_set.
  destruct (ref_sel_opt r w) as [a|] eqn:Hsel.
  - cbn. rewrite run_ref_get, (ref_sel_opt_upd_same r v a w Hsel). cbn. rewrite run_ret. reflexivity.
  - reflexivity.
Qed.

(** ---- Pointers (Go spec "Pointer types") ----

    A Go pointer [*T] is a typed heap LOCATION.  It shares the [w_refs] cell heap with
    [Ref] — both are heap locations — but lowers DIFFERENTLY: a [Ref] is a local Go
    variable (one cell, no aliasing across copies), whereas a [Ptr] lowers to Go [*T],
    so COPYING a pointer makes two handles to the SAME cell (aliasing — the defining
    pointer behaviour).  A [Ptr] may be nil ([ptr_nil], location 0); dereferencing nil
    panics (Go's nil-pointer panic) — the raw [ptr_get]/[ptr_set] are the escape hatch,
    [ptr_get_ok] (below) the safe-by-construction comma-ok form.

    [Ptr A] is its own record so it is a DISTINCT type the plugin renders [*T]; its ops
    go through the SAME [ref_sel]/[ref_upd] (via [ptr_as_ref]), so read-after-write and
    aliasing are inherited from [ref_sel_upd_same] — no new heap, no new axiom. *)
(** [ptr_as_ref tag p]: view a (tag-free) [Ptr A] as a [Ref A] at the same location with the GIVEN
    tag — so the deref ops reuse the [ref_sel]/[ref_upd] heap (read-after-write, aliasing inherited). *)
Definition ptr_as_ref {A} (tag : GoTypeTag A) (p : Ptr A) : Ref A := mkRef (p_loc p) tag.
Definition ptr_nil {A} (tag : GoTypeTag A) : Ptr A := mkPtr 0.
(* A TAG-FREE nil pointer (for a NAMED/recursive type that has no [GoTypeTag], e.g. a recursive
   struct's self-pointer field): same nil handle, but needs no tag.  Lowers to a bare Go [nil] (valid
   where the target type is known — a struct-literal field / typed slot).  The [unit] arg makes it a
   recognizable application at the call site. *)
Definition ptr_nil_tf {A} (_ : unit) : Ptr A := mkPtr 0.

(** [ptr_new tag v]: Go [p := new(T); *p = v] — allocate a FRESH (nonzero) location,
    store [v] (tagged), bump the allocator, return the pointer.  Fresh ⇒ never nil. *)
Definition ptr_new {A} (tag : GoTypeTag A) (v : A) : IO (Ptr A) :=
  fun w => let l := w_next w in
           ORet (mkPtr l)
                (mkWorld (fun k => if Nat.eqb k l then Some (existT _ A (tag, v))
                                   else w_refs w k)
                         (w_chans w) (w_maps w) (S l) (w_output w)).
(** [new(T)] (Go's predeclared [new]): allocate a FRESH [*T] pointing to the ZERO value
    of [T], return it.  = [ptr_new tag (zero_val tag)] — fresh, hence never nil; the
    pointee reads as the zero value.  Lowers to Go [new(T)]. *)
Definition go_new {A} (tag : GoTypeTag A) : IO (Ptr A) := ptr_new tag (zero_val tag).

(** [ptr_get tag p] = [*p] (deref read); [ptr_set tag p v] = [*p = v] (deref write).  Both take the
    pointee tag explicitly (the tag-free handle does not carry it). *)
(** The RAW deref/assign PANIC on a nil pointer, faithful to Go's [*p] / [*p = v].  The
    nil sentinel is location 0, which [AllocFrontierOk] RESERVES (no allocation ever returns it),
    so the [eqb (p_loc p) 0] guard exactly separates "live cell" from "nil".  These are the
    catch-able escape hatches (rule 4); [ptr_get_ok] is the safe-by-construction comma-ok form. *)
(** [ptr_get] panics on a NIL pointer AND on a DANGLING one — a non-nil but
    unallocated/retyped cell panics (checked [ref_sel_opt]) rather than fabricating a zero. *)
Definition ptr_get {A} (tag : GoTypeTag A) (p : Ptr A) : IO A :=
  fun w => if Nat.eqb (p_loc p) 0 then OPanic rt_nil_deref w
           else match ref_sel_opt (ptr_as_ref tag p) w with
                | Some a => ORet a w
                | None   => OPanic rt_nil_deref w
                end.
(** [ptr_set tag p v] = [*p = v] — now SYMMETRIC with [ptr_get]: nil PANICS ([p_loc = 0]) and, on a non-nil
    handle, it writes only through an allocated / correctly-typed cell ([ref_sel_opt = Some _]) and FAILS LOUD
    on a forged / dangling / retyped [p] ([ref_sel_opt = None]) — no longer writing through a non-nil but
    unallocated handle.  Both loud branches leave the world UNCHANGED (see [ptr_set_dangling]). *)
Definition ptr_set {A} (tag : GoTypeTag A) (p : Ptr A) (v : A) : IO unit :=
  fun w => if Nat.eqb (p_loc p) 0 then OPanic rt_nil_deref w
           else match ref_sel_opt (ptr_as_ref tag p) w with
                | Some _ => ORet tt (ref_upd (ptr_as_ref tag p) v w)
                | None   => OPanic rt_nil_deref w
                end.
Lemma run_ptr_get : forall {A} (tag : GoTypeTag A) (p : Ptr A) (w : World),
  run_io (ptr_get tag p) w =
    if Nat.eqb (p_loc p) 0 then OPanic rt_nil_deref w
    else match ref_sel_opt (ptr_as_ref tag p) w with
         | Some a => ORet a w
         | None   => OPanic rt_nil_deref w
         end.
Proof. reflexivity. Qed.
Lemma run_ptr_set : forall {A} (tag : GoTypeTag A) (p : Ptr A) (v : A) (w : World),
  run_io (ptr_set tag p v) w =
    if Nat.eqb (p_loc p) 0 then OPanic rt_nil_deref w
    else match ref_sel_opt (ptr_as_ref tag p) w with
         | Some _ => ORet tt (ref_upd (ptr_as_ref tag p) v w)
         | None   => OPanic rt_nil_deref w
         end.
Proof. reflexivity. Qed.
(** FAIL-LOUD, NO-MUTATION witness: [*p = v] through a non-nil but forged / dangling [p] PANICS and leaves
    the world UNCHANGED — symmetric with [ptr_get] on the same handle (the audit's get/set asymmetry closed). *)
Lemma ptr_set_dangling : forall {A} (tag : GoTypeTag A) (p : Ptr A) (v : A) (w : World),
  Nat.eqb (p_loc p) 0 = false -> ref_sel_opt (ptr_as_ref tag p) w = None ->
  run_io (ptr_set tag p v) w = OPanic rt_nil_deref w.
Proof. intros A tag p v w Hnn Hsel. rewrite run_ptr_set, Hnn, Hsel. reflexivity. Qed.

(** Faithfulness: dereferencing / assigning through a NIL pointer PANICS, exactly as Go's [*nil]. *)
Lemma ptr_get_nil : forall {A} (tag : GoTypeTag A) (w : World),
  run_io (ptr_get tag (ptr_nil tag)) w = OPanic rt_nil_deref w.
Proof. reflexivity. Qed.
Lemma ptr_set_nil : forall {A} (tag : GoTypeTag A) (v : A) (w : World),
  run_io (ptr_set tag (ptr_nil tag) v) w = OPanic rt_nil_deref w.
Proof. reflexivity. Qed.

(** Read-after-write THROUGH a pointer — a THEOREM (inherited from the shared heap): after
    [ptr_set tag p v], [ptr_get tag p] returns [v].  Holds for ALL [p]: on a nil OR forged/dangling pointer
    BOTH sides panic at the [ptr_set] step (so they agree), and on a live pointer the read observes the write. *)
Lemma ptr_get_set_same : forall {A} (tag : GoTypeTag A) (p : Ptr A) (v : A),
  bind (ptr_set tag p v) (fun _ => ptr_get tag p) =io=
  bind (ptr_set tag p v) (fun _ => ret v).
Proof.
  intros. intro w.
  rewrite !run_bind, !run_ptr_set.
  destruct (Nat.eqb (p_loc p) 0) eqn:Hnil.
  - reflexivity.
  - destruct (ref_sel_opt (ptr_as_ref tag p) w) as [a|] eqn:Hsel.
    + cbn. rewrite run_ptr_get, Hnil. cbn. rewrite (ref_sel_opt_upd_same (ptr_as_ref tag p) v a w Hsel). cbn. rewrite run_ret. reflexivity.
    + reflexivity.
Qed.

(** ---- [&x]: the ADDRESS-OF operator (Go's `&`) — the missing inverse of [ptr_as_ref] ----

    Taking the address of a local variable [x] (a [Ref A]) yields a [*T] ([Ptr A]) aliasing x's cell.
    A [Ref] and a [Ptr] share the SAME [w_refs] heap (a [Ref] is a Go local, a [Ptr] its `*T` handle), so
    [&x] is simply the [Ref]'s location wrapped as a (tag-free) [Ptr] — [ptr_as_ref]'s inverse.  KEY SAFETY
    PROPERTY (CONDITIONAL, not blanket): a local allocated by [ref_new] IN A WELL-FORMED WORLD ([AllocFrontierOk
    w], so [w_next w <> 0]) lives at a NONZERO location ([ref_new_loc_nonzero]), so for such an [x] ([r_loc r
    <> 0]) [&x] is NON-NIL ([ref_as_ptr_not_nil] / [ref_new_addr_nonnil], below).  ⚠ NON-NIL IS NOT YET
    SAFE-DEREF: a non-nil [&x] whose cell is ABSENT/wrong-tag ([ref_sel_opt = None]) still FAILS LOUD
    ([rt_nil_deref]); a panic-free read/write ALSO needs the cell LIVE ([ref_sel_opt r w = Some _], which
    [ref_new] establishes — [ref_new_reads]), via [ptr_get_ref_as_ptr]/[ptr_set_ref_as_ptr], which carry BOTH
    premises (neither [ref_as_ptr_not_nil] nor [ref_new_addr_nonnil] proves the live-cell half).  The proven
    END-TO-END safe-deref theorems are [ref_alloc_addr_read_no_panic]/[ref_alloc_addr_write_no_panic] (the ref
    analogue of [ptr_alloc_assign_no_panic]), chaining allocation → both premises → no panic.  This is NOT intrinsic
    to [ref_as_ptr] NOR to [ref_new]: [Ref] is a public record, so the forgeable [mkRef 0] is a representable
    nil ref whose [&] is a nil [Ptr]; and on a malformed [w] ([w_next w = 0]) even [ref_new] would mint a nil
    ref.  The nonzero-location premise is a HYPOTHESIS (discharged by [ref_new] UNDER [AllocFrontierOk], NOT by an
    arbitrary [Ref]).  Read/write THROUGH [&x] alias [x] — the defining pointer behaviour — inherited from the
    shared heap, no new axiom. *)
Definition ref_as_ptr {A} (r : Ref A) : Ptr A := mkPtr (r_loc r).

Lemma ref_as_ptr_loc : forall {A} (r : Ref A), p_loc (ref_as_ptr r) = r_loc r.
Proof. reflexivity. Qed.

(* Viewing [&x] back as a [Ref] (with x's own tag) recovers [x] exactly — same location, same tag. *)
Lemma ptr_as_ref_of_ref_as_ptr : forall {A} (r : Ref A),
  ptr_as_ref (r_tag r) (ref_as_ptr r) = r.
Proof. intros A [l tag]. reflexivity. Qed.

(* [&x] of an ALLOCATED local ([r_loc r <> 0] — the premise, which [ref_new]'s result satisfies UNDER
   [AllocFrontierOk], via [ref_new_loc_nonzero] below) yields a NON-NIL pointer.  (NON-NIL ONLY — this lemma does
   NOT prove safe-deref; a panic-free deref additionally needs the live cell, proven end-to-end by
   [ref_alloc_addr_read_no_panic]/[ref_alloc_addr_write_no_panic] below.)  (Not ALL [Ref]s are nonzero: the
   public [mkRef 0] is a nil ref, so [r_loc r <> 0] is a HYPOTHESIS, not a blanket fact.) *)
Lemma ref_as_ptr_not_nil : forall {A} (r : Ref A),
  r_loc r <> 0 -> p_loc (ref_as_ptr r) <> 0.
Proof. intros A r Hnz. rewrite ref_as_ptr_loc. exact Hnz. Qed.

(* The [ref_new] analogue of [ptr_new_nonzero]: an ALLOCATED local's location is nonzero — but ONLY under
   [AllocFrontierOk w].  [ref_new] mints [l := w_next w]; that is nonzero exactly when the world is well-formed
   ([valid_fresh_nonzero]).  So "[ref_new] gives [r_loc <> 0]" is CONDITIONAL on [AllocFrontierOk], NOT a bare
   fact: on a malformed [w] with [w_next w = 0], [ref_new] would return a nil [Ref].  This is the theorem the
   address-of prose leans on; state its premise. *)
Lemma ref_new_loc_nonzero : forall {A} (tag : GoTypeTag A) (v : A) (w : World) r w',
  AllocFrontierOk w -> run_io (ref_new tag v) w = ORet r w' -> r_loc r <> 0.
Proof.
  intros A tag v w r w' HV Hrun. unfold run_io, ref_new in Hrun. cbv zeta in Hrun.
  injection Hrun as Hr _. subst r. cbn [r_loc].
  pose proof (valid_fresh_nonzero w HV) as Hp. apply Nat.ltb_lt in Hp. lia.
Qed.

(* CLOSED-WORLD end-to-end: [&x] of a FRESHLY allocated local is NON-NIL — chains [ref_new_loc_nonzero] into
   [ref_as_ptr_not_nil].  Needs [AllocFrontierOk w] (the honest premise the informal "&x is never nil" prose
   dropped).  This is a NON-NIL theorem (the ref counterpart of [ptr_new_nonzero]), NOT a no-panic one:
   panic-free read/write THROUGH [&x] additionally needs the live cell ([ref_sel_opt = Some], via
   [ptr_get_ref_as_ptr]/[ptr_set_ref_as_ptr]), proven END-TO-END by [ref_alloc_addr_read_no_panic]/
   [ref_alloc_addr_write_no_panic] below (the ref analogue of [ptr_alloc_assign_no_panic]).  The guarantee is
   a theorem OFF the invariant, never intrinsic to the public [Ref]/[Ptr] record. *)
Corollary ref_new_addr_nonnil : forall {A} (tag : GoTypeTag A) (v : A) (w : World) r w',
  AllocFrontierOk w -> run_io (ref_new tag v) w = ORet r w' -> p_loc (ref_as_ptr r) <> 0.
Proof.
  intros A tag v w r w' HV Hrun.
  apply ref_as_ptr_not_nil. exact (ref_new_loc_nonzero tag v w r w' HV Hrun).
Qed.

(* The [ref_new] analogue of [ptr_new_reads]: a freshly allocated local has a LIVE, correctly-typed cell
   ([ref_sel_opt r w' = Some v]) — [ref_new] installs [Some (existT _ A (tag, v))] at [w_next w].  This is the
   SECOND premise (beside nonzero-location) that the panic-free deref theorems below need; UNCONDITIONAL (no
   [AllocFrontierOk] — installation is intrinsic to [ref_new], location freshness is what needs the invariant). *)
Lemma ref_new_reads : forall {A} (tag : GoTypeTag A) (v : A) (w : World) r w',
  run_io (ref_new tag v) w = ORet r w' -> ref_sel_opt r w' = Some v.
Proof.
  intros A tag v w r w' Hrun. unfold run_io, ref_new in Hrun. cbv zeta in Hrun.
  injection Hrun as Hr Hw. subst r w'.
  unfold ref_sel_opt; cbn. rewrite Nat.eqb_refl; cbn. apply tag_coerce_refl.
Qed.

(* READ through [&x]: [*(&x)] reads [x]'s value (with x's tag) without panicking — for a nonzero-location,
   LIVE [x] (the lemma's [r_loc r <> 0] + [ref_sel_opt r w = Some _] premises; NOT unconditional). *)
Lemma ptr_get_ref_as_ptr : forall {A} (r : Ref A) (a : A) (w : World),
  r_loc r <> 0 ->
  ref_sel_opt r w = Some a ->
  run_io (ptr_get (r_tag r) (ref_as_ptr r)) w = ORet a w.
Proof.
  intros A r a w Hnz Hpres. rewrite run_ptr_get, ref_as_ptr_loc.
  rewrite (proj2 (Nat.eqb_neq (r_loc r) 0) Hnz).
  rewrite ptr_as_ref_of_ref_as_ptr, Hpres. reflexivity.
Qed.

(* WRITE through [&x]: [*(&x) = v] updates [x]'s OWN cell without panicking — for a nonzero-location, LIVE [x]
   ([r_loc r <> 0]; [x]'s cell allocated, [ref_sel_opt r w = Some _]; [ptr_as_ref (r_tag r) (ref_as_ptr r) = r],
   so [&x]'s cell IS [x]'s). BOTH premises are the lemma's; the guarantee is conditional, not unconditional. *)
Lemma ptr_set_ref_as_ptr : forall {A} (r : Ref A) (v a : A) (w : World),
  r_loc r <> 0 -> ref_sel_opt r w = Some a ->
  run_io (ptr_set (r_tag r) (ref_as_ptr r) v) w = ORet tt (ref_upd r v w).
Proof.
  intros A r v a w Hnz Hsel. rewrite run_ptr_set, ref_as_ptr_loc.
  rewrite (proj2 (Nat.eqb_neq (r_loc r) 0) Hnz).
  rewrite ptr_as_ref_of_ref_as_ptr, Hsel. reflexivity.
Qed.

(* THE DEFINING ALIAS: writing through [&x] is visible at [x] — [*(&x) = v], then [x] reads back [v].
   This is the whole point of taking an address: the pointer and the variable share one cell. *)
Theorem ptr_set_ref_as_ptr_aliases : forall {A} (r : Ref A) (v a : A) (w : World),
  r_loc r <> 0 -> ref_sel_opt r w = Some a ->
  exists w', run_io (ptr_set (r_tag r) (ref_as_ptr r) v) w = ORet tt w' /\ ref_sel r w' = v.
Proof.
  intros A r v a w Hnz Hsel. exists (ref_upd r v w). split.
  - exact (ptr_set_ref_as_ptr r v a w Hnz Hsel).
  - exact (ref_sel_upd_same r v a w Hsel).
Qed.

(* CLOSED-WORLD SAFE-DEREF (end-to-end, the ref analogue of [ptr_alloc_assign_no_panic]): allocate a local,
   take its address, and read/write THROUGH [&x] — provably NO panic.  These chain BOTH premises the deref
   lemmas need: nonzero-location ([ref_new_loc_nonzero], under [AllocFrontierOk]) AND live cell ([ref_new_reads],
   unconditional).  THIS is "safe deref end-to-end" — non-nil ([ref_new_addr_nonnil]) alone is NOT it. *)
Corollary ref_alloc_addr_read_no_panic : forall {A} (tag : GoTypeTag A) (v : A) (w : World) r w',
  AllocFrontierOk w -> run_io (ref_new tag v) w = ORet r w' ->
  run_io (ptr_get (r_tag r) (ref_as_ptr r)) w' = ORet v w'.
Proof.
  intros A tag v w r w' HV Hrun. apply (ptr_get_ref_as_ptr r v w').
  - exact (ref_new_loc_nonzero tag v w r w' HV Hrun).
  - exact (ref_new_reads tag v w r w' Hrun).
Qed.
Corollary ref_alloc_addr_write_no_panic : forall {A} (tag : GoTypeTag A) (v v' : A) (w : World) r w',
  AllocFrontierOk w -> run_io (ref_new tag v) w = ORet r w' ->
  exists w'', run_io (ptr_set (r_tag r) (ref_as_ptr r) v') w' = ORet tt w'' /\ ref_sel r w'' = v'.
Proof.
  intros A tag v v' w r w' HV Hrun. apply (ptr_set_ref_as_ptr_aliases r v' v w').
  - exact (ref_new_loc_nonzero tag v w r w' HV Hrun).
  - exact (ref_new_reads tag v w r w' Hrun).
Qed.

(** ---- CLOSED-WORLD nil-safety: the modeled nil panics are UNREACHABLE for ALLOCATED handles ----

    Modeling the nil panic (in [ptr_get]/[ptr_set]/[map_set]) plays TWO roles.  (1) COMPLETENESS: it is
    faithful to Go's [*nil] / nil-map-write.  (2) DEFENCE: it is a cheap RUNTIME guard for the future
    OPEN WORLD (imports), where proofs will rest on axioms about external code that could be WRONG — the
    check turns a bad assumption (an import handing back nil where we assumed non-nil) into a loud panic
    rather than silent heap corruption.  But in the CLOSED WORLD — every handle minted by an allocator —
    the "oops" must never fire: [valid_fresh_nonzero] proves a freshly minted location is
    nonzero, so an allocated pointer/map is provably non-nil and the op takes the heap branch, NEVER
    [OPanic].  ([ptr_alloc_assign_no_panic] / [map_alloc_set_no_panic] are that guarantee.)  The OPEN-WORLD
    boundary — a function handed an ARBITRARY handle — still guards via [ptr_get_ok] / [ptr_is_nil] before
    crossing in.  (Goal: NO panic class — nil, div-by-zero, OOB, send-on-closed — is reachable in a
    well-formed closed-world program; the evidence-carrying APIs ([div_nz], [slice_at], here) are the bricks.) *)
Lemma pos_neq0 : forall x : nat, (0 <? x)%nat = true -> Nat.eqb x 0 = false.
Proof.
  intros x H. apply Nat.eqb_neq. apply Nat.ltb_lt in H. lia.
Qed.

(** An ALLOCATED pointer is non-nil (its handle is the pre-bump [w_next], nonzero by [valid_fresh_nonzero]). *)
Lemma ptr_new_nonzero : forall {A} (tag : GoTypeTag A) (v : A) (w : World) p w',
  AllocFrontierOk w -> run_io (ptr_new tag v) w = ORet p w' -> Nat.eqb (p_loc p) 0 = false.
Proof.
  intros A tag v w p w' HV Hrun. unfold run_io, ptr_new in Hrun. cbv zeta in Hrun.
  injection Hrun as Hp _. subst p. cbn [p_loc]. apply pos_neq0, (valid_fresh_nonzero w HV).
Qed.
(** [ptr_new] is in the [AllocFrontierOk] preservation path (its world-shape is the single-cell [valid_alloc_ref]
    shape) — so a program taking [&x] then allocating again keeps the invariant [ptr_new_nonzero] leans on. *)
Corollary valid_run_ptr_new : forall {A} (tag : GoTypeTag A) (v : A) (w : World) r w',
  AllocFrontierOk w -> run_io (ptr_new tag v) w = ORet r w' -> AllocFrontierOk w'.
Proof.
  intros A tag v w r w' HV Hrun. unfold run_io, ptr_new in Hrun. cbv zeta in Hrun.
  injection Hrun as _ Hw. subst w'. apply valid_alloc_ref; assumption.
Qed.

(** A pointer freshly allocated by [ptr_new] has a live, correctly-typed cell — [ref_sel_opt] reads [Some v]
    — so the [ptr_set]/[ptr_get] cell-existence check is SATISFIED for any [ptr_new] handle (the loud branch
    is UNREACHABLE for real pointers, a boundary defense for the public [mkPtr] only). *)
Lemma ptr_new_reads : forall {A} (tag : GoTypeTag A) (v : A) (w : World) p w',
  run_io (ptr_new tag v) w = ORet p w' -> ref_sel_opt (ptr_as_ref tag p) w' = Some v.
Proof.
  intros A tag v w p w' Hrun. unfold run_io, ptr_new in Hrun. cbv zeta in Hrun.
  injection Hrun as Hp Hw. subst p w'.
  unfold ref_sel_opt, ptr_as_ref; cbn. rewrite Nat.eqb_refl; cbn. apply tag_coerce_refl.
Qed.
(** On a non-nil pointer with a LIVE cell the panic branches are DEAD — deref/assign just hit the heap.
    (Mirrors [ptr_get_nonnil]: same [ref_sel_opt = Some] premise — the write/read symmetry.) *)
Lemma ptr_set_nonnil : forall {A} (tag : GoTypeTag A) (p : Ptr A) (v a : A) (w : World),
  Nat.eqb (p_loc p) 0 = false ->
  ref_sel_opt (ptr_as_ref tag p) w = Some a ->
  run_io (ptr_set tag p v) w = ORet tt (ref_upd (ptr_as_ref tag p) v w).
Proof. intros A tag p v a w Hnn Hsel. rewrite run_ptr_set, Hnn, Hsel. reflexivity. Qed.
Lemma ptr_get_nonnil : forall {A} (tag : GoTypeTag A) (p : Ptr A) (a : A) (w : World),
  Nat.eqb (p_loc p) 0 = false ->
  ref_sel_opt (ptr_as_ref tag p) w = Some a ->
  run_io (ptr_get tag p) w = ORet a w.
Proof. intros A tag p a w Hnn Hpres. rewrite run_ptr_get, Hnn, Hpres. reflexivity. Qed.

(** CLOSED-WORLD GUARANTEE: allocate a pointer, then assign through it — provably NO panic. *)
Corollary ptr_alloc_assign_no_panic : forall {A} (tag : GoTypeTag A) (v v' : A) (w : World) p w',
  AllocFrontierOk w -> run_io (ptr_new tag v) w = ORet p w' ->
  exists w'', run_io (ptr_set tag p v') w' = ORet tt w''.
Proof.
  intros A tag v v' w p w' HV Hrun. eexists.
  apply (ptr_set_nonnil tag p v' v w');
    [ apply (ptr_new_nonzero tag v w p w' HV Hrun) | apply (ptr_new_reads tag v w p w' Hrun) ].
Qed.

(** The map analogue: an allocated map is non-nil ([map_make_typed_nonzero]).  (Non-nil ALONE does not stop
    [map_set] panicking — a non-nil WRONG-TAG handle still fails [map_cell_ok] and panics; tag-correctness
    ([map_cell_ok_make_typed], below) is what discharges the guard.) *)
Lemma map_make_typed_nonzero : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (w : World) m w',
  AllocFrontierOk w -> run_io (map_make_typed kt vt) w = ORet m w' -> Nat.eqb (gm_loc m) 0 = false.
Proof.
  intros K V kt vt w m w' HV Hrun. unfold run_io, map_make_typed in Hrun. cbv zeta in Hrun.
  injection Hrun as Hm _. subst m. cbn [gm_loc]. apply pos_neq0, (valid_fresh_nonzero w HV).
Qed.
(** A freshly [make(map[K]V)]d map is present AND TYPE-CORRECT: [map_make_typed kt vt] installs a [Some] cell at
    [w_next w] whose stored tags ARE [kt]/[vt], and [AllocFrontierOk] forces [w_next w <> 0], so
    [map_cell_ok kt vt m w' = true] (checkpoint-58: the allocator produces the tag-aware evidence the guarded
    map ops demand — [map_set] reaches its real update path, not the fail-loud branch).  DIRECTION: this is
    [map_make_typed ⟹ map_cell_ok] ONLY, NOT provenance — [map_cell_ok] checks nonzero location + cell + tag
    match, so a SAME-TAG forged world satisfies it too; the converse is not claimed. *)
Lemma map_cell_ok_make_typed : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (w : World) m w',
  AllocFrontierOk w -> run_io (map_make_typed kt vt) w = ORet m w' -> map_cell_ok kt vt m w' = true.
Proof.
  intros K V kt vt w m w' HV Hrun. unfold run_io, map_make_typed in Hrun. cbv zeta in Hrun.
  injection Hrun as Hm Hw'. subst m w'. unfold map_cell_ok. cbn [gm_loc].
  rewrite (pos_neq0 _ (valid_fresh_nonzero w HV)).
  cbn [w_maps]. rewrite Nat.eqb_refl. cbn. rewrite !tag_eq_refl. reflexivity.
Qed.

(** ALLOCATOR EVIDENCE (checkpoint-58, channel dual of [map_cell_ok_make_typed]): a freshly made channel is
    TAG-CORRECT — the allocator installs a [Some (existT _ A (tag, …))] cell at the fresh [w_next] location,
    and [AllocFrontierOk] forces [w_next <> 0], so [chan_cell_ok tag ch w' = true].  DIRECTION: this proves
    [make_chan* ⟹ chan_cell_ok] ONLY.  It is NOT provenance — [chan_cell_ok] checks nonzero location + cell
    presence + tag match, so a SAME-TAG forged world ALSO satisfies it; the converse ([chan_cell_ok ⟹ made by
    an allocator]) does NOT hold and is not claimed.  What a genuine allocation supplies is exactly the
    tag-correct-cell evidence the ops now demand (the [chan_write]/[chan_room]/[send]/[recv]/[close] guard, and
    [chan_alloc_close_no_panic] below discharges it).  (Proved directly per allocator — no capacity helper,
    keeping the fuel/cap ratchet clean.) *)
Lemma chan_cell_ok_make_chan : forall {A} (tag : GoTypeTag A) (w : World) ch w',
  AllocFrontierOk w -> run_io (make_chan tag) w = ORet ch w' -> chan_cell_ok tag ch w' = true.
Proof.
  intros A tag w ch w' HV Hrun. unfold run_io, make_chan, make_chan_cap in Hrun. cbv zeta in Hrun.
  injection Hrun as Hch Hw'. subst ch w'. unfold chan_cell_ok. cbn [ch_loc].
  rewrite (pos_neq0 _ (valid_fresh_nonzero w HV)).
  cbn [w_chans]. rewrite Nat.eqb_refl. cbn. rewrite tag_eq_refl. reflexivity.
Qed.
Lemma chan_cell_ok_make_chan_buf : forall {A} (tag : GoTypeTag A) (n : GoInt) (w : World) ch w',
  AllocFrontierOk w -> run_io (make_chan_buf tag n) w = ORet ch w' -> chan_cell_ok tag ch w' = true.
Proof.
  intros A tag n w ch w' HV Hrun. unfold run_io, make_chan_buf in Hrun.
  destruct ((intraw n <? 0)%Z) eqn:Hneg; [ discriminate Hrun | ].
  unfold make_chan_cap in Hrun. cbv zeta in Hrun.
  injection Hrun as Hch Hw'. subst ch w'. unfold chan_cell_ok. cbn [ch_loc].
  rewrite (pos_neq0 _ (valid_fresh_nonzero w HV)).
  cbn [w_chans]. rewrite Nat.eqb_refl. cbn. rewrite tag_eq_refl. reflexivity.
Qed.
(** [map_set] on a TAG-CORRECT cell ([map_cell_ok = true]) takes its real update path.  (Named for its
    actual guard [map_cell_ok] — NOT "nonnil": a non-nil WRONG-TAG handle fails [map_cell_ok] and panics, so
    non-nil is not the write authority.) *)
Lemma map_set_cell_ok : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (v : V) (m : GoMap K V) (w : World),
  map_cell_ok kt vt m w = true ->
  run_io (map_set kt vt k v m) w = ORet tt (map_upd kt vt k v m w).
Proof. intros K V kt vt k v m w Hp. rewrite run_map_set, Hp. reflexivity. Qed.
Corollary map_alloc_set_no_panic : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (v : V) (w : World) m w',
  AllocFrontierOk w -> run_io (map_make_typed kt vt) w = ORet m w' ->
  exists w'', run_io (map_set kt vt k v m) w' = ORet tt w''.
Proof.
  intros K V kt vt k v w m w' HV Hrun. eexists.
  apply map_set_cell_ok, (map_cell_ok_make_typed kt vt w m w' HV Hrun).
Qed.

(** Channel analogue: an ALLOCATED channel is non-nil ([make_chan] mints the pre-bump [w_next], nonzero by
    [valid_fresh_nonzero]), so [close] on it never hits the NIL panic.  [chan_alloc_close_no_panic] is the
    guarantee — and for a FRESH channel it rules out the OTHER [close] panic (double-close) too, since
    [make_chan_open] proves the fresh cell is open; both are discharged from the allocation, no caller premise.
    (In GENERAL — an arbitrary already-owned channel — double-close IS a real panic, gated by [chan_closed];
    that is why the general [close] keeps the guard.)  [send]/[recv] on the same allocated channel likewise
    never hit the nil case.  (Non-nil is
    the NIL-panic guarantee ONLY; it is not tag-correctness.  The wrong-tag write/read hazards are closed by the
    checkpoint-58 op rebase onto the tag-aware [chan_cell_ok] — [chan_write]/[chan_room]/[send]/[recv]/[close]
    all guard on it; the allocation discharges that guard via [chan_cell_ok_make_chan].) *)
Lemma make_chan_nonzero : forall {A} (tag : GoTypeTag A) (w : World) ch w',
  AllocFrontierOk w -> run_io (make_chan tag) w = ORet ch w' -> Nat.eqb (ch_loc ch) 0 = false.
Proof.
  intros A tag w ch w' HV Hrun. unfold run_io, make_chan in Hrun. cbv zeta in Hrun.
  injection Hrun as Hc _. subst ch. cbn [ch_loc]. apply pos_neq0, (valid_fresh_nonzero w HV).
Qed.
(** A freshly-[make]d channel is OPEN ([chan_closed = false]): [make_chan_cap] installs the cell with its
    closed-flag [false] ([… (false, cap)]).  This is the fact [close] needs to reach its real closed-flag path
    — and it is PROVABLE from the allocation, NOT a caller premise: this lemma discharges it internally so the
    no-panic corollary below is a TRUE peer of [ptr_alloc_assign_no_panic] (AllocFrontierOk + alloc result ONLY,
    no leaked [chan_closed] side condition). *)
Lemma make_chan_open : forall {A} (tag : GoTypeTag A) (w : World) ch w',
  AllocFrontierOk w -> run_io (make_chan tag) w = ORet ch w' -> chan_closed ch w' = false.
Proof.
  intros A tag w ch w' HV Hrun.
  assert (Hnz : Nat.eqb (w_next w) 0 = false) by (apply pos_neq0, (valid_fresh_nonzero w HV)).
  unfold run_io, make_chan, make_chan_cap in Hrun. cbv zeta in Hrun.
  injection Hrun as Hc Hw. subst ch w'.
  unfold chan_closed. cbn. rewrite Hnz, Nat.eqb_refl. reflexivity.
Qed.
(** A freshly-[make]d channel's cell is TAG-CORRECT ([chan_cell_ok = true], via [chan_cell_ok_make_chan]) AND
    OPEN ([make_chan_open]).  So [close] on a just-made channel reaches its real closed-flag path (not mistaken
    for an unallocated / forged handle, and not blocked by a stale closed flag) — the allocation discharges
    BOTH premises the guarded [close]/[run_close] demand.  No caller side condition: this is the genuine
    channel peer of [ptr_alloc_assign_no_panic] / [map_alloc_set_no_panic]. *)
Corollary chan_alloc_close_no_panic : forall {A} (tag : GoTypeTag A) (w : World) ch w',
  AllocFrontierOk w -> run_io (make_chan tag) w = ORet ch w' ->
  exists w'', run_io (close_chan tag ch) w' = ORet tt w''.
Proof.
  intros A tag w ch w' HV Hrun. eexists.
  apply run_close; [ apply (chan_cell_ok_make_chan tag w ch w' HV Hrun)
                   | exact (make_chan_open tag w ch w' HV Hrun) ].
Qed.
(** CAPACITY FAITHFULNESS: a freshly-made buffered channel stores the requested capacity [Some n].  The
    [w_next <> 0] the read-back needs (now that [chan_cap] reads a nil handle as [None]) is FORCED by
    [AllocFrontierOk] — the allocator never mints the reserved sentinel — not left as a free side condition. *)
Lemma make_chan_buf_caps : forall {A} (tag : GoTypeTag A) (n : GoInt) (w : World) ch w',
  AllocFrontierOk w -> run_io (make_chan_buf tag n) w = ORet ch w' -> chan_cap ch w' = Some (Z.to_nat (intraw n)).
Proof.
  intros A tag n w ch w' HV H.
  assert (Hnz : Nat.eqb (w_next w) 0 = false) by (apply pos_neq0, (valid_fresh_nonzero w HV)).
  unfold make_chan_buf, make_chan_cap, run_io in H.
  (* a NEGATIVE size would have PANICKED, contradicting the [ORet] result — so only the exact
     non-negative allocation reaches here; no silent [Z.to_nat] clamp is blessed. *)
  revert H. destruct ((intraw n <? 0)%Z); intro H.
  - discriminate H.
  - injection H as Hch Hw. subst ch w'. unfold chan_cap. cbn. rewrite Hnz, Nat.eqb_refl. reflexivity.
Qed.
(** The fresh [make(chan T, n)] handle reads an EMPTY buffer — the constructor establishes the
    [ChanCapOk] invariant with the strongest slack ([length 0 <= cap]).  Mirror of [make_chan_buf_caps]
    (reading [chan_buf] instead of [chan_cap]); the [w_next <> 0] the read-back needs is forced by [AllocFrontierOk]. *)
Lemma make_chan_buf_empty : forall {A} (tag : GoTypeTag A) (n : GoInt) (w : World) ch w',
  AllocFrontierOk w -> run_io (make_chan_buf tag n) w = ORet ch w' -> chan_buf tag ch w' = nil.
Proof.
  intros A tag n w ch w' HV H.
  assert (Hnz : Nat.eqb (w_next w) 0 = false) by (apply pos_neq0, (valid_fresh_nonzero w HV)).
  unfold make_chan_buf, make_chan_cap, run_io in H.
  revert H. destruct ((intraw n <? 0)%Z); intro H.
  - discriminate H.
  - injection H as Hch Hw. subst ch w'. unfold chan_buf. cbn. rewrite Hnz, Nat.eqb_refl, tag_eq_refl. reflexivity.
Qed.
(** ChanStateOk ESTABLISHMENT at construction: a fresh [make(chan T, n)] channel satisfies [ChanCapOk]
    ([length 0 <= Z.to_nat n]).  Pairs [make_chan_buf_caps] (finite cap) with [make_chan_buf_empty] (empty buffer). *)
Lemma make_chan_buf_establishes_chancapok : forall {A} (tag : GoTypeTag A) (n : GoInt) (w : World) ch w',
  AllocFrontierOk w -> run_io (make_chan_buf tag n) w = ORet ch w' -> ChanCapOk tag ch w'.
Proof.
  intros A tag n w ch w' HV H. unfold ChanCapOk.
  rewrite (make_chan_buf_caps tag n w ch w' HV H), (make_chan_buf_empty tag n w ch w' HV H).
  cbn. apply Nat.le_0_l.
Qed.
(** The UNBUFFERED constructor [make(chan T)] (cap [Some 0]) equally establishes [ChanCapOk] ([length 0 <= 0]).
    [make_chan_caps]/[make_chan_empty] mirror the buffered witnesses for the [Some 0] allocator. *)
Lemma make_chan_caps : forall {A} (tag : GoTypeTag A) (w : World) ch w',
  AllocFrontierOk w -> run_io (make_chan tag) w = ORet ch w' -> chan_cap ch w' = Some 0%nat.
Proof.
  intros A tag w ch w' HV H.
  assert (Hnz : Nat.eqb (w_next w) 0 = false) by (apply pos_neq0, (valid_fresh_nonzero w HV)).
  unfold make_chan, make_chan_cap, run_io in H. injection H as Hch Hw. subst ch w'.
  unfold chan_cap. cbn. rewrite Hnz, Nat.eqb_refl. reflexivity.
Qed.
Lemma make_chan_empty : forall {A} (tag : GoTypeTag A) (w : World) ch w',
  AllocFrontierOk w -> run_io (make_chan tag) w = ORet ch w' -> chan_buf tag ch w' = nil.
Proof.
  intros A tag w ch w' HV H.
  assert (Hnz : Nat.eqb (w_next w) 0 = false) by (apply pos_neq0, (valid_fresh_nonzero w HV)).
  unfold make_chan, make_chan_cap, run_io in H. injection H as Hch Hw. subst ch w'.
  unfold chan_buf. cbn. rewrite Hnz, Nat.eqb_refl, tag_eq_refl. reflexivity.
Qed.
Lemma make_chan_establishes_chancapok : forall {A} (tag : GoTypeTag A) (w : World) ch w',
  AllocFrontierOk w -> run_io (make_chan tag) w = ORet ch w' -> ChanCapOk tag ch w'.
Proof.
  intros A tag w ch w' HV H. unfold ChanCapOk.
  rewrite (make_chan_caps tag w ch w' HV H), (make_chan_empty tag w ch w' HV H).
  cbn. apply Nat.le_0_l.
Qed.
(** CHANNEL STATE-OK SURFACE (manifest-gated, zero-axiom): the "no over-full channel" invariant [ChanCapOk]
    (checkpoint-61 #9) — a bounded channel's FIFO length is [<= cap], the analogue of SliceWF for slices.
    Gated across every PRIMITIVE state transition: ESTABLISHED at construction by BOTH allocators
    ([make_chan] unbuffered + [make_chan_buf]), by every [send] (the sole buffer-GROWING op — its [chan_room]
    gate forces [length < cap] before the append), and PRESERVED by the primitive [recv] (dequeue) and [close]
    (flag-only).  ⚠ SCOPE: the comma-ok / select RECEIVE COMBINATORS ([recv_ok]/[select_recv2]/
    [select_recv_default]) are NOT separately gated — they are dequeue-then-CONTINUE forms whose channel effect
    is exactly the same [chan_recv_upd] dequeue already covered by [recv_preserves_chancapok] (it only SHORTENS
    the FIFO), followed by a caller continuation whose final world is out of scope; they add NO buffer-growing
    transition, so they cannot break the invariant.  ⚠ SHAPE (buffer-length) only — a forged same-tag over-full
    handle stays the checkpoint-59 typed-liveness frontier, and [None]-cap (proof-only unbounded bridge) is
    vacuous, the residual finite-vs-unbounded excision of #9. *)
Definition chan_state_ok_surface :=
  (@make_chan_establishes_chancapok, @make_chan_buf_establishes_chancapok, @send_establishes_chancapok,
   @recv_preserves_chancapok, @close_preserves_chancapok).
Print Assumptions chan_state_ok_surface.

(** Both constructors ESTABLISH [ChanFinite] (a bounded [Some] capacity): [make_chan] → [Some 0],
    [make_chan_buf] → [Some (Z.to_nat n)] (from [make_chan_caps]/[make_chan_buf_caps]). *)
Lemma make_chan_establishes_chanfinite : forall {A} (tag : GoTypeTag A) (w : World) ch w',
  AllocFrontierOk w -> run_io (make_chan tag) w = ORet ch w' -> ChanFinite ch w'.
Proof. intros A tag w ch w' HV H. exists 0%nat. exact (make_chan_caps tag w ch w' HV H). Qed.
Lemma make_chan_buf_establishes_chanfinite : forall {A} (tag : GoTypeTag A) (n : GoInt) (w : World) ch w',
  AllocFrontierOk w -> run_io (make_chan_buf tag n) w = ORet ch w' -> ChanFinite ch w'.
Proof. intros A tag n w ch w' HV H. exists (Z.to_nat (intraw n)). exact (make_chan_buf_caps tag n w ch w' HV H). Qed.
(** CHANNEL FINITE SURFACE (manifest-gated, zero-axiom): every CERTIFIED channel is BOUNDED ([Some] cap) — the
    finite-vs-unbounded half of checkpoint-61 #9.  ESTABLISHED by BOTH constructors and PRESERVED by [send] /
    [recv] / [close] (capacity is re-written unchanged by every primitive op).  So the certified channel path
    NEVER yields an unbounded ([None]-cap) channel — the [None] case survives ONLY for nil handles and the
    proof-only concurrency-bridge abstract channels (its residual structural excision).  The comma-ok / select
    receive combinators are dequeue-then-continue forms reusing the cap-invariant [chan_recv_upd], so they too
    cannot un-bound a channel; not separately gated.  Combined with [chan_state_ok_surface], a certified
    channel's FIFO is bounded by a CONCRETE [n]. *)
Definition chan_finite_surface :=
  (@make_chan_establishes_chanfinite, @make_chan_buf_establishes_chanfinite,
   @send_preserves_chanfinite, @recv_preserves_chanfinite, @close_preserves_chanfinite).
Print Assumptions chan_finite_surface.

(** CLOSED-WORLD ALLOCATION-SAFETY SURFACE (manifest-gated, zero-axiom PUBLIC evidence): the allocator
    liveness + panic-free-deref cone for the four SCALAR / single-cell handle families (ptr / ref / map /
    chan), so the [SPEC_CONFORMANCE] "address-of `&x` end-to-end" claim (and the ptr/map/chan analogues it
    leans on) is GATED public evidence, not an ungated internal theorem.  Each family: allocator-mints-nonzero
    (under [AllocFrontierOk]) + allocator-installs-a-live cell + the end-to-end no-panic corollary chaining BOTH
    premises.  The [Print Assumptions] certifies the whole cone axiom-free.  (The AGGREGATE / multi-cell
    handles — [SliceH], [GSPtr] — have their own allocator-liveness in [heap_aggregate_liveness_surface]
    below, next to their later definitions.  The wrong-tag ANTI-forgery half is the separate
    [ref_wrong_tag_antiforgery_surface] / [GoChan.chan_wrong_tag_antiforgery_surface] / [GoMap.map_wrong_tag_antiforgery_surface]; this is the
    positive LIVENESS half.) *)
Definition heap_alloc_safety_surface :=
  (@ptr_new_nonzero, @ptr_new_reads, @ptr_alloc_assign_no_panic,
   @ref_new_loc_nonzero, @ref_new_reads, @ref_new_addr_nonnil,
   @ref_alloc_addr_read_no_panic, @ref_alloc_addr_write_no_panic,
   @map_make_typed_nonzero, @map_alloc_set_no_panic,
   @make_chan_nonzero, @make_chan_open, @chan_alloc_close_no_panic, @make_chan_buf_caps).
Print Assumptions heap_alloc_safety_surface.

(** ---- Live* : the REUSABLE typed-liveness predicate family (checkpoint-59 step 3) ----

    One canonical name per handle for "the cell(s) EXIST at this handle's nonnil location(s) AND store the
    matching tag".  The four SCALAR predicates are here ([LiveRef]/[LivePtr]/[LiveChan]/[LiveMap]); the two
    AGGREGATE peers ([LiveSlice] = well-formed shape [len <= cap] with the whole [0, cap) backing live,
    [LiveStruct] = non-nil pointer with every field live) are defined later next to their multi-cell reps
    ([slice_range_live] / [fields_live]), gated in
    [live_aggregate_handle_surface] — together the SIX cover every handle.  Each unfolds to the per-family cell
    authority ([ref_sel_opt] / [chan_cell_ok] / [map_cell_ok] / [slice_range_live] / [fields_live]).  [LivePtr]
    and [LiveStruct] each pair the cell/field authority with a nonzero-base guard, because their ops are POINTER
    derefs that fault on nil FIRST ([ptr_get]/[ptr_set] and [gsptr_deref]/[gsptr_assign] alike — Go's [*p] panics
    on nil for EVERY pointee, incl. a zero-field struct, so the guard is load-bearing and WIRED, not decorative:
    it is exactly what keeps a nil handle from reading "live", and an empty struct's only failure mode IS the nil
    pointer).  [LiveSlice] does NOT pair on a base guard (a nil slice is a valid empty Go value that never
    faults), but it DOES carry the shape invariant [len <= cap] — without it a [len > cap] header would report an
    index in-bounds with no backing (see [LiveSlice_index_live]).  [Live*] is a NAMED
    INTERFACE over that authority, NOT a second authority; the
    ops' DEFINITIONS branch on the underlying check directly ([Live*] mirrors it, the ops do not reference the
    name).  ⚠ CELL liveness ONLY: the channel ops ([send]/[recv]/[close]) additionally demand room / not-closed
    / non-empty conditions BEYOND [LiveChan] (those are NOT liveness), so [LiveChan] is not the full send/recv
    precondition.  ⚠ TYPED LIVENESS, not origin provenance — a SAME-TAG forged handle satisfies [Live*] too (the
    open origin frontier); the wrong-tag/absent negatives are the [*_wrong_tag_antiforgery] surfaces.  What is
    PROVED about [Live*] is exactly the gated surfaces below: allocators produce it ([live_handle_surface]), the
    raw update roots preserve it ([live_preserve_surface]), the always-succeed-on-live checked writes return with
    it preserved ([live_op_preserve_surface]), and the case-split channel ops keep it through every branch
    ([live_chan_op_preserve_surface]). *)
Definition LiveRef {A} (r : Ref A) (w : World) : Prop := ref_sel_opt r w <> None.
(** [LivePtr] is DEFINED to mirror the POINTER safe-op gate: the ops ([ptr_get_ok]/[ptr_set]) inline-guard
    [Nat.eqb (p_loc p) 0] FIRST (nil deref panics) and THEN the live cell — so both conjuncts belong in
    [LivePtr] (a [Ref] has no such explicit loc-0 guard, hence [LiveRef] is the cell alone).  [LivePtr_ptr_set_op]
    proves the link — [ptr_set] on a [LivePtr] returns and preserves it — while [ptr_set]'s definition branches
    on the inline guard that [LivePtr] mirrors. *)
Definition LivePtr {A} (tag : GoTypeTag A) (p : Ptr A) (w : World) : Prop :=
  Nat.eqb (p_loc p) 0 = false /\ ref_sel_opt (ptr_as_ref tag p) w <> None.
Definition LiveChan {A} (tag : GoTypeTag A) (ch : GoChan A) (w : World) : Prop := chan_cell_ok tag ch w = true.
Definition LiveMap {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (m : GoMap K V) (w : World) : Prop :=
  map_cell_ok kt vt m w = true.

(** ALLOCATORS PRODUCE Live* — the fresh handle a real program obtains is always live (the ABSENT / wrong-tag
    loud branches of the ops are dead for it; a live CHANNEL still has its INDEPENDENT closed / full branches —
    liveness is only the cell).  Only [ref_new] is unconditional (its [LiveRef] is the cell alone).
    [ptr_new] / [make_chan] / [make_chan_buf] / [map_make_typed] need [AllocFrontierOk] for their nonzero-location
    half — [ptr_new_live] because [LivePtr] carries the non-nil check ([ptr_new_nonzero]); the chan/map
    allocators because [chan_cell_ok]/[map_cell_ok] include the nonzero location. *)
Lemma ref_new_live : forall {A} (tag : GoTypeTag A) (v : A) (w : World) r w',
  run_io (ref_new tag v) w = ORet r w' -> LiveRef r w'.
Proof. intros A tag v w r w' Hrun. unfold LiveRef. rewrite (ref_new_reads tag v w r w' Hrun). discriminate. Qed.
Lemma ptr_new_live : forall {A} (tag : GoTypeTag A) (v : A) (w : World) p w',
  AllocFrontierOk w -> run_io (ptr_new tag v) w = ORet p w' -> LivePtr tag p w'.
Proof.
  intros A tag v w p w' HV Hrun. unfold LivePtr. split.
  - exact (ptr_new_nonzero tag v w p w' HV Hrun).
  - rewrite (ptr_new_reads tag v w p w' Hrun). discriminate.
Qed.
Lemma make_chan_live : forall {A} (tag : GoTypeTag A) (w : World) ch w',
  AllocFrontierOk w -> run_io (make_chan tag) w = ORet ch w' -> LiveChan tag ch w'.
Proof. intros A tag w ch w' HV Hrun. unfold LiveChan. exact (chan_cell_ok_make_chan tag w ch w' HV Hrun). Qed.
Lemma make_chan_buf_live : forall {A} (tag : GoTypeTag A) (n : GoInt) (w : World) ch w',
  AllocFrontierOk w -> run_io (make_chan_buf tag n) w = ORet ch w' -> LiveChan tag ch w'.
Proof. intros A tag n w ch w' HV Hrun. unfold LiveChan. exact (chan_cell_ok_make_chan_buf tag n w ch w' HV Hrun). Qed.
Lemma map_make_typed_live : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (w : World) m w',
  AllocFrontierOk w -> run_io (map_make_typed kt vt) w = ORet m w' -> LiveMap kt vt m w'.
Proof. intros K V kt vt w m w' HV Hrun. unfold LiveMap. exact (map_cell_ok_make_typed kt vt w m w' HV Hrun). Qed.

(** Live* ALLOCATOR SURFACE (manifest-gated, zero-axiom): the unified "allocators produce Live*" evidence
    across ref / ptr / chan (UNbuffered AND buffered) / map.  (Preservation is the two surfaces further down.) *)
Definition live_handle_surface :=
  (@ref_new_live, @ptr_new_live, @make_chan_live, @make_chan_buf_live, @map_make_typed_live).
Print Assumptions live_handle_surface.

(** RAW-UPDATE-ROOT PRESERVATION of Live* — the state transformers a checked write calls on its SUCCESS branch
    ([ref_upd], [chan_send_upd]/[chan_recv_upd]/[chan_close_upd], [map_upd]/[map_rem]/[map_clear_upd]) re-install
    the cell with the SAME tag, so a LIVE handle stays Live across the UPDATE.  ⚠ These are UPDATE-ROOT facts,
    NOT full checked-op claims: a checked op — [send]/[recv]/[close] especially — need NOT reach its update root
    (send-on-closed / empty-recv / double-close FAIL LOUD, a full send blocks); those branches leave the world
    UNCHANGED so Live* is trivially preserved there too, but that op-level statement is a SEPARATE fact — the
    always-succeed writes in [live_op_preserve_surface] and the case-split channel ops in
    [live_chan_op_preserve_surface] below — not what these (update-root) lemmas assert.  One update-root
    preservation fact per family. *)
Lemma LiveRef_preserved : forall {A} (r : Ref A) (v : A) (w : World),
  LiveRef r w -> LiveRef r (ref_upd r v w).
Proof.
  intros A r v w H. unfold LiveRef in *.
  destruct (ref_sel_opt r w) as [a|] eqn:Hs; [ | congruence ].
  rewrite (ref_sel_opt_upd_same r v a w Hs). discriminate.
Qed.
Lemma LivePtr_preserved : forall {A} (tag : GoTypeTag A) (p : Ptr A) (v : A) (w : World),
  LivePtr tag p w -> LivePtr tag p (ref_upd (ptr_as_ref tag p) v w).
Proof.
  intros A tag p v w [Hnil Hcell]. unfold LivePtr. split; [ exact Hnil | ].
  destruct (ref_sel_opt (ptr_as_ref tag p) w) as [a|] eqn:Hs; [ | congruence ].
  rewrite (ref_sel_opt_upd_same (ptr_as_ref tag p) v a w Hs). discriminate.
Qed.
Lemma LiveChan_send_preserved : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (v : A) (w : World),
  LiveChan tag ch w -> LiveChan tag ch (chan_send_upd tag ch v w).
Proof. intros A tag ch v w H. unfold LiveChan in *. exact (chan_cell_ok_send tag ch v w H). Qed.
Lemma LiveChan_recv_preserved : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (w : World),
  LiveChan tag ch w -> LiveChan tag ch (chan_recv_upd tag ch w).
Proof. intros A tag ch w H. unfold LiveChan in *. exact (chan_cell_ok_recv tag ch w H). Qed.
Lemma LiveChan_close_preserved : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (w : World),
  LiveChan tag ch w -> LiveChan tag ch (chan_close_upd tag ch w).
Proof. intros A tag ch w H. unfold LiveChan in *. exact (chan_cell_ok_close tag ch w H). Qed.
Lemma LiveMap_set_preserved : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (v : V) (m : GoMap K V) (w : World),
  LiveMap kt vt m w -> LiveMap kt vt m (map_upd kt vt k v m w).
Proof. intros K V kt vt k v m w H. unfold LiveMap in *. unfold map_upd. apply map_cell_ok_write_same; exact H. Qed.
Lemma LiveMap_delete_preserved : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (m : GoMap K V) (w : World),
  LiveMap kt vt m w -> LiveMap kt vt m (map_rem kt vt k m w).
Proof. intros K V kt vt k m w H. unfold LiveMap in *. unfold map_rem. apply map_cell_ok_write_same; exact H. Qed.
Lemma LiveMap_clear_preserved : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (m : GoMap K V) (w : World),
  LiveMap kt vt m w -> LiveMap kt vt m (map_clear_upd kt vt m w).
Proof. intros K V kt vt m w H. unfold LiveMap in *. unfold map_clear_upd. apply map_cell_ok_write_same; exact H. Qed.

(** Live* UPDATE-ROOT PRESERVATION SURFACE (manifest-gated, zero-axiom): each family's RAW UPDATE root keeps a
    live handle Live — ref/ptr [ref_upd], chan send/recv/close [chan_*_upd], map set/delete/clear [map_*].
    (Update-root facts, not full checked-op behavior — see the block comment above.) *)
Definition live_preserve_surface :=
  (@LiveRef_preserved, @LivePtr_preserved, @LiveChan_send_preserved, @LiveChan_recv_preserved,
   @LiveChan_close_preserved, @LiveMap_set_preserved, @LiveMap_delete_preserved, @LiveMap_clear_preserved).
Print Assumptions live_preserve_surface.

(** OP-LEVEL PRESERVATION — the CHECKED op (not just its update root) preserves Live*.  Two forms, by whether
    the op can fail loud on a LIVE handle:
    (1) ALWAYS-SUCCEED writes ([ref_set]/[ptr_set]/[map_set]/[map_delete]/[map_clear] — no panic/block branch
        is reachable when the handle is Live): the op RETURNS ([ORet]) and the handle stays Live, stated
        [exists w', run_io op w = ORet tt w' /\ Live* ... w'] (the world after the op IS Live).
    (2) CASE-SPLIT ops (the channels): [send]/[recv]/[close] keep panic/block branches even on a live channel
        (send-on-closed, empty recv, full send), so the op MAY fail loud — but the channel stays Live either
        way (success → root Live; fail-loud/block → world unchanged, still Live).  Stated over the world AFTER
        the outcome regardless of constructor: [LiveChan tag ch (outcome_world (run_io op w))].  This is
        WEAKER than form (1) (it does not assert [ORet] — the op may legitimately block), and honestly so:
        blocking is real Go behaviour, not a failure. *)
Lemma LiveRef_ref_set_op : forall {A} (r : Ref A) (v : A) (w : World),
  LiveRef r w -> exists w', run_io (ref_set r v) w = ORet tt w' /\ LiveRef r w'.
Proof.
  intros A r v w H.
  destruct (ref_sel_opt r w) as [a|] eqn:Hs; [ | unfold LiveRef in H; congruence ].
  exists (ref_upd r v w). split; [ exact (run_ref_set_some r v a w Hs) | exact (LiveRef_preserved r v w H) ].
Qed.
Lemma LivePtr_ptr_set_op : forall {A} (tag : GoTypeTag A) (p : Ptr A) (v : A) (w : World),
  LivePtr tag p w -> exists w', run_io (ptr_set tag p v) w = ORet tt w' /\ LivePtr tag p w'.
Proof.
  intros A tag p v w H. destruct H as [Hnil Hcell].
  exists (ref_upd (ptr_as_ref tag p) v w). split.
  - rewrite run_ptr_set, Hnil.
    destruct (ref_sel_opt (ptr_as_ref tag p) w) as [a|] eqn:Hs; [ reflexivity | congruence ].
  - exact (LivePtr_preserved tag p v w (conj Hnil Hcell)).
Qed.
Lemma LiveMap_set_op : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (v : V) (m : GoMap K V) (w : World),
  LiveMap kt vt m w -> exists w', run_io (map_set kt vt k v m) w = ORet tt w' /\ LiveMap kt vt m w'.
Proof.
  intros K V kt vt k v m w H. exists (map_upd kt vt k v m w). split.
  - rewrite run_map_set. unfold LiveMap in H. rewrite H. reflexivity.
  - exact (LiveMap_set_preserved kt vt k v m w H).
Qed.
Lemma LiveMap_delete_op : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (m : GoMap K V) (w : World),
  LiveMap kt vt m w -> exists w', run_io (map_delete kt vt k m) w = ORet tt w' /\ LiveMap kt vt m w'.
Proof.
  intros K V kt vt k m w H. exists (map_rem kt vt k m w). split.
  - rewrite run_map_delete. unfold LiveMap in H. rewrite H. reflexivity.
  - exact (LiveMap_delete_preserved kt vt k m w H).
Qed.
Lemma LiveMap_clear_op : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (m : GoMap K V) (w : World),
  LiveMap kt vt m w -> exists w', run_io (map_clear kt vt m) w = ORet tt w' /\ LiveMap kt vt m w'.
Proof.
  intros K V kt vt m w H. exists (map_clear_upd kt vt m w). split.
  - rewrite run_map_clear. unfold LiveMap in H. rewrite H. reflexivity.
  - exact (LiveMap_clear_preserved kt vt m w H).
Qed.

(** Form (2): the CHANNEL ops keep a live channel Live through EVERY branch — the successful update root
    ([chan_*_upd], via the [LiveChan_*_preserved] roots above) and the fail-loud/block branches (world = w,
    so [LiveChan tag ch w] is the premise).  Stated over [outcome_world] so the one claim covers ORet and
    OPanic alike; the case analysis is on each op's own branch structure. *)
Lemma LiveChan_send_op : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (v : A) (w : World),
  LiveChan tag ch w -> LiveChan tag ch (outcome_world (run_io (send tag ch v) w)).
Proof.
  intros A tag ch v w H. unfold run_io, send.
  destruct (chan_cell_ok tag ch w) eqn:Hok; [ | unfold LiveChan in H; congruence ].
  destruct (chan_closed ch w).
  - exact H.
  - destruct (chan_room tag ch w).
    + exact (LiveChan_send_preserved tag ch v w H).
    + exact H.
Qed.
Lemma LiveChan_recv_op : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (w : World),
  LiveChan tag ch w -> LiveChan tag ch (outcome_world (run_io (recv tag ch) w)).
Proof.
  intros A tag ch w H. unfold run_io, recv.
  destruct (chan_buf tag ch w) as [| v rest].
  - destruct (andb (chan_closed ch w) (chan_cell_ok tag ch w)); exact H.
  - exact (LiveChan_recv_preserved tag ch w H).
Qed.
Lemma LiveChan_close_op : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (w : World),
  LiveChan tag ch w -> LiveChan tag ch (outcome_world (run_io (close_chan tag ch) w)).
Proof.
  intros A tag ch w H. unfold run_io, close_chan.
  destruct (chan_cell_ok tag ch w) eqn:Hok; [ | unfold LiveChan in H; congruence ].
  destruct (chan_closed ch w).
  - exact H.
  - exact (LiveChan_close_preserved tag ch w H).
Qed.

(** Live* OP-LEVEL PRESERVATION SURFACE (manifest-gated, zero-axiom): the ALWAYS-SUCCEEDS-on-live checked
    writes (ref/ptr set, map set/delete/clear) return ([ORet]) and keep the handle Live — form (1) above.
    The channels are form (2), the case-split surface [live_chan_op_preserve_surface] just below. *)
Definition live_op_preserve_surface :=
  (@LiveRef_ref_set_op, @LivePtr_ptr_set_op, @LiveMap_set_op, @LiveMap_delete_op, @LiveMap_clear_op).
Print Assumptions live_op_preserve_surface.

(** Live* CHANNEL OP-LEVEL PRESERVATION SURFACE (manifest-gated, zero-axiom): [send]/[recv]/[close] keep a
    live channel Live over the world after the outcome ([outcome_world]) — form (2), covering the block/panic
    branches, NOT asserting [ORet] (blocking is intended-faithful only in the RELATIONAL authority; the
    shallow-IO would-block branch is CURRENTLY an inaccurate [OPanic] stand-in — checkpoint-61, fix tracked in
    plans/result-control-split.md). *)
Definition live_chan_op_preserve_surface :=
  (@LiveChan_send_op, @LiveChan_recv_op, @LiveChan_close_op).
Print Assumptions live_chan_op_preserve_surface.

(** ADDRESS-OF / ASSIGNMENT SEMANTICS SURFACE (manifest-gated, zero-axiom PUBLIC evidence): the read-after-
    write / non-nil / deref / aliasing theorems the [SPEC_CONFORMANCE] "Variables / assignment" + address-of
    `&x` ledger cites, so those public claims are GATED, not ungated internal lemmas.  [ref_sel_upd_same] /
    [ref_get_set_same]: a local reads back its last write.  [ref_as_ptr_not_nil]: [&x] of a nonzero-location
    local is non-nil (NON-NIL ONLY — the panic-free-deref cone is the companion [heap_alloc_safety_surface]).
    [ptr_get_ref_as_ptr] / [ptr_set_ref_as_ptr]: read/write THROUGH [&x] hit x's own cell (both premised on
    the live cell).  [ptr_set_ref_as_ptr_aliases]: a write through [&x] is visible at [x] — the defining
    pointer property. *)
Definition ref_addr_of_surface :=
  (@ref_sel_upd_same, @ref_get_set_same, @ref_as_ptr_not_nil,
   @ptr_get_ref_as_ptr, @ptr_set_ref_as_ptr, @ptr_set_ref_as_ptr_aliases).
Print Assumptions ref_addr_of_surface.

(** ALIASING — the defining pointer property, a THEOREM: two pointers at the SAME
    location ([p] and a copy [q]) see each other's writes.  A write through [q] is
    observed by a read through [p] — impossible for a non-aliasing [Ref] var.  The
    write target [q]'s cell must be LIVE ([ref_sel_opt = Some]) — the guarded [ref_upd]
    only writes through a live cell (a real program's pointer aliases an allocated cell). *)
Lemma ptr_alias : forall {A} (tag : GoTypeTag A) (p q : Ptr A) (v a : A) (w : World),
  p_loc p = p_loc q ->
  ref_sel_opt (ptr_as_ref tag q) w = Some a ->
  ref_sel (ptr_as_ref tag p) (ref_upd (ptr_as_ref tag q) v w) = v.
Proof.
  intros A tag p q v a w Hl Hlive.
  unfold ptr_as_ref in *. rewrite Hl.
  exact (ref_sel_upd_same (mkRef (p_loc q) tag) v a w Hlive).
Qed.

(** ---- nil-deref SAFETY ----

    Dereferencing a nil pointer PANICS in Go.  The raw [ptr_get]/[ptr_set] are the
    escape hatch; [ptr_get_ok] is the safe-by-construction default — a comma-ok CPS
    form (like [slice_at_ok]/[recv_ok]) that BRANCHES on [p ≠ nil]: non-nil-AND-allocated ⇒
    [v = *p, ok = true]; nil ⇒ [v = zero, ok = false].  Because the caller must handle
    [ok = false], the nil-deref panic is UNREACHABLE.  (A [Ptr] is nil iff its location
    is the 0 sentinel — [ptr_nil].  The value is in the world heap, so [ptr_get_ok]
    threads [w]; a read leaves [w] unchanged.)  The non-nil branch reads via the
    CHECKED [ref_sel_opt], so a FORGED / retyped non-nil handle (cell absent or wrong-tagged) FAILS
    LOUD rather than fabricating a zero with [ok = true] — the same hole [ref_get] closed, here in the
    safe comma-ok default.  That loud branch is unreachable for any [Ptr] from [ptr_new]/[ref_as_ptr]
    (their cells are allocated at the matching tag); it guards only the public raw [mkPtr]. *)
Definition ptr_is_nil {A} (p : Ptr A) : bool := Nat.eqb (p_loc p) 0.

Definition ptr_get_ok {A B} (tag : GoTypeTag A) (p : Ptr A) (k : A -> bool -> IO B) : IO B :=
  fun w => if ptr_is_nil p
           then k (zero_val tag) false w
           else match ref_sel_opt (ptr_as_ref tag p) w with
                | Some a => k a true w
                | None   => OPanic rt_nil_deref w   (* forged / retyped non-nil handle: FAIL LOUD, never fabricate *)
                end.

(** Dereferencing a NIL pointer takes the SAFE branch ([ok = false], [v = zero]) —
    never the panic; the nil case is forced on the caller.  A THEOREM. *)
Lemma ptr_get_ok_nil : forall {A B} (tag : GoTypeTag A) (k : A -> bool -> IO B),
  ptr_get_ok tag (ptr_nil tag) k = k (zero_val tag) false.
Proof.
  intros A B tag k. unfold ptr_get_ok, ptr_is_nil, ptr_nil. reflexivity.
Qed.

(** A pointer from [ptr_new] is NON-nil (UNDER [AllocFrontierOk] — [ptr_new_nonzero]; on a malformed world it
    would be nil) AND its cell is allocated at [p]'s own tag ([ptr_new_reads], unconditional), so [ref_sel_opt]
    hits [Some] and [ptr_get_ok] reads through it ([ok = true]) returning the stored value: safe deref of a
    live pointer — the "safe" resting on both the [AllocFrontierOk] non-nil premise and the live cell, NOT on
    [ptr_get_ok] alone.  (A forged / retyped non-nil handle — [ref_sel_opt = None] — instead FAILS LOUD
    rather than fabricating a zero.  That loud branch is UNREACHABLE for any [Ptr] obtained from
    [ptr_new]/[ref_as_ptr], a boundary defense for the public [mkPtr] only.) *)
Lemma ptr_get_ok_nonnil : forall {A B} (tag : GoTypeTag A) (p : Ptr A)
    (k : A -> bool -> IO B) (a : A) (w : World),
  ptr_is_nil p = false ->
  ref_sel_opt (ptr_as_ref tag p) w = Some a ->
  ptr_get_ok tag p k w = k a true w.
Proof. intros A B tag p k a w Hnn Hsel. unfold ptr_get_ok. rewrite Hnn, Hsel. reflexivity. Qed.

(** ---- Slices as ALIASING HANDLES (Go spec "Slice types") ----

    A Go slice is NOT a value — it is a HANDLE [(backing-array, offset, len, cap)] that
    SHARES its backing array, so sub-slicing and writes ALIAS.  The list-based [GoSlice]
    (a value, no aliasing) stays for the immutable cases; [SliceH] is the faithful
    aliasing model.  Backing arrays REUSE the [w_refs] cell heap: element [i] of a
    [SliceH] is the cell at [base + offset + i].  Sub-slicing shifts [offset] over the
    SAME cells, so [sub-slice[j] = parent[a+j]] is the SAME cell — aliasing is then the
    `ref_sel_upd_same` theorem, no new heap, no new axiom.  Lowers to Go [[]T] (which
    IS this handle) with native [make]/index/sub-slice. *)
Record SliceH (A : Type) : Type := mkSliceH
  { sh_base : nat ; sh_off : nat ; sh_len : nat ; sh_cap : nat ; sh_tag : GoTypeTag A }.
Arguments mkSliceH {A} _ _ _ _ _.
Arguments sh_base {A} _.  Arguments sh_off {A} _.  Arguments sh_len {A} _.
Arguments sh_cap {A} _.   Arguments sh_tag {A} _.

(* Element [i]'s cell = [base + (off + i)] — grouped so the sub-slice alias is one
   [add_assoc].  [sh_cell] is the [Ref] view into the shared heap. *)
Definition sh_loc {A} (s : SliceH A) (i : nat) : nat :=
  sh_base s + (sh_off s + i).
Definition sh_cell {A} (s : SliceH A) (i : nat) : Ref A := mkRef (sh_loc s i) (sh_tag s).

(* [make([]T, n)]: allocate [n] fresh consecutive zeroed cells, return the handle.  The size [n]
   is the Go-facing [GoInt] (the make argument the plugin emits); the model converts it to the
   internal [nat] cell count [nn]. *)
Definition slice_make_h {A} (tag : GoTypeTag A) (n : GoInt) : IO (SliceH A) :=
  fun w => if (0 <=? intraw n)%Z then        (* Go: make([]T, n) with n < 0 PANICS *)
             let base := w_next w in
             let nn := Z.to_nat (intraw n) in
             ORet (mkSliceH base 0 nn nn tag)
                  (mkWorld (fun k => if (Nat.leb base k && Nat.ltb k (base + nn))%bool
                                     then Some (existT _ A (tag, zero_val tag))
                                     else w_refs w k)
                           (w_chans w) (w_maps w) (base + nn) (w_output w))
           else OPanic rt_neg_make w.
(* [s[i]] read / [s[i] = v] write, through the shared backing cell.  Go bounds-checks the
   index against LENGTH (NOT capacity) at runtime and PANICS on [i < 0 || i >= len(s)] — so
   the model panics there too: the [GoInt] index [i] is checked [0 <= i] on
   its [Z] carrier AND [i < len] via [Z.to_nat i <? sh_len s] — so a write to a spare
   backing cell ([len <= i < cap]) panics, never silently succeeds.  The native Go [s[i]]
   performs exactly this check, so the lowering is unchanged (body suppressed). *)
Definition slice_in_len {A} (s : SliceH A) (i : GoInt) : bool :=
  (Z.leb 0 (intraw i) && Nat.ltb (Z.to_nat (intraw i)) (sh_len s))%bool.
(** The in-bounds read goes through the CHECKED [ref_sel_opt], so a FORGED slice header
    ([mkSliceH] at a [base]/[off] whose backing cell is unallocated or wrong-tagged) FAILS LOUD instead
    of fabricating a zero.  The loud branch is UNREACHABLE for any slice from [slice_make_h]/[subslice]/
    [slice_append] (their backing cells are allocated at the matching tag), so real programs are
    unaffected; it guards only the public raw [mkSliceH].  Body is plugin-lowered to [s[i]]. *)
(** ⚠ SliceWF GUARD (checkpoint-61): both index ops FIRST reject a malformed [sh_len > sh_cap] header — a
    model-invalid SliceH (Go maintains [len <= cap]) whose in-[len] index [cap <= i < len] would otherwise reach
    a cell BEYOND the backing (a coincidentally same-tagged cell would be silently indexed).  On a WELL-FORMED
    slice ([sh_len <= sh_cap]) the guard is a no-op, so extraction/golden are unchanged.  The malformed
    fail-loud is a MODEL FAULT (currently [OPanic rt_nil_deref], symmetric with the forged-backing-cell branch;
    both become a distinct [ModelFault], proved unreachable under the store-typing authority — cp61). *)
Definition slice_idx_get {A} (tag : GoTypeTag A) (s : SliceH A) (i : GoInt) : IO A :=
  fun w => if Nat.leb (sh_len s) (sh_cap s)
           then (if slice_in_len s i
                 then match ref_sel_opt (sh_cell s (Z.to_nat (intraw i))) w with
                      | Some a => ORet a w
                      | None   => OPanic rt_nil_deref w
                      end
                 else OPanic (rt_index_oob (intraw i) (sh_len s)) w)
           else OPanic rt_nil_deref w.
Definition slice_idx_set {A} (s : SliceH A) (i : GoInt) (v : A) : IO unit :=
  fun w => if Nat.leb (sh_len s) (sh_cap s)
           then (if slice_in_len s i
                 then match ref_sel_opt (sh_cell s (Z.to_nat (intraw i))) w with
                      | Some _ => ORet tt (ref_upd (sh_cell s (Z.to_nat (intraw i))) v w)
                      | None   => OPanic rt_nil_deref w   (* forged backing cell: FAIL LOUD, symmetric with slice_idx_get *)
                      end
                 else OPanic (rt_index_oob (intraw i) (sh_len s)) w)
           else OPanic rt_nil_deref w.
Lemma run_slice_idx_get : forall {A} (tag : GoTypeTag A) (s : SliceH A) (i : GoInt) (a : A) (w : World),
  Nat.leb (sh_len s) (sh_cap s) = true ->
  slice_in_len s i = true ->
  ref_sel_opt (sh_cell s (Z.to_nat (intraw i))) w = Some a ->
  run_io (slice_idx_get tag s i) w = ORet a w.
Proof. intros A tag s i a w Hwf Hi Hsel. unfold slice_idx_get, run_io. rewrite Hwf, Hi, Hsel. reflexivity. Qed.
Lemma run_slice_idx_set : forall {A} (s : SliceH A) (i : GoInt) (v a : A) (w : World),
  Nat.leb (sh_len s) (sh_cap s) = true ->
  slice_in_len s i = true ->
  ref_sel_opt (sh_cell s (Z.to_nat (intraw i))) w = Some a ->
  run_io (slice_idx_set s i v) w = ORet tt (ref_upd (sh_cell s (Z.to_nat (intraw i))) v w).
Proof. intros A s i v a w Hwf Hi Hsel. unfold slice_idx_set, run_io. rewrite Hwf, Hi, Hsel. reflexivity. Qed.
(** Out of range is a PANIC, exactly Go: writing at index = len ('s len=1,cap=2,
    write index 1 witness) is rejected, not silently aimed at the spare capacity cell.
    ([sh_len <= sh_cap] premise: the SliceWF guard clears first on the well-formed header). *)
Lemma run_slice_idx_set_oob : forall {A} (s : SliceH A) (i : GoInt) (v : A) (w : World),
  Nat.leb (sh_len s) (sh_cap s) = true ->
  slice_in_len s i = false ->
  run_io (slice_idx_set s i v) w = OPanic (rt_index_oob (intraw i) (sh_len s)) w.
Proof. intros A s i v w Hwf Hi. unfold slice_idx_set, run_io. rewrite Hwf, Hi. reflexivity. Qed.
(** SliceWF REJECTION (checkpoint-61): a MALFORMED [sh_cap < sh_len] header FAIL-LOUDS at BOTH index ops —
    BEFORE the [slice_in_len] check, so an in-[len]-but-beyond-[cap] index [cap <= i < len] can NEVER reach a
    coincidentally same-tagged cell past the backing.  Shape follows the [slice_clear/copy_bad_shape_rejected]
    peers: [exists p, run_io … = OPanic p w] — a rejection ([OPanic], never a silent [ORet]) leaving the world
    UNCHANGED, WITHOUT pinning the model-internal payload (the fault is [rt_nil_deref] today, becoming a
    distinct non-catchable [ModelFault] after the store-typing split — never an exported marker).  Gated in
    [heap_aggregate_liveness_surface], pinning the index guard BOTH ways as [slice_bulk_write_surface] does for
    clear/copy. *)
Lemma slice_idx_get_bad_shape_rejected : forall {A} (tag : GoTypeTag A) (s : SliceH A) (i : GoInt) (w : World),
  (sh_cap s < sh_len s)%nat -> exists p, run_io (slice_idx_get tag s i) w = OPanic p w.
Proof.
  intros A tag s i w Hbad. unfold run_io, slice_idx_get.
  assert (Hleb : Nat.leb (sh_len s) (sh_cap s) = false) by (apply Nat.leb_gt; exact Hbad).
  rewrite Hleb. eexists. reflexivity.
Qed.
Lemma slice_idx_set_bad_shape_rejected : forall {A} (s : SliceH A) (i : GoInt) (v : A) (w : World),
  (sh_cap s < sh_len s)%nat -> exists p, run_io (slice_idx_set s i v) w = OPanic p w.
Proof.
  intros A s i v w Hbad. unfold run_io, slice_idx_set.
  assert (Hleb : Nat.leb (sh_len s) (sh_cap s) = false) by (apply Nat.leb_gt; exact Hbad).
  rewrite Hleb. eexists. reflexivity.
Qed.
(* [s[a:b]]: same backing [base], [offset] shifted by [a] — SHARES the cells.  [subslice_desc]
   is the PURE descriptor on internal [nat] indices (the aliasing lemmas reason about it);
   [subslice] is the Go-level op taking the [GoInt] bounds and converting at the boundary. *)
Definition subslice_desc {A} (s : SliceH A) (a b : nat) : SliceH A :=
  mkSliceH (sh_base s) (sh_off s + a)
           (b - a) (sh_cap s - a) (sh_tag s).
(* Go's [s[a:b]] bounds-checks [0 <= a <= b <= cap(s)] at runtime and PANICS otherwise
   — note the upper bound is CAPACITY for a 2-index slice.
   So [subslice] is an IO action that panics on a bad triple instead of silently producing a
   wrapped descriptor whose bogus [sh_len] would defeat the index bounds check.  The native Go
   [s[a:b]] performs the SAME check, so the lowering (a `:=` binding) is faithful.
   ⚠ SliceWF GUARD (checkpoint-61): a malformed [sh_cap < sh_len] PARENT FAILS LOUD FIRST — it is NEVER
   normalized into a well-formed child.  Without this, [subslice]'s bounds check ([b <= cap]) alone would
   LAUNDER a forged [cap < len] header into a clean [len = b-a <= cap-a] descriptor, hiding the forgery; the
   guard rejects it exactly as the index ops and [slice_append]'s [len > cap] branch do (a model fault,
   [OPanic rt_nil_deref] today, a distinct [ModelFault] after the result/control split).  On a well-formed
   parent the guard is a no-op — extraction/golden unchanged (name-lowered op). *)
Definition subslice_inb {A} (s : SliceH A) (a b : GoInt) : bool :=
  (Z.leb 0 (intraw a) && Z.leb (intraw a) (intraw b) && Z.leb (intraw b) (Z.of_nat (sh_cap s)))%bool.
Definition subslice {A} (s : SliceH A) (a b : GoInt) : IO (SliceH A) :=
  fun w => if Nat.leb (sh_len s) (sh_cap s)
           then (if subslice_inb s a b
                 then ORet (subslice_desc s (Z.to_nat (intraw a)) (Z.to_nat (intraw b))) w
                 else OPanic rt_slice_bounds w)
           else OPanic rt_nil_deref w.
Lemma run_subslice : forall {A} (s : SliceH A) (a b : GoInt) (w : World),
  Nat.leb (sh_len s) (sh_cap s) = true ->
  subslice_inb s a b = true ->
  run_io (subslice s a b) w = ORet (subslice_desc s (Z.to_nat (intraw a)) (Z.to_nat (intraw b))) w.
Proof. intros A s a b w Hwf H. unfold subslice, run_io. rewrite Hwf, H. reflexivity. Qed.

(** Sub-slice element [j] IS parent element [a+j] — the SAME backing cell. *)
Lemma subslice_shares_cell : forall {A} (s : SliceH A) (a b j : nat),
  sh_cell (subslice_desc s a b) j = sh_cell s (a + j).
Proof.
  intros A s a b j. unfold sh_cell, sh_loc, subslice_desc. cbn.
  rewrite (Nat.add_assoc (sh_off s) a j). reflexivity.
Qed.

(** ALIASING — the defining slice property, a THEOREM: a write through a SUB-SLICE is
    observed through the PARENT (they share the backing array).  Write [sub[j]] (=
    [parent[a+j]]), read [parent[a+j]] → the written value. *)
Lemma subslice_alias : forall {A} (s : SliceH A) (a b j : nat) (v a0 : A) (w : World),
  ref_sel_opt (sh_cell s (a + j)) w = Some a0 ->
  ref_sel (sh_cell s (a + j))
          (ref_upd (sh_cell (subslice_desc s a b) j) v w) = v.
Proof.
  intros A s a b j v a0 w Hlive. rewrite subslice_shares_cell.
  exact (ref_sel_upd_same (sh_cell s (a + j)) v a0 w Hlive).
Qed.

(** SEPARATION — the COMPLEMENT of aliasing, equally defining for a faithful reference-type model: a
    write to cell [i] of slice [s] leaves cell [j] of slice [s'] UNCHANGED whenever they are DIFFERENT
    backing cells ([sh_loc s i <> sh_loc s' j]).  So aliasing holds exactly where the cells COINCIDE
    ([subslice_alias]) and independence exactly where they DIFFER — e.g. a write to [s[0:2]] is
    invisible through [s[2:4]], and writes to distinct indices of one slice don't interfere. *)
Lemma slice_idx_set_frame : forall {A B} (s : SliceH A) (s' : SliceH B) (i j : nat) (v : A) (w : World),
  sh_loc s i <> sh_loc s' j ->
  ref_sel (sh_cell s' j) (ref_upd (sh_cell s i) v w) = ref_sel (sh_cell s' j) w.
Proof.
  intros A B s s' i j v w Hne. unfold ref_upd.
  destruct (ref_sel_opt (sh_cell s i) w) as [x|]; [| reflexivity].
  apply (ref_sel_install_diff (sh_cell s i) (sh_cell s' j) v w).
  unfold sh_cell; cbn [r_loc]. exact Hne.
Qed.

(** Read-after-write at an index — a THEOREM (from the shared heap).
    ([sh_len <= sh_cap] premise: the SliceWF guard must clear before either index op reaches the cell). *)
Lemma slice_idx_get_set_same : forall {A} (tag : GoTypeTag A) (s : SliceH A) (i : GoInt) (v : A),
  Nat.leb (sh_len s) (sh_cap s) = true ->
  slice_in_len s i = true ->
  bind (slice_idx_set s i v) (fun _ => slice_idx_get tag s i) =io=
  bind (slice_idx_set s i v) (fun _ => ret v).
Proof.
  intros A tag s i v Hwf Hi. intro w.
  rewrite !run_bind.
  destruct (ref_sel_opt (sh_cell s (Z.to_nat (intraw i))) w) as [a|] eqn:Hsel.
  - rewrite !(run_slice_idx_set s i v a w Hwf Hi Hsel). cbn.
    rewrite (run_slice_idx_get tag s i v (ref_upd (sh_cell s (Z.to_nat (intraw i))) v w) Hwf Hi
               (ref_sel_opt_upd_same (sh_cell s (Z.to_nat (intraw i))) v a w Hsel)), run_ret.
    reflexivity.
  - unfold slice_idx_set, run_io. rewrite Hwf, Hi, Hsel. reflexivity.
Qed.

(** [slice_range_live s n w] — every backing cell [0, n) of [s] reads back LIVE (a real allocation).  Used to
    gate the realloc copy: a forged / dangling source (some cell absent) must FAIL LOUD, never copy fabricated
    zero elements out of unallocated locations. *)
Fixpoint slice_range_live {A} (s : SliceH A) (n : nat) (w : World) : bool :=
  match n with
  | O    => true
  | S m  => match ref_sel_opt (sh_cell s m) w with
            | Some _ => slice_range_live s m w
            | None   => false
            end
  end.

(** [append(s, v)] — the SUBTLE Go semantics:
    - WITHIN cap ([len < cap]): writes the cell at index [len] IN PLACE and returns a
      [len+1] handle over the SAME backing — so it ALIASES the original (and any
      sub-slice sharing those cells).
    - PAST cap ([len = cap]): REALLOCATES a fresh backing of [len+1] cells (at the
      fresh [w_next], DISJOINT from the old), copies the old elements, appends [v] —
      so the result does NOT alias the original.
    Lowers to Go's native [append(s, v)] (which makes exactly this choice on [cap]). *)
Definition slice_append {A} (tag : GoTypeTag A) (s : SliceH A) (v : A) : IO (SliceH A) :=
  fun w =>
    if (sh_len s <? sh_cap s)%nat
    then (* in place: write the spare-capacity cell at index len — only if it is LIVE (a real
            slice_make allocates cap cells; a forged handle's spare cell is absent -> FAIL LOUD,
            never fabricate a cell), then a len+1 handle over the SAME base/off/cap *)
      match ref_sel_opt (sh_cell s (sh_len s)) w with
      | Some _ => ORet (mkSliceH (sh_base s) (sh_off s) (S (sh_len s)) (sh_cap s) tag)
                       (ref_upd (sh_cell s (sh_len s)) v w)
      | None   => OPanic rt_nil_deref w
      end
    else if Nat.eqb (sh_len s) (sh_cap s) then
      (* PAST cap, at the SOLE valid grow point [len = cap]: reallocate a fresh disjoint backing of
         len+1, copy old, append v — but ONLY if every source cell [0, len) is LIVE; a forged / dangling
         handle FAILS LOUD instead of copying fabricated (zero-filled) elements out of unallocated cells *)
      if slice_range_live s (sh_len s) w then
        let base' := w_next w in
        let n := sh_len s in
        ORet (mkSliceH base' 0 (S n) (S n) tag)
             (mkWorld (fun k =>
                if (Nat.leb base' k
                    && Nat.ltb k (base' + S n))%bool
                then (let j := k - base' in
                      if Nat.eqb j n
                      then Some (existT _ A (tag, v))                         (* the appended element *)
                      else Some (existT _ A (tag, ref_sel (sh_cell s j) w)))  (* a copy of old s[j] *)
                else w_refs w k)
                (w_chans w) (w_maps w) (base' + S n) (w_output w))
      else OPanic rt_nil_deref w
    else (* [len > cap]: an IMPOSSIBLE SliceH — Go maintains the [len <= cap] invariant, so no real
            slice reaches here; a forged handle that violates it FAILS LOUD, never a phantom grow *)
      OPanic rt_nil_deref w.

(** WITHIN-cap append is IN PLACE: it updates exactly [s]'s cell at index [len], so the
    new element is written into the SHARED backing — a THEOREM.  (Reading [result[len]]
    or [parent[off+len]] sees [v].) *)
Lemma slice_append_incap : forall {A} (tag : GoTypeTag A) (s : SliceH A) (v a : A) (w : World),
  (sh_len s <? sh_cap s)%nat = true ->
  ref_sel_opt (sh_cell s (sh_len s)) w = Some a ->
  run_io (slice_append tag s v) w
    = ORet (mkSliceH (sh_base s) (sh_off s) (S (sh_len s)) (sh_cap s) tag)
           (ref_upd (sh_cell s (sh_len s)) v w).
Proof. intros A tag s v a w Hlt Hsel. unfold slice_append, run_io. rewrite Hlt, Hsel. reflexivity. Qed.

(** ...and that in-place write is OBSERVED through the parent backing: reading the cell
    at index [len] after the append returns [v] (the appended element aliases). *)
Lemma slice_append_incap_aliases : forall {A} (tag : GoTypeTag A) (s : SliceH A) (v a : A) (w : World),
  (sh_len s <? sh_cap s)%nat = true ->
  ref_sel_opt (sh_cell s (sh_len s)) w = Some a ->
  ref_sel (sh_cell s (sh_len s))
          (match run_io (slice_append tag s v) w with ORet _ w' => w' | OPanic _ w' => w' end) = v.
Proof.
  intros A tag s v a w Hlt Hsel. rewrite (slice_append_incap tag s v a w Hlt Hsel). cbn.
  exact (ref_sel_upd_same (sh_cell s (sh_len s)) v a w Hsel).
Qed.

(** A [len > cap] [SliceH] is IMPOSSIBLE for a real slice (Go maintains [len <= cap]); a forged handle that
    violates the invariant makes [append] FAIL LOUD — it never phantom-grows an over-long slice.  This is the
    anti-forgery witness for the malformed-shape case (paired with [slice_range_live]'s dangling-source guard). *)
Lemma slice_append_len_gt_cap_panics : forall {A} (tag : GoTypeTag A) (s : SliceH A) (v : A) (w : World),
  (sh_cap s < sh_len s)%nat ->
  run_io (slice_append tag s v) w = OPanic rt_nil_deref w.
Proof.
  intros A tag s v w Hgt. unfold slice_append, run_io.
  assert (H1 : (sh_len s <? sh_cap s)%nat = false) by (apply Nat.ltb_ge; lia).
  assert (H2 : Nat.eqb (sh_len s) (sh_cap s) = false) by (apply Nat.eqb_neq; lia).
  rewrite H1, H2. reflexivity.
Qed.

(** SliceWF on the TRANSFORMERS (checkpoint-61 step 4) — pinned BOTH ways, so a malformed [sh_cap < sh_len]
    header is neither LAUNDERED nor MANUFACTURED:
    - REJECT: a malformed PARENT FAILS LOUD ([subslice_bad_shape_rejected]/[slice_append_bad_shape_rejected],
      [exists p, = OPanic p w], no exported marker).  Crucially [subslice] must guard on [len <= cap] — its
      bounds check ([b <= cap]) alone would otherwise silently NORMALIZE a forged [cap < len] parent into a
      clean [len = b-a <= cap-a] child, hiding the forgery.
    - PRESERVE: whenever a transformer RETURNS ([ORet]) the output satisfies [sh_len <= sh_cap]
      ([subslice_preserves_wf]/[slice_append_preserves_wf]).
    So a malformed header can ONLY come from a raw [mkSliceH] forgery, and the index ops reject THAT
    ([slice_idx_{get,set}_bad_shape_rejected]) — the well-formed slice algebra is CLOSED. *)
Lemma subslice_preserves_wf : forall {A} (s : SliceH A) (a b : GoInt) (w : World) s' w',
  run_io (subslice s a b) w = ORet s' w' -> Nat.leb (sh_len s') (sh_cap s') = true.
Proof.
  intros A s a b w s' w' Hrun. unfold run_io, subslice in Hrun.
  destruct (Nat.leb (sh_len s) (sh_cap s)) eqn:Hwf; [ | discriminate Hrun ].
  destruct (subslice_inb s a b) eqn:Hinb; [ | discriminate Hrun ].
  injection Hrun as Hs' _. subst s'.
  unfold subslice_inb in Hinb.
  apply andb_prop in Hinb as [Hab1 Hbc]. apply andb_prop in Hab1 as [H0a Hab].
  apply Z.leb_le in H0a. apply Z.leb_le in Hab. apply Z.leb_le in Hbc.
  unfold subslice_desc; cbn [sh_len sh_cap]. apply Nat.leb_le. lia.
Qed.
Lemma slice_append_preserves_wf : forall {A} (tag : GoTypeTag A) (s : SliceH A) (v : A) (w : World) s' w',
  run_io (slice_append tag s v) w = ORet s' w' -> Nat.leb (sh_len s') (sh_cap s') = true.
Proof.
  intros A tag s v w s' w' Hrun. unfold run_io, slice_append in Hrun. cbv zeta in Hrun.
  destruct (sh_len s <? sh_cap s)%nat eqn:Hlc.
  - destruct (ref_sel_opt (sh_cell s (sh_len s)) w) as [a|] eqn:Hs; [ | discriminate Hrun ].
    injection Hrun as Hs' _. subst s'. cbn [sh_len sh_cap].
    apply Nat.leb_le. apply Nat.ltb_lt in Hlc. lia.
  - destruct (Nat.eqb (sh_len s) (sh_cap s)) eqn:Heq; [ | discriminate Hrun ].
    destruct (slice_range_live s (sh_len s) w) eqn:Hlive; [ | discriminate Hrun ].
    injection Hrun as Hs' _. subst s'. cbn [sh_len sh_cap]. apply Nat.leb_refl.
Qed.
Lemma subslice_bad_shape_rejected : forall {A} (s : SliceH A) (a b : GoInt) (w : World),
  (sh_cap s < sh_len s)%nat -> exists p, run_io (subslice s a b) w = OPanic p w.
Proof.
  intros A s a b w Hbad. unfold run_io, subslice.
  assert (Hleb : Nat.leb (sh_len s) (sh_cap s) = false) by (apply Nat.leb_gt; exact Hbad).
  rewrite Hleb. eexists. reflexivity.
Qed.
Lemma slice_append_bad_shape_rejected : forall {A} (tag : GoTypeTag A) (s : SliceH A) (v : A) (w : World),
  (sh_cap s < sh_len s)%nat -> exists p, run_io (slice_append tag s v) w = OPanic p w.
Proof. intros A tag s v w Hbad. eexists. apply slice_append_len_gt_cap_panics; exact Hbad. Qed.
(** SLICE TRANSFORMER WF SURFACE (manifest-gated, zero-axiom): [subslice]/[slice_append] pin the
    [sh_len <= sh_cap] SliceWF shape BOTH ways — REJECT a malformed [cap < len] parent ([*_bad_shape_rejected],
    fail loud, no exported marker) AND PRESERVE well-formedness on every [ORet] output ([*_preserves_wf]).  So
    a transformer neither launders nor manufactures a malformed header; this is checkpoint-61 step 4's
    transformer half, pairing with the index ops' [heap_aggregate_liveness_surface] rejection.  ⚠ nat-SHAPE
    invariant ONLY — NOT backing-object identity; a same-tag alias over a live backing is still the standing
    checkpoint-59 typed-liveness frontier. *)
Definition slice_transformer_wf_surface :=
  (@subslice_preserves_wf, @slice_append_preserves_wf,
   @subslice_bad_shape_rejected, @slice_append_bad_shape_rejected).
Print Assumptions slice_transformer_wf_surface.

(** [make([]T, len, cap)]: allocate [cap] fresh zeroed cells; the handle
    has length [len] and capacity [cap] (so it has [cap - len] spare slots — appending
    within them is IN PLACE, [slice_append_incap]).  Same heap shape as [slice_make_h]
    (which is the [len = cap] case), but distinguishes len from cap. *)
Definition slice_make_lc {A} (tag : GoTypeTag A) (len cap : GoInt) : IO (SliceH A) :=
  fun w => if (Z.leb 0 (intraw len) && Z.leb (intraw len) (intraw cap))%bool then   (* Go: 0 <= len <= cap, else PANIC *)
             let base := w_next w in
             let ln := Z.to_nat (intraw len) in
             let cp := Z.to_nat (intraw cap) in
             ORet (mkSliceH base 0 ln cp tag)
                  (mkWorld (fun k => if (Nat.leb base k
                                         && Nat.ltb k (base + cp))%bool
                                     then Some (existT _ A (tag, zero_val tag))
                                     else w_refs w k)
                           (w_chans w) (w_maps w) (base + cp) (w_output w))
           else OPanic rt_neg_make w.

(** A cell of a [make([]T,len,cap)] backing (any [j < cap]) is LIVE — reads [Some zero_val].  So liveness for
    these ops is DERIVED from the allocation, never leaked to callers as a bare precondition. *)
Lemma slice_make_lc_cell_live : forall {A} (tag : GoTypeTag A) (len cap : GoInt) (w : World) s w0 (j : nat),
  run_io (slice_make_lc tag len cap) w = ORet s w0 ->
  (j < sh_cap s)%nat ->
  ref_sel_opt (sh_cell s j) w0 = Some (zero_val tag).
Proof.
  intros A tag len cap w s w0 j Hmk Hj.
  unfold slice_make_lc, run_io in Hmk. cbv zeta in Hmk.
  destruct (Z.leb 0 (intraw len) && Z.leb (intraw len) (intraw cap))%bool eqn:Hc; [ | discriminate Hmk ].
  injection Hmk as Hs Hw0. subst s w0. cbn [sh_cap] in Hj.
  unfold ref_sel_opt, sh_cell, sh_loc; cbn [sh_base sh_off sh_tag r_loc r_tag w_refs].
  rewrite !Nat.add_0_l.
  rewrite (proj2 (Nat.leb_le (w_next w) (w_next w + j)) (Nat.le_add_r _ _)).
  rewrite (proj2 (Nat.ltb_lt (w_next w + j) (w_next w + Z.to_nat (intraw cap))) ltac:(lia)).
  cbn -[tag_coerce]. apply tag_coerce_refl.
Qed.

(** A fresh [make([]T,len,cap)] has [len <= cap] (Go's own make precondition, checked in [slice_make_lc]);
    extracted so the slice no-panic corollaries can turn an IN-LEN index ([i < len]) into the [i < cap] the
    backing-cell liveness needs. *)
Lemma slice_make_lc_len_fits : forall {A} (tag : GoTypeTag A) (len cap : GoInt) (w : World) s w0,
  run_io (slice_make_lc tag len cap) w = ORet s w0 -> (sh_len s <= sh_cap s)%nat.
Proof.
  intros A tag len cap w s w0 Hmk.
  unfold slice_make_lc, run_io in Hmk. cbv zeta in Hmk.
  destruct (Z.leb 0 (intraw len) && Z.leb (intraw len) (intraw cap))%bool eqn:Hc; [ | discriminate Hmk ].
  injection Hmk as Hs Hw0. subst s. cbn [sh_len sh_cap].
  apply andb_prop in Hc as [H0 Hlc]. apply Z.leb_le in H0. apply Z.leb_le in Hlc. lia.
Qed.

(** The slice ops that mint or grow a backing are in the [AllocFrontierOk] preservation path — both makes and
    [slice_append]'s realloc RANGE-install ([valid_alloc_range]); [slice_append]'s in-cap branch writes in
    place ([valid_ref_upd]).  So a program making / growing a slice then allocating again keeps the invariant. *)
Corollary valid_run_slice_make_lc : forall {A} (tag : GoTypeTag A) (len cap : GoInt) (w : World) s w',
  AllocFrontierOk w -> run_io (slice_make_lc tag len cap) w = ORet s w' -> AllocFrontierOk w'.
Proof.
  intros A tag len cap w s w' HV Hrun. unfold run_io, slice_make_lc in Hrun. cbv zeta in Hrun.
  destruct (Z.leb 0 (intraw len) && Z.leb (intraw len) (intraw cap))%bool eqn:Hc; [ | discriminate Hrun ].
  injection Hrun as _ Hw. subst w'. apply valid_alloc_range; assumption.
Qed.
Corollary valid_run_slice_make_h : forall {A} (tag : GoTypeTag A) (n : GoInt) (w : World) s w',
  AllocFrontierOk w -> run_io (slice_make_h tag n) w = ORet s w' -> AllocFrontierOk w'.
Proof.
  intros A tag n w s w' HV Hrun. unfold run_io, slice_make_h in Hrun. cbv zeta in Hrun.
  destruct (0 <=? intraw n)%Z eqn:Hc; [ | discriminate Hrun ].
  injection Hrun as _ Hw. subst w'. apply valid_alloc_range; assumption.
Qed.
Corollary valid_run_slice_append : forall {A} (tag : GoTypeTag A) (s : SliceH A) (v : A) (w : World) s' w',
  AllocFrontierOk w -> run_io (slice_append tag s v) w = ORet s' w' -> AllocFrontierOk w'.
Proof.
  intros A tag s v w s' w' HV Hrun. unfold run_io, slice_append in Hrun. cbv zeta in Hrun.
  destruct (sh_len s <? sh_cap s)%nat eqn:Hlc.
  - destruct (ref_sel_opt (sh_cell s (sh_len s)) w) as [a|] eqn:Hs; [ | discriminate Hrun ].
    injection Hrun as _ Hw. subst w'. apply valid_ref_upd; exact HV.
  - destruct (Nat.eqb (sh_len s) (sh_cap s)) eqn:Heq; [ | discriminate Hrun ].
    destruct (slice_range_live s (sh_len s) w) eqn:Hlive; [ | discriminate Hrun ].
    injection Hrun as _ Hw. subst w'. apply valid_alloc_range; exact HV.
Qed.

(** SLICE OP NO-PANIC (the aggregate no-panic frontier, now CLOSED): reading or writing a FRESH
    [make([]T,len,cap)] slice at an IN-BOUNDS index does NOT panic — an [ORet].  Unlike the struct case this
    carries a genuine [slice_in_len] precondition: Go PANICS on out-of-range ([run_slice_idx_set_oob]), so
    in-bounds is a real CALLER obligation, not a leaked derivable premise.  Given it, the backing cell's
    liveness (for [i < len <= cap]) is DISCHARGED from the allocation ([slice_make_lc_cell_live] +
    [slice_make_lc_len_fits]). *)
Corollary slice_make_idx_get_no_panic : forall {A} (tag : GoTypeTag A) (len cap : GoInt) (w : World) s w0 (i : GoInt),
  run_io (slice_make_lc tag len cap) w = ORet s w0 ->
  slice_in_len s i = true ->
  run_io (slice_idx_get tag s i) w0 = ORet (zero_val tag) w0.
Proof.
  intros A tag len cap w s w0 i Hmk Hin.
  pose proof (proj2 (Nat.leb_le (sh_len s) (sh_cap s)) (slice_make_lc_len_fits tag len cap w s w0 Hmk)) as Hwf.
  assert (Hj : (Z.to_nat (intraw i) < sh_cap s)%nat).
  { pose proof (slice_make_lc_len_fits tag len cap w s w0 Hmk) as Hlc.
    pose proof Hin as Hin'. unfold slice_in_len in Hin'. apply andb_prop in Hin' as [_ Hlt].
    apply Nat.ltb_lt in Hlt. lia. }
  exact (run_slice_idx_get tag s i (zero_val tag) w0 Hwf Hin
           (slice_make_lc_cell_live tag len cap w s w0 (Z.to_nat (intraw i)) Hmk Hj)).
Qed.
Corollary slice_make_idx_set_no_panic : forall {A} (tag : GoTypeTag A) (len cap : GoInt) (w : World) s w0 (i : GoInt) (v : A),
  run_io (slice_make_lc tag len cap) w = ORet s w0 ->
  slice_in_len s i = true ->
  exists w1, run_io (slice_idx_set s i v) w0 = ORet tt w1.
Proof.
  intros A tag len cap w s w0 i v Hmk Hin. eexists.
  pose proof (proj2 (Nat.leb_le (sh_len s) (sh_cap s)) (slice_make_lc_len_fits tag len cap w s w0 Hmk)) as Hwf.
  assert (Hj : (Z.to_nat (intraw i) < sh_cap s)%nat).
  { pose proof (slice_make_lc_len_fits tag len cap w s w0 Hmk) as Hlc.
    pose proof Hin as Hin'. unfold slice_in_len in Hin'. apply andb_prop in Hin' as [_ Hlt].
    apply Nat.ltb_lt in Hlt. lia. }
  exact (run_slice_idx_set s i v (zero_val tag) w0 Hwf Hin
           (slice_make_lc_cell_live tag len cap w s w0 (Z.to_nat (intraw i)) Hmk Hj)).
Qed.

(** The len=cap allocator [slice_make_h] ([make([]T,n)]) gets the SAME no-panic evidence — it is live code
    beside [slice_make_lc], not a special case of it (separate definition).  Here len = cap, so an IN-LEN
    index already satisfies the backing-cell bound ([slice_make_h_cell_live] takes [j < sh_len] directly — no
    [len<=cap] step needed). *)
Lemma slice_make_h_cell_live : forall {A} (tag : GoTypeTag A) (n : GoInt) (w : World) s w0 (j : nat),
  run_io (slice_make_h tag n) w = ORet s w0 ->
  (j < sh_len s)%nat ->
  ref_sel_opt (sh_cell s j) w0 = Some (zero_val tag).
Proof.
  intros A tag n w s w0 j Hmk Hj.
  unfold slice_make_h, run_io in Hmk. cbv zeta in Hmk.
  destruct (0 <=? intraw n)%Z eqn:Hc; [ | discriminate Hmk ].
  injection Hmk as Hs Hw0. subst s w0. cbn [sh_len] in Hj.
  unfold ref_sel_opt, sh_cell, sh_loc; cbn [sh_base sh_off sh_tag r_loc r_tag w_refs].
  rewrite !Nat.add_0_l.
  rewrite (proj2 (Nat.leb_le (w_next w) (w_next w + j)) (Nat.le_add_r _ _)).
  rewrite (proj2 (Nat.ltb_lt (w_next w + j) (w_next w + Z.to_nat (intraw n))) ltac:(lia)).
  cbn -[tag_coerce]. apply tag_coerce_refl.
Qed.
(** [make([]T,n)] has [len = cap = n], so trivially [len <= cap] (Go's slice invariant) — the SliceWF guard
    on the index ops clears.  Mirror of [slice_make_lc_len_fits] for the len=cap allocator. *)
Lemma slice_make_h_len_fits : forall {A} (tag : GoTypeTag A) (n : GoInt) (w : World) s w0,
  run_io (slice_make_h tag n) w = ORet s w0 -> Nat.leb (sh_len s) (sh_cap s) = true.
Proof.
  intros A tag n w s w0 Hmk.
  unfold slice_make_h, run_io in Hmk. cbv zeta in Hmk.
  destruct (0 <=? intraw n)%Z eqn:Hc; [ | discriminate Hmk ].
  injection Hmk as Hs Hw0. subst s. cbn [sh_len sh_cap]. apply Nat.leb_refl.
Qed.
Corollary slice_make_h_idx_get_no_panic : forall {A} (tag : GoTypeTag A) (n : GoInt) (w : World) s w0 (i : GoInt),
  run_io (slice_make_h tag n) w = ORet s w0 ->
  slice_in_len s i = true ->
  run_io (slice_idx_get tag s i) w0 = ORet (zero_val tag) w0.
Proof.
  intros A tag n w s w0 i Hmk Hin.
  pose proof (slice_make_h_len_fits tag n w s w0 Hmk) as Hwf.
  assert (Hj : (Z.to_nat (intraw i) < sh_len s)%nat).
  { pose proof Hin as Hin'. unfold slice_in_len in Hin'. apply andb_prop in Hin' as [_ Hlt].
    apply Nat.ltb_lt in Hlt. exact Hlt. }
  exact (run_slice_idx_get tag s i (zero_val tag) w0 Hwf Hin
           (slice_make_h_cell_live tag n w s w0 (Z.to_nat (intraw i)) Hmk Hj)).
Qed.
Corollary slice_make_h_idx_set_no_panic : forall {A} (tag : GoTypeTag A) (n : GoInt) (w : World) s w0 (i : GoInt) (v : A),
  run_io (slice_make_h tag n) w = ORet s w0 ->
  slice_in_len s i = true ->
  exists w1, run_io (slice_idx_set s i v) w0 = ORet tt w1.
Proof.
  intros A tag n w s w0 i v Hmk Hin. eexists.
  pose proof (slice_make_h_len_fits tag n w s w0 Hmk) as Hwf.
  assert (Hj : (Z.to_nat (intraw i) < sh_len s)%nat).
  { pose proof Hin as Hin'. unfold slice_in_len in Hin'. apply andb_prop in Hin' as [_ Hlt].
    apply Nat.ltb_lt in Hlt. exact Hlt. }
  exact (run_slice_idx_set s i v (zero_val tag) w0 Hwf Hin
           (slice_make_h_cell_live tag n w s w0 (Z.to_nat (intraw i)) Hmk Hj)).
Qed.

(** LiveSlice — a WELL-FORMED slice handle: its shape is POSSIBLE ([sh_len <= sh_cap], Go's own slice invariant)
    AND its whole backing range [0, cap) reads back LIVE.  BOTH conjuncts are load-bearing — WITHOUT [len <= cap]
    a forged header like [mkSliceH 1 0 1 0 tag] (len 1, cap 0) satisfies the VACUOUS [slice_range_live s 0] yet
    reports index 0 in-bounds ([slice_in_len] checks [len], not [cap]) with NO backing cell; the payoff
    [LiveSlice_index_live] (an in-[len] index has a LIVE typed cell) is exactly what fails there, so the shape
    conjunct is not optional.  The backing authority [slice_range_live s (sh_cap s)] is a NAMED interface (TYPED
    liveness — a same-tag header over a live backing satisfies it; origin is not checked, the checkpoint-59
    frontier), CONSUMED by the semantics ([append]'s realloc-copy guards on it).  [slice_range_live_of_cells] is
    the generic cells→range lift both slice allocators share; [slice_range_live_cell] is its converse. *)
Definition LiveSlice {A} (s : SliceH A) (w : World) : Prop :=
  (sh_len s <= sh_cap s)%nat /\ slice_range_live s (sh_cap s) w = true.
Lemma slice_range_live_of_cells : forall {A} (tag : GoTypeTag A) (s : SliceH A) (w0 : World) (k : nat),
  (forall j, (j < k)%nat -> ref_sel_opt (sh_cell s j) w0 = Some (zero_val tag)) ->
  slice_range_live s k w0 = true.
Proof.
  intros A tag s w0 k. induction k as [| m IH]; intros Hcells.
  - reflexivity.
  - cbn [slice_range_live]. rewrite (Hcells m (Nat.lt_succ_diag_r m)).
    apply IH. intros j Hj. apply Hcells. lia.
Qed.
Lemma slice_range_live_cell : forall {A} (s : SliceH A) (n : nat) (w : World) (j : nat),
  slice_range_live s n w = true -> (j < n)%nat -> ref_sel_opt (sh_cell s j) w <> None.
Proof.
  intros A s n w j. revert j. induction n as [| m IH]; intros j Hlive Hj; [ lia | ].
  cbn [slice_range_live] in Hlive.
  destruct (ref_sel_opt (sh_cell s m) w) as [a|] eqn:Hm; [ | discriminate Hlive ].
  destruct (Nat.eq_dec j m) as [->|Hne]; [ rewrite Hm; discriminate | apply IH; [ exact Hlive | lia ] ].
Qed.
(** THE PAYOFF: from a well-formed [LiveSlice], every IN-[len] index has a LIVE typed backing cell.  This is the
    theorem the [mkSliceH 1 0 1 0] counterexample breaks without the [len <= cap] conjunct. *)
Lemma LiveSlice_index_live : forall {A} (s : SliceH A) (w : World) (j : nat),
  LiveSlice s w -> (j < sh_len s)%nat -> exists v, ref_sel_opt (sh_cell s j) w = Some v.
Proof.
  intros A s w j [Hlc Hlive] Hj.
  pose proof (slice_range_live_cell s (sh_cap s) w j Hlive ltac:(lia)) as Hne.
  destruct (ref_sel_opt (sh_cell s j) w) as [v|] eqn:E; [ exists v; reflexivity | congruence ].
Qed.
(** BOTH slice allocators produce a LiveSlice — [make([]T,len,cap)] (cell fact over [j < cap] directly) and
    [make([]T,n)] (len=cap, so its [j < len] cell fact covers the whole [0, cap) backing — the len=cap
    identity destructed inline, no capacity-named helper). *)
Lemma slice_make_lc_live : forall {A} (tag : GoTypeTag A) (len cap : GoInt) (w : World) s w0,
  run_io (slice_make_lc tag len cap) w = ORet s w0 -> LiveSlice s w0.
Proof.
  intros A tag len cap w s w0 Hmk. unfold LiveSlice. split.
  - exact (slice_make_lc_len_fits tag len cap w s w0 Hmk).
  - apply (slice_range_live_of_cells tag s w0 (sh_cap s)).
    intros j Hj. exact (slice_make_lc_cell_live tag len cap w s w0 j Hmk Hj).
Qed.
Lemma slice_make_h_live : forall {A} (tag : GoTypeTag A) (n : GoInt) (w : World) s w0,
  run_io (slice_make_h tag n) w = ORet s w0 -> LiveSlice s w0.
Proof.
  intros A tag n w s w0 Hmk. unfold LiveSlice.
  assert (Hcl : sh_cap s = sh_len s).
  { unfold slice_make_h, run_io in Hmk. cbv zeta in Hmk.
    destruct (0 <=? intraw n)%Z eqn:Hc; [ | discriminate Hmk ].
    injection Hmk as Hs Hw0. subst s. reflexivity. }
  split; [ lia | ].
  apply (slice_range_live_of_cells tag s w0 (sh_cap s)).
  intros j Hj. rewrite Hcl in Hj.
  exact (slice_make_h_cell_live tag n w s w0 j Hmk Hj).
Qed.

(** A [make([]T, len, cap)] slice has spare capacity, so [append] is IN PLACE and the
    result SHARES its backing — a THEOREM directly from [slice_append_incap]: the append
    writes the cell at index [len] of the ORIGINAL handle.  Liveness of the spare cell is
    DERIVED from the allocation ([slice_make_lc_cell_live]), not leaked. *)
Lemma make_lc_append_inplace : forall {A} (tag : GoTypeTag A) (len cap : GoInt) (v : A) (w : World),
  (intraw len <? intraw cap)%Z = true ->
  forall s w0, run_io (slice_make_lc tag len cap) w = ORet s w0 ->
  run_io (slice_append tag s v) w0
    = ORet (mkSliceH (sh_base s) (sh_off s) (S (sh_len s)) (sh_cap s) tag)
           (ref_upd (sh_cell s (sh_len s)) v w0).
Proof.
  intros A tag len cap v w Hlt s w0 Hmk.
  pose proof Hmk as Hmk0. unfold slice_make_lc, run_io in Hmk0. cbv zeta in Hmk0.
  destruct (Z.leb 0 (intraw len) && Z.leb (intraw len) (intraw cap))%bool eqn:Hc; [ | discriminate Hmk0 ].
  injection Hmk0 as Hs _.
  assert (Hlen : (sh_len s < sh_cap s)%nat).
  { rewrite <- Hs; cbn [sh_len sh_cap]. apply andb_prop in Hc. destruct Hc as [Hc0 Hc1].
    apply Z.leb_le in Hc0. apply Z.leb_le in Hc1. apply Z.ltb_lt in Hlt. lia. }
  apply (slice_append_incap tag s v (zero_val tag)).
  - apply Nat.ltb_lt. exact Hlen.
  - exact (slice_make_lc_cell_live tag len cap w s w0 (sh_len s) Hmk Hlen).
Qed.

(* Element [i]'s cell is [sh_start s + i] (= [sh_loc s i] by [add_assoc]); the
   clear/copy ranges are the interval [[sh_start s, sh_start s + len)]. *)
Definition sh_start {A} (s : SliceH A) : nat := sh_base s + sh_off s.

(** [clear(s)] (Go 1.21): zero [s]'s [len] elements.  FAILS LOUD ([rt_nil_deref]) unless the shape is possible
    ([sh_len <= sh_cap] — Go's slice invariant; an impossible [len > cap] forged header would else zero cells
    BEYOND its own backing) AND EVERY element cell reads LIVE + TAG-CORRECT ([slice_range_live s (sh_len s) w] —
    itself the tag-aware [ref_sel_opt] range check): a shape-impossible handle, or one with ANY absent /
    dangling / wrong-tag element, does NOT silently succeed, exactly like [slice_idx_set] / [slice_append].
    (A SAME-TAG handle aliasing a LIVE backing still PASSES — liveness is TYPED, not origin-checked; the standing
    checkpoint-59 frontier.  So this rejects malformed/dangling/wrong-tag handles, NOT every forged one.)  On the
    live path each cell is zeroed
    through a TAG-AWARE per-cell guard — an absent / foreign-typed cell is left unchanged, so by CONSTRUCTION
    the write never fabricates or retypes a cell (a design property of the [ref_sel_opt]-keyed guard, not itself
    a separate theorem).  The GATED facts are [valid_run_slice_clear_h] (the live path preserves [AllocFrontierOk] —
    no cell is created at loc 0 / a fresh location) and [slice_clear_rejected] (a malformed slice fails loud).
    For a real slice the whole range is zeroed.  Lowered by name ([clear(s)]); the fail-loud branch is
    model-only (a real [clear] always sees live cells). *)
Definition slice_clear_h {A} (tag : GoTypeTag A) (s : SliceH A) : IO unit :=
  fun w => if (Nat.leb (sh_len s) (sh_cap s) && slice_range_live s (sh_len s) w)%bool
           then ORet tt
             (mkWorld (fun k => if (Nat.leb (sh_start s) k
                                    && Nat.ltb k (sh_start s + sh_len s))%bool
                                then match ref_sel_opt (mkRef k tag) w with
                                     | Some _ => Some (existT _ A (tag, zero_val tag))
                                     | None   => w_refs w k
                                     end
                                else w_refs w k)
                      (w_chans w) (w_maps w) (w_next w) (w_output w))
           else OPanic rt_nil_deref w.

(** [copy(dst, src)]: copy [min(len dst, len src)] elements [src → dst], return the count.  FAILS LOUD
    ([rt_nil_deref]) unless BOTH shapes are possible ([sh_len <= sh_cap] for [dst] and [src], so [n <= cap] and
    neither range spills past its backing) AND the first [n] cells of BOTH read LIVE + TAG-CORRECT
    ([slice_range_live dst n w && slice_range_live src n w]) — a shape-impossible handle, or one with ANY absent
    / dangling / wrong-tag element in [dst] or [src], does NOT silently succeed.  (A SAME-TAG handle over a LIVE
    backing still PASSES — typed liveness, not origin; the checkpoint-59 frontier — so this rejects malformed /
    dangling / wrong-tag handles, NOT every forged one.)  On the live path each [dst] cell takes the [src] value through a TAG-AWARE
    per-cell guard reading the REAL [src] value ([ref_sel_opt = Some sv], never a fabricated zero); an absent /
    foreign-typed [dst] or [src] cell leaves [dst] unchanged, so by CONSTRUCTION the write never fabricates or
    retypes a cell (a design property of the guard, not itself a theorem).  The GATED facts are
    [valid_run_slice_copy] (the live path preserves [AllocFrontierOk]) and [slice_copy_rejected] (a malformed slice
    fails loud).  For real slices the whole range is written.  Lowered by name ([copy(dst, src)]); the fail-loud
    branch is model-only. *)
Definition slice_copy {A} (tag : GoTypeTag A) (dst src : SliceH A) : IO GoInt :=
  fun w => let n := if Nat.leb (sh_len dst) (sh_len src) then sh_len dst else sh_len src in
           if (Nat.leb (sh_len dst) (sh_cap dst) && Nat.leb (sh_len src) (sh_cap src)
               && slice_range_live dst n w && slice_range_live src n w)%bool
           then ORet (intwrap (Z.of_nat n))
             (mkWorld (fun k => if (Nat.leb (sh_start dst) k
                                    && Nat.ltb k (sh_start dst + n))%bool
                                then match ref_sel_opt (mkRef k tag) w,
                                           ref_sel_opt (mkRef (sh_start src + (k - sh_start dst)) (sh_tag src)) w with
                                     | Some _, Some sv => Some (existT _ A (tag, sv))
                                     | _, _            => w_refs w k
                                     end
                                else w_refs w k)
                      (w_chans w) (w_maps w) (w_next w) (w_output w))
           else OPanic rt_nil_deref w.
Corollary valid_run_slice_clear_h : forall {A} (tag : GoTypeTag A) (s : SliceH A) (w : World) r w',
  AllocFrontierOk w -> run_io (slice_clear_h tag s) w = ORet r w' -> AllocFrontierOk w'.
Proof.
  intros A tag s w r w' HV Hrun. unfold run_io, slice_clear_h in Hrun.
  destruct (Nat.leb (sh_len s) (sh_cap s) && slice_range_live s (sh_len s) w)%bool; [ | discriminate Hrun ].
  injection Hrun as _ Hw. subst w'.
  apply valid_guarded_refs; [ exact HV | ]. intros k Hk. cbn beta.
  assert (Hns : ref_sel_opt (mkRef k tag) w = None) by (unfold ref_sel_opt; cbn [r_loc]; rewrite Hk; reflexivity).
  destruct (Nat.leb (sh_start s) k && Nat.ltb k (sh_start s + sh_len s))%bool; [ rewrite Hns | ]; exact Hk.
Qed.
Corollary valid_run_slice_copy : forall {A} (tag : GoTypeTag A) (dst src : SliceH A) (w : World) r w',
  AllocFrontierOk w -> run_io (slice_copy tag dst src) w = ORet r w' -> AllocFrontierOk w'.
Proof.
  intros A tag dst src w r w' HV Hrun. unfold run_io, slice_copy in Hrun. cbv zeta in Hrun.
  set (n := if Nat.leb (sh_len dst) (sh_len src) then sh_len dst else sh_len src) in Hrun.
  destruct (Nat.leb (sh_len dst) (sh_cap dst) && Nat.leb (sh_len src) (sh_cap src)
            && slice_range_live dst n w && slice_range_live src n w)%bool; [ | discriminate Hrun ].
  injection Hrun as _ Hw. subst w'.
  apply valid_guarded_refs; [ exact HV | ]. intros k Hk. cbn beta.
  assert (Hns : ref_sel_opt (mkRef k tag) w = None) by (unfold ref_sel_opt; cbn [r_loc]; rewrite Hk; reflexivity).
  destruct (Nat.leb (sh_start dst) k && Nat.ltb k (sh_start dst + n))%bool; [ rewrite Hns | ]; exact Hk.
Qed.

(** REJECTION — whenever the fail-loud guard is [false] (an impossible [len > cap] shape OR any dead / wrong-tag
    element), [clear]/[copy] FAIL LOUD: [exists p, run_io … = OPanic p w] — a rejection ([OPanic], never a silent
    [ORet]) that leaves the world UNCHANGED ([… p w], no mutation), without pinning the model-internal payload.
    These are the proofs that the guard actually rejects (not just an asserted [if]); the [_bad_shape_] corollaries
    specialise them to the impossible-shape case for BOTH operands — the peer of [slice_append]'s [len > cap]
    panic. *)
Lemma slice_clear_rejected : forall {A} (tag : GoTypeTag A) (s : SliceH A) (w : World),
  (Nat.leb (sh_len s) (sh_cap s) && slice_range_live s (sh_len s) w)%bool = false ->
  exists p, run_io (slice_clear_h tag s) w = OPanic p w.
Proof.
  intros A tag s w Hbad. unfold run_io, slice_clear_h. rewrite Hbad. eexists. reflexivity.
Qed.
Lemma slice_copy_rejected : forall {A} (tag : GoTypeTag A) (dst src : SliceH A) (w : World),
  (Nat.leb (sh_len dst) (sh_cap dst) && Nat.leb (sh_len src) (sh_cap src)
   && slice_range_live dst (if Nat.leb (sh_len dst) (sh_len src) then sh_len dst else sh_len src) w
   && slice_range_live src (if Nat.leb (sh_len dst) (sh_len src) then sh_len dst else sh_len src) w)%bool = false ->
  exists p, run_io (slice_copy tag dst src) w = OPanic p w.
Proof.
  intros A tag dst src w Hbad. unfold run_io, slice_copy. cbv zeta. rewrite Hbad. eexists. reflexivity.
Qed.
Corollary slice_clear_bad_shape_rejected : forall {A} (tag : GoTypeTag A) (s : SliceH A) (w : World),
  (sh_cap s < sh_len s)%nat -> exists p, run_io (slice_clear_h tag s) w = OPanic p w.
Proof.
  intros A tag s w Hbad. apply slice_clear_rejected.
  assert (Hleb : Nat.leb (sh_len s) (sh_cap s) = false) by (apply Nat.leb_gt; exact Hbad).
  rewrite Hleb. reflexivity.
Qed.
Corollary slice_copy_bad_shape_rejected : forall {A} (tag : GoTypeTag A) (dst src : SliceH A) (w : World),
  (sh_cap dst < sh_len dst)%nat -> exists p, run_io (slice_copy tag dst src) w = OPanic p w.
Proof.
  intros A tag dst src w Hbad. apply slice_copy_rejected.
  assert (Hleb : Nat.leb (sh_len dst) (sh_cap dst) = false) by (apply Nat.leb_gt; exact Hbad).
  rewrite Hleb. reflexivity.
Qed.
Corollary slice_copy_bad_shape_rejected_src : forall {A} (tag : GoTypeTag A) (dst src : SliceH A) (w : World),
  (sh_cap src < sh_len src)%nat -> exists p, run_io (slice_copy tag dst src) w = OPanic p w.
Proof.
  intros A tag dst src w Hbad. apply slice_copy_rejected.
  assert (Hleb : Nat.leb (sh_len src) (sh_cap src) = false) by (apply Nat.leb_gt; exact Hbad).
  rewrite Hleb. destruct (Nat.leb (sh_len dst) (sh_cap dst)); reflexivity.
Qed.

(** BULK-SLICE-WRITE SURFACE (manifest-gated, zero-axiom): the bulk slice ops [clear]/[copy] are BOTH safe on
    the live path (preserve [AllocFrontierOk] — [valid_run_slice_clear_h]/[valid_run_slice_copy]) AND rejecting when
    the guard is FALSE — [slice_clear_rejected]/[slice_copy_rejected] fail loud whenever an impossible [len>cap]
    shape OR a dead / dangling / wrong-tag element makes the guard [false], with the [_bad_shape_] corollaries
    pinning the impossible shape for [clear], [copy]'s DST, and [copy]'s SRC specifically.  So the guard is
    PINNED both ways for every operand, not just asserted.  ⚠ This rejects a MALFORMED / DANGLING / WRONG-TAG
    handle — NOT every forged one: a SAME-TAG handle aliasing a live backing passes the tag-aware liveness check
    (typed liveness, not origin; the standing checkpoint-59 frontier). *)
Definition slice_bulk_write_surface :=
  (@valid_run_slice_clear_h, @valid_run_slice_copy, @slice_clear_rejected, @slice_copy_rejected,
   @slice_clear_bad_shape_rejected, @slice_copy_bad_shape_rejected, @slice_copy_bad_shape_rejected_src).
Print Assumptions slice_bulk_write_surface.

(** ---- Heap-backed STRUCTS as field-cell bundles ----

    A user struct cannot be a single [w_refs] cell: [GoTypeTag] has no struct
    constructor (and [tag_eq]'s decidable type-equality cannot produce the [A = B] proof
    for opaque struct types — the wall).  The principled model: a struct value in storage
    is a BUNDLE of scalar FIELD-CELLS — field [k] lives at cell [base + k], tagged with
    its OWN scalar [GoTypeTag] — so only the scalar field tags are ever needed,
    sidestepping the wall (the same consecutive-cell shape as [SliceH], but the fields
    are HETEROGENEOUS).  A struct POINTER is just the [base] location.  Every law is
    inherited from [ref_sel_upd_same] — NO new heap, NO new axiom. *)
Record HStruct := mkHStruct { hs_base : nat }.
(* [ref_sel_opt] + its laws were moved UP to just before [ref_get] (needed there for the fail-loud read). *)

Definition hfield_cell {A} (h : HStruct) (k : nat) (tag : GoTypeTag A) : Ref A :=
  mkRef (hs_base h + k) tag.
(** Read a struct field.  FAILS LOUD on a missing/retyped cell — a forged [GSPtr] (e.g.
    [mkGSPtr 5] addressing an unallocated base) panics with the Go nil-pointer/invalid-address message
    instead of fabricating a zero.  Body is plugin-lowered to [p.Field], so the loud check never reaches
    the emitted Go (a real [p] is always allocated); it only rules out the model accepting a WRONG-TAG or
    ABSENT forged read (a SAME-TAG forged alias still reads the aliased cell — the origin frontier). *)
Definition hfield_get {A} (h : HStruct) (k : nat) (tag : GoTypeTag A) : IO A :=
  fun w => match ref_sel_opt (hfield_cell h k tag) w with
           | Some a => ORet a w
           | None   => OPanic rt_nil_deref w
           end.
Definition hfield_set {A} (h : HStruct) (k : nat) (tag : GoTypeTag A) (v : A) : IO unit :=
  fun w => match ref_sel_opt (hfield_cell h k tag) w with
           | Some _ => ORet tt (ref_upd (hfield_cell h k tag) v w)
           | None   => OPanic rt_nil_deref w   (* forged struct cell: FAIL LOUD, symmetric with hfield_get *)
           end.
Lemma run_hfield_get : forall {A} (h : HStruct) (k : nat) (tag : GoTypeTag A) (w : World),
  run_io (hfield_get h k tag) w =
    match ref_sel_opt (hfield_cell h k tag) w with
    | Some a => ORet a w
    | None   => OPanic rt_nil_deref w
    end.
Proof. reflexivity. Qed.
(** When the field cell is genuinely allocated + correctly typed (the only case real programs hit), the
    checked read delivers the value — so read-after-write reasoning is unchanged for valid heaps. *)
Lemma run_hfield_get_some : forall {A} (h : HStruct) (k : nat) (tag : GoTypeTag A) (a : A) (w : World),
  ref_sel_opt (hfield_cell h k tag) w = Some a ->
  run_io (hfield_get h k tag) w = ORet a w.
Proof. intros A h k tag a w H. unfold run_io, hfield_get. rewrite H. reflexivity. Qed.
Lemma run_hfield_set : forall {A} (h : HStruct) (k : nat) (tag : GoTypeTag A) (v a : A) (w : World),
  ref_sel_opt (hfield_cell h k tag) w = Some a ->
  run_io (hfield_set h k tag v) w = ORet tt (ref_upd (hfield_cell h k tag) v w).
Proof. intros A h k tag v a w Hsel. unfold hfield_set, run_io. rewrite Hsel. reflexivity. Qed.

(** A [ref_sel] at a DIFFERENT location is unaffected by a [ref_upd] — the foundation
    for field INDEPENDENCE (writing one field leaves the others alone). *)
Lemma ref_sel_upd_diff : forall {A B} (r : Ref A) (r' : Ref B) (v : A) (w : World),
  r_loc r <> r_loc r' -> ref_sel r' (ref_upd r v w) = ref_sel r' w.
Proof.
  intros A B r r' v w Hne. unfold ref_upd.
  destruct (ref_sel_opt r w) as [a|]; [ apply ref_sel_install_diff; exact Hne | reflexivity ].
Qed.

(** CROSS-RESOURCE separation: the [World]'s ref-heap and channel-heap are INDEPENDENT components
    ([w_refs] vs [w_chans]), so a CHANNEL op leaves every ref untouched and a REF op leaves every
    channel untouched.  These let a single [run_io] world match BOTH the calculus's channel AND heap
    state at once (the combined state refinement). *)
Lemma ref_sel_chan_write_frame : forall {A B} (tag : GoTypeTag A) (ch : GoChan A) buf cl cap (r : Ref B) (w : World),
  ref_sel r (chan_write tag ch buf cl cap w) = ref_sel r w.
Proof. intros. unfold ref_sel, chan_write. destruct (chan_cell_ok tag ch w); reflexivity. Qed.

Lemma ref_sel_chan_send_upd : forall {A B} (tag : GoTypeTag A) (ch : GoChan A) (v : A) (r : Ref B) (w : World),
  ref_sel r (chan_send_upd tag ch v w) = ref_sel r w.
Proof. intros. unfold chan_send_upd. apply ref_sel_chan_write_frame. Qed.

Lemma ref_sel_chan_recv_upd : forall {A B} (tag : GoTypeTag A) (ch : GoChan A) (r : Ref B) (w : World),
  ref_sel r (chan_recv_upd tag ch w) = ref_sel r w.
Proof. intros. unfold chan_recv_upd. apply ref_sel_chan_write_frame. Qed.
(* The CHECKED selector [ref_sel_opt] is framed by channel ops the same way (refs and channel cells are
   independent World components) — needed by the heap bridge after the fail-loud read. *)
Lemma ref_sel_opt_chan_write_frame : forall {A B} (tag : GoTypeTag A) (ch : GoChan A) buf cl cap (r : Ref B) (w : World),
  ref_sel_opt r (chan_write tag ch buf cl cap w) = ref_sel_opt r w.
Proof. intros. unfold ref_sel_opt, chan_write. destruct (chan_cell_ok tag ch w); reflexivity. Qed.
Lemma ref_sel_opt_chan_send_upd : forall {A B} (tag : GoTypeTag A) (ch : GoChan A) (v : A) (r : Ref B) (w : World),
  ref_sel_opt r (chan_send_upd tag ch v w) = ref_sel_opt r w.
Proof. intros. unfold chan_send_upd. apply ref_sel_opt_chan_write_frame. Qed.
Lemma ref_sel_opt_chan_recv_upd : forall {A B} (tag : GoTypeTag A) (ch : GoChan A) (r : Ref B) (w : World),
  ref_sel_opt r (chan_recv_upd tag ch w) = ref_sel_opt r w.
Proof. intros. unfold chan_recv_upd. apply ref_sel_opt_chan_write_frame. Qed.

Lemma chan_buf_ref_upd_frame : forall {A B} (tag : GoTypeTag A) (ch : GoChan A) (r : Ref B) (v : B) (w : World),
  chan_buf tag ch (ref_upd r v w) = chan_buf tag ch w.
Proof. intros. unfold chan_buf, ref_upd, ref_install. destruct (ref_sel_opt r w); reflexivity. Qed.
(** A ref write leaves channel TAG-CORRECT status untouched ([ref_upd] touches only [w_refs]; [chan_cell_ok]
    reads [w_chans]) — frames the [WPresent] (tag-correct-channels) conjunct of the multi-channel refinement
    across the heap-write step, so the bridge's channels stay tag-correct through a [CWrite]. *)
Lemma chan_cell_ok_ref_upd_frame : forall {A B} (tag : GoTypeTag A) (ch : GoChan A) (r : Ref B) (v : B) (w : World),
  chan_cell_ok tag ch (ref_upd r v w) = chan_cell_ok tag ch w.
Proof. intros. unfold chan_cell_ok, ref_upd, ref_install. destruct (ref_sel_opt r w); reflexivity. Qed.
(** A ref write leaves channel ROOM untouched too ([chan_room] reads only [w_chans], which [ref_upd] preserves) —
    the send-side condition frames across a heap write in the typed handoff bridge. *)
Lemma chan_room_ref_upd_frame : forall {A B} (tag : GoTypeTag A) (ch : GoChan A) (r : Ref B) (v : B) (w : World),
  chan_room tag ch (ref_upd r v w) = chan_room tag ch w.
Proof. intros. unfold chan_room, ref_upd, ref_install. destruct (ref_sel_opt r w); reflexivity. Qed.

(** ---- World-component independence for the CLOSEDNESS refinement ----
    [chan_close_upd] touches only the channel-closed flag of ONE channel; it leaves buffers and refs
    untouched and leaves every OTHER channel's closedness untouched; and a ref write ([ref_upd]) leaves
    closedness untouched.  These frame the [WClosedMatch] conjunct of the combined state refinement. *)
Lemma chan_buf_close_frame : forall {A} (tag : GoTypeTag A) (ch ch' : GoChan A) (w : World),
  ch <> ch' -> chan_buf tag ch' (chan_close_upd tag ch w) = chan_buf tag ch' w.
Proof.
  intros A tag ch ch' w Hne. unfold chan_close_upd, chan_buf.
  rewrite (chan_read_write_frame tag ch ch' _ _ _ w Hne). reflexivity.
Qed.
Lemma ref_sel_chan_close_upd : forall {A B} (tag : GoTypeTag A) (ch : GoChan A) (r : Ref B) (w : World),
  ref_sel r (chan_close_upd tag ch w) = ref_sel r w.
Proof. intros. unfold chan_close_upd. apply ref_sel_chan_write_frame. Qed.
(* The CHECKED selector is framed through a channel close too (refs vs channel cells are independent) —
   the combined-state bridge needs it now [WHMatchC] tracks [ref_sel_opt] liveness. *)
Lemma ref_sel_opt_chan_close_upd : forall {A B} (tag : GoTypeTag A) (ch : GoChan A) (r : Ref B) (w : World),
  ref_sel_opt r (chan_close_upd tag ch w) = ref_sel_opt r w.
Proof. intros. unfold chan_close_upd. apply ref_sel_opt_chan_write_frame. Qed.
Lemma chan_closed_close_frame : forall {A} (tag : GoTypeTag A) (ch ch' : GoChan A) (w : World),
  ch <> ch' -> chan_closed ch' (chan_close_upd tag ch w) = chan_closed ch' w.
Proof.
  intros A tag ch ch' w Hne. unfold chan_close_upd, chan_closed.
  rewrite (chan_read_write_frame tag ch ch' _ _ _ w Hne). reflexivity.
Qed.
Lemma chan_closed_ref_upd : forall {A B} (r : Ref B) (v : B) (ch : GoChan A) (w : World),
  chan_closed ch (ref_upd r v w) = chan_closed ch w.
Proof. intros. unfold chan_closed, ref_upd, ref_install. destruct (ref_sel_opt r w); reflexivity. Qed.
(** A send/recv on one channel leaves a DIFFERENT channel's closedness untouched (the closed flag of the
    sent/recv'd channel is itself preserved — [chan_closed_send]/[chan_closed_recv] — so [WClosedMatch] is
    framed across every step). *)
Lemma chan_closed_send_frame : forall {A} (tag : GoTypeTag A) (ch ch' : GoChan A) (v : A) (w : World),
  ch <> ch' -> chan_closed ch' (chan_send_upd tag ch v w) = chan_closed ch' w.
Proof.
  intros A tag ch ch' v w Hne. unfold chan_send_upd, chan_closed.
  rewrite (chan_read_write_frame tag ch ch' _ _ _ w Hne). reflexivity.
Qed.
Lemma chan_closed_recv_frame : forall {A} (tag : GoTypeTag A) (ch ch' : GoChan A) (w : World),
  ch <> ch' -> chan_closed ch' (chan_recv_upd tag ch w) = chan_closed ch' w.
Proof.
  intros A tag ch ch' w Hne. unfold chan_recv_upd, chan_closed.
  rewrite (chan_read_write_frame tag ch ch' _ _ _ w Hne). reflexivity.
Qed.

(** Field read-after-write — a THEOREM: after [hfield_set h k tag v], reading field [k]
    returns [v] (from [ref_sel_upd_same]). *)
Lemma hfield_get_set_same : forall {A} (h : HStruct) (k : nat) (tag : GoTypeTag A) (v : A),
  bind (hfield_set h k tag v) (fun _ => hfield_get h k tag) =io=
  bind (hfield_set h k tag v) (fun _ => ret v).
Proof.
  intros. intro w.
  rewrite !run_bind.
  destruct (ref_sel_opt (hfield_cell h k tag) w) as [a|] eqn:Hsel.
  - rewrite !(run_hfield_set h k tag v a w Hsel). cbn.
    rewrite run_hfield_get, (ref_sel_opt_upd_same (hfield_cell h k tag) v a w Hsel). cbn. rewrite run_ret. reflexivity.
  - unfold hfield_set, run_io. rewrite Hsel. reflexivity.
Qed.

(** DIFFERENT fields are INDEPENDENT — writing field [k] does NOT change field [k']
    (distinct field CELLS), even when the fields have DIFFERENT types.  A THEOREM
    stated directly on the field INDICES [k ≠ k']: with [nat] field indices the
    index ⇒ location step ([hs_base + k ≠ hs_base + k']) is plain [Nat.add]
    cancellation, immediate by [lia]. *)
Lemma hfield_independent : forall {A B} (h : HStruct) (k k' : nat)
    (ta : GoTypeTag A) (tb : GoTypeTag B) (v : A) (w : World),
  k <> k' ->
  ref_sel (hfield_cell h k' tb) (ref_upd (hfield_cell h k ta) v w)
    = ref_sel (hfield_cell h k' tb) w.
Proof.
  intros A B h k k' ta tb v w Hne. apply ref_sel_upd_diff. cbn.
  intro He. apply Hne. lia.
Qed.

(** Two pointers to the SAME struct (same [base]) see each other's field writes — the
    aliasing a [*T] receiver relies on.  A THEOREM.  The written field cell of [h'] must be LIVE
    ([ref_sel_opt = Some]) — the guarded [ref_upd] writes only through a live cell (a real struct
    from [gsptr_new] has every field cell allocated). *)
Lemma hstruct_alias : forall {A} (h h' : HStruct) (k : nat) (tag : GoTypeTag A) (v a : A) (w : World),
  hs_base h = hs_base h' ->
  ref_sel_opt (hfield_cell h' k tag) w = Some a ->
  ref_sel (hfield_cell h k tag) (ref_upd (hfield_cell h' k tag) v w) = v.
Proof.
  intros A h h' k tag v a w Hb Hlive. unfold hfield_cell in *. rewrite Hb.
  exact (ref_sel_upd_same (mkRef (hs_base h' + k) tag) v a w Hlive).
Qed.

(** ---- Struct POINTERS: a heap-backed struct ↔ Go [*R] ----

    A [*R] is the [base] of the struct's field-cell bundle PLUS a [StructRep]
    — the per-record DATA (its field projections + constructor + the record eta law)
    that lets the generic ops DECOMPOSE a struct value into field cells and RECONSTRUCT
    it.  Coq has no generic record reflection, so [StructRep] is the one bit of
    per-struct data; it is DATA-only (the function fields are plain projections, NOT
    [GoTypeTag] — so it does NOT reintroduce the [tag_eq] wall).  [GSPtr R] carries
    only the heap base ([gsp_base]); the rep arrives at each op as the [StructRepOf R]
    dictionary, and the type parameter [R] survives extraction so the plugin can emit
    [*R].  Lowers: [GSPtr R] → [*R], [gsptr_new] → [&R{…}],
    [gsptr_deref] → [*p], [gsptr_assign] → [*p = R{…}], reusing the [Ptr] arms. *)

Local Transparent ref_sel ref_upd ref_install hfield_cell ref_sel_opt hfield_get run_io.

(** ============================================================================
    GENERIC STRUCT REPRESENTATION — one [StructRep R ts] for ALL field arities.

    The honest generalisation is
    the standard one: a struct is a HETEROGENEOUS NESTED PRODUCT [Tup ts] over its field-type list
    [ts : list Type], and a field is a TYPED de Bruijn INDEX [Mem ts t] ([MHere]/[MNext] = Peano
    [FZ]/[FS]).  ONE record [StructRep R ts] (an iso [R ≅ Tup ts]) covers every arity.

    Forged field indices are unrepresentable BY CONSTRUCTION: a field is the SINGLE typed index
    [m : Mem ts t]; its projection IS [mem_get m ∘ sr_to] and its slot IS [mem_depth m] — BOTH
    derived from [m], so there is no independent [proj] to disagree with the slot. *)

(** The canonical carrier: a right-nested product of the field types, ending in [unit]. *)
Fixpoint Tup (ts : list Type) : Type :=
  match ts with
  | nil       => unit
  | t :: rest => (t * Tup rest)%type
  end.

(** A typed de Bruijn index: [Mem ts t] witnesses that some field of [ts] has type [t]. *)
Inductive Mem : list Type -> Type -> Type :=
  | MHere : forall t rest, Mem (t :: rest) t
  | MNext : forall t s rest, Mem rest t -> Mem (s :: rest) t.
Arguments MHere {t rest}.
Arguments MNext {t s rest} _.

(** The projection [Tup ts -> t] a field index names — the canonical accessor for that field. *)
Fixpoint mem_get {ts t} (m : Mem ts t) : Tup ts -> t :=
  match m in Mem ts t return Tup ts -> t with
  | MHere      => fun tp => fst tp
  | MNext m'   => fun tp => mem_get m' (snd tp)
  end.

(** The field's SLOT — its position, the heap cell offset and the Go declared-field index. *)
Fixpoint mem_depth {ts t} (m : Mem ts t) : nat :=
  match m with
  | MHere    => 0
  | MNext m' => S (mem_depth m')
  end.

(** Per-field type tags, parallel to [Tup], so the typed heap cells can be read/written. *)
Fixpoint TagTup (ts : list Type) : Type :=
  match ts with
  | nil       => unit
  | t :: rest => (GoTypeTag t * TagTup rest)%type
  end.

Fixpoint mem_tag {ts t} (m : Mem ts t) : TagTup ts -> GoTypeTag t :=
  match m in Mem ts t return TagTup ts -> GoTypeTag t with
  | MHere      => fun tgs => fst tgs
  | MNext m'   => fun tgs => mem_tag m' (snd tgs)
  end.

(** The generic struct representation: the field tags + an iso to the canonical tuple. *)
Record StructRep (R : Type) (ts : list Type) : Type := mkSR {
  sr_tags : TagTup ts ;
  sr_to   : R -> Tup ts ;
  sr_from : Tup ts -> R ;
  sr_eta  : forall v, sr_from (sr_to v) = v ;
}.
Arguments mkSR {R ts} _ _ _ _.
Arguments sr_tags {R ts} _.  Arguments sr_to {R ts} _.
Arguments sr_from {R ts} _.  Arguments sr_eta {R ts} _ _.

(** The canonical rep is bound to the TYPE — [R] determines [srep_ts] (its field-type list) and the
    rep. *)
Class StructRepOf (R : Type) : Type := {
  srep_ts  : list Type ;
  srep_rep : StructRep R srep_ts ;
}.

(** A struct pointer — Go [*R].  Carries only its base (canonical rep, no per-handle data). *)
Record GSPtr (R : Type) := mkGSPtr { gsp_base : nat }.
Arguments mkGSPtr {R} _.
Arguments gsp_base {R} _.
Definition gsptr_hs {R} (p : GSPtr R) : HStruct := mkHStruct (gsp_base p).

(** FIELD access through the pointer.  The SLOT is the typed index [m] ([mem_depth m] cell, [mem_tag m]
    tag) — the model semantics depend ONLY on [m].  [proj] is a NAMING witness for the backend (the
    plugin emits [p.<proj's field>], the same [record_proj_field] map [x.Field] uses) and is PINNED to
    [m] by [gfield_coh]: [proj] must be EXACTLY the projection [m] denotes through the canonical rep
    ([mem_get m ∘ sr_to]).  So the slot and the named field CANNOT disagree — a mismatched [(m, proj)]
    has no [coh] witness.  [proj]/[coh] erase; the cell op is the substrate. *)
Definition gfield_coh {R t} `{StructRepOf R} (m : Mem srep_ts t) (proj : R -> t) : Prop :=
  proj = (fun v => mem_get m (sr_to srep_rep v)).
(** Receiver-FIRST ([p] before the index [m]): [p : GSPtr R] fixes [R] immediately, so the typed index
    [m : Mem srep_ts t] resolves against the right instance (with several structs in scope, [m]-first
    would force a premature, possibly-wrong [StructRepOf] choice). *)
Definition gsptr_get_field {R t} `{StructRepOf R} (p : GSPtr R) (m : Mem srep_ts t) (proj : R -> t)
    (coh : gfield_coh m proj) : IO t :=
  hfield_get (gsptr_hs p) (mem_depth m) (mem_tag m (sr_tags srep_rep)).
Definition gsptr_set_field {R t} `{StructRepOf R} (p : GSPtr R) (m : Mem srep_ts t) (proj : R -> t)
    (coh : gfield_coh m proj) (v : t) : IO unit :=
  hfield_set (gsptr_hs p) (mem_depth m) (mem_tag m (sr_tags srep_rep)) v.

(** Read-after-write THROUGH the pointer — a THEOREM, for ANY field, ANY arity: after writing field
    [m], reading [m] returns the written value.  Reduces to the same generic [hfield_get_set_same]. *)
Lemma gsptr_field_get_set : forall {R t} `{StructRepOf R} (p : GSPtr R) (m : Mem srep_ts t) (proj : R -> t)
    (coh : gfield_coh m proj) (v : t),
  bind (gsptr_set_field p m proj coh v) (fun _ => gsptr_get_field p m proj coh) =io=
  bind (gsptr_set_field p m proj coh v) (fun _ => ret v).
Proof. intros. unfold gsptr_set_field, gsptr_get_field. apply hfield_get_set_same. Qed.

(** Two handles to the SAME base see each other's writes to a field — the [*R]-receiver ALIASING.
    The written field cell must be LIVE (inherited from [hstruct_alias]). *)
Lemma gsptr_alias : forall {R t} `{StructRepOf R} (p q : GSPtr R) (m : Mem srep_ts t) (v a : t) (w : World),
  gsp_base p = gsp_base q ->
  ref_sel_opt (hfield_cell (gsptr_hs q) (mem_depth m) (mem_tag m (sr_tags srep_rep))) w = Some a ->
  ref_sel (hfield_cell (gsptr_hs p) (mem_depth m) (mem_tag m (sr_tags srep_rep)))
          (ref_upd (hfield_cell (gsptr_hs q) (mem_depth m) (mem_tag m (sr_tags srep_rep))) v w)
    = v.
Proof.
  intros R t Hrep p q m v a w Hb Hlive.
  apply (hstruct_alias (gsptr_hs p) (gsptr_hs q) (mem_depth m) (mem_tag m (sr_tags srep_rep)) v a w).
  - unfold gsptr_hs. cbn. exact Hb.
  - exact Hlive.
Qed.

(** WHOLE-STRUCT ops — [new]/[deref]/[assign].  Generic over arity: [write_fields]/[read_fields]
    recurse over the field-type list, writing/reading cells [k, k+1, …] with each field's tag. *)
Fixpoint write_fields (ts : list Type) (h : HStruct) (k : nat) : TagTup ts -> Tup ts -> IO unit :=
  match ts return TagTup ts -> Tup ts -> IO unit with
  | nil       => fun _ _ => ret tt
  | t :: rest => fun tgs vls =>
      bind (hfield_set h k (fst tgs) (fst vls)) (fun _ =>
            write_fields rest h (S k) (snd tgs) (snd vls))
  end.

Fixpoint read_fields (ts : list Type) (h : HStruct) (k : nat) : TagTup ts -> IO (Tup ts) :=
  match ts return TagTup ts -> IO (Tup ts) with
  | nil       => fun _ => ret tt
  | t :: rest => fun tgs =>
      bind (hfield_get h k (fst tgs)) (fun x =>
      bind (read_fields rest h (S k) (snd tgs)) (fun xs =>
      ret (x, xs)))
  end.

(** The pure world transformer the whole-struct write effects — used to characterise the post-write heap AND
    the initialiser [gsptr_new] runs.  It uses the ALLOCATOR install [ref_install] (unconditional), NOT the
    guarded [ref_upd]: [gsptr_new] CREATES the field cells here (they are absent in the freshly-bumped world),
    so the initialiser must install, not no-op.  On a heap where the fields are already LIVE, [ref_install]
    coincides with the guarded [ref_upd] ([ref_upd_live_eq]) — which is exactly what [run_write_fields] uses to
    relate the guarded public [write_fields] to this transformer. *)
Fixpoint wr_fields (ts : list Type) (h : HStruct) (k : nat) : TagTup ts -> Tup ts -> World -> World :=
  match ts return TagTup ts -> Tup ts -> World -> World with
  | nil       => fun _ _ w => w
  | t :: rest => fun tgs vls w =>
      wr_fields rest h (S k) (snd tgs) (snd vls)
                (ref_install (hfield_cell h k (fst tgs)) (fst vls) w)
  end.

Definition gsptr_new {R} `{StructRepOf R} (v : R) : IO (GSPtr R) :=
  fun w =>
    let l := w_next w in
    let p := mkGSPtr l in
    let wa := mkWorld (w_refs w) (w_chans w) (w_maps w) (l + List.length srep_ts) (w_output w) in
    ORet p (wr_fields srep_ts (gsptr_hs p) 0 (sr_tags srep_rep) (sr_to srep_rep v) wa).

(** [gsptr_deref] / [gsptr_assign] NIL-GUARD on [gsp_base p = 0] FIRST — a struct pointer is a pointer, so a nil
    deref/assign FAILS LOUD ([rt_nil_deref]) exactly like the scalar [Ptr] ops ([ptr_get_ok]/[ptr_set]) and like
    Go's generated [*p] / [*p = v], which panic on nil REGARDLESS of the pointee (a zero-size / zero-field type
    is no exception — the indirection still faults).  Without this guard an EMPTY struct (no field cells) would
    read/write a nil pointer as a silent no-op, contradicting Go.  For a nonempty struct a nil base ALSO makes
    the field cell absent, so the else-branch would fail loud too; the explicit guard is what covers the empty
    case uniformly.  Lowered by name ([*p] / [*p = v]); the guard branch is Go's own native nil panic. *)
Definition gsptr_deref {R} `{StructRepOf R} (p : GSPtr R) : IO R :=
  fun w => if Nat.eqb (gsp_base p) 0 then OPanic rt_nil_deref w
           else bind (read_fields srep_ts (gsptr_hs p) 0 (sr_tags srep_rep)) (fun tp => ret (sr_from srep_rep tp)) w.

Definition gsptr_assign {R} `{StructRepOf R} (p : GSPtr R) (v : R) : IO unit :=
  fun w => if Nat.eqb (gsp_base p) 0 then OPanic rt_nil_deref w
           else write_fields srep_ts (gsptr_hs p) 0 (sr_tags srep_rep) (sr_to srep_rep v) w.

(** Under a NON-nil base the guard collapses to the raw field read/write — the [run_*] laws below drive
    everything through these two, so the guard is dispatched once here. *)
Lemma run_gsptr_assign : forall {R} `{StructRepOf R} (p : GSPtr R) (v : R) (w : World),
  Nat.eqb (gsp_base p) 0 = false ->
  run_io (gsptr_assign p v) w = run_io (write_fields srep_ts (gsptr_hs p) 0 (sr_tags srep_rep) (sr_to srep_rep v)) w.
Proof. intros R Hrep p v w Hb. unfold gsptr_assign, run_io. rewrite Hb. reflexivity. Qed.
Lemma run_gsptr_deref : forall {R} `{StructRepOf R} (p : GSPtr R) (w : World),
  Nat.eqb (gsp_base p) 0 = false ->
  run_io (gsptr_deref p) w =
  run_io (bind (read_fields srep_ts (gsptr_hs p) 0 (sr_tags srep_rep)) (fun tp => ret (sr_from srep_rep tp))) w.
Proof. intros R Hrep p w Hb. unfold gsptr_deref, run_io. rewrite Hb. reflexivity. Qed.

(** A struct field cell's heap location is [base + slot] — extracted as a small lemma so the proofs
    below can reason about cell distinctness with [hfield_cell] kept opaque (so [cbn] won't expand it
    inside the [ref_sel_opt]/[ref_upd] redexes the [run_*] lemmas drive). *)
Lemma hfield_cell_loc : forall {A} (h : HStruct) (k : nat) (tag : GoTypeTag A),
  r_loc (hfield_cell h k tag) = hs_base h + k.
Proof. reflexivity. Qed.

(** Every field cell [k, k+1, …] of the struct is LIVE (allocated) in [w] — the precondition a whole-struct
    write needs now that [hfield_set] fails loud on a forged cell (a struct from [gsptr_new] satisfies it —
    the allocator writes each cell).  Distinct fields sit at distinct locations [hs_base + k'], so a write
    to one leaves the others' liveness intact ([fields_live_frame]). *)
Fixpoint fields_live (ts : list Type) (h : HStruct) (k : nat) : TagTup ts -> World -> Prop :=
  match ts return TagTup ts -> World -> Prop with
  | nil       => fun _ _ => True
  | t :: rest => fun tgs w =>
      (exists a, ref_sel_opt (hfield_cell h k (fst tgs)) w = Some a)
      /\ fields_live rest h (S k) (snd tgs) w
  end.
Lemma fields_live_frame : forall ts h j (tgs : TagTup ts) A (tag : GoTypeTag A) k v w,
  k < j -> fields_live ts h j tgs w -> fields_live ts h j tgs (ref_install (hfield_cell h k tag) v w).
Proof.
  induction ts as [ | t rest IH ]; intros h j tgs A tag k v w Hkj Hlive; cbn [fields_live] in *.
  - exact I.
  - destruct Hlive as [[a Ha] Hrest]. split.
    + exists a. rewrite ref_sel_opt_install_diff; [ exact Ha | rewrite !hfield_cell_loc; lia ].
    + apply (IH h (S j) (snd tgs) A tag k v w); [ lia | exact Hrest ].
Qed.

Local Opaque run_io bind ret hfield_get hfield_set ref_sel_opt ref_upd ref_install hfield_cell gsptr_assign gsptr_deref.

Lemma run_write_fields : forall ts h k tgs vls w,
  fields_live ts h k tgs w ->
  run_io (write_fields ts h k tgs vls) w = ORet tt (wr_fields ts h k tgs vls w).
Proof.
  induction ts as [ | t rest IH ]; intros h k tgs vls w Hlive; cbn [write_fields wr_fields fields_live] in *.
  - rewrite run_ret. reflexivity.
  - destruct Hlive as [[a Ha] Hrest].
    rewrite run_bind, (run_hfield_set h k (fst tgs) (fst vls) a w Ha). cbn.
    rewrite (ref_upd_live_eq (hfield_cell h k (fst tgs)) (fst vls) a w Ha).
    rewrite (IH h (S k) (snd tgs) (snd vls) (ref_install (hfield_cell h k (fst tgs)) (fst vls) w)
               (fields_live_frame rest h (S k) (snd tgs) t (fst tgs) k (fst vls) w (Nat.lt_succ_diag_r k) Hrest)).
    reflexivity.
Qed.

(** Writes at cells [≥ j] leave a cell [k < j] untouched — the field-independence frame. *)
Lemma wr_fields_frame : forall ts h j tgs vls A (tag : GoTypeTag A) k w,
  k < j -> ref_sel_opt (hfield_cell h k tag) (wr_fields ts h j tgs vls w)
         = ref_sel_opt (hfield_cell h k tag) w.
Proof.
  induction ts as [ | t rest IH ]; intros h j tgs vls A tag k w Hlt; cbn [wr_fields]; [ reflexivity | ].
  rewrite IH by lia.
  apply ref_sel_opt_install_diff. rewrite !hfield_cell_loc. lia.
Qed.

(** Reading the fields back from the post-write heap recovers exactly the written tuple — ANY arity. *)
Lemma read_after_wr : forall ts h k tgs vls w,
  run_io (read_fields ts h k tgs) (wr_fields ts h k tgs vls w)
    = ORet vls (wr_fields ts h k tgs vls w).
Proof.
  induction ts as [ | t rest IH ]; intros h k tgs vls w; cbn [read_fields wr_fields].
  - rewrite run_ret. destruct vls. reflexivity.
  - destruct tgs as [tg tgs']. destruct vls as [v0 vs]. cbn [fst snd].
    rewrite run_bind, run_hfield_get.
    rewrite (wr_fields_frame rest h (S k) tgs' vs _ tg k _ (Nat.lt_succ_diag_r k)).
    rewrite ref_sel_opt_install_same. cbn.
    rewrite run_bind, IH. cbn. rewrite run_ret. reflexivity.
Qed.

(** WHOLE-STRUCT round-trip — a THEOREM, ANY arity: after [assign v], [deref] reconstructs [v]
    EXACTLY ([read_after_wr] recovers the tuple, [sr_eta] reassembles the struct). *)
Lemma gsptr_deref_assign : forall {R} `{StructRepOf R} (p : GSPtr R) (v : R) (w : World),
  Nat.eqb (gsp_base p) 0 = false ->                            (* the pointer is NON-nil (else assign/deref FAIL LOUD) *)
  fields_live srep_ts (gsptr_hs p) 0 (sr_tags srep_rep) w ->   (* the struct's field cells are LIVE (from gsptr_new) *)
  run_io (bind (gsptr_assign p v) (fun _ => gsptr_deref p)) w =
  run_io (bind (gsptr_assign p v) (fun _ => ret v)) w.
Proof.
  intros R Hrep p v w Hb Hlive.
  rewrite !run_bind, !(run_gsptr_assign p v w Hb),
          !(run_write_fields srep_ts (gsptr_hs p) 0 (sr_tags srep_rep) (sr_to srep_rep v) w Hlive). cbn.
  rewrite (run_gsptr_deref p (wr_fields srep_ts (gsptr_hs p) 0 (sr_tags srep_rep) (sr_to srep_rep v) w) Hb).
  rewrite run_bind, read_after_wr. cbn.
  rewrite !run_ret, (sr_eta srep_rep v). reflexivity.
Qed.

Local Transparent run_io bind ret hfield_get hfield_set ref_sel_opt ref_upd ref_install hfield_cell.

(** LIVENESS from ALLOCATION: [wr_fields] (the transformer [gsptr_new] runs) makes EVERY field cell LIVE —
    so [fields_live] is a CONSEQUENCE of allocation, not an unforced precondition leaked to callers. *)
Lemma wr_fields_live : forall ts h k tgs vls w,
  fields_live ts h k tgs (wr_fields ts h k tgs vls w).
Proof.
  induction ts as [ | t rest IH ]; intros h k tgs vls w; cbn [wr_fields fields_live]; [ exact I | ].
  split.
  - exists (fst vls).
    rewrite (wr_fields_frame rest h (S k) (snd tgs) (snd vls) t (fst tgs) k
               (ref_install (hfield_cell h k (fst tgs)) (fst vls) w) (Nat.lt_succ_diag_r k)).
    apply ref_sel_opt_install_same.
  - apply IH.
Qed.
Lemma gsptr_new_fields_live : forall {R} `{StructRepOf R} (v0 : R) (w : World) p w1,
  run_io (gsptr_new v0) w = ORet p w1 ->
  fields_live srep_ts (gsptr_hs p) 0 (sr_tags srep_rep) w1.
Proof.
  intros R Hrep v0 w p w1 Hnew. unfold run_io, gsptr_new in Hnew. cbv zeta in Hnew.
  injection Hnew as Hp Hw1. subst p w1. apply wr_fields_live.
Qed.
(** [wr_fields] preserves [AllocFrontierOk]: it is a SEQUENCE of interior ref installs (each field cell sits in
    [(0, w_next)] — nonzero because the base is positive, below the frontier because the block [base+k ..
    base+k+len) was reserved under [w_next]), and [valid_ref_install_interior] handles each step. *)
Lemma valid_wr_fields : forall ts h k tgs vls w,
  AllocFrontierOk w -> (0 < hs_base h)%nat -> (hs_base h + k + length ts <= w_next w)%nat ->
  AllocFrontierOk (wr_fields ts h k tgs vls w).
Proof.
  induction ts as [| t rest IH]; intros h k tgs vls w HV Hbase Hfit; cbn [wr_fields length] in *.
  - exact HV.
  - apply IH.
    + apply valid_ref_install_interior; [ exact HV | rewrite hfield_cell_loc; lia | rewrite hfield_cell_loc; lia ].
    + exact Hbase.
    + unfold ref_install; cbn [w_next]; lia.
Qed.
(** [valid_run_gsptr_new] — the struct allocator is in the [AllocFrontierOk] preservation path (like
    [valid_run_ref_new] &c.): reserve the field block ([valid_bump]) then fill it ([valid_wr_fields]). *)
Corollary valid_run_gsptr_new : forall {R} `{StructRepOf R} (v : R) (w : World) p w1,
  AllocFrontierOk w -> run_io (gsptr_new v) w = ORet p w1 -> AllocFrontierOk w1.
Proof.
  intros R Hrep v w p w1 HV Hrun. unfold run_io, gsptr_new in Hrun. cbv zeta in Hrun.
  injection Hrun as Hp Hw1. subst p w1.
  apply valid_wr_fields.
  - exact (valid_bump w (List.length srep_ts) HV).
  - cbn [gsptr_hs gsp_base hs_base]. destruct HV as [Hpos _]. apply Nat.ltb_lt in Hpos. exact Hpos.
  - cbn [gsptr_hs gsp_base hs_base w_next]. lia.
Qed.
(** A [gsptr_new] pointer has a NONZERO base — it is minted at [w_next w], positive under [AllocFrontierOk]. *)
Lemma gsptr_new_base_nonzero : forall {R} `{StructRepOf R} (v0 : R) (w : World) p w1,
  AllocFrontierOk w -> run_io (gsptr_new v0) w = ORet p w1 -> Nat.eqb (gsp_base p) 0 = false.
Proof.
  intros R Hrep v0 w p w1 Hvw Hnew.
  unfold run_io, gsptr_new in Hnew. cbv zeta in Hnew. injection Hnew as Hp Hw1. subst p. cbn [gsp_base].
  apply Nat.eqb_neq. pose proof (valid_fresh_nonzero w Hvw) as Hnz. apply Nat.ltb_lt in Hnz. lia.
Qed.
(** LiveStruct — the aggregate peer for struct pointers: a NON-nil pointer ([gsp_base <> 0]) whose every field
    cell is LIVE.  The base-nonzero conjunct is BOTH necessary AND wired: [gsptr_deref]/[gsptr_assign] fail loud
    ([rt_nil_deref]) on a nil base (faithful to Go's [*p], which panics on nil for EVERY pointee incl. zero-size),
    and [gsptr_assign_live] below CONSUMES it (the assign RETURNS only because the base passes the guard AND the
    fields are live).  Unfolds to a nil-check plus the single struct authority [fields_live srep_ts (gsptr_hs p)
    0 (sr_tags srep_rep)] (a NAMED interface, not a second authority).  ⚠ For a ZERO-FIELD struct [fields_live
    nil] is trivially [True], so LiveStruct collapses to just the nil-check — which is EXACTLY right: an empty
    struct has no field memory, so the ONLY way its deref/assign can fail is a nil pointer, and the base-nonzero
    conjunct is precisely that precondition (it does NOT read "live" for a nil handle).  For a NONEMPTY struct the
    field liveness adds the genuine precondition (a nil/dangling field cell also makes [gsptr_deref] fail loud). *)
Definition LiveStruct {R} `{StructRepOf R} (p : GSPtr R) (w : World) : Prop :=
  Nat.eqb (gsp_base p) 0 = false /\ fields_live srep_ts (gsptr_hs p) 0 (sr_tags srep_rep) w.
Lemma gsptr_new_live : forall {R} `{StructRepOf R} (v0 : R) (w : World) p w1,
  AllocFrontierOk w -> run_io (gsptr_new v0) w = ORet p w1 -> LiveStruct p w1.
Proof.
  intros R Hrep v0 w p w1 Hvw Hnew. unfold LiveStruct. split.
  - exact (gsptr_new_base_nonzero v0 w p w1 Hvw Hnew).
  - exact (gsptr_new_fields_live v0 w p w1 Hnew).
Qed.
(** WIRING: a whole-struct assign to a [LiveStruct] pointer RETURNS ([ORet tt]) — BOTH conjuncts are consumed
    (base-nonzero clears the nil guard [run_gsptr_assign], fields-live makes the write return
    [run_write_fields]), so [LiveStruct] is the genuine precondition, not a free-floating predicate.  A nil
    pointer is EXCLUDED (it fails loud), so this never claims a nil deref/assign is safe. *)
Lemma gsptr_assign_live : forall {R} `{StructRepOf R} (p : GSPtr R) (v : R) (w : World),
  LiveStruct p w -> exists w', run_io (gsptr_assign p v) w = ORet tt w'.
Proof.
  intros R Hrep p v w [Hb Hlive]. eexists. rewrite (run_gsptr_assign p v w Hb).
  exact (run_write_fields srep_ts (gsptr_hs p) 0 (sr_tags srep_rep) (sr_to srep_rep v) w Hlive).
Qed.

(** Live* AGGREGATE-HANDLE SURFACE (manifest-gated, zero-axiom): the allocators produce the NAMED aggregate
    Live* predicate — the two slice makes give [LiveSlice] (well-formed [len <= cap] + whole [0, cap) backing
    live), with [LiveSlice_index_live] the payoff (an in-[len] index has a live typed cell); [gsptr_new] gives
    [LiveStruct] (non-nil pointer with all fields live; needs [AllocFrontierOk] for the nonzero base) — and
    [gsptr_assign_live] WIRES [LiveStruct] into the whole-struct semantics (a live struct's assign returns, BOTH
    conjuncts consumed: base-nonzero clears the nil guard, fields-live makes the write return; a nil pointer is
    excluded, never claimed safe).  Completes the reusable [Live*] family across all SIX handle types ([LiveRef]/
    [LivePtr]/[LiveChan]/[LiveMap] scalars in [live_handle_surface] + [LiveSlice]/[LiveStruct] here).  The
    underlying per-cell/fields facts stay in [heap_aggregate_liveness_surface]; this is their Live* face. *)
Definition live_aggregate_handle_surface :=
  (@slice_make_lc_live, @slice_make_h_live, @LiveSlice_index_live, @gsptr_new_live, @gsptr_assign_live).
Print Assumptions live_aggregate_handle_surface.
(** The FORCED whole-struct round-trip: from a pointer FRESH from [gsptr_new] (its cells provably LIVE),
    [assign] then [deref] recovers the value — [fields_live] is DISCHARGED by the allocation, not leaked. *)
Corollary gsptr_new_deref_assign : forall {R} `{StructRepOf R} (v0 v : R) (w : World) p w1,
  AllocFrontierOk w -> run_io (gsptr_new v0) w = ORet p w1 ->
  run_io (bind (gsptr_assign p v) (fun _ => gsptr_deref p)) w1 =
  run_io (bind (gsptr_assign p v) (fun _ => ret v)) w1.
Proof.
  intros R Hrep v0 v w p w1 Hvw Hnew.
  exact (gsptr_deref_assign p v w1 (gsptr_new_base_nonzero v0 w p w1 Hvw Hnew)
                                   (gsptr_new_fields_live v0 w p w1 Hnew)).
Qed.

(** STRUCT NO-PANIC (existence — the genuine struct no-panic peer, correct SHAPE): a whole-struct assign to a
    FRESH [gsptr_new] pointer definitely RETURNS ([exists w2, … = ORet tt w2], never [OPanic]) — [run_write_fields]
    on the allocation's LIVE fields ([gsptr_new_fields_live]).  Unlike [gsptr_new_deref_assign] (an equality),
    this is an existence of an [ORet] — the shape a no-panic claim requires. *)
Corollary gsptr_new_assign_no_panic : forall {R} `{StructRepOf R} (v0 v : R) (w : World) p w1,
  AllocFrontierOk w -> run_io (gsptr_new v0) w = ORet p w1 ->
  exists w2, run_io (gsptr_assign p v) w1 = ORet tt w2.
Proof.
  intros R Hrep v0 v w p w1 Hvw Hnew. eexists.
  rewrite (run_gsptr_assign p v w1 (gsptr_new_base_nonzero v0 w p w1 Hvw Hnew)).
  exact (run_write_fields srep_ts (gsptr_hs p) 0 (sr_tags srep_rep) (sr_to srep_rep v) w1
           (gsptr_new_fields_live v0 w p w1 Hnew)).
Qed.

(** AGGREGATE-HANDLE SURFACE (manifest-gated, zero-axiom PUBLIC evidence): companion to
    [heap_alloc_safety_surface] for the MULTI-CELL handles — a slice's backing and a struct's fields.
    LIVENESS (allocator produces a live cell — the checkpoint-58 "allocators produce Live*" fact, discharged
    from the allocation like [ref_new_reads]): [slice_make_lc_cell_live] (every [make([]T,len,cap)] backing
    cell, any [j < cap], reads [Some zero_val]); [slice_make_h_cell_live] (the len=cap [make([]T,n)] backing,
    any [j < len], reads [Some zero_val]); [gsptr_new_fields_live] (every [gsptr_new] field cell is live).
    STRUCT NO-PANIC (genuine, correct SHAPE = existence of an [ORet]): [gsptr_new_assign_no_panic] — a
    whole-struct assign to a fresh pointer definitely returns.  FIDELITY: [gsptr_new_deref_assign] —
    assign-then-deref RECOVERS THE VALUE (an EQUALITY, NOT a no-panic on its own).  SLICE NO-PANIC (existence,
    IN-BOUNDS-gated) for BOTH slice MAKE allocators — [slice_make_lc] ([make([]T,len,cap)]) via
    [slice_make_idx_get_no_panic]/[slice_make_idx_set_no_panic], and [slice_make_h] ([make([]T,n)], len=cap)
    via [slice_make_h_idx_get_no_panic]/[slice_make_h_idx_set_no_panic] — read/write a fresh slice at an
    in-bounds index returns; unlike the struct case these keep a genuine [slice_in_len] premise (Go panics on
    OOB — a real caller obligation, not a leaked derivable one), with the cell liveness discharged from the
    allocation.  SLICE INDEX REJECTION (the guard's OTHER direction, checkpoint-61): [slice_idx_{get,set}_bad_shape_rejected]
    — a malformed [cap < len] header FAIL-LOUDS ([exists p, = OPanic p w], no exported marker) BEFORE reaching a
    cell, so the SliceWF guard is pinned BOTH ways for the index ops, mirroring [slice_bulk_write_surface].
    SCOPE: the fresh-MAKE allocators ONLY; slice TRANSFORMERS ([subslice] aliases an existing backing,
    [slice_append] may grow) are a separate concern, NOT gated here.  For the make allocators the aggregate
    no-panic cone matches the scalar families (modulo the honest, Go-faithful bounds premise on slice indexing). *)
Definition heap_aggregate_liveness_surface :=
  (@slice_make_lc_cell_live, @gsptr_new_fields_live, @gsptr_new_assign_no_panic, @gsptr_new_deref_assign,
   @slice_make_idx_get_no_panic, @slice_make_idx_set_no_panic,
   @slice_make_h_cell_live, @slice_make_h_idx_get_no_panic, @slice_make_h_idx_set_no_panic,
   @slice_idx_get_bad_shape_rejected, @slice_idx_set_bad_shape_rejected).
Print Assumptions heap_aggregate_liveness_surface.

(** STRUCTURAL EQUALITY — Go's [==] on a struct compares fields pairwise.  Generic over arity: an
    [EqTup ts] is a per-field equality-test bundle; [tup_eqb] [&&]s them, and [gstruct_eqb] compares two
    [R] values through the rep.  When every field's test REFLECTS [=] ([EqTupOk]), so does the whole
    struct ([gstruct_eqb_true_iff]) — using [sr_to] injectivity (from the iso).  This is the model that
    the plugin lowers to [a == b]. *)
Fixpoint EqTup (ts : list Type) : Type :=
  match ts with
  | nil       => unit
  | t :: rest => ((t -> t -> bool) * EqTup rest)%type
  end.

Fixpoint tup_eqb (ts : list Type) : EqTup ts -> Tup ts -> Tup ts -> bool :=
  match ts return EqTup ts -> Tup ts -> Tup ts -> bool with
  | nil       => fun _ _ _ => true
  | t :: rest => fun eqs a b => andb (fst eqs (fst a) (fst b)) (tup_eqb rest (snd eqs) (snd a) (snd b))
  end.

Fixpoint EqTupOk (ts : list Type) : EqTup ts -> Prop :=
  match ts return EqTup ts -> Prop with
  | nil       => fun _ => True
  | t :: rest => fun eqs => (forall x y, fst eqs x y = true <-> x = y) /\ EqTupOk rest (snd eqs)
  end.

Lemma tup_eqb_true_iff : forall ts eqs a b, EqTupOk ts eqs -> (tup_eqb ts eqs a b = true <-> a = b).
Proof.
  induction ts as [ | t rest IH ]; intros eqs a b Hok.
  - cbn. destruct a, b. split; reflexivity.
  - destruct eqs as [eq0 eqs']. destruct a as [a0 a'], b as [b0 b']. destruct Hok as [Hok0 Hok'].
    cbn [tup_eqb fst snd]. split.
    + intros Hand. destruct (eq0 a0 b0) eqn:E0; cbn in Hand; [ | discriminate Hand ].
      apply Hok0 in E0. apply (IH eqs' a' b' Hok') in Hand. subst. reflexivity.
    + intros Heq. injection Heq as Ha0 Ha'. subst.
      assert (E0 : eq0 b0 b0 = true) by (apply Hok0; reflexivity).
      rewrite E0. cbn [andb]. rewrite (IH eqs' b' b' Hok'). reflexivity.
Qed.

Definition gstruct_eqb {R ts} (rep : StructRep R ts) (eqs : EqTup ts) (a b : R) : bool :=
  tup_eqb ts eqs (sr_to rep a) (sr_to rep b).

(** Build the per-field equality bundle straight from the field TAGS — [key_eqb] is the tag-indexed
    Go-comparable equality, so a struct of comparable fields gets its [EqTup] for free (no N-tuple of
    eqbs to write by hand).  [gstruct_eqb rep (eqs_of_tags …)] is the canonical struct [==]. *)
Fixpoint eqs_of_tags (ts : list Type) : TagTup ts -> EqTup ts :=
  match ts return TagTup ts -> EqTup ts with
  | nil       => fun _ => tt
  | t :: rest => fun tgs => (key_eqb (fst tgs), eqs_of_tags rest (snd tgs))
  end.

Lemma sr_to_inj : forall {R ts} (rep : StructRep R ts) a b, sr_to rep a = sr_to rep b -> a = b.
Proof. intros R ts rep a b H. rewrite <- (sr_eta rep a), <- (sr_eta rep b), H. reflexivity. Qed.

(** [struct_eqb] REFLECTS structural equality — Go [a == b] is [true] iff the structs are equal. *)
Lemma gstruct_eqb_true_iff : forall {R ts} (rep : StructRep R ts) (eqs : EqTup ts) a b,
  EqTupOk ts eqs -> (gstruct_eqb rep eqs a b = true <-> a = b).
Proof.
  intros R ts rep eqs a b Hok. unfold gstruct_eqb.
  rewrite (tup_eqb_true_iff ts eqs (sr_to rep a) (sr_to rep b) Hok).
  split; [ apply sr_to_inj | intros ->; reflexivity ].
Qed.
