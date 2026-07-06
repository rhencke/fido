(** ==================================================================================================
    GoHeap — the world's REF HEAP as Go's mutable memory: mutable local variables ([Ref]/[ref_new]/
    [ref_get]/[ref_set]), the [ValidWorld] allocation-freshness invariant (location 0 IS Go's nil,
    freshness/disjointness are THEOREMS), pointers ([Ptr]/[ptr_new]/[ptr_get]/[ptr_set]) and the
    address-of operator ([&x]), the CLOSED-WORLD nil-safety proofs (modeled nil panics are UNREACHABLE
    for allocated handles), slices as ALIASING HANDLES ([SliceH]: shared backing cells, [subslice] —
    the representation where Go aliasing is REAL, unlike GoSlice's pure single-goroutine lists), and
    heap-backed structs ([HStruct] field-cell bundles; the generic [StructRep]/[GSPtr] typed struct
    heap).  ONE module owns the ref-heap story; the map and channel heaps live in GoMap/GoChan.
    Mined out of the frozen builtins.v monolith (plans/builtins-split.md).
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

(** [ref_upd r v w]: write [v] (tagged with [r]'s own tag) at [r]'s location. *)
Definition ref_upd {A : Type} (r : Ref A) (v : A) (w : World) : World :=
  mkWorld (fun l => if Nat.eqb l (r_loc r)
                    then Some (existT _ A (r_tag r, v))
                    else w_refs w l)
          (w_chans w) (w_maps w) (w_next w) (w_output w).

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

(** ---- [ValidWorld]: allocation freshness as a MACHINE-CHECKED invariant ----

    Every allocator ([map_make]/[map_make_typed]/[make_chan]/[ref_new]) mints [l := w_next w] and bumps
    [w_next] to [l+1].  For "fresh" / "nonzero" / "disjoint" to be THEOREMS rather than comments we carry an
    invariant [ValidWorld]: the allocator pointer is positive (so location 0 is RESERVED — it is Go's [nil])
    AND it bounds the live region (every heap is [None] at and above [w_next]).  Two payoffs follow from the
    invariant ALONE (no side conditions): the next location is nonzero ([valid_fresh_nonzero] — a fresh
    pointer/chan/map is never nil) and is currently unallocated in all three heaps ([valid_fresh_disjoint] —
    a fresh allocation overwrites nothing).  The invariant holds at the initial world ([valid_w_init]) and is
    PRESERVED by every allocator ([valid_alloc_*]) UNCONDITIONALLY — locations are [nat], so the allocator
    counter never overflows. *)
Definition ValidWorld (w : World) : Prop :=
  (0 <? w_next w)%nat = true /\
  (forall l, (w_next w <=? l)%nat = true ->
     w_refs w l = None /\ w_chans w l = None /\ w_maps w l = None).

(** The initial world: empty heaps, allocator at 1 — so location 0 is reserved for [nil]. *)
Definition w_init : World := mkWorld (fun _ => None) (fun _ => None) (fun _ => None) 1 nil.

Lemma valid_w_init : ValidWorld w_init.
Proof.
  split.
  - now vm_compute.
  - intros l _. unfold w_init; cbn. repeat split; reflexivity.
Qed.

(** PAYOFF 1: the freshly minted location [w_next w] is nonzero — a fresh pointer/chan/map is never [nil]. *)
Lemma valid_fresh_nonzero : forall w, ValidWorld w -> (0 <? w_next w)%nat = true.
Proof. intros w [Hpos _]. exact Hpos. Qed.

(** PAYOFF 2: the freshly minted location is currently unallocated in ALL three heaps — so installing a
    cell there (what every allocator does) overwrites nothing; allocations never alias a live object. *)
Lemma valid_fresh_disjoint : forall w, ValidWorld w ->
  w_refs w (w_next w) = None /\ w_chans w (w_next w) = None /\ w_maps w (w_next w) = None.
Proof.
  intros w [_ Hfresh]. apply Hfresh. apply Nat.leb_le. lia.
Qed.

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

(** PRESERVATION: each allocator carries [ValidWorld] to the post-allocation world (unconditionally —
    [nat] locations never overflow, so no [HasRoom] side condition). *)
Lemma valid_alloc_ref : forall {A} (tag : GoTypeTag A) (v : A) (w : World),
  ValidWorld w ->
  ValidWorld (mkWorld
    (fun k => if Nat.eqb k (w_next w) then Some (existT _ A (tag, v)) else w_refs w k)
    (w_chans w) (w_maps w) (S (w_next w)) (w_output w)).
Proof.
  intros A tag v w HV. destruct HV as [Hpos Hfresh]. split.
  - cbn [w_next]. apply Nat.ltb_lt. lia.
  - intros l' Hle. cbn [w_next w_refs w_chans w_maps] in *.
    assert (Hle0 : (w_next w <=? l')%nat = true) by (apply (bump_le w l' Hle)).
    assert (Hneq : Nat.eqb l' (w_next w) = false) by (apply (bump_neq w l' Hle)).
    destruct (Hfresh l' Hle0) as [Hr [Hc Hm]].
    rewrite Hneq. repeat split; assumption.
Qed.

Lemma valid_alloc_chan : forall {A} (tag : GoTypeTag A) (cap : option nat) (w : World),
  ValidWorld w ->
  ValidWorld (mkWorld (w_refs w)
    (fun k => if Nat.eqb k (w_next w) then Some (existT _ A (tag, (nil, (false, cap)))) else w_chans w k)
    (w_maps w) (S (w_next w)) (w_output w)).
Proof.
  intros A tag cap w HV. destruct HV as [Hpos Hfresh]. split.
  - cbn [w_next]. apply Nat.ltb_lt. lia.
  - intros l' Hle. cbn [w_next w_refs w_chans w_maps] in *.
    assert (Hle0 : (w_next w <=? l')%nat = true) by (apply (bump_le w l' Hle)).
    assert (Hneq : Nat.eqb l' (w_next w) = false) by (apply (bump_neq w l' Hle)).
    destruct (Hfresh l' Hle0) as [Hr [Hc Hm]].
    rewrite Hneq. repeat split; assumption.
Qed.

Lemma valid_alloc_map_bump : forall (w : World),
  ValidWorld w ->
  ValidWorld (mkWorld (w_refs w) (w_chans w) (w_maps w) (S (w_next w)) (w_output w)).
Proof.
  intros w HV. destruct HV as [Hpos Hfresh]. split.
  - cbn [w_next]. apply Nat.ltb_lt. lia.
  - intros l' Hle. cbn [w_next w_refs w_chans w_maps] in *.
    apply Hfresh. apply (bump_le w l' Hle).
Qed.

Lemma valid_alloc_map_typed : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (w : World),
  ValidWorld w ->
  ValidWorld (mkWorld (w_refs w) (w_chans w)
    (fun k => if Nat.eqb k (w_next w)
              then Some (0, existT _ K (kt, existT _ V (vt, fun _ => None))) else w_maps w k)
    (S (w_next w)) (w_output w)).
Proof.
  intros K V kt vt w HV. destruct HV as [Hpos Hfresh]. split.
  - cbn [w_next]. apply Nat.ltb_lt. lia.
  - intros l' Hle. cbn [w_next w_refs w_chans w_maps] in *.
    assert (Hle0 : (w_next w <=? l')%nat = true) by (apply (bump_le w l' Hle)).
    assert (Hneq : Nat.eqb l' (w_next w) = false) by (apply (bump_neq w l' Hle)).
    destruct (Hfresh l' Hle0) as [Hr [Hc Hm]].
    rewrite Hneq. repeat split; assumption.
Qed.

(** The invariant is genuinely INDUCTIVE across the REAL allocator API (not just the world-shapes above):
    running any allocator on a valid world yields a valid world.  With [valid_w_init] this means
    EVERY world reachable by a finite allocation sequence is valid — so [valid_fresh_nonzero] /
    [valid_fresh_disjoint] apply at every allocation, making "fresh ⇒ nonzero ∧ disjoint" a theorem about
    [ref_new]/[make_chan]/[map_make]/[map_make_typed] BY NAME. *)
Corollary valid_run_ref_new : forall {A} (tag : GoTypeTag A) (v : A) (w : World) r w',
  ValidWorld w -> run_io (ref_new tag v) w = ORet r w' -> ValidWorld w'.
Proof.
  intros A tag v w r w' HV Hrun. unfold run_io, ref_new in Hrun. cbv zeta in Hrun.
  injection Hrun as _ Hw. subst w'. apply valid_alloc_ref; assumption.
Qed.

Corollary valid_run_make_chan : forall {A} (tag : GoTypeTag A) (w : World) r w',
  ValidWorld w -> run_io (make_chan tag) w = ORet r w' -> ValidWorld w'.
Proof.
  intros A tag w r w' HV Hrun. unfold run_io, make_chan, make_chan_cap in Hrun. cbv zeta in Hrun.
  injection Hrun as _ Hw. subst w'. apply valid_alloc_chan; assumption.
Qed.

Corollary valid_run_map_typed : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (w : World) r w',
  ValidWorld w -> run_io (map_make_typed kt vt) w = ORet r w' -> ValidWorld w'.
Proof.
  intros K V kt vt w r w' HV Hrun. unfold run_io, map_make_typed in Hrun. cbv zeta in Hrun.
  injection Hrun as _ Hw. subst w'. apply valid_alloc_map_typed; assumption.
Qed.

Corollary valid_run_map_make : forall {K V} (w : World) r w',
  ValidWorld w -> run_io (@map_make K V) w = ORet r w' -> ValidWorld w'.
Proof.
  intros K V w r w' HV Hrun. unfold run_io, map_make in Hrun.
  injection Hrun as _ Hw. subst w'. apply valid_alloc_map_bump; assumption.
Qed.

(* [ref_get] carries a [GoTypeTag] so that, when a read is bound inside a loop
   block, the lowering knows the Go type to hoist its declaration. *)
(** A CHECKED read.  [ref_sel] (above) is TOTAL — it returns the type's zero value when the
    cell is absent or carries the WRONG tag, which silently accepts a FORGED / dangling / retyped handle.
    [ref_sel_opt] instead returns [None] in those cases, so a reader can FAIL LOUD rather than fabricate a
    zero (the tenet: "mismatched/missing cells should be impossible in safe APIs, not silently
    zero-filled").  A genuinely allocated, correctly-typed cell still reads [Some] ([ref_sel_opt_upd_same]),
    so real programs are unaffected.  [ref_sel] stays for the pure proof/bridge layer. *)
Definition ref_sel_opt {A : Type} (r : Ref A) (w : World) : option A :=
  match w_refs w (r_loc r) with
  | Some (existT _ _ (tag0, x0)) => tag_coerce (r_tag r) tag0 x0
  | None => None
  end.
Lemma ref_sel_opt_upd_same : forall {A} (r : Ref A) (v : A) (w : World),
  ref_sel_opt r (ref_upd r v w) = Some v.
Proof.
  intros A r v w. unfold ref_sel_opt, ref_upd; cbn.
  rewrite (Nat.eqb_refl (r_loc r)); cbn. apply tag_coerce_refl.
Qed.
Lemma ref_sel_opt_upd_diff : forall {A B} (r : Ref A) (r' : Ref B) (v : B) (w : World),
  r_loc r <> r_loc r' -> ref_sel_opt r (ref_upd r' v w) = ref_sel_opt r w.
Proof.
  intros A B r r' v w Hne. unfold ref_sel_opt, ref_upd; cbn.
  rewrite (proj2 (Nat.eqb_neq (r_loc r) (r_loc r')) Hne). reflexivity.
Qed.

(** [ref_get] — FAILS LOUD on a missing/retyped cell: dereferencing a forged / dangling
    [Ref] (e.g. [mkRef 5 …] at an unallocated location) panics with the Go nil-pointer/invalid-address
    message instead of fabricating a zero.  Body is plugin-lowered to [*r], so the loud check never reaches
    the emitted Go (a real [r] is always allocated); it only rules out the model accepting a forged read. *)
Definition ref_get {A} (tag : GoTypeTag A) (r : Ref A) : IO A :=
  fun w => match ref_sel_opt r w with
           | Some a => ORet a w
           | None   => OPanic rt_nil_deref w
           end.
Definition ref_set {A} (r : Ref A) (v : A) : IO unit :=
  fun w => ORet tt (ref_upd r v w).
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
  run_io (ref_set r v) w = ORet tt (ref_upd r v w).
Proof. reflexivity. Qed.

(** Read-after-write at the STATE level: [ref_upd]
    tags the cell with [r]'s own tag, so the subsequent [ref_sel]'s [tag_coerce]
    is reflexive ([tag_coerce_refl]) and the location lookup hits ([eqb_refl]). *)
Lemma ref_sel_upd_same : forall {A} (r : Ref A) (v : A) (w : World),
  ref_sel r (ref_upd r v w) = v.
Proof.
  intros A r v w. unfold ref_sel, ref_upd. cbn.
  rewrite (Nat.eqb_refl (r_loc r)).
  rewrite tag_coerce_refl. reflexivity.
Qed.

(** Read-after-write — a THEOREM: after [ref_set r v], [ref_get] returns [v]. *)
Lemma ref_get_set_same : forall {A} (tag : GoTypeTag A) (r : Ref A) (v : A),
  bind (ref_set r v) (fun _ => ref_get tag r) =io=
  bind (ref_set r v) (fun _ => ret v).
Proof.
  intros. intro w.
  rewrite !run_bind, !run_ref_set. cbn.
  rewrite run_ref_get, ref_sel_opt_upd_same. cbn. rewrite run_ret. reflexivity.
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
    nil sentinel is location 0, which [ValidWorld] RESERVES (no allocation ever returns it),
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
Definition ptr_set {A} (tag : GoTypeTag A) (p : Ptr A) (v : A) : IO unit :=
  fun w => if Nat.eqb (p_loc p) 0 then OPanic rt_nil_deref w
           else ORet tt (ref_upd (ptr_as_ref tag p) v w).
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
    else ORet tt (ref_upd (ptr_as_ref tag p) v w).
Proof. reflexivity. Qed.

(** Faithfulness: dereferencing / assigning through a NIL pointer PANICS, exactly as Go's [*nil]. *)
Lemma ptr_get_nil : forall {A} (tag : GoTypeTag A) (w : World),
  run_io (ptr_get tag (ptr_nil tag)) w = OPanic rt_nil_deref w.
Proof. reflexivity. Qed.
Lemma ptr_set_nil : forall {A} (tag : GoTypeTag A) (v : A) (w : World),
  run_io (ptr_set tag (ptr_nil tag) v) w = OPanic rt_nil_deref w.
Proof. reflexivity. Qed.

(** Read-after-write THROUGH a pointer — a THEOREM (inherited from the shared heap): after
    [ptr_set tag p v], [ptr_get tag p] returns [v].  Holds for ALL [p]: on a nil pointer BOTH sides
    panic at the [ptr_set] step (so they agree), and on a live pointer the read observes the write. *)
Lemma ptr_get_set_same : forall {A} (tag : GoTypeTag A) (p : Ptr A) (v : A),
  bind (ptr_set tag p v) (fun _ => ptr_get tag p) =io=
  bind (ptr_set tag p v) (fun _ => ret v).
Proof.
  intros. intro w.
  rewrite !run_bind, !run_ptr_set.
  destruct (Nat.eqb (p_loc p) 0) eqn:Hnil.
  - reflexivity.
  - cbn. rewrite run_ptr_get, Hnil. cbn. rewrite ref_sel_opt_upd_same. cbn. rewrite run_ret. reflexivity.
Qed.

(** ---- [&x]: the ADDRESS-OF operator (Go's `&`) — the missing inverse of [ptr_as_ref] ----

    Taking the address of a local variable [x] (a [Ref A]) yields a [*T] ([Ptr A]) aliasing x's cell.
    A [Ref] and a [Ptr] share the SAME [w_refs] heap (a [Ref] is a Go local, a [Ptr] its `*T` handle), so
    [&x] is simply the [Ref]'s location wrapped as a (tag-free) [Ptr] — [ptr_as_ref]'s inverse.  KEY SAFETY
    PROPERTY: a [Ref] always lives at a NONZERO location ([ValidWorld] reserves 0 for nil), so
    [&x] is NEVER nil; dereferencing it therefore never panics.  Taking an address is ALWAYS safe (unlike a
    raw [*T], which may be nil).  Read/write THROUGH [&x] alias [x] — the defining pointer behaviour —
    inherited from the shared heap, no new axiom. *)
Definition ref_as_ptr {A} (r : Ref A) : Ptr A := mkPtr (r_loc r).

Lemma ref_as_ptr_loc : forall {A} (r : Ref A), p_loc (ref_as_ptr r) = r_loc r.
Proof. reflexivity. Qed.

(* Viewing [&x] back as a [Ref] (with x's own tag) recovers [x] exactly — same location, same tag. *)
Lemma ptr_as_ref_of_ref_as_ptr : forall {A} (r : Ref A),
  ptr_as_ref (r_tag r) (ref_as_ptr r) = r.
Proof. intros A [l tag]. reflexivity. Qed.

(* [&x] is never nil (a [Ref]'s location is nonzero), so it is SAFE to dereference — never panics. *)
Lemma ref_as_ptr_not_nil : forall {A} (r : Ref A),
  r_loc r <> 0 -> p_loc (ref_as_ptr r) <> 0.
Proof. intros A r Hnz. rewrite ref_as_ptr_loc. exact Hnz. Qed.

(* READ through [&x]: [*(&x)] reads [x]'s value (with x's tag) and NEVER panics. *)
Lemma ptr_get_ref_as_ptr : forall {A} (r : Ref A) (a : A) (w : World),
  r_loc r <> 0 ->
  ref_sel_opt r w = Some a ->
  run_io (ptr_get (r_tag r) (ref_as_ptr r)) w = ORet a w.
Proof.
  intros A r a w Hnz Hpres. rewrite run_ptr_get, ref_as_ptr_loc.
  rewrite (proj2 (Nat.eqb_neq (r_loc r) 0) Hnz).
  rewrite ptr_as_ref_of_ref_as_ptr, Hpres. reflexivity.
Qed.

(* WRITE through [&x]: [*(&x) = v] updates [x]'s OWN cell and never panics. *)
Lemma ptr_set_ref_as_ptr : forall {A} (r : Ref A) (v : A) (w : World),
  r_loc r <> 0 ->
  run_io (ptr_set (r_tag r) (ref_as_ptr r) v) w = ORet tt (ref_upd r v w).
Proof.
  intros A r v w Hnz. rewrite run_ptr_set, ref_as_ptr_loc.
  rewrite (proj2 (Nat.eqb_neq (r_loc r) 0) Hnz).
  rewrite ptr_as_ref_of_ref_as_ptr. reflexivity.
Qed.

(* THE DEFINING ALIAS: writing through [&x] is visible at [x] — [*(&x) = v], then [x] reads back [v].
   This is the whole point of taking an address: the pointer and the variable share one cell. *)
Theorem ptr_set_ref_as_ptr_aliases : forall {A} (r : Ref A) (v : A) (w : World),
  r_loc r <> 0 ->
  exists w', run_io (ptr_set (r_tag r) (ref_as_ptr r) v) w = ORet tt w' /\ ref_sel r w' = v.
Proof.
  intros A r v w Hnz. exists (ref_upd r v w). split.
  - exact (ptr_set_ref_as_ptr r v w Hnz).
  - apply ref_sel_upd_same.
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
  ValidWorld w -> run_io (ptr_new tag v) w = ORet p w' -> Nat.eqb (p_loc p) 0 = false.
Proof.
  intros A tag v w p w' HV Hrun. unfold run_io, ptr_new in Hrun. cbv zeta in Hrun.
  injection Hrun as Hp _. subst p. cbn [p_loc]. apply pos_neq0, (valid_fresh_nonzero w HV).
Qed.

(** On a non-nil pointer the panic branch is DEAD — deref/assign just hit the heap. *)
Lemma ptr_set_nonnil : forall {A} (tag : GoTypeTag A) (p : Ptr A) (v : A) (w : World),
  Nat.eqb (p_loc p) 0 = false ->
  run_io (ptr_set tag p v) w = ORet tt (ref_upd (ptr_as_ref tag p) v w).
Proof. intros A tag p v w Hnn. rewrite run_ptr_set, Hnn. reflexivity. Qed.
Lemma ptr_get_nonnil : forall {A} (tag : GoTypeTag A) (p : Ptr A) (a : A) (w : World),
  Nat.eqb (p_loc p) 0 = false ->
  ref_sel_opt (ptr_as_ref tag p) w = Some a ->
  run_io (ptr_get tag p) w = ORet a w.
Proof. intros A tag p a w Hnn Hpres. rewrite run_ptr_get, Hnn, Hpres. reflexivity. Qed.

(** CLOSED-WORLD GUARANTEE: allocate a pointer, then assign through it — provably NO panic. *)
Corollary ptr_alloc_assign_no_panic : forall {A} (tag : GoTypeTag A) (v v' : A) (w : World) p w',
  ValidWorld w -> run_io (ptr_new tag v) w = ORet p w' ->
  exists w'', run_io (ptr_set tag p v') w' = ORet tt w''.
Proof.
  intros A tag v v' w p w' HV Hrun. eexists.
  apply ptr_set_nonnil, (ptr_new_nonzero tag v w p w' HV Hrun).
Qed.

(** The map analogues: an allocated map is non-nil, so [map_set] on it never panics. *)
Lemma map_make_typed_nonzero : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (w : World) m w',
  ValidWorld w -> run_io (map_make_typed kt vt) w = ORet m w' -> Nat.eqb (gm_loc m) 0 = false.
Proof.
  intros K V kt vt w m w' HV Hrun. unfold run_io, map_make_typed in Hrun. cbv zeta in Hrun.
  injection Hrun as Hm _. subst m. cbn [gm_loc]. apply pos_neq0, (valid_fresh_nonzero w HV).
Qed.
Lemma map_set_nonnil : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (v : V) (m : GoMap K V) (w : World),
  Nat.eqb (gm_loc m) 0 = false ->
  run_io (map_set kt vt k v m) w = ORet tt (map_upd kt vt k v m w).
Proof. intros K V kt vt k v m w Hnn. rewrite run_map_set, Hnn. reflexivity. Qed.
Corollary map_alloc_set_no_panic : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (v : V) (w : World) m w',
  ValidWorld w -> run_io (map_make_typed kt vt) w = ORet m w' ->
  exists w'', run_io (map_set kt vt k v m) w' = ORet tt w''.
Proof.
  intros K V kt vt k v w m w' HV Hrun. eexists.
  apply map_set_nonnil, (map_make_typed_nonzero kt vt w m w' HV Hrun).
Qed.

(** Channel analogue: an ALLOCATED channel is non-nil ([make_chan] mints the pre-bump [w_next], nonzero by
    [valid_fresh_nonzero]), so [close] on it never hits the nil panic.  [chan_alloc_close_no_panic] is the guarantee
    (the remaining [close] panic — double-close — is the send-on-closed class, gated separately by
    [chan_closed]).  [send]/[recv] on the same allocated channel likewise never hit the nil case. *)
Lemma make_chan_nonzero : forall {A} (tag : GoTypeTag A) (w : World) ch w',
  ValidWorld w -> run_io (make_chan tag) w = ORet ch w' -> Nat.eqb (ch_loc ch) 0 = false.
Proof.
  intros A tag w ch w' HV Hrun. unfold run_io, make_chan in Hrun. cbv zeta in Hrun.
  injection Hrun as Hc _. subst ch. cbn [ch_loc]. apply pos_neq0, (valid_fresh_nonzero w HV).
Qed.
Corollary chan_alloc_close_no_panic : forall {A} (tag : GoTypeTag A) (w : World) ch w',
  ValidWorld w -> run_io (make_chan tag) w = ORet ch w' -> chan_closed ch w' = false ->
  exists w'', run_io (close_chan tag ch) w' = ORet tt w''.
Proof.
  intros A tag w ch w' HV Hrun Hcl. eexists.
  apply run_close; [ apply (make_chan_nonzero tag w ch w' HV Hrun) | exact Hcl ].
Qed.

(** ALIASING — the defining pointer property, a THEOREM: two pointers at the SAME
    location ([p] and a copy [q]) see each other's writes.  A write through [q] is
    observed by a read through [p] — impossible for a non-aliasing [Ref] var. *)
Lemma ptr_alias : forall {A} (tag : GoTypeTag A) (p q : Ptr A) (v : A) (w : World),
  p_loc p = p_loc q ->
  ref_sel (ptr_as_ref tag p) (ref_upd (ptr_as_ref tag q) v w) = v.
Proof.
  intros A tag p q v w Hl.
  unfold ptr_as_ref. rewrite Hl.
  apply (ref_sel_upd_same (mkRef (p_loc q) tag) v w).
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

(** A pointer from [ptr_new] is NON-nil AND its cell is allocated at [p]'s own tag, so [ref_sel_opt] hits
    [Some] and [ptr_get_ok] reads through it ([ok = true]) returning the stored value: safe deref of a live
    pointer.  (A forged / retyped non-nil handle — [ref_sel_opt = None] — instead FAILS LOUD
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
Definition slice_idx_get {A} (tag : GoTypeTag A) (s : SliceH A) (i : GoInt) : IO A :=
  fun w => if slice_in_len s i
           then match ref_sel_opt (sh_cell s (Z.to_nat (intraw i))) w with
                | Some a => ORet a w
                | None   => OPanic rt_nil_deref w
                end
           else OPanic (rt_index_oob (intraw i) (sh_len s)) w.
Definition slice_idx_set {A} (s : SliceH A) (i : GoInt) (v : A) : IO unit :=
  fun w => if slice_in_len s i then ORet tt (ref_upd (sh_cell s (Z.to_nat (intraw i))) v w)
           else OPanic (rt_index_oob (intraw i) (sh_len s)) w.
Lemma run_slice_idx_get : forall {A} (tag : GoTypeTag A) (s : SliceH A) (i : GoInt) (a : A) (w : World),
  slice_in_len s i = true ->
  ref_sel_opt (sh_cell s (Z.to_nat (intraw i))) w = Some a ->
  run_io (slice_idx_get tag s i) w = ORet a w.
Proof. intros A tag s i a w Hi Hsel. unfold slice_idx_get, run_io. rewrite Hi, Hsel. reflexivity. Qed.
Lemma run_slice_idx_set : forall {A} (s : SliceH A) (i : GoInt) (v : A) (w : World),
  slice_in_len s i = true ->
  run_io (slice_idx_set s i v) w = ORet tt (ref_upd (sh_cell s (Z.to_nat (intraw i))) v w).
Proof. intros A s i v w Hi. unfold slice_idx_set, run_io. rewrite Hi. reflexivity. Qed.
(** Out of range is a PANIC, exactly Go: writing at index = len ('s len=1,cap=2,
    write index 1 witness) is rejected, not silently aimed at the spare capacity cell. *)
Lemma run_slice_idx_set_oob : forall {A} (s : SliceH A) (i : GoInt) (v : A) (w : World),
  slice_in_len s i = false ->
  run_io (slice_idx_set s i v) w = OPanic (rt_index_oob (intraw i) (sh_len s)) w.
Proof. intros A s i v w Hi. unfold slice_idx_set, run_io. rewrite Hi. reflexivity. Qed.
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
   [s[a:b]] performs the SAME check, so the lowering (a `:=` binding) is faithful. *)
Definition subslice_inb {A} (s : SliceH A) (a b : GoInt) : bool :=
  (Z.leb 0 (intraw a) && Z.leb (intraw a) (intraw b) && Z.leb (intraw b) (Z.of_nat (sh_cap s)))%bool.
Definition subslice {A} (s : SliceH A) (a b : GoInt) : IO (SliceH A) :=
  fun w => if subslice_inb s a b
           then ORet (subslice_desc s (Z.to_nat (intraw a)) (Z.to_nat (intraw b))) w
           else OPanic rt_slice_bounds w.
Lemma run_subslice : forall {A} (s : SliceH A) (a b : GoInt) (w : World),
  subslice_inb s a b = true ->
  run_io (subslice s a b) w = ORet (subslice_desc s (Z.to_nat (intraw a)) (Z.to_nat (intraw b))) w.
Proof. intros A s a b w H. unfold subslice, run_io. rewrite H. reflexivity. Qed.

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
Lemma subslice_alias : forall {A} (s : SliceH A) (a b j : nat) (v : A) (w : World),
  ref_sel (sh_cell s (a + j))
          (ref_upd (sh_cell (subslice_desc s a b) j) v w) = v.
Proof.
  intros A s a b j v w. rewrite subslice_shares_cell. apply ref_sel_upd_same.
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
  intros A B s s' i j v w Hne. unfold ref_sel, ref_upd, sh_cell. cbn [r_loc r_tag w_refs].
  destruct (Nat.eqb (sh_loc s' j) (sh_loc s i)) eqn:E; [|reflexivity].
  apply Nat.eqb_eq in E. exfalso. apply Hne. symmetry. exact E.
Qed.

(** Read-after-write at an index — a THEOREM (from the shared heap). *)
Lemma slice_idx_get_set_same : forall {A} (tag : GoTypeTag A) (s : SliceH A) (i : GoInt) (v : A),
  slice_in_len s i = true ->
  bind (slice_idx_set s i v) (fun _ => slice_idx_get tag s i) =io=
  bind (slice_idx_set s i v) (fun _ => ret v).
Proof.
  intros A tag s i v Hi. intro w.
  rewrite !run_bind, !(run_slice_idx_set s i v w Hi). cbn.
  rewrite (run_slice_idx_get tag s i v (ref_upd (sh_cell s (Z.to_nat (intraw i))) v w) Hi
             (ref_sel_opt_upd_same (sh_cell s (Z.to_nat (intraw i))) v w)), run_ret.
  reflexivity.
Qed.

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
    then (* in place: write index len, len+1, SAME base/off/cap *)
      ORet (mkSliceH (sh_base s) (sh_off s) (S (sh_len s)) (sh_cap s) tag)
           (ref_upd (sh_cell s (sh_len s)) v w)
    else (* reallocate: fresh disjoint backing of len+1, copy old, append v *)
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
              (w_chans w) (w_maps w) (base' + S n) (w_output w)).

(** WITHIN-cap append is IN PLACE: it updates exactly [s]'s cell at index [len], so the
    new element is written into the SHARED backing — a THEOREM.  (Reading [result[len]]
    or [parent[off+len]] sees [v].) *)
Lemma slice_append_incap : forall {A} (tag : GoTypeTag A) (s : SliceH A) (v : A) (w : World),
  (sh_len s <? sh_cap s)%nat = true ->
  run_io (slice_append tag s v) w
    = ORet (mkSliceH (sh_base s) (sh_off s) (S (sh_len s)) (sh_cap s) tag)
           (ref_upd (sh_cell s (sh_len s)) v w).
Proof. intros A tag s v w Hlt. unfold slice_append, run_io. rewrite Hlt. reflexivity. Qed.

(** ...and that in-place write is OBSERVED through the parent backing: reading the cell
    at index [len] after the append returns [v] (the appended element aliases). *)
Lemma slice_append_incap_aliases : forall {A} (tag : GoTypeTag A) (s : SliceH A) (v : A) (w : World),
  (sh_len s <? sh_cap s)%nat = true ->
  ref_sel (sh_cell s (sh_len s))
          (match run_io (slice_append tag s v) w with ORet _ w' => w' | OPanic _ w' => w' end) = v.
Proof.
  intros A tag s v w Hlt. rewrite slice_append_incap by exact Hlt. cbn.
  apply ref_sel_upd_same.
Qed.

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

(** A [make([]T, len, cap)] slice has spare capacity, so [append] is IN PLACE and the
    result SHARES its backing — a THEOREM directly from [slice_append_incap]: the append
    writes the cell at index [len] of the ORIGINAL handle. *)
Lemma make_lc_append_inplace : forall {A} (tag : GoTypeTag A) (len cap : GoInt) (v : A) (w : World),
  (intraw len <? intraw cap)%Z = true ->
  forall s w0, run_io (slice_make_lc tag len cap) w = ORet s w0 ->
  run_io (slice_append tag s v) w0
    = ORet (mkSliceH (sh_base s) (sh_off s) (S (sh_len s)) (sh_cap s) tag)
           (ref_upd (sh_cell s (sh_len s)) v w0).
Proof.
  intros A tag len cap v w Hlt s w0 Hmk.
  (* the handle from make_lc has sh_len = Z.to_nat len, sh_cap = Z.to_nat cap, so len < cap ⇒ in place.
     make_lc now PANICS unless 0 <= len <= cap; the success hypothesis Hmk forces that branch. *)
  unfold slice_make_lc, run_io in Hmk.
  destruct (Z.leb 0 (intraw len) && Z.leb (intraw len) (intraw cap))%bool eqn:Hc.
  - injection Hmk as Hs _. subst s. apply slice_append_incap. cbn [sh_len sh_cap].
    apply Nat.ltb_lt. apply andb_prop in Hc. destruct Hc as [Hc0 Hc1].
    apply Z.leb_le in Hc0. apply Z.leb_le in Hc1. apply Z.ltb_lt in Hlt. lia.
  - discriminate Hmk.
Qed.

(* Element [i]'s cell is [sh_start s + i] (= [sh_loc s i] by [add_assoc]); the
   clear/copy ranges are the interval [[sh_start s, sh_start s + len)]. *)
Definition sh_start {A} (s : SliceH A) : nat := sh_base s + sh_off s.

(** [clear(s)] (Go 1.21): zero [s]'s [len] elements.  A single declarative
    heap update — the cells in [s]'s range map to the zero value, the rest unchanged. *)
Definition slice_clear_h {A} (tag : GoTypeTag A) (s : SliceH A) : IO unit :=
  fun w => ORet tt
    (mkWorld (fun k => if (Nat.leb (sh_start s) k
                           && Nat.ltb k (sh_start s + sh_len s))%bool
                       then Some (existT _ A (tag, zero_val tag))
                       else w_refs w k)
             (w_chans w) (w_maps w) (w_next w) (w_output w)).

(** [copy(dst, src)]: copy [min(len dst, len src)] elements [src → dst],
    return the count (a Go [int], so the [nat] count is widened to a [GoInt]).  A single
    declarative heap update — each [dst] cell in range takes the corresponding [src] value
    ([src]'s cell at the same relative index). *)
Definition slice_copy {A} (tag : GoTypeTag A) (dst src : SliceH A) : IO GoInt :=
  fun w => let n := if Nat.leb (sh_len dst) (sh_len src) then sh_len dst else sh_len src in
           ORet (intwrap (Z.of_nat n))
    (mkWorld (fun k => if (Nat.leb (sh_start dst) k
                           && Nat.ltb k (sh_start dst + n))%bool
                       then Some (existT _ A
                              (tag, ref_sel (mkRef (sh_start src + (k - sh_start dst))
                                                   (sh_tag src)) w))
                       else w_refs w k)
             (w_chans w) (w_maps w) (w_next w) (w_output w)).

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
    the emitted Go (a real [p] is always allocated); it only rules out the model accepting a forged read. *)
Definition hfield_get {A} (h : HStruct) (k : nat) (tag : GoTypeTag A) : IO A :=
  fun w => match ref_sel_opt (hfield_cell h k tag) w with
           | Some a => ORet a w
           | None   => OPanic rt_nil_deref w
           end.
Definition hfield_set {A} (h : HStruct) (k : nat) (tag : GoTypeTag A) (v : A) : IO unit :=
  fun w => ORet tt (ref_upd (hfield_cell h k tag) v w).
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
Lemma run_hfield_set : forall {A} (h : HStruct) (k : nat) (tag : GoTypeTag A) (v : A) (w : World),
  run_io (hfield_set h k tag v) w = ORet tt (ref_upd (hfield_cell h k tag) v w).
Proof. reflexivity. Qed.

(** A [ref_sel] at a DIFFERENT location is unaffected by a [ref_upd] — the foundation
    for field INDEPENDENCE (writing one field leaves the others alone). *)
Lemma ref_sel_upd_diff : forall {A B} (r : Ref A) (r' : Ref B) (v : A) (w : World),
  r_loc r <> r_loc r' -> ref_sel r' (ref_upd r v w) = ref_sel r' w.
Proof.
  intros A B r r' v w Hne. unfold ref_sel, ref_upd. cbn.
  destruct (Nat.eqb (r_loc r') (r_loc r)) eqn:E; [|reflexivity].
  apply Nat.eqb_eq in E. congruence.
Qed.

(** CROSS-RESOURCE separation: the [World]'s ref-heap and channel-heap are INDEPENDENT components
    ([w_refs] vs [w_chans]), so a CHANNEL op leaves every ref untouched and a REF op leaves every
    channel untouched.  These let a single [run_io] world match BOTH the calculus's channel AND heap
    state at once (the combined state refinement). *)
Lemma ref_sel_chan_write_frame : forall {A B} (tag : GoTypeTag A) (ch : GoChan A) buf cl cap (r : Ref B) (w : World),
  ref_sel r (chan_write tag ch buf cl cap w) = ref_sel r w.
Proof. intros. unfold ref_sel, chan_write. reflexivity. Qed.

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
Proof. intros. unfold ref_sel_opt, chan_write. reflexivity. Qed.
Lemma ref_sel_opt_chan_send_upd : forall {A B} (tag : GoTypeTag A) (ch : GoChan A) (v : A) (r : Ref B) (w : World),
  ref_sel_opt r (chan_send_upd tag ch v w) = ref_sel_opt r w.
Proof. intros. unfold chan_send_upd. apply ref_sel_opt_chan_write_frame. Qed.
Lemma ref_sel_opt_chan_recv_upd : forall {A B} (tag : GoTypeTag A) (ch : GoChan A) (r : Ref B) (w : World),
  ref_sel_opt r (chan_recv_upd tag ch w) = ref_sel_opt r w.
Proof. intros. unfold chan_recv_upd. apply ref_sel_opt_chan_write_frame. Qed.

Lemma chan_buf_ref_upd_frame : forall {A B} (tag : GoTypeTag A) (ch : GoChan A) (r : Ref B) (v : B) (w : World),
  chan_buf tag ch (ref_upd r v w) = chan_buf tag ch w.
Proof. intros. unfold chan_buf, ref_upd. reflexivity. Qed.

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
Lemma chan_closed_close_frame : forall {A} (tag : GoTypeTag A) (ch ch' : GoChan A) (w : World),
  ch <> ch' -> chan_closed ch' (chan_close_upd tag ch w) = chan_closed ch' w.
Proof.
  intros A tag ch ch' w Hne. unfold chan_close_upd, chan_closed.
  rewrite (chan_read_write_frame tag ch ch' _ _ _ w Hne). reflexivity.
Qed.
Lemma chan_closed_ref_upd : forall {A B} (r : Ref B) (v : B) (ch : GoChan A) (w : World),
  chan_closed ch (ref_upd r v w) = chan_closed ch w.
Proof. intros. unfold chan_closed, ref_upd. reflexivity. Qed.
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
  rewrite !run_bind, run_hfield_set. cbn.
  rewrite run_hfield_get, ref_sel_opt_upd_same. cbn. rewrite run_ret. reflexivity.
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
    aliasing a [*T] receiver relies on.  A THEOREM. *)
Lemma hstruct_alias : forall {A} (h h' : HStruct) (k : nat) (tag : GoTypeTag A) (v : A) (w : World),
  hs_base h = hs_base h' ->
  ref_sel (hfield_cell h k tag) (ref_upd (hfield_cell h' k tag) v w) = v.
Proof.
  intros A h h' k tag v w Hb. unfold hfield_cell. rewrite Hb.
  apply (ref_sel_upd_same (mkRef (hs_base h' + k) tag) v w).
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

Local Transparent ref_sel ref_upd hfield_cell ref_sel_opt hfield_get run_io.

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

(** Two handles to the SAME base see each other's writes to a field — the [*R]-receiver ALIASING. *)
Lemma gsptr_alias : forall {R t} `{StructRepOf R} (p q : GSPtr R) (m : Mem srep_ts t) (v : t) (w : World),
  gsp_base p = gsp_base q ->
  ref_sel (hfield_cell (gsptr_hs p) (mem_depth m) (mem_tag m (sr_tags srep_rep)))
          (ref_upd (hfield_cell (gsptr_hs q) (mem_depth m) (mem_tag m (sr_tags srep_rep))) v w)
    = v.
Proof.
  intros R t Hrep p q m v w Hb. apply hstruct_alias. unfold gsptr_hs. cbn. exact Hb.
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

(** The pure world transformer [write_fields] effects — used to characterise the post-write heap. *)
Fixpoint wr_fields (ts : list Type) (h : HStruct) (k : nat) : TagTup ts -> Tup ts -> World -> World :=
  match ts return TagTup ts -> Tup ts -> World -> World with
  | nil       => fun _ _ w => w
  | t :: rest => fun tgs vls w =>
      wr_fields rest h (S k) (snd tgs) (snd vls)
                (ref_upd (hfield_cell h k (fst tgs)) (fst vls) w)
  end.

Definition gsptr_new {R} `{StructRepOf R} (v : R) : IO (GSPtr R) :=
  fun w =>
    let l := w_next w in
    let p := mkGSPtr l in
    let wa := mkWorld (w_refs w) (w_chans w) (w_maps w) (l + List.length srep_ts) (w_output w) in
    ORet p (wr_fields srep_ts (gsptr_hs p) 0 (sr_tags srep_rep) (sr_to srep_rep v) wa).

Definition gsptr_deref {R} `{StructRepOf R} (p : GSPtr R) : IO R :=
  bind (read_fields srep_ts (gsptr_hs p) 0 (sr_tags srep_rep)) (fun tp => ret (sr_from srep_rep tp)).

Definition gsptr_assign {R} `{StructRepOf R} (p : GSPtr R) (v : R) : IO unit :=
  write_fields srep_ts (gsptr_hs p) 0 (sr_tags srep_rep) (sr_to srep_rep v).

(** A struct field cell's heap location is [base + slot] — extracted as a small lemma so the proofs
    below can reason about cell distinctness with [hfield_cell] kept opaque (so [cbn] won't expand it
    inside the [ref_sel_opt]/[ref_upd] redexes the [run_*] lemmas drive). *)
Lemma hfield_cell_loc : forall {A} (h : HStruct) (k : nat) (tag : GoTypeTag A),
  r_loc (hfield_cell h k tag) = hs_base h + k.
Proof. reflexivity. Qed.

Local Opaque run_io bind ret hfield_get hfield_set ref_sel_opt ref_upd hfield_cell.

Lemma run_write_fields : forall ts h k tgs vls w,
  run_io (write_fields ts h k tgs vls) w = ORet tt (wr_fields ts h k tgs vls w).
Proof.
  induction ts as [ | t rest IH ]; intros h k tgs vls w; cbn [write_fields wr_fields].
  - rewrite run_ret. reflexivity.
  - rewrite run_bind, run_hfield_set. cbn. rewrite IH. reflexivity.
Qed.

(** Writes at cells [≥ j] leave a cell [k < j] untouched — the field-independence frame. *)
Lemma wr_fields_frame : forall ts h j tgs vls A (tag : GoTypeTag A) k w,
  k < j -> ref_sel_opt (hfield_cell h k tag) (wr_fields ts h j tgs vls w)
         = ref_sel_opt (hfield_cell h k tag) w.
Proof.
  induction ts as [ | t rest IH ]; intros h j tgs vls A tag k w Hlt; cbn [wr_fields]; [ reflexivity | ].
  rewrite IH by lia.
  apply ref_sel_opt_upd_diff. rewrite !hfield_cell_loc. lia.
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
    rewrite ref_sel_opt_upd_same. cbn.
    rewrite run_bind, IH. cbn. rewrite run_ret. reflexivity.
Qed.

(** WHOLE-STRUCT round-trip — a THEOREM, ANY arity: after [assign v], [deref] reconstructs [v]
    EXACTLY ([read_after_wr] recovers the tuple, [sr_eta] reassembles the struct). *)
Lemma gsptr_deref_assign : forall {R} `{StructRepOf R} (p : GSPtr R) (v : R),
  bind (gsptr_assign p v) (fun _ => gsptr_deref p) =io=
  bind (gsptr_assign p v) (fun _ => ret v).
Proof.
  intros R Hrep p v. intro w.
  unfold gsptr_assign, gsptr_deref.
  rewrite run_bind, run_write_fields. cbn.
  rewrite run_bind, read_after_wr. cbn.
  rewrite run_ret, run_bind, run_write_fields. cbn.
  rewrite run_ret, (sr_eta srep_rep v). reflexivity.
Qed.

Local Transparent run_io bind ret hfield_get hfield_set ref_sel_opt ref_upd hfield_cell.

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
