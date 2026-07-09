(** ==================================================================================================
    GoMap — Go's [map[K]V] over the world's map heap.  Ops are IO where they touch the heap
    ([map_make]/[map_set]/[map_delete]/…); reads recover the typed view through the stored tags.
    Reference-type semantics: the pure-update model matches Go's in-place mutation for
    single-goroutine programs (no observable aliasing difference).
    ================================================================================================ *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.
From Fido Require Import GoNumeric.
From Fido Require Import GoRuntimeTypes.
From Fido Require Import GoEffects.
From Fido Require Import GoPanic.

(** ---- GoMap ----

    [GoMap K V] models Go's [map[K]V].  Operations are modelled as pure
    functions returning updated maps; extraction emits in-place mutations,
    which are semantically equivalent in single-goroutine programs since
    maps are reference types with no observable aliasing difference.

    [map_make] is in [IO] because it allocates a new map reference.
    [map_get_opt] returns [option V]; its extraction is deferred until we
    handle [option] lowering properly. *)

(** The allocators are DEFINITIONS: a [GoMap]/[GoChan] is a concrete location
    handle, so they simply mint one.  [map_empty] is the nil map
    (a fixed [MkMap 0] handle — [map_set] on it would panic, like Go's nil map);
    the [IO] allocators take a fresh location from [w_next] and bump it.  The map
    CONTENTS live in the concrete [w_maps] heap, where [map_sel]/[map_upd] are
    DEFINITIONS and the map laws are THEOREMS.  Lowered by name ([make(map[K]V)] /
    nil), the bodies are proof-only. *)
Definition map_empty {K V : Type} : GoMap K V := MkMap 0.

(** [map_make_typed kt vt] creates an empty map with concrete key/value types.
    The [GoTypeTag] witnesses survive extraction so the plugin can emit
    [make(map[K]V)] with the correct Go type — unlike bare [map_make] which
    loses the types to erasure and falls back to [map[any]any].

    NOTE: Go map access never panics on a missing key — it returns the zero
    value (two-value form gives [false] for [ok]).  This differs from slice
    indexing, which DOES panic out of bounds. *)
Definition map_make_typed {K V : Type} (kt : GoTypeTag K) (vt : GoTypeTag V) : IO (GoMap K V) :=
  fun w => let l := w_next w in
           ORet (MkMap l)
                (mkWorld (w_refs w) (w_chans w)
                         (fun k => if Nat.eqb k l
                                   then Some (0, existT _ K (kt, existT _ V (vt, fun _ => None)))
                                   else w_maps w k)
                         (S l) (w_output w)).

(** Untyped fallback — loses key/value types to erasure, emits map[any]any.  No
    tags to seed a cell, so it just mints the handle (the first [map_set] creates
    the typed cell; an unwritten read is [None], Go's empty-map behaviour). *)
Definition map_make {K V : Type} : IO (GoMap K V) :=
  fun w => ORet (MkMap (w_next w))
                (mkWorld (w_refs w) (w_chans w) (w_maps w)
                         (S (w_next w)) (w_output w)).

(** ---- Maps via a heap in the world ----

    A Go map read observes the map's CURRENT (mutable) contents, so map reads are
    in [IO] (world-dependent).  The contents live in the world through an abstract
    heap interface: [map_sel k m w] is the value at key [k] of map [m] in world
    [w]; [map_upd] / [map_rem] are the world-updates that [map_set] / [map_delete]
    perform; [map_size] is the length.  These characterise a STANDARD heap, so
    they are satisfiable — hence CONSISTENT and non-degenerate — and the
    get-after-write laws below are THEOREMS derived from them, not asserted.
    Map access never panics: a missing key reads [None] (Go's zero value /
    [ok=false]); unlike slice indexing, which panics out of bounds. *)
(** The map STATE accessors/updates are DEFINITIONS over [w_maps].
    Like channels, [GoMap] carries no tag, so the accessors THREAD the
    key + value [GoTypeTag]s; they coerce the cell's stored contents (a function
    [K' -> option V']) to the caller's [K -> option V] view (equal by construction,
    [tag_eq] recovers the proofs).  Each update REWRITES the cell with the caller's
    tags, so a read round-trips via [tag_eq_refl] (just as for channels). *)
Definition map_get_fn {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
                       (m : GoMap K V) (w : World) : K -> option V :=
  match w_maps w (gm_loc m) with
  | Some (_, existT _ _ (kt', existT _ _ (vt', f))) =>
      match tag_eq kt kt', tag_eq vt vt' with
      | Some pk, Some pv =>
          fun k => eq_rect _ (fun Y : Type => option Y)
                           (f (eq_rect _ (fun X : Type => X) k _ pk)) _ (eq_sym pv)
      | _, _ => fun _ => None
      end
  | None => fun _ => None
  end.
(** The single map-cell WRITE.  Location 0 is the RESERVED nil sentinel: [map_write] on a nil map
    ([gm_loc = 0]) is a NO-OP — so NO map update ([map_upd]/[map_rem]/[map_clear_upd]) can EVER mutate
    location 0, regardless of caller.  The loc-0 write path is closed at its root, not just at the IO
    wrappers (checkpoint-56 audit: make the bad state impossible, not merely avoided).  Read-back-after-write
    theorems below therefore carry a [gm_loc m <> 0] side condition. *)
Definition map_write {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
                      (m : GoMap K V) (f : K -> option V) (sz : nat) (w : World) : World :=
  if Nat.eqb (gm_loc m) 0 then w
  else mkWorld (w_refs w) (w_chans w)
          (fun l => if Nat.eqb l (gm_loc m)
                    then Some (sz, existT _ K (kt, existT _ V (vt, f)))
                    else w_maps w l)
          (w_next w) (w_output w).
Definition map_sel {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
                   (k : K) (m : GoMap K V) (w : World) : option V :=
  map_get_fn kt vt m w k.
(** [map_size] = Go's [len(m)]: the live-key count stored in the map's cell (0 if the map has no cell yet
    / is nil).  The plugin lowers [map_len] by name to Go [len(m)]; this model AGREES with it. *)
(* The map's live-key count as the RAW heap-internal [nat] (the cell stores [nat]); [map_upd]/[map_rem]
   do their +1/-1 bookkeeping here.  [map_size] is the Go-facing [len(m)] — the same count widened to
   the [Z]-carried [GoInt]. *)
Definition map_count {K V} (m : GoMap K V) (w : World) : nat :=
  match w_maps w (gm_loc m) with Some (sz, _) => sz | None => 0 end.
Definition map_size {K V} (m : GoMap K V) (w : World) : GoInt :=
  intwrap (Z.of_nat (map_count m w)).
Definition map_upd {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
                   (k : K) (v : V) (m : GoMap K V) (w : World) : World :=
  map_write kt vt m (fun k' => if key_eqb kt k k' then Some v else map_get_fn kt vt m w k')
    (match map_get_fn kt vt m w k with         (* len UNCHANGED on an existing key; +1 on a new one *)
     | Some _ => map_count m w | None => S (map_count m w) end) w.
Definition map_rem {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
                   (k : K) (m : GoMap K V) (w : World) : World :=
  map_write kt vt m (fun k' => if key_eqb kt k k' then None else map_get_fn kt vt m w k')
    (match map_get_fn kt vt m w k with         (* len −1 on a present key; UNCHANGED if absent *)
     | Some _ => Nat.pred (map_count m w) | None => map_count m w end) w.

(** Read-back-after-write: [map_get_fn] of a [map_write] (with the SAME tags) is
    the written function — via [eqb_refl] (location hit) + [tag_eq_refl] (the K/V
    coercions become identities, then eta). *)
Lemma map_get_fn_write_same : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) m f sz w,
  Nat.eqb (gm_loc m) 0 = false ->
  map_get_fn kt vt m (map_write kt vt m f sz w) = f.
Proof.
  intros K V kt vt m f sz w Hnil. unfold map_get_fn, map_write. rewrite Hnil. cbn.
  rewrite (Nat.eqb_refl (gm_loc m)), !tag_eq_refl. reflexivity.
Qed.

(** Witness (machine-checked): [map_size] reports the REAL live-key count = Go's [len(m)].
    Insert keys 1,2; overwrite key 1 (len stays 2); delete key 2 (len → 1). *)
Example map_len_counts :
  match run_io (map_make_typed TI64 TI64)
               (mkWorld (fun _ => None) (fun _ => None) (fun _ => None) 1 nil) with
  | ORet m w1 =>
      let w2 := map_upd TI64 TI64 (i64wrap 1%Z) (i64wrap 10%Z) m w1 in
      let w3 := map_upd TI64 TI64 (i64wrap 2%Z) (i64wrap 20%Z) m w2 in
      let w4 := map_upd TI64 TI64 (i64wrap 1%Z) (i64wrap 99%Z) m w3 in  (* overwrite key 1 — len stays 2 *)
      let w5 := map_rem TI64 TI64 (i64wrap 2%Z) m w4 in                 (* delete key 2 — len → 1 *)
      andb (Z.eqb (intraw (map_size m w4)) 2%Z)
           (Z.eqb (intraw (map_size m w5)) 1%Z) = true
  | OPanic _ _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** The map OPERATIONS, DEFINED over the abstract heap state above; their [run_*]
    laws are THEOREMS.  Extraction lowers each by NAME to Go map syntax (the
    proof-only [map_sel]/[map_upd]/[map_rem]/[map_size] bodies are suppressed). *)
Definition map_get_opt {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (m : GoMap K V) : IO (option V) :=
  fun w => ORet (map_sel kt vt k m w) w.
Definition map_len {K V} (m : GoMap K V) : IO GoInt :=
  fun w => ORet (map_size m w) w.
(** [map_get_or k default m]: the value at [k], or [default] if absent. *)
Definition map_get_or {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (default : V) (m : GoMap K V) : IO V :=
  fun w => ORet (match map_sel kt vt k m w with Some v => v | None => default end) w.
(** A WRITE to a NIL map ([MkMap 0], [gm_loc = 0]) PANICS — Go's "assignment to entry in nil map" — so
    [map_set] carries a nil guard that PANICS ([rt_nil_map]).  Go's nil map READS as zero for every key and
    [delete]/[clear] are NO-OPS on it: [map_delete]/[map_clear] return the world UNCHANGED, and — since
    [map_write] itself no-ops at [gm_loc = 0] — NO map update ever writes the reserved location 0.  Location 0
    is reserved by [ValidWorld], so [eqb (gm_loc m) 0] exactly detects nil.  Lowered by name ([m[k] = v]). *)
Definition map_set {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (v : V) (m : GoMap K V) : IO unit :=
  fun w => if Nat.eqb (gm_loc m) 0 then OPanic rt_nil_map w
           else ORet tt (map_upd kt vt k v m w).
(** [delete(m, k)] on a NIL map ([gm_loc = 0]) is a NO-OP in Go — and MUST NOT write (a raw [map_rem]
    would mutate the reserved location 0).  Only a non-nil map is removed from; the nil guard makes the
    world UNCHANGED, matching Go and preserving [ValidWorld] (see [map_delete_nil_noop]). *)
Definition map_delete {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (m : GoMap K V) : IO unit :=
  fun w => if Nat.eqb (gm_loc m) 0 then ORet tt w
           else ORet tt (map_rem kt vt k m w).

Lemma run_map_get_opt : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (m : GoMap K V) (w : World),
  run_io (map_get_opt kt vt k m) w = ORet (map_sel kt vt k m w) w.
Proof. reflexivity. Qed.
Lemma run_map_len : forall {K V} (m : GoMap K V) (w : World),
  run_io (map_len m) w = ORet (map_size m w) w.
Proof. reflexivity. Qed.
Lemma run_map_get_or : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (default : V) (m : GoMap K V) (w : World),
  run_io (map_get_or kt vt k default m) w =
  ORet (match map_sel kt vt k m w with Some v => v | None => default end) w.
Proof. reflexivity. Qed.
Lemma run_map_set : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (v : V) (m : GoMap K V) (w : World),
  run_io (map_set kt vt k v m) w =
    if Nat.eqb (gm_loc m) 0 then OPanic rt_nil_map w
    else ORet tt (map_upd kt vt k v m w).
Proof. reflexivity. Qed.

(** Faithfulness: assigning to a NIL map PANICS, exactly as Go's [m[k] = v] on a nil [m]. *)
Lemma map_set_nil : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (v : V) (w : World),
  run_io (map_set kt vt k v (@map_empty K V)) w = OPanic rt_nil_map w.
Proof. reflexivity. Qed.
Lemma run_map_delete : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (m : GoMap K V) (w : World),
  run_io (map_delete kt vt k m) w =
    if Nat.eqb (gm_loc m) 0 then ORet tt w else ORet tt (map_rem kt vt k m w).
Proof. reflexivity. Qed.
(** Faithfulness: deleting from a NIL map is a NO-OP (Go), leaving the world UNCHANGED (no loc-0 write). *)
Lemma map_delete_nil_noop : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (w : World),
  run_io (map_delete kt vt k (@map_empty K V)) w = ORet tt w.
Proof. reflexivity. Qed.

(** Heap-interface laws — how [map_sel] reads after each update.
    The hypotheses make explicit the side conditions Go imposes: the key must be self-equal under
    [key_eqb] (true for comparable keys, FALSE for a [NaN] float key — which Go's
    map genuinely does not round-trip), and [_diff] needs the key type Comparable
    (so distinct keys compare false).  The demos discharge them via
    [comparable_TInt64]. *)
Theorem map_sel_upd_same : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
    (k : K) (v : V) (m : GoMap K V) (w : World),
  key_eqb kt k k = true -> Nat.eqb (gm_loc m) 0 = false ->
  map_sel kt vt k m (map_upd kt vt k v m w) = Some v.
Proof.
  intros K V kt vt k v m w Hk Hnil. unfold map_sel, map_upd.
  rewrite map_get_fn_write_same by exact Hnil. cbn. rewrite Hk. reflexivity.
Qed.
Theorem map_sel_upd_diff : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
    (k1 k2 : K) (v : V) (m : GoMap K V) (w : World),
  Comparable kt -> k1 <> k2 -> Nat.eqb (gm_loc m) 0 = false ->
  map_sel kt vt k1 m (map_upd kt vt k2 v m w) = map_sel kt vt k1 m w.
Proof.
  intros K V kt vt k1 k2 v m w Hcmp Hne Hnil. unfold map_sel, map_upd.
  rewrite map_get_fn_write_same by exact Hnil. cbn.
  destruct (key_eqb kt k2 k1) eqn:E.
  - exfalso. apply Hne. symmetry. apply Hcmp. exact E.
  - reflexivity.
Qed.
Theorem map_sel_rem : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
    (k : K) (m : GoMap K V) (w : World),
  key_eqb kt k k = true -> Nat.eqb (gm_loc m) 0 = false ->
  map_sel kt vt k m (map_rem kt vt k m w) = None.
Proof.
  intros K V kt vt k m w Hk Hnil. unfold map_sel, map_rem.
  rewrite map_get_fn_write_same by exact Hnil. cbn. rewrite Hk. reflexivity.
Qed.
(** DELETE FRAME (the dual of [map_sel_rem], mirroring [map_sel_upd_diff] for set): deleting key [k2]
    leaves a DIFFERENT key [k1] reading exactly what it read before — Go's `delete(m, k2)` touches only
    [k2].  Independence of keys is as defining for a map as [map_sel_rem] is. *)
Theorem map_sel_rem_diff : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
    (k1 k2 : K) (m : GoMap K V) (w : World),
  Comparable kt -> k1 <> k2 -> Nat.eqb (gm_loc m) 0 = false ->
  map_sel kt vt k1 m (map_rem kt vt k2 m w) = map_sel kt vt k1 m w.
Proof.
  intros K V kt vt k1 k2 m w Hcmp Hne Hnil. unfold map_sel, map_rem.
  rewrite map_get_fn_write_same by exact Hnil. cbn.
  destruct (key_eqb kt k2 k1) eqn:E.
  - exfalso. apply Hne. symmetry. apply Hcmp. exact E.
  - reflexivity.
Qed.
Theorem map_sel_empty : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (w : World),
  w_maps w 0 = None ->
  map_sel kt vt k (@map_empty K V) w = None.
Proof.
  intros K V kt vt k w Hw. unfold map_sel, map_get_fn, map_empty. cbn.
  rewrite Hw. reflexivity.
Qed.

(** GET-AFTER-WRITE laws — THEOREMS, derived from the heap interface. *)
(** A comparable key is self-equal under [key_eqb] (the [_same]/[_rem] side
    condition, discharged from [Comparable]). *)
Lemma comparable_key_refl : forall {K} (t : GoTypeTag K) (k : K),
  Comparable t -> key_eqb t k k = true.
Proof. intros K t k Hc. apply (proj2 (Hc k k)). reflexivity. Qed.

Lemma map_get_set_same : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
    (k : K) (v : V) (m : GoMap K V),
  Comparable kt ->
  bind (map_set kt vt k v m) (fun _ => map_get_opt kt vt k m) =io=
  bind (map_set kt vt k v m) (fun _ => ret (Some v)).
Proof.
  intros K V kt vt k v m Hcmp. intro w.
  rewrite !run_bind, !run_map_set.
  destruct (Nat.eqb (gm_loc m) 0) eqn:Hnil.
  - reflexivity.   (* nil map: both sides panic at the [map_set] step *)
  - cbn. rewrite run_map_get_opt, map_sel_upd_same
      by first [ apply comparable_key_refl; exact Hcmp | exact Hnil ].
    rewrite run_ret. reflexivity.
Qed.

Lemma map_get_delete_same : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
    (k : K) (m : GoMap K V),
  Comparable kt -> Nat.eqb (gm_loc m) 0 = false ->
  bind (map_delete kt vt k m) (fun _ => map_get_opt kt vt k m) =io=
  bind (map_delete kt vt k m) (fun _ => ret (@None V)).
Proof.
  intros K V kt vt k m Hcmp Hnil. intro w.
  rewrite !run_bind, !run_map_delete, !Hnil. cbn.
  rewrite run_map_get_opt, map_sel_rem
    by first [ apply comparable_key_refl; exact Hcmp | exact Hnil ].
  rewrite run_ret. reflexivity.
Qed.

(** Reading the empty (nil) map gives [None] — in a world where its location is
    unallocated (Go's nil map reads the zero value for every key). *)
Lemma map_get_empty : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (w : World),
  w_maps w 0 = None ->
  run_io (@map_get_opt K V kt vt k map_empty) w = ORet None w.
Proof.
  intros K V kt vt k w Hw. rewrite run_map_get_opt, map_sel_empty by exact Hw. reflexivity.
Qed.

(** Setting key [k2] leaves the read at a different key [k1] unchanged — on a NON-NIL map (a nil map
    would panic at the [map_set], so the post-state is not [map_upd]). *)
Lemma map_get_set_diff : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
    (k1 k2 : K) (v : V) (m : GoMap K V) (w : World),
  Comparable kt -> k1 <> k2 -> Nat.eqb (gm_loc m) 0 = false ->
  run_io (bind (map_set kt vt k2 v m) (fun _ => map_get_opt kt vt k1 m)) w =
  ORet (map_sel kt vt k1 m w) (map_upd kt vt k2 v m w).
Proof.
  intros K V kt vt k1 k2 v m w Hcmp Hne Hnil.
  rewrite run_bind, run_map_set, Hnil. cbn.
  rewrite run_map_get_opt, map_sel_upd_diff by assumption. reflexivity.
Qed.

(** IO-level delete frame (the comma-ok dual of [map_get_set_diff]): after `delete(m, k2)`, the
    two-value lookup of a DIFFERENT key [k1] returns exactly what it returned before the delete. *)
Lemma map_get_delete_diff : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
    (k1 k2 : K) (m : GoMap K V) (w : World),
  Comparable kt -> k1 <> k2 -> Nat.eqb (gm_loc m) 0 = false ->
  run_io (bind (map_delete kt vt k2 m) (fun _ => map_get_opt kt vt k1 m)) w =
  ORet (map_sel kt vt k1 m w) (map_rem kt vt k2 m w).
Proof.
  intros K V kt vt k1 k2 m w Hcmp Hne Hnil.
  rewrite run_bind, run_map_delete, Hnil. cbn.
  rewrite run_map_get_opt, map_sel_rem_diff by assumption. reflexivity.
Qed.

(** [map_get_or] hits the stored value when present, falls back when absent. *)
Lemma map_get_or_hit : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
    (k : K) (v default : V) (m : GoMap K V) (w : World),
  map_sel kt vt k m w = Some v -> run_io (map_get_or kt vt k default m) w = ORet v w.
Proof. intros K V kt vt k v default m w H. rewrite run_map_get_or, H. reflexivity. Qed.
Lemma map_get_or_miss : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
    (k : K) (default : V) (m : GoMap K V) (w : World),
  map_sel kt vt k m w = None -> run_io (map_get_or kt vt k default m) w = ORet default w.
Proof. intros K V kt vt k default m w H. rewrite run_map_get_or, H. reflexivity. Qed.

(** [clear(m)] (Go 1.21): remove ALL entries — write the everywhere-[None]
    function.  [map_sel_clear] (every key reads [None]) is a THEOREM, so
    GET-AFTER-CLEAR is too. *)
Definition map_clear_upd {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
                         (m : GoMap K V) (w : World) : World :=
  map_write kt vt m (fun _ => None) 0 w.   (* clear ⇒ empty ⇒ len 0 *)
(** [clear(m)] on a NIL map ([gm_loc = 0]) is a NO-OP in Go — and MUST NOT write location 0. *)
Definition map_clear {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (m : GoMap K V) : IO unit :=
  fun w => if Nat.eqb (gm_loc m) 0 then ORet tt w
           else ORet tt (map_clear_upd kt vt m w).
Lemma run_map_clear : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (m : GoMap K V) (w : World),
  run_io (map_clear kt vt m) w =
    if Nat.eqb (gm_loc m) 0 then ORet tt w else ORet tt (map_clear_upd kt vt m w).
Proof. reflexivity. Qed.
Lemma map_clear_nil_noop : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (w : World),
  run_io (map_clear kt vt (@map_empty K V)) w = ORet tt w.
Proof. reflexivity. Qed.
Theorem map_sel_clear : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
    (k : K) (m : GoMap K V) (w : World),
  Nat.eqb (gm_loc m) 0 = false ->
  map_sel kt vt k m (map_clear_upd kt vt m w) = None.
Proof. intros K V kt vt k m w Hnil. unfold map_sel, map_clear_upd. rewrite map_get_fn_write_same by exact Hnil. reflexivity. Qed.

Lemma map_get_clear : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (m : GoMap K V),
  Nat.eqb (gm_loc m) 0 = false ->
  bind (map_clear kt vt m) (fun _ => map_get_opt kt vt k m) =io=
  bind (map_clear kt vt m) (fun _ => ret (@None V)).
Proof.
  intros K V kt vt k m Hnil. intro w.
  rewrite !run_bind, !run_map_clear, !Hnil. cbn.
  rewrite run_map_get_opt. rewrite map_sel_clear by exact Hnil. rewrite run_ret. reflexivity.
Qed.
