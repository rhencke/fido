(** ==================================================================================================
    GoMap — Go's [map[K]V] over the world's map heap.  Ops are IO where they touch the heap
    ([map_make_typed]/[map_set]/[map_delete]/…); reads recover the typed view through the stored tags.
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

    [map_make_typed] is in [IO] because it allocates a new map reference AND installs its cell.
    [map_get_opt] returns [option V]; its extraction is deferred until we
    handle [option] lowering properly. *)

(** The CERTIFIED allocator [map_make_typed] mints a fresh location ([w_next], bumped) AND installs its
    (empty, typed) cell there — so under [ValidWorld] (which forces [w_next <> 0]) a made map is present AND
    type-correct ([map_cell_ok_make_typed]).  ([map_empty] is the nil map, a fixed [MkMap 0] handle on which [map_set] panics.)
    The map CONTENTS live in the concrete [w_maps] heap, where [map_sel]/[map_upd] are DEFINITIONS and the map
    laws are THEOREMS.  Lowered by name ([make(map[K]V)] / nil), the bodies are proof-only. *)
Definition map_empty {K V : Type} : GoMap K V := MkMap 0.

(** [map_make_typed kt vt] creates an empty map with concrete key/value types.
    The [GoTypeTag] witnesses survive extraction so the plugin can emit
    [make(map[K]V)] with the correct Go type — an untyped [make(map[any]any)] would instead lose the types to
    erasure; there is no NAMED untyped map allocator (only [map_make_typed]; the cell-less [map_make] was
    deleted — see below).

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

(** There is no NAMED untyped map allocator (checkpoint-58: the cell-less [map_make] was DELETED).
    [map_make_typed], which carries the key/value [GoTypeTag]s and installs the cell, is the ONLY map
    allocator.  ⚠ This is NOT unrepresentability: a forged CELL-LESS handle ([MkMap l] whose [w_maps] cell is
    absent) is still CONSTRUCTIBLE via the public [MkMap] / [mkWorld] constructors — deleting a named helper
    removes a convenience trap, it does not seal raw allocation.  What makes such a handle INERT is the
    tag-aware [map_cell_ok] WRITE-GUARD (below): on a cell-less / wrong-tag handle [map_cell_ok = false], so
    every public write fails loud / no-ops, value-reads are [None] ([map_sel]), and [len] is 0 ([map_len] is
    tag-aware too — it never observes a foreign cell's size).  The GUARD is the seal, not the deletion. *)

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
(** A NIL map ([gm_loc = 0]) reads as the ZERO value for EVERY key (Go's nil-map read), NEVER trusting a
    forged cell at the reserved location 0 — the read-side dual of the [map_write] nil guard below.  The
    public [mkWorld]/[MkMap] constructors could fabricate a loc-0 cell; this guard makes it unobservable. *)
Definition map_get_fn {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
                       (m : GoMap K V) (w : World) : K -> option V :=
  if Nat.eqb (gm_loc m) 0 then (fun _ => None)
  else match w_maps w (gm_loc m) with
  | Some (_, existT _ _ (kt', existT _ _ (vt', f))) =>
      match tag_eq kt kt', tag_eq vt vt' with
      | Some pk, Some pv =>
          fun k => eq_rect _ (fun Y : Type => option Y)
                           (f (eq_rect _ (fun X : Type => X) k _ pk)) _ (eq_sym pv)
      | _, _ => fun _ => None
      end
  | None => fun _ => None
  end.
(** [gm_present m w] — is [m]'s cell ALLOCATED?  FALSE for the nil sentinel ([gm_loc = 0]) AND for a nonzero
    ABSENT location (a forged / dangling handle whose [w_maps] cell is [None]).  The map WRITE root ([map_write])
    UPDATES only a present cell — an unallocated handle never fabricates one — and the write IO ops fail loud /
    no-op on it.  ([map_make_typed] installs a cell, so a [ValidWorld]-made map is present AND type-correct
    [map_cell_ok_make_typed]; it is the ONLY NAMED map allocator — but a forged cell-less handle is still
    constructible via [MkMap], and it is the [map_cell_ok] guard, not the absence of a named allocator, that
    makes such a handle inert.)
    ⚠ [gm_present] is TAG-AGNOSTIC: it checks a cell EXISTS, NOT that its stored key/value tags match [m]'s —
    so a forged wrong-tag handle aliasing a real cell reads [gm_present = true].  It is therefore NOT the write
    guard: the tag-aware [map_cell_ok] (below) is.  What IS mechanically closed (checkpoint-58 #3): a wrong-tag
    handle cannot RETYPE a live cell through any public map write ([map_cell_ok_wrong_tag] +
    [no_public_map_retyping]).  STILL OPEN (checkpoint-58 step 6): the raw [map_write] root is not yet
    internalized behind the checked API — so "the map provenance wall is fully closed" would OVERCLAIM.
    [gm_present] survives only as the existence half of the read-side proofs. *)
Definition gm_present {K V} (m : GoMap K V) (w : World) : bool :=
  if Nat.eqb (gm_loc m) 0 then false
  else match w_maps w (gm_loc m) with Some _ => true | None => false end.
Lemma gm_present_nonnil : forall {K V} (m : GoMap K V) w,
  gm_present m w = true -> Nat.eqb (gm_loc m) 0 = false.
Proof. intros K V m w H. unfold gm_present in H. destruct (Nat.eqb (gm_loc m) 0); [ discriminate H | reflexivity ]. Qed.
(** [map_cell_ok kt vt m w] — TAG-AWARE cell check / TYPED LIVENESS: the cell exists AND its
    STORED key/value tags MATCH [kt]/[vt].  This is typed liveness, NOT origin provenance — a same-tag forged
    handle still satisfies it.  Strictly stronger than [gm_present] (which only checks existence),
    so a forged WRONG-TAG handle aliasing a real cell of another type reads [map_cell_ok = false].  The map
    WRITE path guards on THIS, not [gm_present]: a wrong-tag handle can neither RETYPE (write) nor be treated as
    its own map — public write ops fail loud / no-op, so no forged handle retypes an existing cell. *)
Definition map_cell_ok {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (m : GoMap K V) (w : World) : bool :=
  if Nat.eqb (gm_loc m) 0 then false
  else match w_maps w (gm_loc m) with
       | Some (_, existT _ _ (kt', existT _ _ (vt', _))) =>
           match tag_eq kt kt', tag_eq vt vt' with Some _, Some _ => true | _, _ => false end
       | None => false
       end.
Lemma map_cell_ok_nonnil : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (m : GoMap K V) w,
  map_cell_ok kt vt m w = true -> Nat.eqb (gm_loc m) 0 = false.
Proof. intros K V kt vt m w H. unfold map_cell_ok in H. destruct (Nat.eqb (gm_loc m) 0); [ discriminate H | reflexivity ]. Qed.
(** WRONG-TAG at a PRESENT cell ⟹ [map_cell_ok = false] (checkpoint-58): given a NONZERO location holding a
    REAL cell whose STORED key/value tags DISAGREE with the caller's [kt]/[vt] (a forged handle aliasing a cell
    of ANOTHER type), the cell is genuinely PRESENT ([gm_present = true], PROVED here) yet the tag-aware guard
    REJECTS it.  The nonzero premise is what makes the "present" claim mechanically true — WITHOUT it a forged
    loc-0 cell would satisfy the [w_maps]/tag hypotheses while [gm_present] stays [false] (the loc-0 guard), so
    the presence claim would be prose.  The nil / nonzero-ABSENT class is covered separately by the [*_absent]
    lemmas; this lemma isolates the LIVE wrong-tag case, and is what the wrong-tag anti-forgery theorems below
    stand on. *)
Lemma map_cell_ok_wrong_tag :
  forall {K V K' V'} (kt : GoTypeTag K) (vt : GoTypeTag V)
         (kt' : GoTypeTag K') (vt' : GoTypeTag V')
         (m : GoMap K V) (w : World) n (f : K' -> option V'),
  Nat.eqb (gm_loc m) 0 = false ->
  w_maps w (gm_loc m) = Some (n, existT _ K' (kt', existT _ V' (vt', f))) ->
  tag_eq kt kt' = None \/ tag_eq vt vt' = None ->
  gm_present m w = true /\ map_cell_ok kt vt m w = false.
Proof.
  intros K V K' V' kt vt kt' vt' m w n f Hnn Hcell Hmis. split.
  - unfold gm_present. destruct (Nat.eqb (gm_loc m) 0); [ discriminate Hnn | rewrite Hcell; reflexivity ].
  - unfold map_cell_ok. destruct (Nat.eqb (gm_loc m) 0); [ discriminate Hnn | ].
    rewrite Hcell. destruct Hmis as [Hk | Hv].
    + rewrite Hk. reflexivity.
    + rewrite Hv. destruct (tag_eq kt kt'); reflexivity.
Qed.
(** The single map-cell WRITE.  ROOT-GUARDED on [map_cell_ok] (TAG-AWARE): [map_write] UPDATES a cell only when
    it EXISTS AND its stored tags MATCH [kt]/[vt] — on any other handle (nil, nonzero-ABSENT, OR wrong-tag) it
    is a NO-OP.  So NO map update ([map_upd]/[map_rem]/[map_clear_upd]) can EVER fabricate a cell OR RETYPE an
    existing cell through a forged handle, regardless of caller; the ONLY cell CREATION is [map_make_typed].
    The write path is closed at its root (checkpoint-56/57/58: make the bad state impossible, not merely avoided;
    [map_write_absent_noop] pins it).  Read-back-after-write theorems below therefore carry a [map_cell_ok] condition. *)
Definition map_write {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
                      (m : GoMap K V) (f : K -> option V) (sz : nat) (w : World) : World :=
  if map_cell_ok kt vt m w
  then mkWorld (w_refs w) (w_chans w)
          (fun l => if Nat.eqb l (gm_loc m)
                    then Some (sz, existT _ K (kt, existT _ V (vt, f)))
                    else w_maps w l)
          (w_next w) (w_output w)
  else w.   (* ROOT GUARD (tag-aware): updates a MATCHING existing cell only — a nil / absent / WRONG-TAG handle
               is a NO-OP, so the raw updates never fabricate OR retype a cell; only [map_make_typed] creates. *)
Definition map_sel {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
                   (k : K) (m : GoMap K V) (w : World) : option V :=
  map_get_fn kt vt m w k.
(** [map_size] = Go's [len(m)]: the live-key count stored in the map's cell — 0 if the handle has no
    TAG-CORRECT cell ([map_cell_ok = false]: nil, nonzero-absent, OR wrong-tag), so a forged handle never
    observes a foreign cell's size (the read-side dual of the write guard).  The plugin lowers [map_len] by
    name to Go [len(m)] (the [GoTypeTag] args are model-only, dropped in emission); this model AGREES with it. *)
(* The map's live-key count as the RAW heap-internal [nat] (the cell stores [nat]); [map_upd]/[map_rem]
   do their +1/-1 bookkeeping here.  [map_size] is the Go-facing [len(m)] — the same count widened to
   the [Z]-carried [GoInt]. *)
Definition map_count {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (m : GoMap K V) (w : World) : nat :=
  if map_cell_ok kt vt m w   (* TAG-AWARE (checkpoint-58): a nil / nonzero-absent / WRONG-TAG handle has [len] 0
                                — [map_len] never observes a foreign cell's size (the read-side dual of the
                                [map_write] guard; [map_sel] likewise reads [None] on such a handle) *)
  then match w_maps w (gm_loc m) with Some (sz, _) => sz | None => 0 end
  else 0.
(** A map with NO USABLE cell ([map_cell_ok = false] — nil, nonzero-absent, OR WRONG-TAG) reads [None] at
    EVERY key: the read-side dual of the write guards.  [map_get_fn] and [map_cell_ok] branch on the SAME
    conditions (existence + [tag_eq]), so a wrong-tag forged handle observes no entries — it cannot read the
    real cell's values (defensive fail-closed read; the checkpoint-58 read-side anti-forgery witness). *)
Lemma map_sel_absent : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (m : GoMap K V) (w : World),
  map_cell_ok kt vt m w = false -> map_sel kt vt k m w = None.
Proof.
  intros K V kt vt k m w H. unfold map_cell_ok in H. unfold map_sel, map_get_fn.
  destruct (Nat.eqb (gm_loc m) 0); [ reflexivity | ].
  destruct (w_maps w (gm_loc m)) as [ [? [? [kt' [? [vt' ?]]]]] | ]; [ | reflexivity ].
  destruct (tag_eq kt kt'), (tag_eq vt vt'); [ discriminate H | reflexivity | reflexivity | reflexivity ].
Qed.
Definition map_size {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (m : GoMap K V) (w : World) : GoInt :=
  intwrap (Z.of_nat (map_count kt vt m w)).
Definition map_upd {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
                   (k : K) (v : V) (m : GoMap K V) (w : World) : World :=
  map_write kt vt m (fun k' => if key_eqb kt k k' then Some v else map_get_fn kt vt m w k')
    (match map_get_fn kt vt m w k with         (* len UNCHANGED on an existing key; +1 on a new one *)
     | Some _ => map_count kt vt m w | None => S (map_count kt vt m w) end) w.
Definition map_rem {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
                   (k : K) (m : GoMap K V) (w : World) : World :=
  map_write kt vt m (fun k' => if key_eqb kt k k' then None else map_get_fn kt vt m w k')
    (match map_get_fn kt vt m w k with         (* len −1 on a present key; UNCHANGED if absent *)
     | Some _ => Nat.pred (map_count kt vt m w) | None => map_count kt vt m w end) w.

(** Read-back-after-write: [map_get_fn] of a [map_write] (with the SAME tags) is
    the written function — via [eqb_refl] (location hit) + [tag_eq_refl] (the K/V
    coercions become identities, then eta). *)
Lemma map_get_fn_write_same : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) m f sz w,
  map_cell_ok kt vt m w = true ->
  map_get_fn kt vt m (map_write kt vt m f sz w) = f.
Proof.
  intros K V kt vt m f sz w Hp. unfold map_get_fn, map_write.
  rewrite Hp, (map_cell_ok_nonnil kt vt m w Hp). cbn.
  rewrite (Nat.eqb_refl (gm_loc m)), !tag_eq_refl. reflexivity.
Qed.

(** RAW ANTI-FABRICATION GATE (the live proof, not just a comment): every RAW map world-update on an
    UNALLOCATED map ([map_cell_ok = false] — nil, absent, OR WRONG-TAG) is the IDENTITY.  So [map_write] and the
    updates built on it ([map_upd]/[map_rem]/[map_clear_upd]) can NEVER fabricate a cell for a forged / dangling
    handle — the ONLY cell CREATION is [map_make_typed].  This PINS the [map_write] root guard: a forged handle
    provably cannot construct map state, at the raw layer, independent of the checked IO wrappers. *)
Lemma map_write_absent_noop : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (m : GoMap K V) f sz w,
  map_cell_ok kt vt m w = false -> map_write kt vt m f sz w = w.
Proof. intros K V kt vt m f sz w H. unfold map_write. rewrite H. reflexivity. Qed.
Lemma map_upd_absent_noop : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (v : V) (m : GoMap K V) w,
  map_cell_ok kt vt m w = false -> map_upd kt vt k v m w = w.
Proof. intros K V kt vt k v m w H. unfold map_upd. apply map_write_absent_noop; exact H. Qed.
Lemma map_rem_absent_noop : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (m : GoMap K V) w,
  map_cell_ok kt vt m w = false -> map_rem kt vt k m w = w.
Proof. intros K V kt vt k m w H. unfold map_rem. apply map_write_absent_noop; exact H. Qed.

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
      andb (Z.eqb (intraw (map_size TI64 TI64 m w4)) 2%Z)
           (Z.eqb (intraw (map_size TI64 TI64 m w5)) 1%Z) = true
  | OPanic _ _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** The map OPERATIONS, DEFINED over the abstract heap state above; their [run_*]
    laws are THEOREMS.  Extraction lowers each by NAME to Go map syntax (the
    proof-only [map_sel]/[map_upd]/[map_rem]/[map_size] bodies are suppressed). *)
Definition map_get_opt {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (m : GoMap K V) : IO (option V) :=
  fun w => ORet (map_sel kt vt k m w) w.
Definition map_len {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (m : GoMap K V) : IO GoInt :=
  fun w => ORet (map_size kt vt m w) w.
(** [map_get_or k default m]: the value at [k], or [default] if absent. *)
Definition map_get_or {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (default : V) (m : GoMap K V) : IO V :=
  fun w => ORet (match map_sel kt vt k m w with Some v => v | None => default end) w.
(** A WRITE to a map with NO TAG-CORRECT cell — nil ([MkMap 0]), nonzero-ABSENT (forged/dangling), OR WRONG-TAG
    (a forged handle aliasing a real cell of a DIFFERENT key/value type) — is refused: [map_set] guards on
    [map_cell_ok] and PANICS ([rt_nil_map]) otherwise (Go's "assignment to entry in nil map", generalised to the
    whole no-usable-cell class); [delete]/[clear] are NO-OPS on it (world UNCHANGED).  The raw [map_write] itself
    no-ops on any such handle ([map_write_absent_noop]), so NO map update fabricates OR RETYPES a cell, regardless
    of caller — the only cell CREATION is [map_make_typed].  ([map_get_fn] READS a no-cell map as zero for every
    key; [map_sel] READS a wrong-tag cell as [None].)  Lowered by name ([m[k] = v]). *)
Definition map_set {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (v : V) (m : GoMap K V) : IO unit :=
  fun w => if map_cell_ok kt vt m w then ORet tt (map_upd kt vt k v m w) else OPanic rt_nil_map w.
  (* [m[k] = v] with no tag-correct cell (nil [gm_loc = 0], nonzero ABSENT — forged/dangling, OR WRONG-TAG) FAILS
     LOUD (Go's "assignment to entry in nil map", generalised to the whole no-usable-cell class): a forged handle
     never fabricates NOR retypes a cell.  Only a tag-correct cell ([map_make_typed] installs one) reaches [map_upd]. *)
(** [delete(m, k)] removes key [k].  With no tag-correct cell (nil [gm_loc = 0], nonzero-absent, OR WRONG-TAG)
    it is a NO-OP (Go: delete on nil no-ops), guarded on [map_cell_ok] — the world is UNCHANGED and no cell is
    fabricated OR retyped
    ([map_delete_nil_noop] / [map_delete_absent_noop]; [map_rem] itself no-ops via [map_rem_absent_noop]). *)
Definition map_delete {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (m : GoMap K V) : IO unit :=
  fun w => if map_cell_ok kt vt m w then ORet tt (map_rem kt vt k m w) else ORet tt w.
  (* [delete(m, k)] with no tag-correct cell (nil, absent, OR wrong-tag) is a NO-OP (Go: delete on nil no-ops),
     and crucially never FABRICATES a cell for a forged/dangling handle nor RETYPES a wrong-tag one. *)

Lemma run_map_get_opt : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (m : GoMap K V) (w : World),
  run_io (map_get_opt kt vt k m) w = ORet (map_sel kt vt k m w) w.
Proof. reflexivity. Qed.
Lemma run_map_len : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (m : GoMap K V) (w : World),
  run_io (map_len kt vt m) w = ORet (map_size kt vt m w) w.
Proof. reflexivity. Qed.
Lemma run_map_get_or : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (default : V) (m : GoMap K V) (w : World),
  run_io (map_get_or kt vt k default m) w =
  ORet (match map_sel kt vt k m w with Some v => v | None => default end) w.
Proof. reflexivity. Qed.
Lemma run_map_set : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (v : V) (m : GoMap K V) (w : World),
  run_io (map_set kt vt k v m) w =
    if map_cell_ok kt vt m w then ORet tt (map_upd kt vt k v m w) else OPanic rt_nil_map w.
Proof. reflexivity. Qed.
(** ANTI-FORGERY: [map_set] on an UNALLOCATED map ([map_cell_ok = false] — nil, absent, OR WRONG-TAG) FAILS LOUD
    with NO mutation (the world is returned unchanged in the [OPanic]) — it never fabricates a cell. *)
Lemma map_set_absent : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (v : V) (m : GoMap K V) (w : World),
  map_cell_ok kt vt m w = false -> run_io (map_set kt vt k v m) w = OPanic rt_nil_map w.
Proof. intros K V kt vt k v m w H. unfold map_set, run_io. rewrite H. reflexivity. Qed.

(** Faithfulness: assigning to a NIL map PANICS, exactly as Go's [m[k] = v] on a nil [m]. *)
Lemma map_set_nil : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (v : V) (w : World),
  run_io (map_set kt vt k v (@map_empty K V)) w = OPanic rt_nil_map w.
Proof. reflexivity. Qed.
Lemma run_map_delete : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (m : GoMap K V) (w : World),
  run_io (map_delete kt vt k m) w =
    if map_cell_ok kt vt m w then ORet tt (map_rem kt vt k m w) else ORet tt w.
Proof. reflexivity. Qed.
(** ANTI-FORGERY: [delete] with no tag-correct cell ([map_cell_ok = false] — nil, absent, OR WRONG-TAG) is a
    NO-OP (world UNCHANGED) — it never fabricates a cell for a forged/dangling handle nor retypes a wrong-tag one. *)
Lemma map_delete_absent_noop : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (m : GoMap K V) (w : World),
  map_cell_ok kt vt m w = false -> run_io (map_delete kt vt k m) w = ORet tt w.
Proof. intros K V kt vt k m w H. unfold map_delete, run_io. rewrite H. reflexivity. Qed.
(** Faithfulness: deleting from a NIL map is a NO-OP (Go), leaving the world UNCHANGED — [map_delete] guards on
    [map_cell_ok] (nil is [map_cell_ok = false]).  (Absent/wrong-tag more generally: [map_delete_absent_noop].) *)
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
  key_eqb kt k k = true -> map_cell_ok kt vt m w = true ->
  map_sel kt vt k m (map_upd kt vt k v m w) = Some v.
Proof.
  intros K V kt vt k v m w Hk Hnil. unfold map_sel, map_upd.
  rewrite map_get_fn_write_same by exact Hnil. cbn. rewrite Hk. reflexivity.
Qed.
Theorem map_sel_upd_diff : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
    (k1 k2 : K) (v : V) (m : GoMap K V) (w : World),
  Comparable kt -> k1 <> k2 -> map_cell_ok kt vt m w = true ->
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
  key_eqb kt k k = true -> map_cell_ok kt vt m w = true ->
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
  Comparable kt -> k1 <> k2 -> map_cell_ok kt vt m w = true ->
  map_sel kt vt k1 m (map_rem kt vt k2 m w) = map_sel kt vt k1 m w.
Proof.
  intros K V kt vt k1 k2 m w Hcmp Hne Hnil. unfold map_sel, map_rem.
  rewrite map_get_fn_write_same by exact Hnil. cbn.
  destruct (key_eqb kt k2 k1) eqn:E.
  - exfalso. apply Hne. symmetry. apply Hcmp. exact E.
  - reflexivity.
Qed.
(** Reading a NIL map ([map_empty = MkMap 0]) gives [None] for every key in ANY world [w] — even one
    forging a cell at location 0.  The nil guard in [map_get_fn] makes [w_maps 0] unobservable, so this is
    the map read-side anti-forgery witness (the dual of the [map_write] nil no-op). *)
Theorem map_sel_empty : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (w : World),
  map_sel kt vt k (@map_empty K V) w = None.
Proof. reflexivity. Qed.
(** [len] of a nil map is 0 in ANY world — the [map_count] nil guard ignores a forged loc-0 cell's size. *)
Theorem map_size_empty : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (w : World), map_size kt vt (@map_empty K V) w = intwrap 0%Z.
Proof. reflexivity. Qed.

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
  destruct (map_cell_ok kt vt m w) eqn:Hp.
  - cbn. rewrite run_map_get_opt, map_sel_upd_same
      by first [ apply comparable_key_refl; exact Hcmp | exact Hp ].
    rewrite run_ret. reflexivity.
  - reflexivity.   (* no tag-correct cell (nil, absent, OR wrong-tag): both sides panic at the [map_set] step *)
Qed.

Lemma map_get_delete_same : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
    (k : K) (m : GoMap K V),
  Comparable kt ->
  bind (map_delete kt vt k m) (fun _ => map_get_opt kt vt k m) =io=
  bind (map_delete kt vt k m) (fun _ => ret (@None V)).
Proof.
  intros K V kt vt k m Hcmp. intro w.
  rewrite !run_bind, !run_map_delete.
  destruct (map_cell_ok kt vt m w) eqn:Hp.
  - cbn. rewrite run_map_get_opt, map_sel_rem
      by first [ apply comparable_key_refl; exact Hcmp | exact Hp ].
    rewrite run_ret. reflexivity.
  - cbn. rewrite run_map_get_opt, (map_sel_absent kt vt k m w Hp), run_ret. reflexivity.
Qed.

(** Reading the nil map gives [None] in ANY world (Go's nil map reads the zero value for every key) —
    the guard in [map_get_fn] holds even against a forged loc-0 cell. *)
Lemma map_get_empty : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (w : World),
  run_io (@map_get_opt K V kt vt k map_empty) w = ORet None w.
Proof.
  intros K V kt vt k w. rewrite run_map_get_opt, map_sel_empty. reflexivity.
Qed.

(** Setting key [k2] leaves the read at a different key [k1] unchanged — on a TAG-CORRECT map ([map_cell_ok],
    the actual [map_set] guard; a nil / absent / wrong-tag handle would panic / no-op at the [map_set], so the
    post-state would not be [map_upd]). *)
Lemma map_get_set_diff : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
    (k1 k2 : K) (v : V) (m : GoMap K V) (w : World),
  Comparable kt -> k1 <> k2 -> map_cell_ok kt vt m w = true ->
  run_io (bind (map_set kt vt k2 v m) (fun _ => map_get_opt kt vt k1 m)) w =
  ORet (map_sel kt vt k1 m w) (map_upd kt vt k2 v m w).
Proof.
  intros K V kt vt k1 k2 v m w Hcmp Hne Hp.
  rewrite run_bind, run_map_set, Hp. cbn.
  rewrite run_map_get_opt, map_sel_upd_diff by first [ assumption | exact Hp ].
  reflexivity.
Qed.

(** IO-level delete frame (the comma-ok dual of [map_get_set_diff]): after `delete(m, k2)`, the
    two-value lookup of a DIFFERENT key [k1] returns exactly what it returned before the delete. *)
Lemma map_get_delete_diff : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
    (k1 k2 : K) (m : GoMap K V) (w : World),
  Comparable kt -> k1 <> k2 -> map_cell_ok kt vt m w = true ->
  run_io (bind (map_delete kt vt k2 m) (fun _ => map_get_opt kt vt k1 m)) w =
  ORet (map_sel kt vt k1 m w) (map_rem kt vt k2 m w).
Proof.
  intros K V kt vt k1 k2 m w Hcmp Hne Hp.
  rewrite run_bind, run_map_delete, Hp. cbn.
  rewrite run_map_get_opt, map_sel_rem_diff by first [ assumption | exact Hp ].
  reflexivity.
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
Lemma map_clear_upd_absent_noop : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (m : GoMap K V) w,
  map_cell_ok kt vt m w = false -> map_clear_upd kt vt m w = w.
Proof. intros K V kt vt m w H. unfold map_clear_upd. apply map_write_absent_noop; exact H. Qed.
(** [clear(m)] with no tag-correct cell (nil [gm_loc = 0], nonzero-absent, OR wrong-tag) is a NO-OP —
    AUTOMATICALLY: [map_clear_upd] no-ops at the [map_write] root ([map_cell_ok = false], so no cell is
    written/fabricated/retyped). *)
Definition map_clear {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (m : GoMap K V) : IO unit :=
  fun w => if map_cell_ok kt vt m w then ORet tt (map_clear_upd kt vt m w) else ORet tt w.
  (* [clear(m)] with no tag-correct cell (nil, absent, OR wrong-tag) is a NO-OP, never fabricating/retyping a cell. *)
Lemma run_map_clear : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (m : GoMap K V) (w : World),
  run_io (map_clear kt vt m) w =
    if map_cell_ok kt vt m w then ORet tt (map_clear_upd kt vt m w) else ORet tt w.
Proof. reflexivity. Qed.
(** ANTI-FORGERY: [clear] with no tag-correct cell ([map_cell_ok = false] — nil, absent, OR WRONG-TAG) is a
    NO-OP (world UNCHANGED), never retyping a wrong-tag cell. *)
Lemma map_clear_absent_noop : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (m : GoMap K V) (w : World),
  map_cell_ok kt vt m w = false -> run_io (map_clear kt vt m) w = ORet tt w.
Proof. intros K V kt vt m w H. unfold map_clear, run_io. rewrite H. reflexivity. Qed.
Lemma map_clear_nil_noop : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (w : World),
  run_io (map_clear kt vt (@map_empty K V)) w = ORet tt w.
Proof. reflexivity. Qed.

(** ==================================================================================================
    WRONG-TAG ANTI-FORGERY (checkpoint-58 #3, maps).  The hypotheses below isolate the WRONG-TAG case
    STRUCTURALLY: a NONZERO location ([Nat.eqb (gm_loc m) 0 = false]) holding a REAL cell (so [gm_present = true]
    — PROVED in [map_cell_ok_wrong_tag], not just asserted) whose stored key/value tags DISAGREE with the
    caller's [kt]/[vt] — a forged public [MkMap l] handle aliasing a LIVE map of ANOTHER key/value type.  Each
    theorem PINS that no public map write can retype (or clear) that cell: it fails loud with the world
    UNCHANGED, or no-ops.  This is strictly beyond the nil / nonzero-ABSENT class (covered by the [*_absent]
    lemmas) — the cell is genuinely there, just of the wrong type.  The nonzero premise is essential: without
    it a forged loc-0 cell would satisfy the [w_maps]/tag hypotheses while [gm_present] is [false], collapsing
    the "live wrong-tag" claim into the already-covered loc-0 case.
    ================================================================================================ *)

(** [m[k] = v] through a WRONG-TAG handle FAILS LOUD ([rt_nil_map]) with the world UNCHANGED — it never
    RETYPES the aliased cell. *)
Theorem map_set_wrong_tag_no_mutation :
  forall {K V K' V'} (kt : GoTypeTag K) (vt : GoTypeTag V)
         (kt' : GoTypeTag K') (vt' : GoTypeTag V')
         (k : K) (v : V) (m : GoMap K V) (w : World) n (f : K' -> option V'),
  Nat.eqb (gm_loc m) 0 = false ->
  w_maps w (gm_loc m) = Some (n, existT _ K' (kt', existT _ V' (vt', f))) ->
  tag_eq kt kt' = None \/ tag_eq vt vt' = None ->
  run_io (map_set kt vt k v m) w = OPanic rt_nil_map w.
Proof.
  intros K V K' V' kt vt kt' vt' k v m w n f Hnn Hcell Hmis.
  apply map_set_absent. exact (proj2 (map_cell_ok_wrong_tag kt vt kt' vt' m w n f Hnn Hcell Hmis)).
Qed.

(** [delete(m, k)] through a WRONG-TAG handle is a NO-OP (world UNCHANGED) — it never retypes/mutates the
    aliased cell. *)
Theorem map_delete_wrong_tag_no_mutation :
  forall {K V K' V'} (kt : GoTypeTag K) (vt : GoTypeTag V)
         (kt' : GoTypeTag K') (vt' : GoTypeTag V')
         (k : K) (m : GoMap K V) (w : World) n (f : K' -> option V'),
  Nat.eqb (gm_loc m) 0 = false ->
  w_maps w (gm_loc m) = Some (n, existT _ K' (kt', existT _ V' (vt', f))) ->
  tag_eq kt kt' = None \/ tag_eq vt vt' = None ->
  run_io (map_delete kt vt k m) w = ORet tt w.
Proof.
  intros K V K' V' kt vt kt' vt' k m w n f Hnn Hcell Hmis.
  apply map_delete_absent_noop. exact (proj2 (map_cell_ok_wrong_tag kt vt kt' vt' m w n f Hnn Hcell Hmis)).
Qed.

(** [clear(m)] through a WRONG-TAG handle is a NO-OP (world UNCHANGED) — it never clears/retypes the
    aliased cell. *)
Theorem map_clear_wrong_tag_no_mutation :
  forall {K V K' V'} (kt : GoTypeTag K) (vt : GoTypeTag V)
         (kt' : GoTypeTag K') (vt' : GoTypeTag V')
         (m : GoMap K V) (w : World) n (f : K' -> option V'),
  Nat.eqb (gm_loc m) 0 = false ->
  w_maps w (gm_loc m) = Some (n, existT _ K' (kt', existT _ V' (vt', f))) ->
  tag_eq kt kt' = None \/ tag_eq vt vt' = None ->
  run_io (map_clear kt vt m) w = ORet tt w.
Proof.
  intros K V K' V' kt vt kt' vt' m w n f Hnn Hcell Hmis.
  apply map_clear_absent_noop. exact (proj2 (map_cell_ok_wrong_tag kt vt kt' vt' m w n f Hnn Hcell Hmis)).
Qed.

(** Even the RAW cell-write root refuses a WRONG-TAG handle: [map_write] (hence [map_upd]/[map_rem]/
    [map_clear_upd]) is the IDENTITY on it.  So retyping is impossible at the raw layer too, independent of
    the checked IO wrappers. *)
Theorem map_write_wrong_tag_no_retype :
  forall {K V K' V'} (kt : GoTypeTag K) (vt : GoTypeTag V)
         (kt' : GoTypeTag K') (vt' : GoTypeTag V')
         (m : GoMap K V) (fn : K -> option V) (sz : nat) (w : World) n (f : K' -> option V'),
  Nat.eqb (gm_loc m) 0 = false ->
  w_maps w (gm_loc m) = Some (n, existT _ K' (kt', existT _ V' (vt', f))) ->
  tag_eq kt kt' = None \/ tag_eq vt vt' = None ->
  map_write kt vt m fn sz w = w.
Proof.
  intros K V K' V' kt vt kt' vt' m fn sz w n f Hnn Hcell Hmis.
  apply map_write_absent_noop. exact (proj2 (map_cell_ok_wrong_tag kt vt kt' vt' m w n f Hnn Hcell Hmis)).
Qed.

(** CAPSTONE — NO PUBLIC MAP RETYPING: a forged WRONG-TAG handle aliasing a live cell of another key/value
    type cannot RETYPE it through the public map WRITES ([map_set]/[delete]/[clear]).  [map_set] fails loud
    (world unchanged), [delete] and [clear] no-op.  Together with [map_set_absent]/[…_absent_noop] (the nil /
    nonzero-ABSENT class) and the raw [map_write_wrong_tag_no_retype], NO forged-handle write — through the
    checked ops OR the raw [map_write] root — fabricates or retypes a cell.  (SCOPE: this is the write-path
    WRONG-TAG ANTI-FORGERY guarantee — typed liveness, NOT origin provenance: a SAME-TAG forged handle aliasing
    a real same-tag cell is Go reference-value aliasing and is NOT ruled out here.  It also does NOT assert the
    raw root is internalized.  The named cell-less allocator [map_make] is deleted, but a forged cell-less
    handle stays constructible via [MkMap] — the [map_cell_ok] guard is what makes such a CELL-LESS handle
    inert, not the deletion.) *)
Theorem no_public_map_retyping :
  forall {K V K' V'} (kt : GoTypeTag K) (vt : GoTypeTag V)
         (kt' : GoTypeTag K') (vt' : GoTypeTag V')
         (k : K) (v : V) (m : GoMap K V) (w : World) n (f : K' -> option V'),
  Nat.eqb (gm_loc m) 0 = false ->
  w_maps w (gm_loc m) = Some (n, existT _ K' (kt', existT _ V' (vt', f))) ->
  tag_eq kt kt' = None \/ tag_eq vt vt' = None ->
     run_io (map_set kt vt k v m) w = OPanic rt_nil_map w
  /\ run_io (map_delete kt vt k m) w = ORet tt w
  /\ run_io (map_clear kt vt m) w = ORet tt w.
Proof.
  intros K V K' V' kt vt kt' vt' k v m w n f Hnn Hcell Hmis.
  assert (Hbad : map_cell_ok kt vt m w = false)
    by (exact (proj2 (map_cell_ok_wrong_tag kt vt kt' vt' m w n f Hnn Hcell Hmis))).
  split; [ | split ].
  - apply map_set_absent; exact Hbad.
  - apply map_delete_absent_noop; exact Hbad.
  - apply map_clear_absent_noop; exact Hbad.
Qed.
Theorem map_sel_clear : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
    (k : K) (m : GoMap K V) (w : World),
  map_cell_ok kt vt m w = true ->
  map_sel kt vt k m (map_clear_upd kt vt m w) = None.
Proof. intros K V kt vt k m w Hnil. unfold map_sel, map_clear_upd. rewrite map_get_fn_write_same by exact Hnil. reflexivity. Qed.

Lemma map_get_clear : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (m : GoMap K V),
  bind (map_clear kt vt m) (fun _ => map_get_opt kt vt k m) =io=
  bind (map_clear kt vt m) (fun _ => ret (@None V)).
Proof.
  intros K V kt vt k m. intro w.
  rewrite !run_bind, !run_map_clear.
  destruct (map_cell_ok kt vt m w) eqn:Hp.
  - cbn. rewrite run_map_get_opt, map_sel_clear by exact Hp.
    rewrite run_ret. reflexivity.
  - cbn. rewrite run_map_get_opt, (map_sel_absent kt vt k m w Hp), run_ret. reflexivity.
Qed.

(** [len(m)] through a WRONG-TAG handle reads 0 — [map_len] never OBSERVES the aliased foreign cell's size
    (the read-side dual of the write anti-forgery; [map_count]/[map_size]/[map_len] guard on [map_cell_ok]). *)
Theorem map_len_wrong_tag_zero : forall {K V K' V'} (kt : GoTypeTag K) (vt : GoTypeTag V)
    (kt' : GoTypeTag K') (vt' : GoTypeTag V') (m : GoMap K V) (w : World) n (f : K' -> option V'),
  Nat.eqb (gm_loc m) 0 = false ->
  w_maps w (gm_loc m) = Some (n, existT _ K' (kt', existT _ V' (vt', f))) ->
  tag_eq kt kt' = None \/ tag_eq vt vt' = None ->
  run_io (map_len kt vt m) w = ORet (intwrap 0%Z) w.
Proof.
  intros K V K' V' kt vt kt' vt' m w n f Hnn Hcell Hmis.
  assert (Hbad : map_cell_ok kt vt m w = false)
    by exact (proj2 (map_cell_ok_wrong_tag kt vt kt' vt' m w n f Hnn Hcell Hmis)).
  unfold map_len, run_io, map_size, map_count. rewrite Hbad. reflexivity.
Qed.

(** MANIFEST-GATED WRONG-TAG ANTI-FORGERY SURFACE: the map wrong-tag anti-forgery theorems as PUBLIC,
    zero-axiom evidence.  (Typed-liveness negatives, NOT origin provenance — a SAME-TAG alias is not stopped
    here.)  A forged wrong-tag handle cannot fabricate OR retype a map cell through any public
    write ([map_set]/[delete]/[clear]) nor the raw [map_write] root, NOR observe a foreign cell's size
    ([map_len_wrong_tag_zero] — the read-side seal); [map_cell_ok_wrong_tag] pins the present-but-mistyped case
    (proving [gm_present = true] alongside).  The [Print Assumptions] below certifies the whole cone axiom-free
    — so these anti-forgery claims are manifest-gated public evidence, not merely ungated internal lemmas. *)
Definition map_wrong_tag_antiforgery_surface :=
  (@map_cell_ok_wrong_tag, @map_set_wrong_tag_no_mutation, @map_delete_wrong_tag_no_mutation,
   @map_clear_wrong_tag_no_mutation, @map_write_wrong_tag_no_retype, @no_public_map_retyping,
   @map_len_wrong_tag_zero).
Print Assumptions map_wrong_tag_antiforgery_surface.
