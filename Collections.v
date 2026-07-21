(** Collections — the ONE standard-collection foundation.  Fido authors NO general-purpose map/set
    implementation: every identity-keyed collection is backed by a mature pinned-Rocq-stdlib map, and every
    membership-only collection by a mature standard set, behind a thin domain wrapper.  This module only
    instantiates standard functors and re-exports the facts Fido needs — it defines no tree/list-backed
    map/set.

    Selected implementations (pinned rocq-stdlib 9.1.0):
    - general string/ordered-key finite map: [FMapAVL] (Rocq's mature standard ordered map; the standard
      implementation uses AVL-tree operations);
    - positive-key finite map: [FMapPositive.PositiveMap] (Rocq's mature standard positive-key map).

    Honest claim: Fido PROVES the functional map semantics it consumes (and the project-specific facts below);
    Fido does NOT claim a project kernel theorem for the AVL balance invariant or a machine-level O(log n)
    complexity.  [FMapFullAVL] is the standard layer that additionally packages/proves the balance invariant —
    NOT redundant; it is the appropriate candidate if formally-packaged balance ever becomes a required Fido
    theorem (do not switch merely for wording). *)
From Stdlib Require Import String.
From Stdlib Require Import Structures.OrderedType Structures.OrderedTypeEx.
From Stdlib Require Import FSets.FMapInterface FSets.FMapAVL FSets.FMapFacts.
From Stdlib Require Import FSets.FMapPositive.
From Stdlib Require Import SetoidList.
From Fido Require Import FilePath.

(** the standard positive-key map (a certified stdlib binary-trie map) — for per-file local-node indexes. *)
Module NodeMapBase := FMapPositive.PositiveMap.

(** the standard AVL map over the standard String ordered key — for the package-directory map. *)
Module PackageMapBase := FMapAVL.Make String_as_OT.
Module PackageMapFacts := FMapFacts.WFacts_fun String_as_OT PackageMapBase.
Module PackageMapProps := FMapFacts.WProperties_fun String_as_OT PackageMapBase.

(** ---- the [FilePath] ordered key: a total lexicographic order via [fp_string], reusing the pinned
    standard [String_as_OT].  The exposed equality is Leibniz [FilePath] equality (paths are proof-irrelevant
    on their well-formedness field), so map keys behave as identities. ---- *)

Lemma fp_str_inj : forall a b : FilePath, fp_str a = fp_str b -> a = b.
Proof. intros a b H. apply (proj1 (fp_eqb_eq a b)). unfold fp_eqb. rewrite H. apply String.eqb_refl. Qed.

Module FilePath_OT <: OrderedType.OrderedType.
  Definition t := FilePath.
  Definition eq (a b : t) := a = b.
  Definition lt (a b : t) := String_as_OT.lt (fp_str a) (fp_str b).
  Lemma eq_refl : forall x, eq x x. Proof. reflexivity. Qed.
  Lemma eq_sym : forall x y, eq x y -> eq y x. Proof. unfold eq; intros x y H; symmetry; exact H. Qed.
  Lemma eq_trans : forall x y z, eq x y -> eq y z -> eq x z.
  Proof. unfold eq; intros x y z Hxy Hyz; rewrite Hxy; exact Hyz. Qed.
  Lemma lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
  Proof. unfold lt; intros x y z; apply String_as_OT.lt_trans. Qed.
  Lemma lt_not_eq : forall x y, lt x y -> ~ eq x y.
  Proof.
    unfold lt, eq; intros x y H Hxy; subst y.
    apply (String_as_OT.lt_not_eq H); reflexivity.
  Qed.
  Definition compare (a b : t) : OrderedType.Compare lt eq a b.
  Proof.
    destruct (String_as_OT.compare (fp_str a) (fp_str b)) as [Hlt|Heq|Hgt].
    - apply OrderedType.LT; exact Hlt.
    - apply OrderedType.EQ; unfold eq; apply fp_str_inj; exact Heq.
    - apply OrderedType.GT; unfold lt; exact Hgt.
  Defined.
  Definition eq_dec (a b : t) : {eq a b} + {~ eq a b}.
  Proof.
    unfold eq. destruct (fp_eqb a b) eqn:E.
    - left. apply fp_eqb_eq. exact E.
    - right. intro H. apply (proj2 (fp_eqb_eq a b)) in H. rewrite H in E. discriminate.
  Defined.
End FilePath_OT.

(** ---- the standard AVL file map keyed by [FilePath], plus its standard facts. ---- *)
Module FileMapBase := FMapAVL.Make FilePath_OT.
Module FileMapFacts := FMapFacts.WFacts_fun FilePath_OT FileMapBase.
Module FileMapProps := FMapFacts.WProperties_fun FilePath_OT FileMapBase.
Module FileMapOrd := FMapFacts.OrdProperties FileMapBase.

(** ---- wrapper theorem: because the standard AVL map's [elements] is SORTED by key, two SEMANTICALLY
    equal ([Equal]) file maps have the very SAME canonical [elements] list — the derived enumeration is a true
    function of the map's meaning, not of its balancing history.  (The FilePath key equality is Leibniz, so
    [eqlistA eq_key_elt] collapses to list equality.) ---- *)
Lemma eqlistA_eqke_eq {A} : forall (l1 l2 : list (FilePath * A)),
  eqlistA (@FileMapBase.eq_key_elt A) l1 l2 -> l1 = l2.
Proof.
  induction l1 as [|[k e] l1' IH]; intros l2 H; inversion H as [|x y l l' Hxy Htl]; subst; [ reflexivity | ].
  destruct y as [k' e']. destruct Hxy as [Hk He]. cbn in Hk, He. subst. f_equal. apply IH; exact Htl.
Qed.

Lemma filemap_elements_Equal {A} : forall (m1 m2 : FileMapBase.t A),
  FileMapBase.Equal m1 m2 -> FileMapBase.elements m1 = FileMapBase.elements m2.
Proof.
  intros m1 m2 Heq. apply eqlistA_eqke_eq.
  apply FileMapOrd.sort_equivlistA_eqlistA;
    [ apply FileMapBase.elements_3 | apply FileMapBase.elements_3 | ].
  intros [k e]. rewrite <- !FileMapFacts.elements_mapsto_iff, !FileMapFacts.find_mapsto_iff, (Heq k).
  reflexivity.
Qed.

(** ---- the same canonical-elements facts for the PACKAGE map (String key, Leibniz eq): [Equal] maps have the
    SAME [elements], and [map]ping a value function commutes with [elements] (keys preserved, sorted order
    preserved).  Used by the cross-snapshot determinism to compare erased package buckets. ---- *)
Module PackageMapOrd := FMapFacts.OrdProperties PackageMapBase.

Lemma eqlistA_eqke_eq_str {A} : forall (l1 l2 : list (string * A)),
  eqlistA (@PackageMapBase.eq_key_elt A) l1 l2 -> l1 = l2.
Proof.
  induction l1 as [|[k e] l1' IH]; intros l2 H; inversion H as [|x y l l' Hxy Htl]; subst; [ reflexivity | ].
  destruct y as [k' e']. destruct Hxy as [Hk He]. cbn in Hk, He. subst. f_equal. apply IH; exact Htl.
Qed.

Lemma packagemap_elements_Equal {A} : forall (m1 m2 : PackageMapBase.t A),
  PackageMapBase.Equal m1 m2 -> PackageMapBase.elements m1 = PackageMapBase.elements m2.
Proof.
  intros m1 m2 Heq. apply eqlistA_eqke_eq_str.
  apply PackageMapOrd.sort_equivlistA_eqlistA;
    [ apply PackageMapBase.elements_3 | apply PackageMapBase.elements_3 | ].
  intros [k e]. rewrite <- !PackageMapFacts.elements_mapsto_iff, !PackageMapFacts.find_mapsto_iff, (Heq k).
  reflexivity.
Qed.

Lemma sorted_map_fst {A B} (f : A -> B) : forall l,
  Sorted (@PackageMapBase.lt_key A) l ->
  Sorted (@PackageMapBase.lt_key B) (map (fun kv => (fst kv, f (snd kv))) l).
Proof.
  induction l as [|a l IH]; intro Hs; cbn [map]; [constructor|].
  apply Sorted_inv in Hs. destruct Hs as [Hs Hhd]. constructor; [apply IH; exact Hs|].
  destruct l as [|b l']; cbn [map]; [constructor|]. apply HdRel_inv in Hhd. constructor. exact Hhd.
Qed.

Lemma packagemap_map_elements {A B} (f : A -> B) : forall (m : PackageMapBase.t A),
  PackageMapBase.elements (PackageMapBase.map f m)
  = map (fun kv => (fst kv, f (snd kv))) (PackageMapBase.elements m).
Proof.
  intro m. apply eqlistA_eqke_eq_str.
  apply PackageMapOrd.sort_equivlistA_eqlistA;
    [ apply PackageMapBase.elements_3
    | apply sorted_map_fst, PackageMapBase.elements_3 | ].
  intros [k e].
  rewrite <- PackageMapFacts.elements_mapsto_iff, PackageMapFacts.map_mapsto_iff, InA_alt.
  split.
  - intros [a [He Hmt]]. subst e.
    apply PackageMapFacts.elements_mapsto_iff in Hmt. rewrite InA_alt in Hmt.
    destruct Hmt as [[k' a'] [[Hk Ha] Hin]]. cbn in Hk, Ha. subst k' a'.
    exists (k, f a). split; [ split; reflexivity | ].
    apply in_map_iff. exists (k, a). split; [reflexivity | exact Hin].
  - intros [[k' e'] [[Hk He] Hin]]. cbn in Hk, He. subst k' e'.
    apply in_map_iff in Hin. destruct Hin as [[k'' a] [Heq Hin]]. injection Heq as Hk2 He2. subst k'' e.
    exists a. split; [reflexivity | ].
    apply PackageMapFacts.elements_mapsto_iff. rewrite InA_alt. exists (k, a).
    split; [ split; reflexivity | exact Hin ].
Qed.

(** ---- the same [map]-commutes-with-[elements] facts for the FILE map (FilePath key): [FMapAVL.map] preserves
    the key domain AND their canonical sorted order, so the elements of a mapped file map are exactly the source
    elements with the value function applied.  Consumed by the DirectoryImage layout bridge (the rendered
    image's `.go` file KEYS are exactly the source FilePaths, in the same order). ---- *)
Lemma sorted_map_fst_file {A B} (f : A -> B) : forall l,
  Sorted (@FileMapBase.lt_key A) l ->
  Sorted (@FileMapBase.lt_key B) (map (fun kv => (fst kv, f (snd kv))) l).
Proof.
  induction l as [|a l IH]; intro Hs; cbn [map]; [constructor|].
  apply Sorted_inv in Hs. destruct Hs as [Hs Hhd]. constructor; [apply IH; exact Hs|].
  destruct l as [|b l']; cbn [map]; [constructor|]. apply HdRel_inv in Hhd. constructor. exact Hhd.
Qed.

Lemma filemap_map_elements {A B} (f : A -> B) : forall (m : FileMapBase.t A),
  FileMapBase.elements (FileMapBase.map f m)
  = map (fun kv => (fst kv, f (snd kv))) (FileMapBase.elements m).
Proof.
  intro m. apply eqlistA_eqke_eq.
  apply FileMapOrd.sort_equivlistA_eqlistA;
    [ apply FileMapBase.elements_3
    | apply sorted_map_fst_file, FileMapBase.elements_3 | ].
  intros [k e].
  rewrite <- FileMapFacts.elements_mapsto_iff, FileMapFacts.map_mapsto_iff, InA_alt.
  split.
  - intros [a [He Hmt]]. subst e.
    apply FileMapFacts.elements_mapsto_iff in Hmt. rewrite InA_alt in Hmt.
    destruct Hmt as [[k' a'] [[Hk Ha] Hin]]. cbn in Hk, Ha. subst k' a'.
    exists (k, f a). split; [ split; reflexivity | ].
    apply in_map_iff. exists (k, a). split; [reflexivity | exact Hin].
  - intros [[k' e'] [[Hk He] Hin]]. cbn in Hk, He. subst k' e'.
    apply in_map_iff in Hin. destruct Hin as [[k'' a] [Heq Hin]]. injection Heq as Hk2 He2. subst k'' e.
    exists a. split; [reflexivity | ].
    apply FileMapFacts.elements_mapsto_iff. rewrite InA_alt. exists (k, a).
    split; [ split; reflexivity | exact Hin ].
Qed.

Lemma filemap_map_fst_elements {A B} (f : A -> B) (m : FileMapBase.t A) :
  map fst (FileMapBase.elements (FileMapBase.map f m)) = map fst (FileMapBase.elements m).
Proof. rewrite filemap_map_elements, map_map. reflexivity. Qed.

Lemma packagemap_map_fst_elements {A B} (f : A -> B) (m : PackageMapBase.t A) :
  map fst (PackageMapBase.elements (PackageMapBase.map f m)) = map fst (PackageMapBase.elements m).
Proof. rewrite packagemap_map_elements, map_map. reflexivity. Qed.

(** ---- two package maps with the SAME key DOMAIN (possibly different value types) have the SAME canonical key
    list.  (Map each to a common unit value; equal domains give [PM.Equal] unit maps, so
    [packagemap_elements_Equal] gives equal elements, hence equal keys.)  Used by the retention: the
    fresh-build plan derived from the RETAINED package buckets equals the one over [package_summaries]. ---- *)
Lemma packagemap_same_domain_keys {A B} (m1 : PackageMapBase.t A) (m2 : PackageMapBase.t B) :
  (forall k, PackageMapBase.In k m1 <-> PackageMapBase.In k m2) ->
  map fst (PackageMapBase.elements m1) = map fst (PackageMapBase.elements m2).
Proof.
  intro Hdom.
  rewrite <- (packagemap_map_fst_elements (fun _ => tt) m1), <- (packagemap_map_fst_elements (fun _ => tt) m2).
  f_equal. apply packagemap_elements_Equal.
  intro k. rewrite !PackageMapFacts.map_o.
  destruct (PackageMapBase.find k m1) as [a|] eqn:E1; destruct (PackageMapBase.find k m2) as [b|] eqn:E2;
    cbn [option_map]; try reflexivity.
  - exfalso. assert (PackageMapBase.In k m2) as Hin by
      (apply Hdom; exists a; apply PackageMapFacts.find_mapsto_iff; exact E1).
    apply PackageMapFacts.in_find_iff in Hin. rewrite E2 in Hin. exact (Hin eq_refl).
  - exfalso. assert (PackageMapBase.In k m1) as Hin by
      (apply Hdom; exists b; apply PackageMapFacts.find_mapsto_iff; exact E2).
    apply PackageMapFacts.in_find_iff in Hin. rewrite E1 in Hin. exact (Hin eq_refl).
Qed.
