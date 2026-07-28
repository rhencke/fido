From Stdlib Require Import String.
From Stdlib Require Import Structures.OrderedType Structures.OrderedTypeEx.
From Stdlib Require Import FSets.FMapInterface FSets.FMapAVL FSets.FMapFacts.
From Stdlib Require Import FSets.FMapPositive.
From Stdlib Require Import SetoidList.
From Fido Require Import FilePath.

Module NodeMap := FMapPositive.PositiveMap.

Module PackageMap := FMapAVL.Make String_as_OT.
Module PackageFacts := FMapFacts.WFacts_fun String_as_OT PackageMap.
Module PackageProperties := FMapFacts.WProperties_fun String_as_OT PackageMap.

(* Path equality is Leibniz, so a [FilePath.T] map key behaves as an identity rather than a setoid class. *)
Lemma file_path_text_inj : forall a b : FilePath.T, FilePath.text a = FilePath.text b -> a = b.
Proof. intros a b H. apply (proj1 (FilePath.equalb_spec a b)). unfold FilePath.equalb. rewrite H. apply String.eqb_refl. Qed.

Module FilePathOrder <: OrderedType.OrderedType.
  Definition t := FilePath.T.
  Definition eq (a b : t) := a = b.
  Definition lt (a b : t) := String_as_OT.lt (FilePath.text a) (FilePath.text b).
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
    destruct (String_as_OT.compare (FilePath.text a) (FilePath.text b)) as [Hlt|Heq|Hgt].
    - apply OrderedType.LT; exact Hlt.
    - apply OrderedType.EQ; unfold eq; apply file_path_text_inj; exact Heq.
    - apply OrderedType.GT; unfold lt; exact Hgt.
  Defined.
  Definition eq_dec (a b : t) : {eq a b} + {~ eq a b}.
  Proof.
    unfold eq. destruct (FilePath.equalb a b) eqn:E.
    - left. apply FilePath.equalb_spec. exact E.
    - right. intro H. apply (proj2 (FilePath.equalb_spec a b)) in H. rewrite H in E. discriminate.
  Defined.
End FilePathOrder.

Module FileMap := FMapAVL.Make FilePathOrder.
Module FileFacts := FMapFacts.WFacts_fun FilePathOrder FileMap.
Module FileProperties := FMapFacts.WProperties_fun FilePathOrder FileMap.
Module FileOrder := FMapFacts.OrdProperties FileMap.

(* [elements] is sorted by key, so equal maps enumerate identically — a function of meaning, not of balancing. *)
Lemma equal_list_key_element_eq {A} : forall (l1 l2 : list (FilePath.T * A)),
  eqlistA (@FileMap.eq_key_elt A) l1 l2 -> l1 = l2.
Proof.
  induction l1 as [|[k e] l1' IH]; intros l2 H; inversion H as [|x y l l' Hxy Htl]; subst; [ reflexivity | ].
  destruct y as [k' e']. destruct Hxy as [Hk He]. cbn in Hk, He. subst. f_equal. apply IH; exact Htl.
Qed.

Lemma file_elements_equal {A} : forall (m1 m2 : FileMap.t A),
  FileMap.Equal m1 m2 -> FileMap.elements m1 = FileMap.elements m2.
Proof.
  intros m1 m2 Heq. apply equal_list_key_element_eq.
  apply FileOrder.sort_equivlistA_eqlistA;
    [ apply FileMap.elements_3 | apply FileMap.elements_3 | ].
  intros [k e]. rewrite <- !FileFacts.elements_mapsto_iff, !FileFacts.find_mapsto_iff, (Heq k).
  reflexivity.
Qed.

Module PackageOrder := FMapFacts.OrdProperties PackageMap.

Lemma equal_list_key_element_eq_str {A} : forall (l1 l2 : list (string * A)),
  eqlistA (@PackageMap.eq_key_elt A) l1 l2 -> l1 = l2.
Proof.
  induction l1 as [|[k e] l1' IH]; intros l2 H; inversion H as [|x y l l' Hxy Htl]; subst; [ reflexivity | ].
  destruct y as [k' e']. destruct Hxy as [Hk He]. cbn in Hk, He. subst. f_equal. apply IH; exact Htl.
Qed.

Lemma package_elements_equal {A} : forall (m1 m2 : PackageMap.t A),
  PackageMap.Equal m1 m2 -> PackageMap.elements m1 = PackageMap.elements m2.
Proof.
  intros m1 m2 Heq. apply equal_list_key_element_eq_str.
  apply PackageOrder.sort_equivlistA_eqlistA;
    [ apply PackageMap.elements_3 | apply PackageMap.elements_3 | ].
  intros [k e]. rewrite <- !PackageFacts.elements_mapsto_iff, !PackageFacts.find_mapsto_iff, (Heq k).
  reflexivity.
Qed.

Lemma sorted_map_fst {A B} (f : A -> B) : forall l,
  Sorted (@PackageMap.lt_key A) l ->
  Sorted (@PackageMap.lt_key B) (map (fun kv => (fst kv, f (snd kv))) l).
Proof.
  induction l as [|a l IH]; intro Hs; cbn [map]; [constructor|].
  apply Sorted_inv in Hs. destruct Hs as [Hs Hhd]. constructor; [apply IH; exact Hs|].
  destruct l as [|b l']; cbn [map]; [constructor|]. apply HdRel_inv in Hhd. constructor. exact Hhd.
Qed.

Lemma package_map_elements {A B} (f : A -> B) : forall (m : PackageMap.t A),
  PackageMap.elements (PackageMap.map f m)
  = map (fun kv => (fst kv, f (snd kv))) (PackageMap.elements m).
Proof.
  intro m. apply equal_list_key_element_eq_str.
  apply PackageOrder.sort_equivlistA_eqlistA;
    [ apply PackageMap.elements_3
    | apply sorted_map_fst, PackageMap.elements_3 | ].
  intros [k e].
  rewrite <- PackageFacts.elements_mapsto_iff, PackageFacts.map_mapsto_iff, InA_alt.
  split.
  - intros [a [He Hmt]]. subst e.
    apply PackageFacts.elements_mapsto_iff in Hmt. rewrite InA_alt in Hmt.
    destruct Hmt as [[k' a'] [[Hk Ha] Hin]]. cbn in Hk, Ha. subst k' a'.
    exists (k, f a). split; [ split; reflexivity | ].
    apply in_map_iff. exists (k, a). split; [reflexivity | exact Hin].
  - intros [[k' e'] [[Hk He] Hin]]. cbn in Hk, He. subst k' e'.
    apply in_map_iff in Hin. destruct Hin as [[k'' a] [Heq Hin]]. injection Heq as Hk2 He2. subst k'' e.
    exists a. split; [reflexivity | ].
    apply PackageFacts.elements_mapsto_iff. rewrite InA_alt. exists (k, a).
    split; [ split; reflexivity | exact Hin ].
Qed.

Lemma sorted_map_fst_file {A B} (f : A -> B) : forall l,
  Sorted (@FileMap.lt_key A) l ->
  Sorted (@FileMap.lt_key B) (map (fun kv => (fst kv, f (snd kv))) l).
Proof.
  induction l as [|a l IH]; intro Hs; cbn [map]; [constructor|].
  apply Sorted_inv in Hs. destruct Hs as [Hs Hhd]. constructor; [apply IH; exact Hs|].
  destruct l as [|b l']; cbn [map]; [constructor|]. apply HdRel_inv in Hhd. constructor. exact Hhd.
Qed.

Lemma file_map_elements {A B} (f : A -> B) : forall (m : FileMap.t A),
  FileMap.elements (FileMap.map f m)
  = map (fun kv => (fst kv, f (snd kv))) (FileMap.elements m).
Proof.
  intro m. apply equal_list_key_element_eq.
  apply FileOrder.sort_equivlistA_eqlistA;
    [ apply FileMap.elements_3
    | apply sorted_map_fst_file, FileMap.elements_3 | ].
  intros [k e].
  rewrite <- FileFacts.elements_mapsto_iff, FileFacts.map_mapsto_iff, InA_alt.
  split.
  - intros [a [He Hmt]]. subst e.
    apply FileFacts.elements_mapsto_iff in Hmt. rewrite InA_alt in Hmt.
    destruct Hmt as [[k' a'] [[Hk Ha] Hin]]. cbn in Hk, Ha. subst k' a'.
    exists (k, f a). split; [ split; reflexivity | ].
    apply in_map_iff. exists (k, a). split; [reflexivity | exact Hin].
  - intros [[k' e'] [[Hk He] Hin]]. cbn in Hk, He. subst k' e'.
    apply in_map_iff in Hin. destruct Hin as [[k'' a] [Heq Hin]]. injection Heq as Hk2 He2. subst k'' e.
    exists a. split; [reflexivity | ].
    apply FileFacts.elements_mapsto_iff. rewrite InA_alt. exists (k, a).
    split; [ split; reflexivity | exact Hin ].
Qed.

Lemma file_map_fst_elements {A B} (f : A -> B) (m : FileMap.t A) :
  map fst (FileMap.elements (FileMap.map f m)) = map fst (FileMap.elements m).
Proof. rewrite file_map_elements, map_map. reflexivity. Qed.

Lemma package_map_fst_elements {A B} (f : A -> B) (m : PackageMap.t A) :
  map fst (PackageMap.elements (PackageMap.map f m)) = map fst (PackageMap.elements m).
Proof. rewrite package_map_elements, map_map. reflexivity. Qed.

Lemma package_same_domain_keys {A B} (m1 : PackageMap.t A) (m2 : PackageMap.t B) :
  (forall k, PackageMap.In k m1 <-> PackageMap.In k m2) ->
  map fst (PackageMap.elements m1) = map fst (PackageMap.elements m2).
Proof.
  intro Hdom.
  rewrite <- (package_map_fst_elements (fun _ => tt) m1), <- (package_map_fst_elements (fun _ => tt) m2).
  f_equal. apply package_elements_equal.
  intro k. rewrite !PackageFacts.map_o.
  destruct (PackageMap.find k m1) as [a|] eqn:E1; destruct (PackageMap.find k m2) as [b|] eqn:E2;
    cbn [option_map]; try reflexivity.
  - exfalso. assert (PackageMap.In k m2) as Hin by
      (apply Hdom; exists a; apply PackageFacts.find_mapsto_iff; exact E1).
    apply PackageFacts.in_find_iff in Hin. rewrite E2 in Hin. exact (Hin eq_refl).
  - exfalso. assert (PackageMap.In k m1) as Hin by
      (apply Hdom; exists b; apply PackageFacts.find_mapsto_iff; exact E2).
    apply PackageFacts.in_find_iff in Hin. rewrite E1 in Hin. exact (Hin eq_refl).
Qed.
