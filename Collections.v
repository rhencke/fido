(** ============================================================================
    Collections — the ONE standard-collection foundation (C1A).  Fido authors NO general-purpose map/set
    implementation: every identity-keyed collection is backed by a mature pinned-Rocq-stdlib map, and every
    membership-only collection by a mature standard set, behind a thin domain wrapper.  This module only
    instantiates standard functors and re-exports the facts Fido needs — it defines no tree/list-backed
    map/set.  (§2 pinned-stdlib research + §4 wrapper module.)

    Selected implementations (pinned rocq-stdlib 9.1.0):
    - general string/ordered-key finite map: [FMapAVL] (the standard mature AVL finite map);
    - positive-key finite map: [FMapPositive.PositiveMap] (the standard certified binary-trie map).
    ============================================================================ *)
From Stdlib Require Import String.
From Stdlib Require Import Structures.OrderedType Structures.OrderedTypeEx.
From Stdlib Require Import FSets.FMapInterface FSets.FMapAVL FSets.FMapFacts.
From Stdlib Require Import FSets.FMapPositive.
From Fido Require Import FilePath.

(** the standard positive-key map (a certified stdlib binary-trie map) — for per-file local-node indexes. *)
Module NodeMapBase := FMapPositive.PositiveMap.

(** the standard AVL map over the standard String ordered key — for the package-directory map. *)
Module PackageMapBase := FMapAVL.Make String_as_OT.
Module PackageMapFacts := FMapFacts.WFacts_fun String_as_OT PackageMapBase.

(** ---- §4.1 the [FilePath] ordered key: a total lexicographic order via [fp_string], reusing the pinned
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

(** ---- §4.2 the standard AVL file map keyed by [FilePath], plus its standard facts. ---- *)
Module FileMapBase := FMapAVL.Make FilePath_OT.
Module FileMapFacts := FMapFacts.WFacts_fun FilePath_OT FileMapBase.
Module FileMapProps := FMapFacts.WProperties_fun FilePath_OT FileMapBase.
