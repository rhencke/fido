(** ============================================================================
    FMap — a minimal immutable finite map from keys of ANY type (with decidable equality) to values.
    Keys are UNIQUE BY CONSTRUCTION: the record carries a [NoDup] proof over the keys, so duplicate keys
    are unrepresentable.  THE structural invariant is [fm_keys_nodup] (the keys are duplicate-free)
    together with [dup_key_unrepresentable] (a key-colliding list cannot satisfy the constructor
    obligation).  A functional first-match lookup ([fm_MapsTo_fun]) is a DISTINCT, weaker fact — it is
    functional even over a duplicate association list — so it is NOT the evidence for uniqueness.

    Enumeration is finite ([fm_list]); there is NO imposed key order; SEMANTIC equality is EXTENSIONAL
    by lookup ([fm_Equal]) and is deliberately distinct from Rocq record equality [=] (which is
    representation-sensitive: two maps with the same entries in a different list order are [fm_Equal] but
    not [eq]).  A list builder ([fm_of_list]) REJECTS duplicate keys and returns a map whose uniqueness
    proof is intrinsic — there is no last-write-wins and no list-plus-later-dedup.

    The key type is a parameter, not fixed to [string]: the program is keyed by the intrinsic [FilePath].
    ============================================================================ *)
From Stdlib Require Import List Bool.
Import ListNotations.

Record fmap (K A : Type) : Type := mkFMap {
  fm_list  : list (K * A);
  fm_nodup : NoDup (List.map fst fm_list)
}.
Arguments mkFMap {K A}.
Arguments fm_list {K A}.
Arguments fm_nodup {K A}.

Definition fm_keys {K A} (m : fmap K A) : list K := List.map fst (fm_list m).

(** THE structural invariant: the keys are duplicate-free (this is what "duplicate keys unrepresentable"
    means, with [dup_key_unrepresentable]); DISTINCT from the deterministic-lookup fact below. *)
Definition fm_keys_nodup {K A} (m : fmap K A) : NoDup (fm_keys m) := fm_nodup m.

Lemma dup_key_unrepresentable {K A} : forall (k : K) (x y : A),
  ~ NoDup (List.map fst [(k, x); (k, y)]).
Proof.
  intros k x y H; simpl in H; inversion H as [ | h t Hni Hnd ]; subst.
  apply Hni; left; reflexivity.
Qed.

(** ---- deterministic lookup (needs the key's boolean equality) ---- *)

Fixpoint fm_assoc {K A} (eqb : K -> K -> bool) (k : K) (l : list (K * A)) : option A :=
  match l with
  | [] => None
  | (k', v) :: l' => if eqb k k' then Some v else fm_assoc eqb k l'
  end.

Definition fm_find {K A} (eqb : K -> K -> bool) (k : K) (m : fmap K A) : option A :=
  fm_assoc eqb k (fm_list m).

Definition fm_MapsTo {K A} (eqb : K -> K -> bool) (k : K) (v : A) (m : fmap K A) : Prop :=
  fm_find eqb k m = Some v.

(** Deterministic lookup ⇒ a key never maps to two values (a real finite map, not a multimap).  NOTE:
    this is functional even for a duplicate-keyed list, so it is NOT evidence of key uniqueness. *)
Lemma fm_MapsTo_fun {K A} (eqb : K -> K -> bool) :
  forall k (v1 v2 : A) m, fm_MapsTo eqb k v1 m -> fm_MapsTo eqb k v2 m -> v1 = v2.
Proof. unfold fm_MapsTo; intros k v1 v2 m H1 H2; rewrite H1 in H2; injection H2; auto. Qed.

(** SEMANTIC map equality — order/representation-independent; distinct from record [=]. *)
Definition fm_Equal {K A} (eqb : K -> K -> bool) (m1 m2 : fmap K A) : Prop :=
  forall k, fm_find eqb k m1 = fm_find eqb k m2.

(** ---- the empty map and singletons ---- *)

Lemma nodup_nil_key {K A} : NoDup (List.map fst (@nil (K * A))).
Proof. constructor. Qed.

Definition fm_empty {K A} : fmap K A := mkFMap [] nodup_nil_key.

Lemma nodup_singleton_key {K A} : forall (k : K) (v : A), NoDup (List.map fst [(k, v)]).
Proof. intros k v; simpl; constructor; [ intro H; inversion H | constructor ]. Qed.

Definition fm_singleton {K A} (k : K) (v : A) : fmap K A := mkFMap [(k, v)] (nodup_singleton_key k v).

Lemma fm_keys_singleton {K A} : forall (k : K) (v : A), fm_keys (fm_singleton k v) = [k].
Proof. reflexivity. Qed.

(** ---- a list builder that REJECTS duplicate keys ---- *)

Fixpoint no_dup_keysb {K A} (eqb : K -> K -> bool) (l : list (K * A)) : bool :=
  match l with
  | [] => true
  | (k, _) :: l' => negb (existsb (fun kv => eqb k (fst kv)) l') && no_dup_keysb eqb l'
  end.

Section Builder.
  Context {K A : Type} (eqb : K -> K -> bool) (eqb_eq : forall x y, eqb x y = true <-> x = y).

  Lemma existsb_key_In : forall (k : K) (l : list (K * A)),
    existsb (fun kv => eqb k (fst kv)) l = true <-> In k (List.map fst l).
  Proof.
    intros k l; induction l as [ | [k' v] l' IH ]; simpl.
    - split; [ discriminate | intros [] ].
    - rewrite Bool.orb_true_iff, IH. split.
      + intros [He | Hin]; [ left; symmetry; apply eqb_eq; exact He | right; exact Hin ].
      + intros [He | Hin]; [ left; apply eqb_eq; symmetry; exact He | right; exact Hin ].
  Qed.

  Lemma no_dup_keysb_correct : forall (l : list (K * A)),
    no_dup_keysb eqb l = true -> NoDup (List.map fst l).
  Proof.
    induction l as [ | [k v] l' IH ]; simpl; intro H.
    - constructor.
    - apply Bool.andb_true_iff in H; destruct H as [Hne Hrest].
      constructor.
      + rewrite <- existsb_key_In. rewrite Bool.negb_true_iff in Hne. rewrite Hne. discriminate.
      + apply IH; exact Hrest.
  Qed.

  Definition fm_of_list (l : list (K * A)) : option (fmap K A) :=
    (match no_dup_keysb eqb l as b return no_dup_keysb eqb l = b -> option (fmap K A) with
     | true  => fun H => Some (mkFMap l (no_dup_keysb_correct l H))
     | false => fun _ => None
     end) eq_refl.

  Lemma fm_of_list_list : forall l m, fm_of_list l = Some m -> fm_list m = l.
  Proof.
    intros l m. unfold fm_of_list.
    generalize (@eq_refl bool (no_dup_keysb eqb l)).
    destruct (no_dup_keysb eqb l) at 2 3; intro H; [ | discriminate ].
    intro Heq; injection Heq as <-; reflexivity.
  Qed.
End Builder.

(** ---- map over values (keys preserved) ---- *)

Definition fm_mapv {K A B} (f : A -> B) (l : list (K * A)) : list (K * B) :=
  List.map (fun kv => (fst kv, f (snd kv))) l.

Lemma fm_mapv_keys {K A B} : forall (f : A -> B) (l : list (K * A)),
  List.map fst (fm_mapv f l) = List.map fst l.
Proof. intros f l; induction l as [ | a l' IH ]; simpl; [ reflexivity | rewrite IH; reflexivity ]. Qed.

Definition fm_map {K A B} (f : A -> B) (m : fmap K A) : fmap K B :=
  mkFMap (fm_mapv f (fm_list m))
         (eq_ind_r (fun ks => NoDup ks) (fm_nodup m) (fm_mapv_keys f (fm_list m))).

Lemma fm_keys_map {K A B} : forall (f : A -> B) (m : fmap K A), fm_keys (fm_map f m) = fm_keys m.
Proof. intros f m; unfold fm_keys, fm_map; simpl; apply fm_mapv_keys. Qed.

Lemma fm_list_map {K A B} : forall (f : A -> B) (m : fmap K A),
  fm_list (fm_map f m) = List.map (fun kv => (fst kv, f (snd kv))) (fm_list m).
Proof. reflexivity. Qed.
