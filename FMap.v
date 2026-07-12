(** ============================================================================
    FMap — a minimal immutable finite map from string keys to values.  Keys are UNIQUE BY
    CONSTRUCTION (duplicate keys are unrepresentable — the record carries a [NoDup] proof over the
    keys, and lookup is a function, so a key cannot map to two values).  Lookup is deterministic,
    enumeration is finite, and equality is EXTENSIONAL by lookup.  There is NO imposed key order —
    it is an insertion-order association list, and the order is not part of map meaning (equality is
    by lookup).  A NoDup-keyed association list is the standard finite-map representation (cf. the
    Stdlib FMapWeakList); this one is kept small and self-contained so every theorem is direct.

    This is the shared spine of both the raw program (paths -> file ASTs) and the directory image
    (paths -> exact bytes).
    ============================================================================ *)
From Stdlib Require Import String List Bool.
Import ListNotations.

Record fmap (A : Type) : Type := mkFMap {
  fm_list  : list (string * A);
  fm_nodup : NoDup (List.map fst fm_list)
}.
Arguments mkFMap {A}.
Arguments fm_list {A}.
Arguments fm_nodup {A}.

Definition fm_keys {A} (m : fmap A) : list string := List.map fst (fm_list m).

(** THE structural invariant: the keys are duplicate-free.  This is [fm_nodup] exposed at [fm_keys] —
    it is the property that makes duplicate keys unrepresentable (below), distinct from the
    deterministic-lookup fact [fm_MapsTo_fun]. *)
Definition fm_keys_nodup {A} (m : fmap A) : NoDup (fm_keys m) := fm_nodup m.

(** Duplicate keys are UNREPRESENTABLE: the [NoDup] obligation [mkFMap] demands is uninhabited for any
    key-colliding list, so no [fmap] can carry the same key twice. *)
Lemma dup_key_unrepresentable {A} : forall (k : string) (x y : A),
  ~ NoDup (List.map fst [(k, x); (k, y)]).
Proof.
  intros k x y H; simpl in H; inversion H as [ | h t Hni Hnd ]; subst.
  apply Hni; left; reflexivity.
Qed.

Fixpoint fm_assoc {A} (k : string) (l : list (string * A)) : option A :=
  match l with
  | [] => None
  | (k', v) :: l' => if String.eqb k k' then Some v else fm_assoc k l'
  end.

Definition fm_find {A} (k : string) (m : fmap A) : option A := fm_assoc k (fm_list m).

Definition fm_MapsTo {A} (k : string) (v : A) (m : fmap A) : Prop := fm_find k m = Some v.

(** Deterministic lookup ⇒ a key never maps to two values (duplicate keys are inexpressible). *)
Lemma fm_MapsTo_fun {A} : forall k (v1 v2 : A) m, fm_MapsTo k v1 m -> fm_MapsTo k v2 m -> v1 = v2.
Proof. unfold fm_MapsTo; intros k v1 v2 m H1 H2; rewrite H1 in H2; injection H2; auto. Qed.

(** Extensional equality — order- and representation-independent. *)
Definition fm_Equal {A} (m1 m2 : fmap A) : Prop := forall k, fm_find k m1 = fm_find k m2.

(** ---- the empty map and singletons ---- *)

Lemma nodup_nil_key {A} : NoDup (List.map fst (@nil (string * A))).
Proof. constructor. Qed.

Definition fm_empty {A} : fmap A := mkFMap [] nodup_nil_key.

Lemma nodup_singleton_key {A} : forall (k : string) (v : A), NoDup (List.map fst [(k, v)]).
Proof. intros k v; simpl; constructor; [ intro H; inversion H | constructor ]. Qed.

Definition fm_singleton {A} (k : string) (v : A) : fmap A := mkFMap [(k, v)] (nodup_singleton_key k v).

Lemma fm_find_singleton {A} : forall k (v : A) k',
  fm_find k' (fm_singleton k v) = (if String.eqb k' k then Some v else None).
Proof. reflexivity. Qed.

Lemma fm_keys_singleton {A} : forall k (v : A), fm_keys (fm_singleton k v) = [k].
Proof. reflexivity. Qed.

(** ---- map over values (keys preserved) ---- *)

Definition fm_mapv {A B} (f : A -> B) (l : list (string * A)) : list (string * B) :=
  List.map (fun kv => (fst kv, f (snd kv))) l.

Lemma fm_mapv_keys {A B} : forall (f : A -> B) l, List.map fst (fm_mapv f l) = List.map fst l.
Proof. intros f l; induction l as [ | a l' IH ]; simpl; [ reflexivity | rewrite IH; reflexivity ]. Qed.

Definition fm_map {A B} (f : A -> B) (m : fmap A) : fmap B :=
  mkFMap (fm_mapv f (fm_list m))
         (eq_ind_r (fun ks => NoDup ks) (fm_nodup m) (fm_mapv_keys f (fm_list m))).

Lemma fm_keys_map {A B} : forall (f : A -> B) m, fm_keys (fm_map f m) = fm_keys m.
Proof. intros f m; unfold fm_keys, fm_map; simpl; apply fm_mapv_keys. Qed.

Lemma fm_map_find {A B} : forall (f : A -> B) m k,
  fm_find k (fm_map f m) = option_map f (fm_find k m).
Proof.
  intros f m k; unfold fm_find, fm_map, fm_mapv; simpl.
  induction (fm_list m) as [ | [k' v] l' IH ]; simpl; [ reflexivity | ].
  destruct (String.eqb k k'); [ reflexivity | exact IH ].
Qed.
