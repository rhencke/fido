(* Index.Child — the one canonical direct-child identity ChildAt and its generic laws. *)
From Stdlib Require Import List Bool Arith PeanoNat Lia Eqdep_dec PArith FSets.FMapFacts.
From Fido Require Import Index.Model Index.
Import ListNotations.

(* the one canonical positional direct-child identity: exact parent and source ordinal in the type *)
Record ChildAt {p} {idx : ProgramIndex p} (parent : NodeRef idx) (ordinal : nat) : Type := mkChildAt {
  ca_child : NodeRef idx ;
  ca_at    : nth_error (node_children parent) ordinal = Some ca_child
}.
Arguments mkChildAt {p idx parent ordinal} _ _.
Arguments ca_child {p idx parent ordinal} _.
Arguments ca_at {p idx parent ordinal} _.
Definition ca_parent {p} {idx : ProgramIndex p} {parent : NodeRef idx} {ordinal : nat}
  (_ : ChildAt parent ordinal) : NodeRef idx := parent.
Definition ca_ordinal {p} {idx : ProgramIndex p} {parent : NodeRef idx} {ordinal : nat}
  (_ : ChildAt parent ordinal) : nat := ordinal.

(* parent and ordinal determine the child: the canonical edge is a function of its type indices *)
Lemma ca_det {p} {idx : ProgramIndex p} {parent : NodeRef idx} {ordinal : nat}
  (e1 e2 : ChildAt parent ordinal) : ca_child e1 = ca_child e2.
Proof. pose proof (ca_at e1) as H1. pose proof (ca_at e2) as H2. rewrite H1 in H2. injection H2 as H2. exact H2. Qed.

(* the child is a genuine direct child of the exact parent *)
Lemma ca_in {p} {idx : ProgramIndex p} {parent : NodeRef idx} {ordinal : nat} (e : ChildAt parent ordinal) :
  In (ca_child e) (node_children parent).
Proof. exact (nth_error_In _ _ (ca_at e)). Qed.

(* parent round trip: the retained Index parent relation points the child back to the exact parent *)
Lemma ca_node_parent {p} {idx : ProgramIndex p} {parent : NodeRef idx} {ordinal : nat}
  (e : ChildAt parent ordinal) : node_parent (ca_child e) = Some parent.
Proof. apply node_children_inverse, ca_in. Qed.

(* strict structural progress: the exact direct child's position strictly follows its parent's — parent <> child *)
Lemma child_pos_gt_parent {p} {idx : ProgramIndex p} {parent : NodeRef idx} {ordinal : nat}
  (e : ChildAt parent ordinal) : nr_pos parent < nr_pos (ca_child e).
Proof. exact (node_parent_pos_lt (ca_child e) parent (ca_node_parent e)). Qed.

(* the child's role is exactly the layout role its parent's view fixes at this ordinal *)
Lemma ca_role {p} {idx : ProgramIndex p} {parent : NodeRef idx} {ordinal : nat}
  (e : ChildAt parent ordinal) : node_role (ca_child e) = layout_role (node_view parent) ordinal.
Proof. exact (node_child_role parent (ca_child e) ordinal (ca_at e)). Qed.

(* ordinal order is source order across the canonical edges of one parent *)
Lemma ca_pos_lt {p} {idx : ProgramIndex p} {parent : NodeRef idx} {i j : nat}
  (ei : ChildAt parent i) (ej : ChildAt parent j) : i < j -> nr_pos (ca_child ei) < nr_pos (ca_child ej).
Proof. intro H. exact (node_children_asc parent _ _ i j H (ca_at ei) (ca_at ej)). Qed.

(* every direct child has a canonical positional identity *)
Lemma ca_exists {p} {idx : ProgramIndex p} (parent c : NodeRef idx) :
  In c (node_children parent) -> exists (k : nat) (e : ChildAt parent k), ca_child e = c.
Proof.
  intro Hin. destruct (In_nth_error _ _ Hin) as [k Hk]. exists k, (mkChildAt c Hk). reflexivity.
Qed.

(* ...and exactly one: two canonical edges sharing a child share the ordinal *)
Lemma ca_ord_unique {p} {idx : ProgramIndex p} {parent : NodeRef idx} {i j : nat}
  (ei : ChildAt parent i) (ej : ChildAt parent j) : ca_child ei = ca_child ej -> i = j.
Proof.
  intro H. apply (node_child_ord_unique parent (ca_child ej) i j); [ rewrite <- H; exact (ca_at ei) | exact (ca_at ej) ].
Qed.

(* index transport along a proven ordinal equality; never a silent renumbering *)
Definition ca_cast {p} {idx : ProgramIndex p} {parent : NodeRef idx} {i j : nat}
  (E : i = j) (e : ChildAt parent i) : ChildAt parent j :=
  match E in _ = j0 return ChildAt parent j0 with eq_refl => e end.

(* the total in-range constructor: an ordinal below the children length resolves without option *)
Definition child_at_lt {p} {idx : ProgramIndex p} (r : NodeRef idx) (k : nat)
  (H : k < length (node_children r)) : ChildAt r k :=
  mkChildAt (nth_lt (node_children r) k H) (nth_lt_nth_error (node_children r) k H).

(* total ordinal-indexed child access: the exact canonical edge below the child count, None beyond it *)
Definition child_at_opt {p} {idx : ProgramIndex p} (r : NodeRef idx) (k : nat) : option (ChildAt r k) :=
  (match nth_error (node_children r) k as o
         return nth_error (node_children r) k = o -> option (ChildAt r k) with
   | Some c => fun H => Some (mkChildAt c H)
   | None => fun _ => None
   end) eq_refl.

(* an inhabited ordinal is never refused: any canonical edge at k forces the total access to answer *)
Lemma child_at_opt_some {p} {idx : ProgramIndex p} (r : NodeRef idx) (k : nat) (e : ChildAt r k) :
  child_at_opt r k <> None.
Proof.
  unfold child_at_opt.
  generalize (@eq_refl (option (NodeRef idx)) (nth_error (node_children r) k)).
  destruct (nth_error (node_children r) k) at 2 3; intro H; [ discriminate |].
  exfalso. pose proof (ca_at e) as He. rewrite H in He. discriminate He.
Qed.

(* a refused ordinal is out of range: None answers exactly beyond the retained child list *)
Lemma child_at_opt_none {p} {idx : ProgramIndex p} (r : NodeRef idx) (k : nat) :
  child_at_opt r k = None -> nth_error (node_children r) k = None.
Proof.
  unfold child_at_opt.
  generalize (@eq_refl (option (NodeRef idx)) (nth_error (node_children r) k)).
  destruct (nth_error (node_children r) k) at 2 3; intro H; [ discriminate | intros _; exact H ].
Qed.

(* the edge form of the statement-parent law: a statement edge's parent is a block *)
Lemma child_at_stmt_block {p} {idx : ProgramIndex p} {par : NodeRef idx} {k : nat}
  (e : ChildAt par k) (sh : StmtShape) :
  node_view (ca_child e) = VStmt sh -> node_view par = VBlock.
Proof. intro Hv. exact (node_child_stmt_block par (ca_child e) k sh (ca_at e) Hv). Qed.

(* the edge forms of the spec-parent, declaration-parent, and spec-name-parent laws *)
Lemma child_at_spec_decl {p} {idx : ProgramIndex p} {par : NodeRef idx} {k : nat}
  (e : ChildAt par k) (fl : SpecFlavor) :
  spec_view_of_flavor fl (node_view (ca_child e)) -> node_view par = VDecl fl.
Proof. intro Hv. exact (node_child_spec_decl par (ca_child e) k fl (ca_at e) Hv). Qed.

Lemma child_at_decl_parent {p} {idx : ProgramIndex p} {par : NodeRef idx} {k : nat}
  (e : ChildAt par k) (fl : SpecFlavor) :
  node_view (ca_child e) = VDecl fl -> node_view par = VStmt SSDecl \/ node_view par = VTop TSTopDecl.
Proof. intro Hv. exact (node_child_decl_parent par (ca_child e) k fl (ca_at e) Hv). Qed.

Lemma child_at_specname_spec {p} {idx : ProgramIndex p} {par : NodeRef idx} {k : nat}
  (e : ChildAt par k) (fl : SpecFlavor) :
  node_role (ca_child e) = RSpecName fl -> spec_view_of_flavor fl (node_view par).
Proof. intro Hr. exact (node_child_specname_spec par (ca_child e) k fl (ca_at e) Hr). Qed.

(* an edge ordinal is bounded by the parent shape's exact child count *)
Lemma child_at_count_lt {p} {idx : ProgramIndex p} {r : NodeRef idx} {k : nat}
  (e : ChildAt r k) (m : nat) : layout_count (node_view r) = Some m -> k < m.
Proof.
  intro Hc.
  assert (Hlt : k < length (node_children r))
    by (apply nth_error_Some; rewrite (ca_at e); discriminate).
  rewrite (node_children_count r m Hc) in Hlt. exact Hlt.
Qed.

(* a one-child parent admits child edges at ordinal zero alone *)
Lemma singleton_child_ordinal {p} {idx : ProgramIndex p} {r : NodeRef idx} {k : nat}
  (e : ChildAt r k) : layout_count (node_view r) = Some 1 -> k = 0.
Proof. intro Hc. pose proof (child_at_count_lt e 1 Hc). lia. Qed.


Lemma skipn_nth : forall {A} (k : nat) (l : list A) (j : nat), nth_error (skipn k l) j = nth_error l (k + j).
Proof.
  intros A k; induction k as [|k' IH]; intros l j; [ reflexivity |].
  destruct l as [|x xs]; cbn; [ destruct j; reflexivity | apply IH ].
Qed.

Lemma skipn_head_at : forall {A} (l l' : list A) (k : nat) (c : A),
  c :: l' = skipn k l -> nth_error l k = Some c.
Proof.
  intros A l l' k c E. pose proof (skipn_nth k l 0) as H.
  rewrite <- E in H. cbn in H. rewrite Nat.add_0_r in H. symmetry. exact H.
Qed.

Lemma skipn_succ : forall {A} (k : nat) (l : list A), skipn (S k) l = tl (skipn k l).
Proof.
  intros A k; induction k as [|k' IH]; intros [|x xs]; cbn; try reflexivity. exact (IH xs).
Qed.

Lemma skipn_tail_at : forall {A} (l l' : list A) (k : nat) (c : A),
  c :: l' = skipn k l -> l' = skipn (S k) l.
Proof. intros A l l' k c E. rewrite skipn_succ, <- E. reflexivity. Qed.

(* the total canonical enumeration: one exact edge per direct child, ordinal-ascending, no filter *)
Fixpoint children_from {p} {idx : ProgramIndex p} (r : NodeRef idx) (k : nat) (l : list (NodeRef idx))
  {struct l} : l = skipn k (node_children r) -> list { o : nat & ChildAt r o } :=
  match l with
  | [] => fun _ => []
  | c :: rest => fun E =>
      existT _ k (mkChildAt c (skipn_head_at (node_children r) rest k c E))
      :: children_from r (S k) rest (skipn_tail_at (node_children r) rest k c E)
  end.
Definition all_children {p} {idx : ProgramIndex p} (r : NodeRef idx) : list { o : nat & ChildAt r o } :=
  children_from r 0 (node_children r) eq_refl.

Lemma children_from_ords {p} {idx : ProgramIndex p} (r : NodeRef idx) :
  forall l k E, map (@projT1 _ _) (children_from r k l E) = seq k (length l).
Proof.
  induction l as [|c rest IH]; intros k E; cbn; [ reflexivity | f_equal; apply IH ].
Qed.

Lemma children_from_childs {p} {idx : ProgramIndex p} (r : NodeRef idx) :
  forall l k E, map (fun x => ca_child (projT2 x)) (children_from r k l E) = l.
Proof.
  induction l as [|c rest IH]; intros k E; cbn; [ reflexivity | f_equal; apply IH ].
Qed.

(* the canonical enumeration covers exactly the direct children, in exact source order *)
Lemma all_children_ords {p} {idx : ProgramIndex p} (r : NodeRef idx) :
  map (@projT1 _ _) (all_children r) = seq 0 (length (node_children r)).
Proof. apply children_from_ords. Qed.
Lemma all_children_childs {p} {idx : ProgramIndex p} (r : NodeRef idx) :
  map (fun x => ca_child (projT2 x)) (all_children r) = node_children r.
Proof. apply children_from_childs. Qed.


