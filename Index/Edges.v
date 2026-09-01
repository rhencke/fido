(* Index.Edges — specialized ChildAt refinements: app/unary/exprstmt/spec/short/main/preceding edges + collections. *)
From Stdlib Require Import List Bool Arith PeanoNat Lia Eqdep_dec PArith FSets.FMapFacts.
From Fido Require Import Index.Model Index Index.Child Index.Refs.
Import ListNotations.

(* the specialized edges: each retains the one canonical ChildAt at its exact formula ordinal *)
Record ApplicationHeadEdge {p} {idx : ProgramIndex p} (a : AppRef idx) : Type := mkAppHead {
  ah_at : ChildAt (app_node a) 0
}.
Arguments mkAppHead {p idx a} _.
Arguments ah_at {p idx a} _.
Definition ah_child {p} {idx : ProgramIndex p} {a : AppRef idx} (e : ApplicationHeadEdge a) : NodeRef idx :=
  ca_child (ah_at e).

Record ApplicationArgEdge {p} {idx : ProgramIndex p} (a : AppRef idx) (i : nat) : Type := mkAppArg {
  aa_at : ChildAt (app_node a) (S i)
}.
Arguments mkAppArg {p idx a i} _.
Arguments aa_at {p idx a i} _.
Definition aa_child {p} {idx : ProgramIndex p} {a : AppRef idx} {i : nat} (e : ApplicationArgEdge a i)
  : NodeRef idx := ca_child (aa_at e).

Record UnaryOperandEdge {p} {idx : ProgramIndex p} (u : UnaryRef idx) : Type := mkUnOperand {
  uo_at : ChildAt (un_node u) 0
}.
Arguments mkUnOperand {p idx u} _.
Arguments uo_at {p idx u} _.
Definition uo_child {p} {idx : ProgramIndex p} {u : UnaryRef idx} (e : UnaryOperandEdge u) : NodeRef idx :=
  ca_child (uo_at e).

Record ExprStmtExprEdge {p} {idx : ProgramIndex p} (s : ExprStmtRef idx) : Type := mkExprStmtE {
  ee_at : ChildAt (exs_node s) 0
}.
Arguments mkExprStmtE {p idx s} _.
Arguments ee_at {p idx s} _.
Definition ee_child {p} {idx : ProgramIndex p} {s : ExprStmtRef idx} (e : ExprStmtExprEdge s) : NodeRef idx :=
  ca_child (ee_at e).

Record MainBodyEdge {p} {idx : ProgramIndex p} (m : MainOccurrenceRef idx) : Type := mkMainBody {
  mb_at : ChildAt (mo_node m) 0
}.
Arguments mkMainBody {p idx m} _.
Arguments mb_at {p idx m} _.
Definition mb_child {p} {idx : ProgramIndex p} {m : MainOccurrenceRef idx} (e : MainBodyEdge m) : NodeRef idx :=
  ca_child (mb_at e).

Record SpecNameEdge {p} {idx : ProgramIndex p} {fl : SpecFlavor} (sp : SpecRef idx fl) (i : nat) : Type := mkSpecName {
  sn_at : ChildAt (sp_node sp) i ;
  sn_lt : i < shape_names fl (sp_shape sp)
}.
Arguments mkSpecName {p idx fl sp i} _ _.
Arguments sn_at {p idx fl sp i} _.
Arguments sn_lt {p idx fl sp i} _.
Definition sn_child {p} {idx : ProgramIndex p} {fl : SpecFlavor} {sp : SpecRef idx fl} {i : nat}
  (e : SpecNameEdge sp i) : NodeRef idx := ca_child (sn_at e).

Record SpecValueEdge {p} {idx : ProgramIndex p} {fl : SpecFlavor} (sp : SpecRef idx fl) (j : nat) : Type := mkSpecValue {
  sv_at : ChildAt (sp_node sp) (value_ordinal fl (sp_shape sp) j) ;
  sv_lt : j < shape_values fl (sp_shape sp)
}.
Arguments mkSpecValue {p idx fl sp j} _ _.
Arguments sv_at {p idx fl sp j} _.
Arguments sv_lt {p idx fl sp j} _.
Definition sv_child {p} {idx : ProgramIndex p} {fl : SpecFlavor} {sp : SpecRef idx fl} {j : nat}
  (e : SpecValueEdge sp j) : NodeRef idx := ca_child (sv_at e).

(* exact optional presence: absence is a shape fact, never a failed lookup; presence is the exact edge *)
Inductive SpecTypePresence {p} {idx : ProgramIndex p} {fl : SpecFlavor} (sp : SpecRef idx fl) : Type :=
| SpecTypePresent : shape_has_type fl (sp_shape sp) = true
                    -> ChildAt (sp_node sp) (type_ordinal fl (sp_shape sp)) -> SpecTypePresence sp
| SpecTypeAbsent  : shape_has_type fl (sp_shape sp) = false -> SpecTypePresence sp.
Arguments SpecTypePresent {p idx fl sp} _ _.
Arguments SpecTypeAbsent {p idx fl sp} _.

Record ShortLhsEdge {p} {idx : ProgramIndex p} (st : ShortStmtRef idx) (i : nat) : Type := mkShortLhs {
  sl_at : ChildAt (sh_node st) i ;
  sl_lt : i < sh_names st
}.
Arguments mkShortLhs {p idx st i} _ _.
Arguments sl_at {p idx st i} _.
Arguments sl_lt {p idx st i} _.
Definition sl_child {p} {idx : ProgramIndex p} {st : ShortStmtRef idx} {i : nat} (e : ShortLhsEdge st i)
  : NodeRef idx := ca_child (sl_at e).

Record ShortRhsEdge {p} {idx : ProgramIndex p} (st : ShortStmtRef idx) (j : nat) : Type := mkShortRhs {
  sr_at : ChildAt (sh_node st) (sh_names st + j) ;
  sr_lt : j < sh_values st
}.
Arguments mkShortRhs {p idx st j} _ _.
Arguments sr_at {p idx st j} _.
Arguments sr_lt {p idx st j} _.
Definition sr_child {p} {idx : ProgramIndex p} {st : ShortStmtRef idx} {j : nat} (e : ShortRhsEdge st j)
  : NodeRef idx := ca_child (sr_at e).

(* a node's own canonical edge under its exact parent: the retained identity preceding-sibling edges refine *)
Record SelfEdge {p} {idx : ProgramIndex p} (r : NodeRef idx) : Type := mkSelfEdge {
  se_parent   : NodeRef idx ;
  se_ord      : nat ;
  se_at       : ChildAt se_parent se_ord ;
  se_child_eq : ca_child se_at = r
}.
Arguments mkSelfEdge {p idx r} _ _ _ _.
Arguments se_parent {p idx r} _.
Arguments se_ord {p idx r} _.
Arguments se_at {p idx r} _.
Arguments se_child_eq {p idx r} _.

(* an exact preceding sibling: the canonical edges of target and sibling under one parent, ordinal below ordinal *)
Record PrecedingSiblingEdge {p} {idx : ProgramIndex p} (target : NodeRef idx) (i : nat) : Type := mkPrecSib {
  ps_self : SelfEdge target ;
  ps_at   : ChildAt (se_parent ps_self) i ;
  ps_lt   : i < se_ord ps_self
}.
Arguments mkPrecSib {p idx target i} _ _ _.
Arguments ps_self {p idx target i} _.
Arguments ps_at {p idx target i} _.
Arguments ps_lt {p idx target i} _.
Definition ps_sibling {p} {idx : ProgramIndex p} {target : NodeRef idx} {i : nat}
  (e : PrecedingSiblingEdge target i) : NodeRef idx := ca_child (ps_at e).

(* per-family role laws: each edge's child carries exactly the role the parent's shape fixes at its ordinal *)
Lemma layout_role_name : forall fl (sh : SpecShape fl) i,
  i < shape_names fl sh -> layout_role (spec_view_of fl sh) i = RSpecName fl.
Proof.
  destruct fl; intros sh i H; destruct sh; cbn [spec_view_of shape_names layout_role] in H |- *;
    try (rewrite (proj2 (Nat.ltb_lt _ _) H); reflexivity); try reflexivity;
    try (destruct i; [ reflexivity | lia ]).
Qed.

Lemma layout_role_type : forall fl (sh : SpecShape fl),
  shape_has_type fl sh = true -> layout_role (spec_view_of fl sh) (type_ordinal fl sh) = RTypeUse.
Proof.
  destruct fl; intros sh Ht; destruct sh;
    cbn [spec_view_of shape_has_type shape_names type_ordinal layout_role] in Ht |- *;
    try discriminate Ht; subst; try rewrite Nat.ltb_irrefl; try rewrite Nat.eqb_refl; reflexivity.
Qed.

Lemma layout_role_value : forall fl (sh : SpecShape fl) j,
  j < shape_values fl sh -> layout_role (spec_view_of fl sh) (value_ordinal fl sh j) = RPlain.
Proof.
  destruct fl; intros sh j H; destruct sh;
    cbn [spec_view_of shape_values shape_names shape_has_type value_ordinal layout_role] in H |- *; try lia.
  - destruct has_type; unfold value_ordinal; cbn [shape_names shape_has_type]; cbv beta iota zeta.
    + assert (E1 : (n_names + 1 + j <? n_names) = false) by (apply Nat.ltb_ge; lia).
      assert (E2 : (n_names + 1 + j =? n_names) = false) by (apply Nat.eqb_neq; lia).
      rewrite E1, E2. reflexivity.
    + assert (E1 : (n_names + 0 + j <? n_names) = false) by (apply Nat.ltb_ge; lia).
      rewrite E1. reflexivity.
  - destruct has_type; unfold value_ordinal; cbn [shape_names shape_has_type]; cbv beta iota zeta.
    + assert (E1 : (n_names + 1 + j <? n_names) = false) by (apply Nat.ltb_ge; lia).
      assert (E2 : (n_names + 1 + j =? n_names) = false) by (apply Nat.eqb_neq; lia).
      rewrite E1, E2. reflexivity.
    + assert (E1 : (n_names + 0 + j <? n_names) = false) by (apply Nat.ltb_ge; lia).
      rewrite E1. reflexivity.
Qed.

Lemma ah_role {p} {idx : ProgramIndex p} {a : AppRef idx} (e : ApplicationHeadEdge a) :
  node_role (ah_child e) = RApplicationHead.
Proof. unfold ah_child. rewrite (ca_role (ah_at e)), (app_ok a). reflexivity. Qed.

Lemma aa_role {p} {idx : ProgramIndex p} {a : AppRef idx} {i : nat} (e : ApplicationArgEdge a i) :
  node_role (aa_child e) = RApplicationArg i.
Proof. unfold aa_child. rewrite (ca_role (aa_at e)), (app_ok a). reflexivity. Qed.

Lemma uo_role {p} {idx : ProgramIndex p} {u : UnaryRef idx} (e : UnaryOperandEdge u) :
  node_role (uo_child e) = RUnaryOperand.
Proof. unfold uo_child. rewrite (ca_role (uo_at e)), (un_ok u). reflexivity. Qed.

Lemma ee_role {p} {idx : ProgramIndex p} {s : ExprStmtRef idx} (e : ExprStmtExprEdge s) :
  node_role (ee_child e) = RExprStatementExpr.
Proof. unfold ee_child. rewrite (ca_role (ee_at e)), (exs_ok s). reflexivity. Qed.

Lemma sn_role {p} {idx : ProgramIndex p} {fl : SpecFlavor} {sp : SpecRef idx fl} {i : nat}
  (e : SpecNameEdge sp i) : node_role (sn_child e) = RSpecName fl.
Proof. unfold sn_child. rewrite (ca_role (sn_at e)), (sp_ok sp). apply layout_role_name. exact (sn_lt e). Qed.

Lemma sv_role {p} {idx : ProgramIndex p} {fl : SpecFlavor} {sp : SpecRef idx fl} {j : nat}
  (e : SpecValueEdge sp j) : node_role (sv_child e) = RPlain.
Proof. unfold sv_child. rewrite (ca_role (sv_at e)), (sp_ok sp). apply layout_role_value. exact (sv_lt e). Qed.

Lemma type_edge_role {p} {idx : ProgramIndex p} {fl : SpecFlavor} {sp : SpecRef idx fl}
  (Ht : shape_has_type fl (sp_shape sp) = true) (e : ChildAt (sp_node sp) (type_ordinal fl (sp_shape sp))) :
  node_role (ca_child e) = RTypeUse.
Proof. rewrite (ca_role e), (sp_ok sp). apply layout_role_type. exact Ht. Qed.

Lemma sl_role {p} {idx : ProgramIndex p} {st : ShortStmtRef idx} {i : nat} (e : ShortLhsEdge st i) :
  node_role (sl_child e) = RShortLhs.
Proof.
  unfold sl_child. rewrite (ca_role (sl_at e)), (sh_ok st). cbn [layout_role].
  rewrite (proj2 (Nat.ltb_lt _ _) (sl_lt e)). reflexivity.
Qed.

Lemma sr_role {p} {idx : ProgramIndex p} {st : ShortStmtRef idx} {j : nat} (e : ShortRhsEdge st j) :
  node_role (sr_child e) = RPlain.
Proof.
  unfold sr_child. rewrite (ca_role (sr_at e)), (sh_ok st). cbn [layout_role].
  assert (E1 : (sh_names st + j <? sh_names st) = false) by (apply Nat.ltb_ge; lia).
  rewrite E1. reflexivity.
Qed.

(* the fixed-main body is exactly a block, and projects an exact BlockRef *)
Lemma is_main_view_eq : forall v, is_main_view v = true -> v = VTop TSMain.
Proof. destruct v; cbn; intro H; try discriminate H. destruct t; [ discriminate H | reflexivity ]. Qed.

Lemma mb_block {p} {idx : ProgramIndex p} {m : MainOccurrenceRef idx} (e : MainBodyEdge m) :
  node_view (mb_child e) = VBlock.
Proof.
  exact (node_child_main_block (mo_node m) (mb_child e) 0
           (is_main_view_eq _ (mo_ok m)) (ca_at (mb_at e))).
Qed.

Definition mb_body {p} {idx : ProgramIndex p} {m : MainOccurrenceRef idx} (e : MainBodyEdge m) : BlockRef idx :=
  mkBlockRef (mb_child e) (f_equal is_block_view (mb_block e)).

(* totality: each required singleton edge resolves exactly, with no option and no fallback *)
Lemma singleton_child_lt {p} {idx : ProgramIndex p} (r : NodeRef idx) :
  requires_first_edge (node_view r) = true -> 0 < length (node_children r).
Proof.
  intro H. pose proof (occ_first_child_wf r H) as Hw. unfold first_child_wf in Hw.
  rewrite node_children_length. destruct (c_children (occ_at r)); [ destruct Hw | cbn; lia ].
Qed.

Definition app_head {p} {idx : ProgramIndex p} (a : AppRef idx) : ApplicationHeadEdge a :=
  mkAppHead (child_at_lt (app_node a) 0 (singleton_child_lt (app_node a) (f_equal requires_first_edge (app_ok a)))).

Definition unary_operand {p} {idx : ProgramIndex p} (u : UnaryRef idx) : UnaryOperandEdge u :=
  mkUnOperand (child_at_lt (un_node u) 0 (singleton_child_lt (un_node u) (f_equal requires_first_edge (un_ok u)))).

Definition exprstmt_expr {p} {idx : ProgramIndex p} (s : ExprStmtRef idx) : ExprStmtExprEdge s :=
  mkExprStmtE (child_at_lt (exs_node s) 0 (singleton_child_lt (exs_node s) (f_equal requires_first_edge (exs_ok s)))).

Lemma main_child_lt {p} {idx : ProgramIndex p} (m : MainOccurrenceRef idx) :
  0 < length (node_children (mo_node m)).
Proof.
  rewrite (node_children_count (mo_node m) 1); [ lia |].
  rewrite (is_main_view_eq _ (mo_ok m)). reflexivity.
Qed.

Definition main_body {p} {idx : ProgramIndex p} (m : MainOccurrenceRef idx) : MainBodyEdge m :=
  mkMainBody (child_at_lt (mo_node m) 0 (main_child_lt m)).

(* the spec children length is the exact shape formula, so every formula ordinal is in range *)
Lemma spec_children_len {p} {idx : ProgramIndex p} {fl : SpecFlavor} (sp : SpecRef idx fl) :
  length (node_children (sp_node sp))
  = shape_names fl (sp_shape sp) + (if shape_has_type fl (sp_shape sp) then 1 else 0)
    + shape_values fl (sp_shape sp).
Proof. apply node_children_count. rewrite (sp_ok sp). apply spec_layout_count. Qed.

Lemma name_ordinal_lt {p} {idx : ProgramIndex p} {fl : SpecFlavor} (sp : SpecRef idx fl) (i : nat) :
  i < shape_names fl (sp_shape sp) -> i < length (node_children (sp_node sp)).
Proof. intro H. rewrite (spec_children_len sp). lia. Qed.

Lemma type_ordinal_lt {p} {idx : ProgramIndex p} {fl : SpecFlavor} (sp : SpecRef idx fl) :
  shape_has_type fl (sp_shape sp) = true ->
  type_ordinal fl (sp_shape sp) < length (node_children (sp_node sp)).
Proof. intro Ht. rewrite (spec_children_len sp), Ht. unfold type_ordinal. lia. Qed.

Lemma value_ordinal_lt {p} {idx : ProgramIndex p} {fl : SpecFlavor} (sp : SpecRef idx fl) (j : nat) :
  j < shape_values fl (sp_shape sp) ->
  value_ordinal fl (sp_shape sp) j < length (node_children (sp_node sp)).
Proof.
  intro H. rewrite (spec_children_len sp). unfold value_ordinal.
  destruct (shape_has_type fl (sp_shape sp)); lia.
Qed.

Lemma short_children_len {p} {idx : ProgramIndex p} (st : ShortStmtRef idx) :
  length (node_children (sh_node st)) = sh_names st + sh_values st.
Proof. apply node_children_count. rewrite (sh_ok st). reflexivity. Qed.

Lemma lhs_ordinal_lt {p} {idx : ProgramIndex p} (st : ShortStmtRef idx) (i : nat) :
  i < sh_names st -> i < length (node_children (sh_node st)).
Proof. intro H. rewrite (short_children_len st). lia. Qed.

Lemma rhs_ordinal_lt {p} {idx : ProgramIndex p} (st : ShortStmtRef idx) (j : nat) :
  j < sh_values st -> sh_names st + j < length (node_children (sh_node st)).
Proof. intro H. rewrite (short_children_len st). lia. Qed.

(* the exact type-presence status, decided by the shape and carrying the exact edge when present *)
Definition spec_type_status {p} {idx : ProgramIndex p} {fl : SpecFlavor} (sp : SpecRef idx fl)
  : SpecTypePresence sp :=
  match Bool.bool_dec (shape_has_type fl (sp_shape sp)) true with
  | left Ht => SpecTypePresent Ht (child_at_lt (sp_node sp) (type_ordinal fl (sp_shape sp)) (type_ordinal_lt sp Ht))
  | right Hf => SpecTypeAbsent (Bool.not_true_is_false _ Hf)
  end.

(* one indexed-collection builder: every index below the exact total, in ascending order, none missing *)
Lemma ctr_lt : forall total i rem, i + S rem = total -> i < total.
Proof. intros; lia. Qed.
Lemma ctr_succ : forall total i rem, i + S rem = total -> S i + rem = total.
Proof. intros; lia. Qed.

Fixpoint indexed_upto {T : nat -> Type} (total : nat) (build : forall i, i < total -> T i)
  (i rem : nat) {struct rem} : i + rem = total -> list { i0 : nat & T i0 } :=
  match rem with
  | 0 => fun _ => []
  | S rem' => fun E =>
      existT _ i (build i (ctr_lt total i rem' E))
      :: indexed_upto total build (S i) rem' (ctr_succ total i rem' E)
  end.
Definition indexed_all {T : nat -> Type} (total : nat) (build : forall i, i < total -> T i)
  : list { i : nat & T i } := indexed_upto total build 0 total eq_refl.

Lemma indexed_upto_ords {T : nat -> Type} (total : nat) (build : forall i, i < total -> T i) :
  forall rem i E, map (@projT1 _ _) (indexed_upto total build i rem E) = seq i rem.
Proof. induction rem as [|rem' IH]; intros i E; cbn; [ reflexivity | f_equal; apply IH ]. Qed.
Lemma indexed_all_ords {T : nat -> Type} (total : nat) (build : forall i, i < total -> T i) :
  map (@projT1 _ _) (indexed_all total build) = seq 0 total.
Proof. apply indexed_upto_ords. Qed.

(* the exact indexed collections, one member per shape-fixed index, ascending, complete by construction *)
Definition spec_name_edges {p} {idx : ProgramIndex p} {fl : SpecFlavor} (sp : SpecRef idx fl)
  : list { i : nat & SpecNameEdge sp i } :=
  indexed_all (shape_names fl (sp_shape sp))
    (fun i H => mkSpecName (child_at_lt (sp_node sp) i (name_ordinal_lt sp i H)) H).

Definition spec_value_edges {p} {idx : ProgramIndex p} {fl : SpecFlavor} (sp : SpecRef idx fl)
  : list { j : nat & SpecValueEdge sp j } :=
  indexed_all (shape_values fl (sp_shape sp))
    (fun j H => mkSpecValue (child_at_lt (sp_node sp) (value_ordinal fl (sp_shape sp) j) (value_ordinal_lt sp j H)) H).

Definition short_lhs_edges {p} {idx : ProgramIndex p} (st : ShortStmtRef idx)
  : list { i : nat & ShortLhsEdge st i } :=
  indexed_all (sh_names st) (fun i H => mkShortLhs (child_at_lt (sh_node st) i (lhs_ordinal_lt st i H)) H).

Definition short_rhs_edges {p} {idx : ProgramIndex p} (st : ShortStmtRef idx)
  : list { j : nat & ShortRhsEdge st j } :=
  indexed_all (sh_values st) (fun j H => mkShortRhs (child_at_lt (sh_node st) (sh_names st + j) (rhs_ordinal_lt st j H)) H).

(* the ordered argument collection: every canonical non-head child, reindexed by its exact argument index *)
Definition application_args {p} {idx : ProgramIndex p} (a : AppRef idx)
  : list { i : nat & ApplicationArgEdge a i } :=
  flat_map (fun oe => match oe with existT _ o e =>
      match o as o0 return ChildAt (app_node a) o0 -> list { i : nat & ApplicationArgEdge a i } with
      | 0 => fun _ => []
      | S i => fun e0 => [ existT _ i (mkAppArg e0) ]
      end e end)
    (all_children (app_node a)).

Lemma args_of_children_from {p} {idx : ProgramIndex p} (a : AppRef idx) :
  forall l k E,
  map (@projT1 _ _)
      (flat_map (fun oe => match oe with existT _ o e =>
          match o as o0 return ChildAt (app_node a) o0 -> list { i : nat & ApplicationArgEdge a i } with
          | 0 => fun _ => []
          | S i => fun e0 => [ existT _ i (mkAppArg e0) ]
          end e end)
        (children_from (app_node a) (S k) l E)) = seq k (length l)
  /\ map (fun x => aa_child (projT2 x))
      (flat_map (fun oe => match oe with existT _ o e =>
          match o as o0 return ChildAt (app_node a) o0 -> list { i : nat & ApplicationArgEdge a i } with
          | 0 => fun _ => []
          | S i => fun e0 => [ existT _ i (mkAppArg e0) ]
          end e end)
        (children_from (app_node a) (S k) l E)) = l.
Proof.
  induction l as [|c rest IH]; intros k E; cbn; [ split; reflexivity |].
  destruct (IH (S k) (skipn_tail_at (node_children (app_node a)) rest (S k) c E)) as [H1 H2].
  split; f_equal; [ exact H1 | exact H2 ].
Qed.

(* argument order, index and coverage are exact: ordinals 0.. over exactly the non-head children *)
Lemma application_args_exact {p} {idx : ProgramIndex p} (a : AppRef idx) :
  map (@projT1 _ _) (application_args a) = seq 0 (pred (length (node_children (app_node a))))
  /\ map (fun x => aa_child (projT2 x)) (application_args a) = tl (node_children (app_node a)).
Proof.
  unfold application_args, all_children.
  assert (Hgen : forall (l : list (NodeRef idx)) (E : l = skipn 0 (node_children (app_node a))),
    map (@projT1 _ _)
        (flat_map (fun oe => match oe with existT _ o e =>
            match o as o0 return ChildAt (app_node a) o0 -> list { i : nat & ApplicationArgEdge a i } with
            | 0 => fun _ => []
            | S i => fun e0 => [ existT _ i (mkAppArg e0) ]
            end e end)
          (children_from (app_node a) 0 l E)) = seq 0 (pred (length l))
    /\ map (fun x => aa_child (projT2 x))
        (flat_map (fun oe => match oe with existT _ o e =>
            match o as o0 return ChildAt (app_node a) o0 -> list { i : nat & ApplicationArgEdge a i } with
            | 0 => fun _ => []
            | S i => fun e0 => [ existT _ i (mkAppArg e0) ]
            end e end)
          (children_from (app_node a) 0 l E)) = tl l).
  { destruct l as [|c rest]; intro E.
    - cbn. split; reflexivity.
    - cbn [children_from flat_map].
      destruct (args_of_children_from a rest 0
                  (skipn_tail_at (node_children (app_node a)) rest 0 c E)) as [H1 H2].
      cbn [app pred length tl]. split; [ exact H1 | exact H2 ]. }
  exact (Hgen (node_children (app_node a)) eq_refl).
Qed.

Lemma all_children_has {p} {idx : ProgramIndex p} (par c : NodeRef idx) :
  In c (node_children par) -> exists o (e : ChildAt par o), In (existT _ o e) (all_children par) /\ ca_child e = c.
Proof.
  intro Hin.
  assert (Hmap : In c (map (fun x => ca_child (projT2 x)) (all_children par)))
    by (rewrite all_children_childs; exact Hin).
  apply in_map_iff in Hmap. destruct Hmap as [[o e] [Hc Hine]].
  exists o, e. split; [ exact Hine | exact Hc ].
Qed.

(* a parent edge yields the exact canonical child row under that parent *)
Lemma all_children_of_parent {p} {idx : ProgramIndex p} (r par : NodeRef idx) :
  node_parent r = Some par ->
  exists o (e : ChildAt par o), In (existT _ o e) (all_children par) /\ ca_child e = r.
Proof. intro Hp. exact (all_children_has par r (node_parent_children r par Hp)). Qed.

(* the ordinal-edge rows are positionally exact: the row at position j is an edge at ordinal j *)
Lemma all_children_nth {p} {idx : ProgramIndex p} (r : NodeRef idx) (j : nat) (e : ChildAt r j) :
  exists e' : ChildAt r j, nth_error (all_children r) j = Some (existT _ j e').
Proof.
  assert (Hlen : length (all_children r) = length (node_children r)).
  { pose proof (all_children_ords r) as Ho.
    apply (f_equal (@length nat)) in Ho.
    rewrite length_map, length_seq in Ho. exact Ho. }
  assert (Hn : j < length (node_children r))
    by (apply nth_error_Some; rewrite (ca_at e); discriminate).
  assert (Hjlt : j < length (all_children r)) by (rewrite Hlen; exact Hn).
  destruct (nth_error (all_children r) j) as [row|] eqn:Hrow.
  2:{ exfalso. apply nth_error_Some in Hjlt. exact (Hjlt Hrow). }
  assert (Hord : nth_error (map (@projT1 _ _) (all_children r)) j = Some (projT1 row))
    by (exact (map_nth_error _ _ _ Hrow)).
  rewrite (all_children_ords r) in Hord.
  assert (Hseq : nth_error (seq 0 (length (node_children r))) j = Some j).
  { rewrite (nth_error_nth' (seq 0 (length (node_children r))) 0);
      [| rewrite length_seq; exact Hn ].
    rewrite seq_nth; [ reflexivity | exact Hn ]. }
  rewrite Hseq in Hord. injection Hord as Hord.
  destruct row as [j' e']. cbn in Hord. subst j'.
  exists e'. reflexivity.
Qed.

(* the target's own parent edge, recovered in one field read from the stored child slot — never a scan *)
Definition self_edge_of {p} {idx : ProgramIndex p} (r par : NodeRef idx)
  (H : node_parent r = Some par) : SelfEdge r :=
  mkSelfEdge par (c_slot (occ_at r)) (mkChildAt r (node_slot_child r par H)) eq_refl.

(* order and coverage per family: each collection's indices are exactly 0.. its shape-fixed total, ascending *)
Lemma spec_name_edges_ords {p} {idx : ProgramIndex p} {fl : SpecFlavor} (sp : SpecRef idx fl) :
  map (@projT1 _ _) (spec_name_edges sp) = seq 0 (shape_names fl (sp_shape sp)).
Proof. apply indexed_all_ords. Qed.
Lemma spec_value_edges_ords {p} {idx : ProgramIndex p} {fl : SpecFlavor} (sp : SpecRef idx fl) :
  map (@projT1 _ _) (spec_value_edges sp) = seq 0 (shape_values fl (sp_shape sp)).
Proof. apply indexed_all_ords. Qed.
Lemma short_lhs_edges_ords {p} {idx : ProgramIndex p} (st : ShortStmtRef idx) :
  map (@projT1 _ _) (short_lhs_edges st) = seq 0 (sh_names st).
Proof. apply indexed_all_ords. Qed.
Lemma short_rhs_edges_ords {p} {idx : ProgramIndex p} (st : ShortStmtRef idx) :
  map (@projT1 _ _) (short_rhs_edges st) = seq 0 (sh_values st).
Proof. apply indexed_all_ords. Qed.

(* parent round trips per family: each retained edge's child points node_parent back to the exact parent *)
Lemma ah_parent {p} {idx : ProgramIndex p} {a : AppRef idx} (e : ApplicationHeadEdge a) :
  node_parent (ah_child e) = Some (app_node a).
Proof. exact (ca_node_parent (ah_at e)). Qed.
Lemma aa_parent {p} {idx : ProgramIndex p} {a : AppRef idx} {i : nat} (e : ApplicationArgEdge a i) :
  node_parent (aa_child e) = Some (app_node a).
Proof. exact (ca_node_parent (aa_at e)). Qed.
Lemma sn_parent {p} {idx : ProgramIndex p} {fl : SpecFlavor} {sp : SpecRef idx fl} {i : nat}
  (e : SpecNameEdge sp i) : node_parent (sn_child e) = Some (sp_node sp).
Proof. exact (ca_node_parent (sn_at e)). Qed.
Lemma sv_parent {p} {idx : ProgramIndex p} {fl : SpecFlavor} {sp : SpecRef idx fl} {j : nat}
  (e : SpecValueEdge sp j) : node_parent (sv_child e) = Some (sp_node sp).
Proof. exact (ca_node_parent (sv_at e)). Qed.
Lemma sl_parent {p} {idx : ProgramIndex p} {st : ShortStmtRef idx} {i : nat} (e : ShortLhsEdge st i) :
  node_parent (sl_child e) = Some (sh_node st).
Proof. exact (ca_node_parent (sl_at e)). Qed.
Lemma sr_parent {p} {idx : ProgramIndex p} {st : ShortStmtRef idx} {j : nat} (e : ShortRhsEdge st j) :
  node_parent (sr_child e) = Some (sh_node st).
Proof. exact (ca_node_parent (sr_at e)). Qed.
Lemma mb_parent {p} {idx : ProgramIndex p} {m : MainOccurrenceRef idx} (e : MainBodyEdge m) :
  node_parent (mb_child e) = Some (mo_node m).
Proof. exact (ca_node_parent (mb_at e)). Qed.

(* a preceding sibling and its target sit under one exact parent, and the target's parent edge names it *)
Lemma ps_shared_parent {p} {idx : ProgramIndex p} {target : NodeRef idx} {i : nat}
  (e : PrecedingSiblingEdge target i) :
  node_parent (ps_sibling e) = Some (se_parent (ps_self e))
  /\ node_parent target = Some (se_parent (ps_self e)).
Proof.
  split; [ exact (ca_node_parent (ps_at e)) |].
  pose proof (ca_node_parent (se_at (ps_self e))) as H.
  rewrite (se_child_eq (ps_self e)) in H. exact H.
Qed.

(* a canonical edge's ordinal is in range on its parent's exact child list *)
Lemma ca_ordinal_lt {p} {idx : ProgramIndex p} {parent : NodeRef idx} {ordinal : nat}
  (e : ChildAt parent ordinal) : ordinal < length (node_children parent).
Proof. apply nth_error_Some. rewrite (ca_at e). discriminate. Qed.

Lemma prec_ordinal_lt {p} {idx : ProgramIndex p} {r : NodeRef idx} (se : SelfEdge r) (i : nat) :
  i < se_ord se -> i < length (node_children (se_parent se)).
Proof. intro H. pose proof (ca_ordinal_lt (se_at se)). lia. Qed.

(* the ordinal below an inhabited successor ordinal is in range on the same parent *)
Lemma ca_pred_lt {p} {idx : ProgramIndex p} {parent : NodeRef idx} {k : nat} (e : ChildAt parent (S k)) :
  k < length (node_children parent).
Proof. pose proof (ca_ordinal_lt e). lia. Qed.

(* the typed const-spec child of a const declaration, with its exact node identity *)
Definition spec_child_at {p} {idx : ProgramIndex p} (par : NodeRef idx) (k : nat)
  (Hd : node_view par = VDecl ConstSpecF) (e : ChildAt par k)
  : { cs : SpecRef idx ConstSpecF | sp_node cs = ca_child e } :=
  (match node_view (ca_child e) as v
         return node_view (ca_child e) = v -> spec_view_of_flavor ConstSpecF v
                -> { cs : SpecRef idx ConstSpecF | sp_node cs = ca_child e } with
   | VConstSpec sh => fun Hv _ => exist _ (mkSpecRef (fl := ConstSpecF) (ca_child e) sh Hv) eq_refl
   | _ => fun _ F => match F with end
   end) eq_refl (node_child_decl_spec par (ca_child e) ConstSpecF k Hd (ca_at e)).

(* the exact preceding siblings of a target: one edge per ordinal below the target's own ordinal *)
Definition preceding_edges {p} {idx : ProgramIndex p} (target : NodeRef idx)
  : list { i : nat & PrecedingSiblingEdge target i } :=
  (match node_parent target as o return node_parent target = o -> list { i : nat & PrecedingSiblingEdge target i } with
   | Some par => fun H =>
       let se := self_edge_of target par H in
       indexed_all (se_ord se)
         (fun i Hi => mkPrecSib se (child_at_lt (se_parent se) i (prec_ordinal_lt se i Hi)) Hi)
   | None => fun _ => []
   end) eq_refl.


(* the exact path a live expression result flows through: a root, or one link onto the enclosing expression's path *)
Inductive ExprUsePath {p} {idx : ProgramIndex p} : NodeRef idx -> Type :=
| EUPExprStmt : forall (s : ExprStmtRef idx) (e : ExprStmtExprEdge s), ExprUsePath (ee_child e)
| EUPConst : forall (sp : SpecRef idx ConstSpecF) (j : nat) (e : SpecValueEdge sp j), ExprUsePath (sv_child e)
| EUPVarExplicit : forall (sp : SpecRef idx VarSpecF) (j : nat) (e : SpecValueEdge sp j),
    shape_has_type VarSpecF (sp_shape sp) = true -> ExprUsePath (sv_child e)
| EUPVarImplicit : forall (sp : SpecRef idx VarSpecF) (j : nat) (e : SpecValueEdge sp j),
    shape_has_type VarSpecF (sp_shape sp) = false -> ExprUsePath (sv_child e)
| EUPShort : forall (st : ShortStmtRef idx) (j : nat) (e : ShortRhsEdge st j), ExprUsePath (sr_child e)
| EUPUnary : forall (u : UnaryRef idx) (e : UnaryOperandEdge u), ExprUsePath (un_node u) -> ExprUsePath (uo_child e)
| EUPArg : forall (a : AppRef idx) (i : nat) (e : ApplicationArgEdge a i), ExprUsePath (app_node a) -> ExprUsePath (aa_child e)
| EUPHead : forall (a : AppRef idx) (e : ApplicationHeadEdge a), ExprUsePath (app_node a) -> ExprUsePath (ah_child e).

(* a live expression node: its view is one of the four expression head constructors *)
Definition is_expr_node {p} {idx : ProgramIndex p} (r : NodeRef idx) : bool :=
  match node_view r with VName _ | VLiteral _ | VUnary _ | VApplication => true | _ => false end.

(* the parent views that admit an expression child — exactly the six use-context parents *)
Definition admits_expr_child (v : NodeView) : bool :=
  match v with
  | VApplication | VUnary _ | VStmt SSExpr | VConstSpec _ | VVarSpec _ | VStmt (SSShort _ _) => true
  | _ => false
  end.

(* if the child at ordinal k has expression kind, the parent view is one that admits an expression there *)
Lemma layout_kind_expr_admits : forall v k, layout_kind v k = ExprKind -> admits_expr_child v = true.
Proof.
  intros v k H. destruct v as [n|l|op| |te|bn|cs|vs|tsh|fl|s| |t| ]; cbn [admits_expr_child]; try reflexivity.
  - cbn [layout_kind] in H; discriminate H.
  - cbn [layout_kind] in H; discriminate H.
  - cbn [layout_kind] in H; discriminate H.
  - cbn [layout_kind] in H; discriminate H.
  - destruct k; cbn [layout_kind] in H; discriminate H.
  - cbn [layout_kind] in H; discriminate H.
  - destruct s; [ reflexivity | cbn [layout_kind] in H; discriminate H | reflexivity ].
  - cbn [layout_kind] in H; discriminate H.
  - destruct t; cbn [layout_kind] in H; discriminate H.
  - cbn [layout_kind] in H; discriminate H.
Qed.

(* a live expression node is never the file root, so its parent edge is present *)
Lemma expr_has_parent {p} {idx : ProgramIndex p} (r : NodeRef idx) :
  is_expr_node r = true -> exists par, node_parent r = Some par.
Proof.
  intro Hr. destruct (node_parent r) as [par|] eqn:E; [ exists par; reflexivity |].
  exfalso. apply parentless_view_file in E. unfold is_expr_node in Hr. rewrite E in Hr. discriminate Hr.
Qed.

(* a value-position ordinal on a spec is exactly value_ordinal j for some in-range value index j *)
Lemma spec_value_index {p} {idx : ProgramIndex p} {fl : SpecFlavor} (sp : SpecRef idx fl) (o : nat) :
  layout_kind (spec_view_of fl (sp_shape sp)) o = ExprKind ->
  o < length (node_children (sp_node sp)) ->
  { j : nat | j < shape_values fl (sp_shape sp) /\ value_ordinal fl (sp_shape sp) j = o }.
Proof.
  intros Hk Ho. rewrite (spec_children_len sp) in Ho.
  destruct fl;
    [ destruct (sp_shape sp) as [ht nn nv | nn]
    | destruct (sp_shape sp) as [nn | ht nn nv]
    | destruct (sp_shape sp) as [ | ] ];
    cbn [spec_view_of shape_names shape_has_type shape_values value_ordinal layout_kind] in Hk, Ho |- *.
  - destruct (o <? nn) eqn:E1; [ discriminate Hk |]. apply Nat.ltb_ge in E1.
    destruct ht.
    + destruct (o =? nn) eqn:E2; cbn [andb] in Hk; [ discriminate Hk |]. apply Nat.eqb_neq in E2.
      exists (o - (nn + 1)). split; cbn; lia.
    + cbn [andb] in Hk. exists (o - (nn + 0)). split; cbn; lia.
  - discriminate Hk.
  - destruct (o <? nn); discriminate Hk.
  - destruct (o <? nn) eqn:E1; [ discriminate Hk |]. apply Nat.ltb_ge in E1.
    destruct ht.
    + destruct (o =? nn) eqn:E2; cbn [andb] in Hk; [ discriminate Hk |]. apply Nat.eqb_neq in E2.
      exists (o - (nn + 1)). split; cbn; lia.
    + cbn [andb] in Hk. exists (o - (nn + 0)). split; cbn; lia.
  - destruct o; discriminate Hk.
  - destruct o; discriminate Hk.
Qed.

(* a value-position ordinal on a short declaration is exactly sh_names + j for some in-range RHS index j *)
Lemma short_value_index {p} {idx : ProgramIndex p} (st : ShortStmtRef idx) (o : nat) :
  layout_kind (node_view (sh_node st)) o = ExprKind ->
  o < length (node_children (sh_node st)) ->
  { j : nat | j < sh_values st /\ sh_names st + j = o }.
Proof.
  intros Hk Ho. rewrite (sh_ok st) in Hk. cbn [layout_kind] in Hk.
  destruct (o <? sh_names st) eqn:E1; [ discriminate Hk |]. apply Nat.ltb_ge in E1.
  assert (Hlen : length (node_children (sh_node st)) = sh_names st + sh_values st).
  { apply node_children_count. rewrite (sh_ok st). reflexivity. }
  rewrite Hlen in Ho. exists (o - sh_names st). split; lia.
Qed.

(* recasting a canonical edge along a proven ordinal equality preserves its exact child *)
Lemma ca_cast_child {p} {idx : ProgramIndex p} {parent : NodeRef idx} {i j : nat}
  (E : i = j) (e : ChildAt parent i) : ca_child (ca_cast E e) = ca_child e.
Proof. destruct E. reflexivity. Qed.

(* the exact structural expression-use path of every live expression node — one well-founded parent-position walk *)
Definition use_path {p} {idx : ProgramIndex p} (r : NodeRef idx) (Hr : is_expr_node r = true) : ExprUsePath r.
Proof.
  revert Hr. revert r.
  refine (well_founded_induction_type (well_founded_ltof _ (fun x : NodeRef idx => nr_pos x))
            (fun r => is_expr_node r = true -> ExprUsePath r) _).
  intros r rec Hr. unfold ltof in rec.
  destruct (node_parent r) as [par|] eqn:Hpar;
    [ | exfalso; apply parentless_view_file in Hpar;
        unfold is_expr_node in Hr; rewrite Hpar in Hr; discriminate Hr ].
  destruct (self_edge_of r par Hpar) as [pp o eat echeq].
  assert (Hlt : nr_pos pp < nr_pos r) by (rewrite <- echeq; exact (child_pos_gt_parent eat)).
  assert (Hnth : nth_error (node_children pp) o = Some r) by (rewrite <- echeq; exact (ca_at eat)).
  pose proof (node_child_kind pp r o Hnth) as Hkind.
  assert (Hek : kind_of_view (node_view r) = ExprKind)
    by (unfold is_expr_node in Hr; destruct (node_view r); try discriminate Hr; reflexivity).
  rewrite Hek in Hkind. symmetry in Hkind.
  pose proof (layout_kind_expr_admits _ _ Hkind) as Hadm.
  rewrite <- echeq.
  destruct (node_view pp) as [n0|l0|op| |te|bn|cs|vs|tsh|dfl|s| |tsh0| ] eqn:Hv;
    try (cbn [admits_expr_child] in Hadm; discriminate Hadm).
  - (* VUnary op *)
    assert (Ho0 : o = 0).
    { pose proof (ca_ordinal_lt eat) as Hol.
      assert (Hc : length (node_children pp) = 1) by (apply (node_children_count pp 1); rewrite Hv; reflexivity).
      rewrite Hc in Hol; lia. }
    subst o.
    assert (Hpp : is_expr_node pp = true) by (unfold is_expr_node; rewrite Hv; reflexivity).
    pose (u := mkUnaryRef pp op Hv).
    exact (EUPUnary u (mkUnOperand (u := u) eat) (rec pp Hlt Hpp)).
  - (* application parent: ordinal 0 is the head link, every later ordinal an argument link *)
    assert (Hpp : is_expr_node pp = true) by (unfold is_expr_node; rewrite Hv; reflexivity).
    pose (a := mkAppRef pp Hv).
    destruct o as [|i].
    + exact (EUPHead a (mkAppHead (a := a) eat) (rec pp Hlt Hpp)).
    + exact (EUPArg a i (mkAppArg (a := a) eat) (rec pp Hlt Hpp)).
  - (* VConstSpec cs *)
    pose (sp := mkSpecRef (fl:=ConstSpecF) pp cs Hv).
    destruct (spec_value_index sp o Hkind (ca_ordinal_lt eat)) as [j [Hj1 Hj2]].
    assert (Hce : ca_child (ca_cast (eq_sym Hj2) eat) = ca_child eat) by (apply ca_cast_child).
    rewrite <- Hce.
    exact (EUPConst sp j (mkSpecValue (sp := sp) (ca_cast (eq_sym Hj2) eat) Hj1)).
  - (* VVarSpec vs *)
    pose (sp := mkSpecRef (fl:=VarSpecF) pp vs Hv).
    destruct (spec_value_index sp o Hkind (ca_ordinal_lt eat)) as [j [Hj1 Hj2]].
    assert (Hce : ca_child (ca_cast (eq_sym Hj2) eat) = ca_child eat) by (apply ca_cast_child).
    rewrite <- Hce.
    destruct (shape_has_type VarSpecF (sp_shape sp)) eqn:Hht.
    + exact (EUPVarExplicit sp j (mkSpecValue (sp := sp) (ca_cast (eq_sym Hj2) eat) Hj1) Hht).
    + exact (EUPVarImplicit sp j (mkSpecValue (sp := sp) (ca_cast (eq_sym Hj2) eat) Hj1) Hht).
  - (* VStmt s *)
    destruct s as [ | | nn nv ].
    + (* expression-statement parent: its one child is the enclosed statement expression *)
      assert (Ho0 : o = 0).
      { pose proof (ca_ordinal_lt eat) as Hol.
        assert (Hc : length (node_children pp) = 1) by (apply (node_children_count pp 1); rewrite Hv; reflexivity).
        rewrite Hc in Hol; lia. }
      subst o.
      pose (s0 := mkExprStmtRef pp Hv).
      exact (EUPExprStmt s0 (mkExprStmtE (s := s0) eat)).
    + (* declaration-statement parent admits no expression child, so this ordinal is impossible *)
      cbn [admits_expr_child] in Hadm; discriminate Hadm.
    + (* SSShort nn nv *)
      pose (st := mkShortStmtRef pp nn nv Hv).
      assert (Hsl : layout_kind (node_view (sh_node st)) o = ExprKind)
        by (unfold st; cbn [sh_node]; rewrite Hv; exact Hkind).
      destruct (short_value_index st o Hsl (ca_ordinal_lt eat)) as [j [Hj1 Hj2]].
      assert (Hce : ca_child (ca_cast (eq_sym Hj2) eat) = ca_child eat) by (apply ca_cast_child).
      rewrite <- Hce.
      exact (EUPShort st j (mkShortRhs (st := st) (ca_cast (eq_sym Hj2) eat) Hj1)).
Defined.

(* root-family exhaustiveness: every path bottoms out at exactly one value or statement root *)
Fixpoint up_root {p} {idx : ProgramIndex p} {r : NodeRef idx} (path : ExprUsePath r) : NodeRef idx :=
  match path with
  | EUPExprStmt s _ => exs_node s
  | EUPConst sp _ _ => sp_node sp
  | EUPVarExplicit sp _ _ _ => sp_node sp
  | EUPVarImplicit sp _ _ _ => sp_node sp
  | EUPShort st _ _ => sh_node st
  | EUPUnary _ _ sub => up_root sub
  | EUPArg _ _ _ sub => up_root sub
  | EUPHead _ _ sub => up_root sub
  end.

(* progress through arbitrary nesting: the owning root strictly precedes the used expression *)
Lemma up_root_lt {p} {idx : ProgramIndex p} {r : NodeRef idx} (path : ExprUsePath r) :
  nr_pos (up_root path) < nr_pos r.
Proof.
  induction path as [s e | sp j e | sp j e Ht | sp j e Ht | st j e | u e sub IH | a i e sub IH | a e sub IH];
    cbn [up_root].
  - exact (child_pos_gt_parent (ee_at e)).
  - exact (child_pos_gt_parent (sv_at e)).
  - exact (child_pos_gt_parent (sv_at e)).
  - exact (child_pos_gt_parent (sv_at e)).
  - exact (child_pos_gt_parent (sr_at e)).
  - exact (Nat.lt_trans _ _ _ IH (child_pos_gt_parent (uo_at e))).
  - exact (Nat.lt_trans _ _ _ IH (child_pos_gt_parent (aa_at e))).
  - exact (Nat.lt_trans _ _ _ IH (child_pos_gt_parent (ah_at e))).
Qed.

(* the immediate enclosing parent recorded by a path's top edge — a projection, exact by construction *)
Definition up_iparent {p} {idx : ProgramIndex p} {r : NodeRef idx} (path : ExprUsePath r) : NodeRef idx :=
  match path with
  | EUPExprStmt s _ => exs_node s
  | EUPConst sp _ _ => sp_node sp
  | EUPVarExplicit sp _ _ _ => sp_node sp
  | EUPVarImplicit sp _ _ _ => sp_node sp
  | EUPShort st _ _ => sh_node st
  | EUPUnary u _ _ => un_node u
  | EUPArg a _ _ _ => app_node a
  | EUPHead a _ _ => app_node a
  end.

(* the subject-parent round trip: a path's subject really is a direct child of its recorded parent *)
Lemma up_iparent_ok {p} {idx : ProgramIndex p} {r : NodeRef idx} (path : ExprUsePath r) :
  node_parent r = Some (up_iparent path).
Proof.
  destruct path as [s e | sp j e | sp j e Ht | sp j e Ht | st j e | u e sub | a i e sub | a e sub];
    cbn [up_iparent]; apply node_children_inverse.
  - exact (ca_in (ee_at e)).
  - exact (ca_in (sv_at e)).
  - exact (ca_in (sv_at e)).
  - exact (ca_in (sv_at e)).
  - exact (ca_in (sr_at e)).
  - exact (ca_in (uo_at e)).
  - exact (ca_in (aa_at e)).
  - exact (ca_in (ah_at e)).
Qed.

(* the exact ordinal a path's top edge sits at within its parent — a projection *)
Definition up_iord {p} {idx : ProgramIndex p} {r : NodeRef idx} (path : ExprUsePath r) : nat :=
  match path with
  | EUPExprStmt _ _ => 0
  | EUPConst sp j _ => value_ordinal ConstSpecF (sp_shape sp) j
  | EUPVarExplicit sp j _ _ => value_ordinal VarSpecF (sp_shape sp) j
  | EUPVarImplicit sp j _ _ => value_ordinal VarSpecF (sp_shape sp) j
  | EUPShort st j _ => sh_names st + j
  | EUPUnary _ _ _ => 0
  | EUPArg _ i _ _ => S i
  | EUPHead _ _ _ => 0
  end.

(* the subject sits at that exact ordinal in its parent's child list *)
Lemma up_iat {p} {idx : ProgramIndex p} {r : NodeRef idx} (path : ExprUsePath r) :
  nth_error (node_children (up_iparent path)) (up_iord path) = Some r.
Proof.
  destruct path as [s e | sp j e | sp j e Ht | sp j e Ht | st j e | u e sub | a i e sub | a e sub];
    cbn [up_iparent up_iord].
  - exact (ca_at (ee_at e)).
  - exact (ca_at (sv_at e)).
  - exact (ca_at (sv_at e)).
  - exact (ca_at (sv_at e)).
  - exact (ca_at (sr_at e)).
  - exact (ca_at (uo_at e)).
  - exact (ca_at (aa_at e)).
  - exact (ca_at (ah_at e)).
Qed.

(* the ordinal round trip: the stored child slot equals the path's own top ordinal *)
Lemma up_iord_ok {p} {idx : ProgramIndex p} {r : NodeRef idx} (path : ExprUsePath r) :
  c_slot (occ_at r) = up_iord path.
Proof. exact (node_child_slot r (up_iparent path) (up_iord path) (up_iparent_ok path) (up_iat path)). Qed.

(* the role each path constructor implies for its subject — the immediate use-context, syntactically *)
Definition up_role {p} {idx : ProgramIndex p} {r : NodeRef idx} (path : ExprUsePath r) : Role :=
  match path with
  | EUPExprStmt _ _ => RExprStatementExpr
  | EUPConst _ _ _ => RPlain
  | EUPVarExplicit _ _ _ _ => RPlain
  | EUPVarImplicit _ _ _ _ => RPlain
  | EUPShort _ _ _ => RPlain
  | EUPUnary _ _ _ => RUnaryOperand
  | EUPArg _ i _ _ => RApplicationArg i
  | EUPHead _ _ _ => RApplicationHead
  end.

(* the role round trip: the subject's stored role is exactly the one its top constructor implies *)
Lemma up_role_ok {p} {idx : ProgramIndex p} {r : NodeRef idx} (path : ExprUsePath r) :
  node_role r = up_role path.
Proof.
  rewrite (node_child_role (up_iparent path) r (up_iord path) (up_iat path)).
  destruct path as [s e | sp j e | sp j e Ht | sp j e Ht | st j e | u e sub | a i e sub | a e sub];
    cbn [up_iparent up_iord up_role].
  - rewrite (exs_ok s); reflexivity.
  - rewrite (sp_ok sp); exact (layout_role_value ConstSpecF (sp_shape sp) j (sv_lt e)).
  - rewrite (sp_ok sp); exact (layout_role_value VarSpecF (sp_shape sp) j (sv_lt e)).
  - rewrite (sp_ok sp); exact (layout_role_value VarSpecF (sp_shape sp) j (sv_lt e)).
  - rewrite (sh_ok st); cbn [layout_role];
      replace (sh_names st + j <? sh_names st) with false by (symmetry; apply Nat.ltb_ge; lia); reflexivity.
  - rewrite (un_ok u); reflexivity.
  - rewrite (app_ok a); reflexivity.
  - rewrite (app_ok a); reflexivity.
Qed.

(* the iota boundary test: the path bottoms at a const initializer value, through any depth of unary fold links *)
Fixpoint up_const_rooted {p} {idx : ProgramIndex p} {r : NodeRef idx} (path : ExprUsePath r) : bool :=
  match path with
  | EUPConst _ _ _ => true
  | EUPUnary _ _ sub => up_const_rooted sub
  | _ => false
  end.

(* the nil boundary test: the immediate top is an explicit-type var value, never through any other edge *)
Definition up_var_explicit_top {p} {idx : ProgramIndex p} {r : NodeRef idx} (path : ExprUsePath r) : bool :=
  match path with EUPVarExplicit _ _ _ _ => true | _ => false end.

(* the top-constructor family — the immediate use-context kind, finer than the role since it splits const/var/short *)
Inductive UseFamily : Type :=
| UFExprStmt | UFConst | UFVarExplicit | UFVarImplicit | UFShort | UFUnary | UFArg | UFHead.

Definition up_family {p} {idx : ProgramIndex p} {r : NodeRef idx} (path : ExprUsePath r) : UseFamily :=
  match path with
  | EUPExprStmt _ _ => UFExprStmt
  | EUPConst _ _ _ => UFConst
  | EUPVarExplicit _ _ _ _ => UFVarExplicit
  | EUPVarImplicit _ _ _ _ => UFVarImplicit
  | EUPShort _ _ _ => UFShort
  | EUPUnary _ _ _ => UFUnary
  | EUPArg _ _ _ _ => UFArg
  | EUPHead _ _ _ => UFHead
  end.

(* the family classifier over the parent view and ordinal — the syntactic reading of the immediate use-context *)
Definition family_of (v : NodeView) (k : nat) : UseFamily :=
  match v with
  | VStmt SSExpr => UFExprStmt
  | VConstSpec _ => UFConst
  | VVarSpec sh => if shape_has_type VarSpecF sh then UFVarExplicit else UFVarImplicit
  | VStmt (SSShort _ _) => UFShort
  | VUnary _ => UFUnary
  | VApplication => match k with 0 => UFHead | S _ => UFArg end
  | _ => UFExprStmt
  end.

(* a name occurrence is always a live expression node, so its use path is available without a separate check *)
Lemma is_expr_node_name {p} {idx : ProgramIndex p} {r : NodeRef idx} (n : Names.OrdinaryIdentifier) :
  node_view r = VName n -> is_expr_node r = true.
Proof. intro H. unfold is_expr_node. rewrite H. reflexivity. Qed.

(* the family round trip: a path's top family is the syntactic reading of its parent view and ordinal *)
Lemma up_family_ok {p} {idx : ProgramIndex p} {r : NodeRef idx} (path : ExprUsePath r) :
  up_family path = family_of (node_view (up_iparent path)) (up_iord path).
Proof.
  destruct path as [s e | sp j e | sp j e Ht | sp j e Ht | st j e | u e sub | a i e sub | a e sub];
    cbn [up_iparent up_iord up_family].
  - rewrite (exs_ok s); reflexivity.
  - rewrite (sp_ok sp); cbn [spec_view_of family_of]; reflexivity.
  - rewrite (sp_ok sp); cbn [spec_view_of family_of]; rewrite Ht; reflexivity.
  - rewrite (sp_ok sp); cbn [spec_view_of family_of]; rewrite Ht; reflexivity.
  - rewrite (sh_ok st); reflexivity.
  - rewrite (un_ok u); reflexivity.
  - rewrite (app_ok a); reflexivity.
  - rewrite (app_ok a); reflexivity.
Qed.
