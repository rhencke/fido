(* Index.Model — the shallow immutable occurrence vocabulary: flavors, shapes, views, kinds, roles, cells. *)
From Stdlib Require Import List Bool Arith PeanoNat Lia Eqdep_dec PArith FSets.FMapFacts.
From Fido Require Import Names Syntax.
Import ListNotations.

Inductive SpecFlavor := ConstSpecF | VarSpecF | TypeSpecF.

(* shallow local shapes: the immediate constructor and its scalar payload only; substructure is child cells *)
Inductive ConstShape    := CSExplicit (has_type : bool) (n_names n_values : nat) | CSInherited (n_names : nat).
Inductive VarShape       := VSTypeOnly (n_names : nat) | VSValues (has_type : bool) (n_names n_values : nat).
Inductive TypeSpecShape  := TSAlias | TSDef.
Inductive StmtShape      := SSExpr | SSDecl | SSShort (n_names n_values : nat).
Inductive TopShape       := TSTopDecl | TSMain.

(* the occurrence view: one shallow local cell — the head constructor and only immediate scalars, no descendants *)
Inductive NodeView : Type :=
| VName        : Names.OrdinaryIdentifier -> NodeView
| VLiteral     : Syntax.Literal           -> NodeView
| VUnary       : Syntax.UnaryOp           -> NodeView
| VApplication : NodeView
| VTypeExpr    : Syntax.TypeExpr          -> NodeView
| VBindingName : Syntax.BindingName       -> NodeView
| VConstSpec   : ConstShape               -> NodeView
| VVarSpec     : VarShape                  -> NodeView
| VTypeSpec    : TypeSpecShape            -> NodeView
| VDecl        : SpecFlavor               -> NodeView
| VStmt        : StmtShape                 -> NodeView
| VBlock       : NodeView
| VTop         : TopShape                  -> NodeView
| VFile        : NodeView.

Inductive Kind :=
| ExprKind | TypeExprKind | BindingNameKind
| SpecKind : SpecFlavor -> Kind
| DeclKind | StmtKind | BlockKind | TopKind | FileKind.

Inductive Role :=
| RPlain | RApplicationHead | RApplicationArg : nat -> Role
| RUnaryOperand | RSpecName : SpecFlavor -> Role
| RShortLhs | RExprStatementExpr | RTypeUse.

(* the kind each view is classified as; node_kind derives this, so kind is never stored *)
Definition kind_of_view (v : NodeView) : Kind :=
  match v with
  | VName _ | VLiteral _ | VUnary _ | VApplication => ExprKind
  | VTypeExpr _ => TypeExprKind | VBindingName _ => BindingNameKind
  | VConstSpec _ => SpecKind ConstSpecF | VVarSpec _ => SpecKind VarSpecF | VTypeSpec _ => SpecKind TypeSpecF
  | VDecl _ => DeclKind | VStmt _ => StmtKind | VBlock => BlockKind | VTop _ => TopKind | VFile => FileKind
  end.

(* generic total positional list access; the in-range proof makes it a projection, never a fallback *)
Fixpoint nth_lt {A} (l : list A) : forall n, n < length l -> A :=
  match l with
  | [] => fun n H => False_rect A (Nat.nlt_0_r n H)
  | x :: xs => fun n =>
      match n with
      | O => fun _ => x
      | S k => fun H => nth_lt xs k (proj2 (Nat.succ_lt_mono k (length xs)) H)
      end
  end.

Lemma lt_unique (n m : nat) (p q : n < m) : p = q.
Proof. apply Peano_dec.le_unique. Qed.

Lemma nth_lt_nth_error {A} (l : list A) : forall n H, nth_error l n = Some (nth_lt l n H).
Proof.
  induction l as [|x xs IH]; intros [|k] H; cbn in *.
  - exfalso; exact (Nat.nlt_0_r 0 H).
  - exfalso; exact (Nat.nlt_0_r (S k) H).
  - reflexivity.
  - apply IH.
Qed.

(* one shallow cell: view, role, parent position, subtree extent, ordered direct-child positions, own parent slot *)
Record Cell : Type := mkCell {
  c_view     : NodeView ;
  c_role     : Role ;
  c_parent   : option nat ;
  c_extent   : nat ;
  c_children : list nat ;
  c_slot     : nat
}.

(* set only the parent-slot tag, leaving every structural field of the cell untouched *)
Definition set_slot (k : nat) (c : Cell) : Cell :=
  mkCell (c_view c) (c_role c) (c_parent c) (c_extent c) (c_children c) k.

Lemma set_slot_view : forall k c, c_view (set_slot k c) = c_view c. Proof. reflexivity. Qed.
Lemma set_slot_role : forall k c, c_role (set_slot k c) = c_role c. Proof. reflexivity. Qed.
Lemma set_slot_parent : forall k c, c_parent (set_slot k c) = c_parent c. Proof. reflexivity. Qed.
Lemma set_slot_extent : forall k c, c_extent (set_slot k c) = c_extent c. Proof. reflexivity. Qed.
Lemma set_slot_children : forall k c, c_children (set_slot k c) = c_children c. Proof. reflexivity. Qed.
Lemma set_slot_slot : forall k c, c_slot (set_slot k c) = k. Proof. reflexivity. Qed.

(* which views carry a required first-child edge, and the shape of that edge — shared vocabulary of the build *)
Definition requires_first_edge (v : NodeView) : bool :=
  match v with VApplication | VUnary _ | VStmt SSExpr => true | _ => false end.
Definition first_child_wf (children : list nat) (pos bnd : nat) : Prop :=
  match children with hp :: _ => hp = S pos /\ hp < bnd | [] => False end.



(* the exact role each child ordinal carries, a total formula over the parent's shallow view alone *)
Definition layout_role (v : NodeView) (k : nat) : Role :=
  match v with
  | VApplication => match k with 0 => RApplicationHead | S i => RApplicationArg i end
  | VUnary _ => RUnaryOperand
  | VStmt SSExpr => RExprStatementExpr
  | VStmt (SSShort nn _) => if k <? nn then RShortLhs else RPlain
  | VConstSpec (CSExplicit ht nn _) =>
      if k <? nn then RSpecName ConstSpecF else if andb ht (k =? nn) then RTypeUse else RPlain
  | VConstSpec (CSInherited _) => RSpecName ConstSpecF
  | VVarSpec (VSTypeOnly nn) => if k <? nn then RSpecName VarSpecF else RTypeUse
  | VVarSpec (VSValues ht nn _) =>
      if k <? nn then RSpecName VarSpecF else if andb ht (k =? nn) then RTypeUse else RPlain
  | VTypeSpec _ => match k with 0 => RSpecName TypeSpecF | _ => RTypeUse end
  | _ => RPlain
  end.
(* the exact child count a shape fixes; views whose counts live below the shallow scalars stay unconstrained *)
Definition layout_count (v : NodeView) : option nat :=
  match v with
  | VName _ | VLiteral _ | VTypeExpr _ | VBindingName _ => Some 0
  | VUnary _ => Some 1
  | VStmt SSExpr | VStmt SSDecl => Some 1
  | VStmt (SSShort nn nv) => Some (nn + nv)
  | VTop _ => Some 1
  | VConstSpec (CSExplicit ht nn nv) => Some (nn + (if ht then 1 else 0) + nv)
  | VConstSpec (CSInherited nn) => Some nn
  | VVarSpec (VSTypeOnly nn) => Some (nn + 1)
  | VVarSpec (VSValues ht nn nv) => Some (nn + (if ht then 1 else 0) + nv)
  | VTypeSpec _ => Some 2
  | _ => None
  end.
(* the kind of the child at ordinal k, a total formula over the parent view alone — the view-level layout *)
Definition layout_kind (v : NodeView) (k : nat) : Kind :=
  match v with
  | VApplication => ExprKind
  | VUnary _ => ExprKind
  | VStmt SSExpr => ExprKind
  | VStmt SSDecl => DeclKind
  | VStmt (SSShort nn _) => if k <? nn then BindingNameKind else ExprKind
  | VConstSpec (CSExplicit ht nn _) =>
      if k <? nn then BindingNameKind else if andb ht (k =? nn) then TypeExprKind else ExprKind
  | VConstSpec (CSInherited _) => BindingNameKind
  | VVarSpec (VSTypeOnly nn) => if k <? nn then BindingNameKind else TypeExprKind
  | VVarSpec (VSValues ht nn _) =>
      if k <? nn then BindingNameKind else if andb ht (k =? nn) then TypeExprKind else ExprKind
  | VTypeSpec _ => match k with 0 => BindingNameKind | _ => TypeExprKind end
  | VDecl fl => SpecKind fl
  | VBlock => StmtKind
  | VTop TSTopDecl => DeclKind
  | VTop TSMain => BlockKind
  | VFile => TopKind
  | VName _ | VLiteral _ | VTypeExpr _ | VBindingName _ => FileKind
  end.

(* each spec flavor's exact child view class: a declaration's children are exactly its flavor's specs *)
Definition spec_view_of_flavor (fl : SpecFlavor) (v : NodeView) : Prop :=
  match fl, v with
  | ConstSpecF, VConstSpec _ => True
  | VarSpecF, VVarSpec _ => True
  | TypeSpecF, VTypeSpec _ => True
  | _, _ => False
  end.
