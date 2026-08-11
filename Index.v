
From Stdlib Require Import PArith NArith List Bool Lia Sorted Recdef Wf_nat Arith Eqdep_dec String.
From Stdlib Require Import Structures.OrderedType FSets.FMapAVL FSets.FMapFacts SetoidList.
From Fido Require Import FilePath Collections Syntax.
Import ListNotations.
Local Open Scope positive_scope.

(* The node table's abstract interface; the sealing hides the standard map's operations, not its choice. *)

Module Type TABLE.
  Parameter table : Type -> Type.
  Parameter empty : forall {A}, table A.
  Parameter get   : forall {A}, positive -> table A -> option A.
  Parameter set   : forall {A}, positive -> A -> table A -> table A.
  Parameter get_empty     : forall {A} (k : positive), get k (@empty A) = None.
  Parameter get_set_same  : forall {A} (k : positive) (v : A) (t : table A), get k (set k v t) = Some v.
  Parameter get_set_other : forall {A} (j k : positive) (v : A) (t : table A),
    j <> k -> get k (set j v t) = get k t.
End TABLE.

Module Table : TABLE.
  Definition table := Collections.NodeMap.t.
  Definition empty {A} : table A := Collections.NodeMap.empty A.
  Definition get {A} (k : positive) (t : table A) : option A := Collections.NodeMap.find k t.
  Definition set {A} (k : positive) (v : A) (t : table A) : table A := Collections.NodeMap.add k v t.
  Lemma get_empty {A} (k : positive) : get k (@empty A) = None.
  Proof. apply Collections.NodeMap.gempty. Qed.
  Lemma get_set_same {A} (k : positive) (v : A) (t : table A) : get k (set k v t) = Some v.
  Proof. apply Collections.NodeMap.gss. Qed.
  Lemma get_set_other {A} (j k : positive) (v : A) (t : table A) :
    j <> k -> get k (set j v t) = get k t.
  Proof. intro H. apply Collections.NodeMap.gso. congruence. Qed.
End Table.

(* The occurrence universe; no kind exists ahead of the syntax it would designate. *)
Inductive Kind :=
| FileKind | PackageClauseKind
| TopLevelKind | DeclarationKind | SpecKind | BindingNameKind | TypeNameKind
| StatementKind | BlockKind | ExpressionKind.

(* how an occurrence participates in its parent, in source order *)
Inductive Role :=
| FileRoot
| FilePackage
| FileDeclaration (n : nat)
| MainBlock
| BlockStatement (n : nat)
| ExprStatementExpr
| DeclStatementDecl
| ShortLhs (n : nat)
| ShortRhs (n : nat)
| DeclSpec (n : nat)
| SpecName (n : nat)
| SpecTypeUse
| SpecValue (n : nat)
| UnaryOperand
| ApplicationHead
| ApplicationArgument (n : nat).

(* small structural metadata, with no copy of the recursive subtree *)
Record Meta := MakeMeta {
  kind        : Kind;
  parent      : option positive;
  role        : Role;
  subtree_end : positive
}.

Definition root_id : positive := 1.
Definition package_id  : positive := 2.

(* total extraction from a provably-present option, the basis for the total reference API *)
Definition option_get {A} (o : option A) : o <> None -> A :=
  match o with Some a => fun _ => a | None => fun H => False_rect A (H eq_refl) end.
Lemma option_get_eq {A} (o : option A) (H : o <> None) (a : A) : o = Some a -> option_get o H = a.
Proof. intros Heq. subst o. reflexivity. Qed.
Lemma option_get_some {A} (o : option A) : forall (H : o <> None), o = Some (option_get o H).
Proof. destruct o as [a|]; intro H; [reflexivity | exfalso; exact (H eq_refl)]. Qed.

(* the import list is intrinsically nil, and consuming it structurally makes a future constructor break here *)
Lemma import_list_nil : forall (l : list Syntax.ImportSpec), l = [].
Proof. intros [|i rest]; [ reflexivity | destruct i ]. Qed.

(* The one-pass builder: a subtree returns its last id, a sibling run the next free one. *)

Fixpoint build_expr (parent : positive) (role : Role) (me : positive) (e : Syntax.Expr)
                    (t : Table.table Meta) : Table.table Meta * positive  :=
  match e with
  | Syntax.Name _ | Syntax.LiteralExpr _ =>
      (Table.set me (MakeMeta ExpressionKind (Some parent) role me) t, me)
  | Syntax.Unary _ e' =>
      let '(t1, e1) := build_expr me UnaryOperand (Pos.succ me) e' t in
      (Table.set me (MakeMeta ExpressionKind (Some parent) role e1) t1, e1)
  | Syntax.Application head args =>
      (* head subtree from [me+1], then the ordered arguments *)
      let '(th, eh) := build_expr me ApplicationHead (Pos.succ me) head t in
      let '(ta, nx) := (fix ba (i : nat) (mi : positive) (xs : list Syntax.Expr) (tt : Table.table Meta)
                          : Table.table Meta * positive :=
                          match xs with
                          | []        => (tt, mi)
                          | x :: rest =>
                              let '(t1, se) := build_expr me (ApplicationArgument i) mi x tt in
                              ba (S i) (Pos.succ se) rest t1
                          end) 0%nat (Pos.succ eh) args th in
      (Table.set me (MakeMeta ExpressionKind (Some parent) role (Pos.pred nx)) ta, Pos.pred nx)
  end.

(* The one generic sibling-run builder: a subtree returns its last id, a run the next free one. *)
Fixpoint build_seq {X} (bx : positive -> nat -> positive -> X -> Table.table Meta -> Table.table Meta * positive)
                   (parent : positive) (i0 : nat) (me0 : positive) (xs : list X) (t : Table.table Meta)
  : Table.table Meta * positive (* next free id *) :=
  match xs with
  | []        => (t, me0)
  | x :: rest =>
      let '(t1, se) := bx parent i0 me0 x t in
      build_seq bx parent (S i0) (Pos.succ se) rest t1
  end.

(* Leaves: a type use and a binding name each occupy exactly one id and hold no sub-occurrence. *)
Definition build_type_expr (parent : positive) (role : Role) (me : positive) (_ : Syntax.TypeExpr)
                           (t : Table.table Meta) : Table.table Meta * positive :=
  (Table.set me (MakeMeta TypeNameKind (Some parent) role me) t, me).
Definition build_binding_name (parent : positive) (role : Role) (me : positive) (_ : Syntax.BindingName)
                              (t : Table.table Meta) : Table.table Meta * positive :=
  (Table.set me (MakeMeta BindingNameKind (Some parent) role me) t, me).

(* An optional type use consumes one id when present, none when absent, returning the next free id. *)
Definition build_opt_type (parent : positive) (me : positive) (oty : option Syntax.TypeExpr)
                          (t : Table.table Meta) : Table.table Meta * positive :=
  match oty with
  | Some ty => let '(t1, e1) := build_type_expr parent SpecTypeUse me ty t in (t1, Pos.succ e1)
  | None    => (t, me)
  end.

Definition build_names (parent : positive) (me : positive) (ns : Collections.NonEmpty Syntax.BindingName)
                       (t : Table.table Meta) : Table.table Meta * positive :=
  build_seq (fun p i m x tt => build_binding_name p (SpecName i) m x tt) parent 0 me (Collections.ne_to_list ns) t.
Definition build_values (parent : positive) (me : positive) (vs : Collections.NonEmpty Syntax.Expr)
                        (t : Table.table Meta) : Table.table Meta * positive :=
  build_seq (fun p i m x tt => build_expr p (SpecValue i) m x tt) parent 0 me (Collections.ne_to_list vs) t.

Definition build_const_spec (parent : positive) (didx : nat) (me : positive) (s : Syntax.ConstSpec)
                            (t : Table.table Meta) : Table.table Meta * positive :=
  let '(tn, m1) := build_names me (Pos.succ me) (Syntax.const_names s) t in
  let '(tv, nx) :=
    match Syntax.const_init s with
    | Syntax.ExplicitConstInit oty vals =>
        let '(t1, m2) := build_opt_type me m1 oty tn in build_values me m2 vals t1
    | Syntax.InheritedConstInit => (tn, m1)
    end in
  (Table.set me (MakeMeta SpecKind (Some parent) (DeclSpec didx) (Pos.pred nx)) tv, Pos.pred nx).

Definition build_var_spec (parent : positive) (didx : nat) (me : positive) (s : Syntax.VarSpec)
                          (t : Table.table Meta) : Table.table Meta * positive :=
  let '(tn, m1) := build_names me (Pos.succ me) (Syntax.var_names s) t in
  let '(tv, nx) :=
    match Syntax.var_init s with
    | Syntax.VarTypeOnly ty => let '(t1, m2) := build_opt_type me m1 (Some ty) tn in (t1, m2)
    | Syntax.VarValues oty vals =>
        let '(t1, m2) := build_opt_type me m1 oty tn in build_values me m2 vals t1
    end in
  (Table.set me (MakeMeta SpecKind (Some parent) (DeclSpec didx) (Pos.pred nx)) tv, Pos.pred nx).

Definition build_type_spec (parent : positive) (didx : nat) (me : positive) (s : Syntax.TypeSpec)
                           (t : Table.table Meta) : Table.table Meta * positive :=
  let '(tn, target) := match s with Syntax.AliasSpec nm ty | Syntax.DefSpec nm ty =>
    let '(t1, e1) := build_binding_name me (SpecName 0) (Pos.succ me) nm t in
    build_type_expr me SpecTypeUse (Pos.succ e1) ty t1 end in
  (Table.set me (MakeMeta SpecKind (Some parent) (DeclSpec didx) target) tn, target).

Definition build_declaration (parent : positive) (role : Role) (me : positive) (d : Syntax.Declaration)
                             (t : Table.table Meta) : Table.table Meta * positive :=
  let '(t1, nx) :=
    match d with
    | Syntax.ConstDecl specs => build_seq build_const_spec me 0 (Pos.succ me) specs t
    | Syntax.VarDecl specs   => build_seq build_var_spec me 0 (Pos.succ me) specs t
    | Syntax.TypeDecl specs  => build_seq build_type_spec me 0 (Pos.succ me) specs t
    end in
  (Table.set me (MakeMeta DeclarationKind (Some parent) role (Pos.pred nx)) t1, Pos.pred nx).

Definition build_stmt (parent : positive) (sidx : nat) (me : positive) (s : Syntax.Stmt)
                      (t : Table.table Meta) : Table.table Meta * positive :=
  match s with
  | Syntax.ExprStmt e =>
      let '(t1, e1) := build_expr me ExprStatementExpr (Pos.succ me) e t in
      (Table.set me (MakeMeta StatementKind (Some parent) (BlockStatement sidx) e1) t1, e1)
  | Syntax.DeclarationStmt d =>
      let '(t1, e1) := build_declaration me DeclStatementDecl (Pos.succ me) d t in
      (Table.set me (MakeMeta StatementKind (Some parent) (BlockStatement sidx) e1) t1, e1)
  | Syntax.ShortVarDecl names vals =>
      let '(tn, m1) := build_seq (fun p i m x tt => build_binding_name p (ShortLhs i) m x tt)
                         me 0 (Pos.succ me) (Collections.ne_to_list names) t in
      let '(tv, nx) := build_seq (fun p i m x tt => build_expr p (ShortRhs i) m x tt)
                         me 0 m1 (Collections.ne_to_list vals) tn in
      (Table.set me (MakeMeta StatementKind (Some parent) (BlockStatement sidx) (Pos.pred nx)) tv, Pos.pred nx)
  end.

Definition build_block (parent : positive) (role : Role) (me : positive) (b : Syntax.Block)
                       (t : Table.table Meta) : Table.table Meta * positive :=
  match b with
  | Syntax.MakeBlock stmts =>
      let '(t1, nx) := build_seq build_stmt me 0 (Pos.succ me) stmts t in
      (Table.set me (MakeMeta BlockKind (Some parent) role (Pos.pred nx)) t1, Pos.pred nx)
  end.

Definition build_decl (parent : positive) (didx : nat) (me : positive) (d : Syntax.TopLevelDecl)
                      (t : Table.table Meta) : Table.table Meta * positive :=
  match d with
  | Syntax.TopDeclaration dcl =>
      let '(t1, e1) := build_declaration me (FileDeclaration didx) (Pos.succ me) dcl t in
      (Table.set me (MakeMeta TopLevelKind (Some parent) (FileDeclaration didx) e1) t1, e1)
  | Syntax.Main body =>
      let '(t1, e1) := build_block me MainBlock (Pos.succ me) body t in
      (Table.set me (MakeMeta TopLevelKind (Some parent) (FileDeclaration didx) e1) t1, e1)
  end.

(* The per-file index carries NO path (the path is the outer map key — no second file identity). *)
Record File := MakeFile {
  table : Table.table Meta;
  count : positive
}.

(* a file root's children in preorder are its package clause, then its declarations *)
Definition build_file (f : Syntax.File) : File :=
  match Syntax.imports f with
  | i :: _ => match i with end
  | [] =>
      let tp := Table.set package_id (MakeMeta PackageClauseKind (Some root_id) FilePackage package_id) Table.empty in
      let '(t1, nx) := build_seq build_decl root_id 0 (Pos.succ package_id) (Syntax.declarations f) tp in
      let cnt := Pos.pred nx in
      MakeFile (Table.set root_id (MakeMeta FileKind None FileRoot cnt) t1) cnt
  end.

(* The one generic table-free run: given each element's last id, the run's next free id. *)
Fixpoint next_seq {X} (endf : positive -> X -> positive) (me0 : positive) (xs : list X) : positive :=
  match xs with [] => me0 | x :: rest => next_seq endf (Pos.succ (endf me0 x)) rest end.

Fixpoint end_expr (me : positive) (e : Syntax.Expr) : positive :=
  match e with
  | Syntax.Name _ | Syntax.LiteralExpr _ => me
  | Syntax.Unary _ e' => end_expr (Pos.succ me) e'
  | Syntax.Application head args =>
      let eh := end_expr (Pos.succ me) head in
      Pos.pred ((fix ne (mi : positive) (xs : list Syntax.Expr) : positive :=
                   match xs with [] => mi | x :: rest => ne (Pos.succ (end_expr mi x)) rest end)
                (Pos.succ eh) args)
  end.
Definition next_exprs (me : positive) (es : list Syntax.Expr) : positive := next_seq end_expr me es.

Definition end_type_expr (me : positive) (_ : Syntax.TypeExpr) : positive := me.
Definition end_binding_name (me : positive) (_ : Syntax.BindingName) : positive := me.
Definition next_opt_type (me : positive) (oty : option Syntax.TypeExpr) : positive :=
  match oty with Some _ => Pos.succ me | None => me end.

Definition end_const_spec (me : positive) (s : Syntax.ConstSpec) : positive :=
  let m1 := next_seq end_binding_name (Pos.succ me) (Collections.ne_to_list (Syntax.const_names s)) in
  Pos.pred (match Syntax.const_init s with
            | Syntax.ExplicitConstInit oty vals =>
                next_seq end_expr (next_opt_type m1 oty) (Collections.ne_to_list vals)
            | Syntax.InheritedConstInit => m1 end).
Definition end_var_spec (me : positive) (s : Syntax.VarSpec) : positive :=
  let m1 := next_seq end_binding_name (Pos.succ me) (Collections.ne_to_list (Syntax.var_names s)) in
  Pos.pred (match Syntax.var_init s with
            | Syntax.VarTypeOnly ty => next_opt_type m1 (Some ty)
            | Syntax.VarValues oty vals => next_seq end_expr (next_opt_type m1 oty) (Collections.ne_to_list vals) end).
Definition end_type_spec (me : positive) (_ : Syntax.TypeSpec) : positive := Pos.succ (Pos.succ me).

Definition end_declaration (me : positive) (d : Syntax.Declaration) : positive :=
  Pos.pred (match d with
            | Syntax.ConstDecl specs => next_seq end_const_spec (Pos.succ me) specs
            | Syntax.VarDecl specs   => next_seq end_var_spec (Pos.succ me) specs
            | Syntax.TypeDecl specs  => next_seq end_type_spec (Pos.succ me) specs end).

Definition end_stmt (me : positive) (s : Syntax.Stmt) : positive :=
  match s with
  | Syntax.ExprStmt e => end_expr (Pos.succ me) e
  | Syntax.DeclarationStmt d => end_declaration (Pos.succ me) d
  | Syntax.ShortVarDecl names vals =>
      let m1 := next_seq end_binding_name (Pos.succ me) (Collections.ne_to_list names) in
      Pos.pred (next_seq end_expr m1 (Collections.ne_to_list vals))
  end.
Definition next_stmts (me : positive) (ss : list Syntax.Stmt) : positive := next_seq end_stmt me ss.
Definition end_block (me : positive) (b : Syntax.Block) : positive :=
  match b with Syntax.MakeBlock stmts => Pos.pred (next_seq end_stmt (Pos.succ me) stmts) end.

Definition end_decl (me : positive) (d : Syntax.TopLevelDecl) : positive :=
  match d with
  | Syntax.TopDeclaration dcl => end_declaration (Pos.succ me) dcl
  | Syntax.Main body => end_block (Pos.succ me) body
  end.
Definition next_decls (me : positive) (ds : list Syntax.TopLevelDecl) : positive := next_seq end_decl me ds.
Definition count_file (f : Syntax.File) : positive := Pos.pred (next_decls (Pos.succ package_id) (Syntax.declarations f)).

(*  generic sibling-run reasoning, shared by every list position  *)

Lemma next_seq_ge {X} (endx : positive -> X -> positive) :
  (forall me x, (me <= endx me x)%positive) ->
  forall xs me, (me <= next_seq endx me xs)%positive.
Proof.
  intros Hge xs. induction xs as [|x rest IH]; intros me; cbn [next_seq]; [lia|].
  specialize (IH (Pos.succ (endx me x))). pose proof (Hge me x). lia.
Qed.

Lemma build_seq_end {X}
  (bx : positive -> nat -> positive -> X -> Table.table Meta -> Table.table Meta * positive)
  (endx : positive -> X -> positive) (parent : positive) (xs : list X) :
  (forall x, In x xs -> forall i me t, snd (bx parent i me x t) = endx me x) ->
  forall i me t, snd (build_seq bx parent i me xs t) = next_seq endx me xs.
Proof.
  intros H. induction xs as [|x rest IH]; intros i me t; cbn [build_seq next_seq]; [reflexivity|].
  pose proof (H x (or_introl eq_refl) i me t) as He.
  destruct (bx parent i me x t) as [t1 se] eqn:E1. cbn [snd] in He. subst se.
  apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

(* the anonymous inner fixes for application arguments coincide with the named seq combinators *)
Lemma next_exprs_inner : forall args start,
  (fix ne (mi : positive) (xs : list Syntax.Expr) : positive :=
     match xs with [] => mi | x :: rest => ne (Pos.succ (end_expr mi x)) rest end) start args
  = next_exprs start args.
Proof.
  induction args as [|x rest IH]; intros start; [reflexivity|].
  exact (IH (Pos.succ (end_expr start x))).
Qed.

Lemma build_args_inner : forall me args i start th,
  (fix ba (i0 : nat) (mi : positive) (xs : list Syntax.Expr) (tt : Table.table Meta) : Table.table Meta * positive :=
     match xs with
     | [] => (tt, mi)
     | x :: rest => let '(t1, se) := build_expr me (ApplicationArgument i0) mi x tt in ba (S i0) (Pos.succ se) rest t1
     end) i start args th
  = build_seq (fun _ j m x tt => build_expr me (ApplicationArgument j) m x tt) me i start args th.
Proof.
  intros me args. induction args as [|x rest IH]; intros i start th; [reflexivity|].
  simpl. destruct (build_expr me (ApplicationArgument i) start x th) as [t1 se]. apply IH.
Qed.

Lemma end_expr_app : forall me head args,
  end_expr me (Syntax.Application head args)
  = Pos.pred (next_exprs (Pos.succ (end_expr (Pos.succ me) head)) args).
Proof.
  intros me head args.
  change (end_expr me (Syntax.Application head args)) with
    (Pos.pred ((fix ne (mi : positive) (xs : list Syntax.Expr) : positive :=
                  match xs with [] => mi | x :: rest => ne (Pos.succ (end_expr mi x)) rest end)
               (Pos.succ (end_expr (Pos.succ me) head)) args)).
  rewrite next_exprs_inner. reflexivity.
Qed.

Lemma build_expr_app : forall parent role me head args t,
  build_expr parent role me (Syntax.Application head args) t
  = let '(th, eh) := build_expr me ApplicationHead (Pos.succ me) head t in
    let '(ta, nx) := build_seq (fun _ i m x tt => build_expr me (ApplicationArgument i) m x tt)
                       me 0 (Pos.succ eh) args th in
    (Table.set me (MakeMeta ExpressionKind (Some parent) role (Pos.pred nx)) ta, Pos.pred nx).
Proof.
  intros parent role me head args t.
  change (build_expr parent role me (Syntax.Application head args) t) with
    (let '(th, eh) := build_expr me ApplicationHead (Pos.succ me) head t in
     let '(ta, nx) := (fix ba (i0 : nat) (mi : positive) (xs : list Syntax.Expr) (tt : Table.table Meta)
                          : Table.table Meta * positive :=
                          match xs with
                          | [] => (tt, mi)
                          | x :: rest => let '(t1, se) := build_expr me (ApplicationArgument i0) mi x tt in ba (S i0) (Pos.succ se) rest t1
                          end) 0%nat (Pos.succ eh) args th in
     (Table.set me (MakeMeta ExpressionKind (Some parent) role (Pos.pred nx)) ta, Pos.pred nx)).
  destruct (build_expr me ApplicationHead (Pos.succ me) head t) as [th eh].
  rewrite build_args_inner. reflexivity.
Qed.

(* the last-id of any subtree never precedes its first id *)
Lemma end_expr_ge : forall me e, (me <= end_expr me e)%positive.
Proof.
  intros me e; revert me.
  induction e as [ n | l | op e' IH | head args IHhead IHargs ] using Syntax.Expr_ind'; intros me.
  - cbn [end_expr]; lia.
  - cbn [end_expr]; lia.
  - cbn [end_expr]; specialize (IH (Pos.succ me)); lia.
  - rewrite end_expr_app. unfold next_exprs.
    pose proof (IHhead (Pos.succ me)) as Hh.
    assert (Hn : forall mi, (mi <= next_seq end_expr mi args)%positive).
    { clear -IHargs. induction IHargs as [|x rest Hx Hrest IH]; intros mi; cbn [next_seq]; [lia|].
      specialize (Hx mi). specialize (IH (Pos.succ (end_expr mi x))). lia. }
    pose proof (Hn (Pos.succ (end_expr (Pos.succ me) head))). lia.
Qed.

Lemma next_exprs_ge : forall es me, (me <= next_exprs me es)%positive.
Proof. intros es me. apply next_seq_ge. apply end_expr_ge. Qed.

Lemma end_type_expr_ge : forall me t, (me <= end_type_expr me t)%positive.
Proof. intros me t. unfold end_type_expr. lia. Qed.
Lemma end_binding_name_ge : forall me b, (me <= end_binding_name me b)%positive.
Proof. intros me b. unfold end_binding_name. lia. Qed.

Lemma end_const_spec_ge : forall me s, (me <= end_const_spec me s)%positive.
Proof.
  intros me s. unfold end_const_spec.
  set (m1 := next_seq end_binding_name (Pos.succ me) (Collections.ne_to_list (Syntax.const_names s))).
  assert (Hm1 : (Pos.succ me <= m1)%positive) by (apply next_seq_ge; apply end_binding_name_ge).
  destruct (Syntax.const_init s) as [oty vals|].
  - assert (Hnx : (m1 <= next_opt_type m1 oty)%positive) by (unfold next_opt_type; destruct oty; lia).
    pose proof (next_seq_ge end_expr end_expr_ge (Collections.ne_to_list vals) (next_opt_type m1 oty)). lia.
  - lia.
Qed.
Lemma end_var_spec_ge : forall me s, (me <= end_var_spec me s)%positive.
Proof.
  intros me s. unfold end_var_spec.
  set (m1 := next_seq end_binding_name (Pos.succ me) (Collections.ne_to_list (Syntax.var_names s))).
  assert (Hm1 : (Pos.succ me <= m1)%positive) by (apply next_seq_ge; apply end_binding_name_ge).
  destruct (Syntax.var_init s) as [ty|oty vals].
  - unfold next_opt_type. lia.
  - assert (Hnx : (m1 <= next_opt_type m1 oty)%positive) by (unfold next_opt_type; destruct oty; lia).
    pose proof (next_seq_ge end_expr end_expr_ge (Collections.ne_to_list vals) (next_opt_type m1 oty)). lia.
Qed.
Lemma end_type_spec_ge : forall me s, (me <= end_type_spec me s)%positive.
Proof. intros me s. unfold end_type_spec. lia. Qed.

Lemma end_declaration_ge : forall me d, (me <= end_declaration me d)%positive.
Proof.
  intros me d. unfold end_declaration. destruct d as [specs|specs|specs].
  - pose proof (next_seq_ge end_const_spec end_const_spec_ge specs (Pos.succ me)). lia.
  - pose proof (next_seq_ge end_var_spec end_var_spec_ge specs (Pos.succ me)). lia.
  - pose proof (next_seq_ge end_type_spec end_type_spec_ge specs (Pos.succ me)). lia.
Qed.

Lemma end_stmt_ge : forall me s, (me <= end_stmt me s)%positive.
Proof.
  intros me s. destruct s as [e|d|names vals]; cbn [end_stmt].
  - pose proof (end_expr_ge (Pos.succ me) e). lia.
  - pose proof (end_declaration_ge (Pos.succ me) d). lia.
  - set (m1 := next_seq end_binding_name (Pos.succ me) (Collections.ne_to_list names)).
    assert (Hm1 : (Pos.succ me <= m1)%positive) by (apply next_seq_ge; apply end_binding_name_ge).
    pose proof (next_seq_ge end_expr end_expr_ge (Collections.ne_to_list vals) m1). lia.
Qed.
Lemma next_stmts_ge : forall ss me, (me <= next_stmts me ss)%positive.
Proof. intros ss me. apply next_seq_ge. apply end_stmt_ge. Qed.

Lemma end_block_ge : forall me b, (me <= end_block me b)%positive.
Proof. intros me [stmts]. cbn [end_block]. pose proof (next_seq_ge end_stmt end_stmt_ge stmts (Pos.succ me)). lia. Qed.

Lemma end_decl_ge : forall me d, (me <= end_decl me d)%positive.
Proof.
  intros me d. destruct d as [dcl|body]; cbn [end_decl].
  - pose proof (end_declaration_ge (Pos.succ me) dcl). lia.
  - pose proof (end_block_ge (Pos.succ me) body). lia.
Qed.

(* the last id a build emits equals its table-free end boundary function *)

Lemma build_expr_end : forall e parent role me t, snd (build_expr parent role me e t) = end_expr me e.
Proof.
  induction e as [ n | l | op e' IH | head args IHhead IHargs ] using Syntax.Expr_ind';
    intros parent role me t.
  - reflexivity.
  - reflexivity.
  - cbn [build_expr end_expr]. destruct (build_expr me UnaryOperand (Pos.succ me) e' t) as [t1 e1] eqn:E1.
    pose proof (IH me UnaryOperand (Pos.succ me) t) as He. rewrite E1 in He. cbn [snd] in *. exact He.
  - rewrite Forall_forall in IHargs. rewrite build_expr_app, end_expr_app.
    pose proof (IHhead me ApplicationHead (Pos.succ me) t) as Hh.
    destruct (build_expr me ApplicationHead (Pos.succ me) head t) as [th eh] eqn:Eh.
    cbn [snd] in Hh. subst eh.
    assert (Helt : forall x, In x args -> forall i m tt,
              snd (build_expr me (ApplicationArgument i) m x tt) = end_expr m x)
      by (intros x Hx i m tt; exact (IHargs x Hx me (ApplicationArgument i) m tt)).
    pose proof (build_seq_end (fun _ i m x tt => build_expr me (ApplicationArgument i) m x tt)
                  end_expr me args Helt 0 (Pos.succ (end_expr (Pos.succ me) head)) th) as Hs.
    destruct (build_seq (fun _ i m x tt => build_expr me (ApplicationArgument i) m x tt) me 0
                (Pos.succ (end_expr (Pos.succ me) head)) args th) as [ta nx].
    cbn [snd] in Hs |- *. unfold next_exprs. rewrite Hs. reflexivity.
Qed.

Lemma build_type_expr_end : forall ty parent role me t,
  snd (build_type_expr parent role me ty t) = end_type_expr me ty.
Proof. reflexivity. Qed.
Lemma build_binding_name_end : forall b parent role me t,
  snd (build_binding_name parent role me b t) = end_binding_name me b.
Proof. reflexivity. Qed.

Lemma build_names_next : forall ns parent me t,
  snd (build_names parent me ns t) = next_seq end_binding_name me (Collections.ne_to_list ns).
Proof.
  intros ns parent me t. unfold build_names.
  apply (build_seq_end (fun p i m x tt => build_binding_name p (SpecName i) m x tt)
           end_binding_name parent (Collections.ne_to_list ns)).
  intros x _ i m tt. reflexivity.
Qed.
Lemma build_values_next : forall vs parent me t,
  snd (build_values parent me vs t) = next_seq end_expr me (Collections.ne_to_list vs).
Proof.
  intros vs parent me t. unfold build_values.
  apply (build_seq_end (fun p i m x tt => build_expr p (SpecValue i) m x tt)
           end_expr parent (Collections.ne_to_list vs)).
  intros x _ i m tt. apply build_expr_end.
Qed.
Lemma build_opt_type_next : forall oty parent me t,
  snd (build_opt_type parent me oty t) = next_opt_type me oty.
Proof.
  intros oty parent me t. unfold build_opt_type, next_opt_type. destruct oty as [ty|]; reflexivity.
Qed.

Lemma build_const_spec_end : forall s parent didx me t,
  snd (build_const_spec parent didx me s t) = end_const_spec me s.
Proof.
  intros s parent didx me t. unfold build_const_spec, end_const_spec.
  pose proof (build_names_next (Syntax.const_names s) me (Pos.succ me) t) as Hn.
  destruct (build_names me (Pos.succ me) (Syntax.const_names s) t) as [tn m1] eqn:En.
  cbn [snd] in Hn. subst m1.
  set (m1 := next_seq end_binding_name (Pos.succ me) (Collections.ne_to_list (Syntax.const_names s))).
  destruct (Syntax.const_init s) as [oty vals|].
  - pose proof (build_opt_type_next oty me m1 tn) as Ho.
    destruct (build_opt_type me m1 oty tn) as [t1 m2] eqn:Eo. cbn [snd] in Ho. subst m2.
    pose proof (build_values_next vals me (next_opt_type m1 oty) t1) as Hv.
    destruct (build_values me (next_opt_type m1 oty) vals t1) as [tv nx] eqn:Ev.
    cbn [snd] in Hv |- *. subst nx. reflexivity.
  - cbn [snd]. reflexivity.
Qed.
Lemma build_var_spec_end : forall s parent didx me t,
  snd (build_var_spec parent didx me s t) = end_var_spec me s.
Proof.
  intros s parent didx me t. unfold build_var_spec, end_var_spec.
  pose proof (build_names_next (Syntax.var_names s) me (Pos.succ me) t) as Hn.
  destruct (build_names me (Pos.succ me) (Syntax.var_names s) t) as [tn m1] eqn:En.
  cbn [snd] in Hn. subst m1.
  set (m1 := next_seq end_binding_name (Pos.succ me) (Collections.ne_to_list (Syntax.var_names s))).
  destruct (Syntax.var_init s) as [ty|oty vals].
  - pose proof (build_opt_type_next (Some ty) me m1 tn) as Ho.
    destruct (build_opt_type me m1 (Some ty) tn) as [t1 m2] eqn:Eo. cbn [snd] in Ho |- *. subst m2. reflexivity.
  - pose proof (build_opt_type_next oty me m1 tn) as Ho.
    destruct (build_opt_type me m1 oty tn) as [t1 m2] eqn:Eo. cbn [snd] in Ho. subst m2.
    pose proof (build_values_next vals me (next_opt_type m1 oty) t1) as Hv.
    destruct (build_values me (next_opt_type m1 oty) vals t1) as [tv nx] eqn:Ev.
    cbn [snd] in Hv |- *. subst nx. reflexivity.
Qed.
Lemma build_type_spec_end : forall s parent didx me t,
  snd (build_type_spec parent didx me s t) = end_type_spec me s.
Proof.
  intros s parent didx me t. unfold build_type_spec, end_type_spec.
  destruct s as [nm ty|nm ty]; reflexivity.
Qed.

Lemma build_declaration_end : forall d parent role me t,
  snd (build_declaration parent role me d t) = end_declaration me d.
Proof.
  intros d parent role me t. unfold build_declaration, end_declaration.
  destruct d as [specs|specs|specs].
  - pose proof (build_seq_end build_const_spec end_const_spec me specs
                  (fun x _ i m tt => build_const_spec_end x me i m tt) 0 (Pos.succ me) t) as Hs.
    destruct (build_seq build_const_spec me 0 (Pos.succ me) specs t) as [t1 nx].
    cbn [snd] in Hs |- *. subst nx. reflexivity.
  - pose proof (build_seq_end build_var_spec end_var_spec me specs
                  (fun x _ i m tt => build_var_spec_end x me i m tt) 0 (Pos.succ me) t) as Hs.
    destruct (build_seq build_var_spec me 0 (Pos.succ me) specs t) as [t1 nx].
    cbn [snd] in Hs |- *. subst nx. reflexivity.
  - pose proof (build_seq_end build_type_spec end_type_spec me specs
                  (fun x _ i m tt => build_type_spec_end x me i m tt) 0 (Pos.succ me) t) as Hs.
    destruct (build_seq build_type_spec me 0 (Pos.succ me) specs t) as [t1 nx].
    cbn [snd] in Hs |- *. subst nx. reflexivity.
Qed.

Lemma build_stmt_end : forall s parent sidx me t,
  snd (build_stmt parent sidx me s t) = end_stmt me s.
Proof.
  intros s parent sidx me t. destruct s as [e|d|names vals]; cbn [build_stmt end_stmt].
  - pose proof (build_expr_end e me ExprStatementExpr (Pos.succ me) t) as He.
    destruct (build_expr me ExprStatementExpr (Pos.succ me) e t) as [t1 e1].
    cbn [snd] in He |- *. exact He.
  - pose proof (build_declaration_end d me DeclStatementDecl (Pos.succ me) t) as He.
    destruct (build_declaration me DeclStatementDecl (Pos.succ me) d t) as [t1 e1].
    cbn [snd] in He |- *. exact He.
  - pose proof (build_seq_end (fun p i m x tt => build_binding_name p (ShortLhs i) m x tt)
                  end_binding_name me (Collections.ne_to_list names)
                  (fun x _ i m tt => eq_refl) 0 (Pos.succ me) t) as Hn.
    destruct (build_seq (fun p i m x tt => build_binding_name p (ShortLhs i) m x tt) me 0
                (Pos.succ me) (Collections.ne_to_list names) t) as [tn m1].
    cbn [snd] in Hn. subst m1.
    pose proof (build_seq_end (fun p i m x tt => build_expr p (ShortRhs i) m x tt)
                  end_expr me (Collections.ne_to_list vals)
                  (fun x _ i m tt => build_expr_end x me (ShortRhs i) m tt) 0
                  (next_seq end_binding_name (Pos.succ me) (Collections.ne_to_list names)) tn) as Hv.
    destruct (build_seq (fun p i m x tt => build_expr p (ShortRhs i) m x tt) me 0
                (next_seq end_binding_name (Pos.succ me) (Collections.ne_to_list names)) (Collections.ne_to_list vals) tn)
      as [tv nx].
    cbn [snd] in Hv |- *. subst nx. reflexivity.
Qed.

Lemma build_block_end : forall b parent role me t,
  snd (build_block parent role me b t) = end_block me b.
Proof.
  intros b parent role me t. destruct b as [stmts]. cbn [build_block end_block].
  pose proof (build_seq_end build_stmt end_stmt me stmts
                (fun x _ i m tt => build_stmt_end x me i m tt) 0 (Pos.succ me) t) as Hs.
  destruct (build_seq build_stmt me 0 (Pos.succ me) stmts t) as [t1 nx].
  cbn [snd] in Hs |- *. subst nx. reflexivity.
Qed.

Lemma build_decl_end : forall d parent didx me t,
  snd (build_decl parent didx me d t) = end_decl me d.
Proof.
  intros d parent didx me t. destruct d as [dcl|body]; cbn [build_decl end_decl].
  - pose proof (build_declaration_end dcl me (FileDeclaration didx) (Pos.succ me) t) as He.
    destruct (build_declaration me (FileDeclaration didx) (Pos.succ me) dcl t) as [t1 e1].
    cbn [snd] in He |- *. exact He.
  - pose proof (build_block_end body me MainBlock (Pos.succ me) t) as He.
    destruct (build_block me MainBlock (Pos.succ me) body t) as [t1 e1].
    cbn [snd] in He |- *. exact He.
Qed.

Lemma build_file_count : forall f, count (build_file f) = count_file f.
Proof.
  intros f. unfold build_file, count_file. destruct (Syntax.imports f) as [|i ?]; [| destruct i].
  pose proof (build_seq_end build_decl end_decl root_id (Syntax.declarations f)
                (fun x _ i m tt => build_decl_end x root_id i m tt) 0 (Pos.succ package_id)
                (Table.set package_id (MakeMeta PackageClauseKind (Some root_id) FilePackage package_id) Table.empty)) as Hs.
  destruct (build_seq build_decl root_id 0 (Pos.succ package_id) (Syntax.declarations f)
              (Table.set package_id (MakeMeta PackageClauseKind (Some root_id) FilePackage package_id) Table.empty))
    as [t1 nx].
  cbn [count snd] in Hs |- *. unfold next_decls. rewrite Hs. reflexivity.
Qed.
(* the three spec shapes share one occurrence kind; this is the retained spec payload *)
Inductive AnySpec : Type :=
| ASConst : Syntax.ConstSpec -> AnySpec
| ASVar   : Syntax.VarSpec  -> AnySpec
| ASType  : Syntax.TypeSpec -> AnySpec.

Inductive View : Kind -> Type :=
| FileView          : Syntax.File         -> View FileKind
| PackageClauseView : Syntax.PackageClause -> View PackageClauseKind
| TopLevelView      : Syntax.TopLevelDecl -> View TopLevelKind
| DeclarationView   : Syntax.Declaration  -> View DeclarationKind
| SpecView          : AnySpec             -> View SpecKind
| BindingNameView   : Syntax.BindingName  -> View BindingNameKind
| TypeNameView      : Syntax.TypeExpr     -> View TypeNameKind
| StatementView     : Syntax.Stmt         -> View StatementKind
| BlockView         : Syntax.Block        -> View BlockKind
| ExpressionView    : Syntax.Expr         -> View ExpressionKind.

Record Occurrence := MakeOccurrence {
  occurrence_kind        : Kind;
  occurrence_view        : View occurrence_kind;
  occurrence_parent      : option positive;
  occurrence_role        : Role;
  occurrence_subtree_end : positive
}.

Definition occurrence_meta (o : Occurrence) : Meta :=
  MakeMeta (occurrence_kind o) (occurrence_parent o) (occurrence_role o) (occurrence_subtree_end o).

Definition view_expr (o : Occurrence) : option Syntax.Expr :=
  match occurrence_view o with ExpressionView e => Some e | _ => None end.

(* [view_expr] is [Some] EXACTLY for an [ExpressionKind] occurrence (the dependent [View] forces the kind). *)
Lemma view_expr_kind : forall o e, view_expr o = Some e -> occurrence_kind o = ExpressionKind.
Proof.
  intros [k v par role sub] e H. cbn [view_expr occurrence_view occurrence_kind] in *.
  destruct v; try discriminate H. reflexivity.
Qed.
Lemma kind_view_expr : forall o, occurrence_kind o = ExpressionKind -> exists e, view_expr o = Some e.
Proof.
  intros [k v par role sub] H. cbn [occurrence_kind] in H. subst k.
  cbn [view_expr occurrence_view].
  refine (match v as v0 in View k0
          return (match k0 return Prop with
                  | ExpressionKind => exists ex, (match v0 with ExpressionView e => Some e | _ => None end) = Some ex
                  | _ => True end)
          with
          | ExpressionView e => ex_intro _ e eq_refl
          | FileView _ => I | PackageClauseView _ => I | TopLevelView _ => I | DeclarationView _ => I
          | SpecView _ => I | BindingNameView _ => I | TypeNameView _ => I | StatementView _ => I | BlockView _ => I
          end).
Qed.

Definition view_typename (o : Occurrence) : option Syntax.TypeExpr :=
  match occurrence_view o with TypeNameView ts => Some ts | _ => None end.
Lemma view_typename_kind : forall o ts, view_typename o = Some ts -> occurrence_kind o = TypeNameKind.
Proof.
  intros [k v par role sub] ts H. cbn [view_typename occurrence_view occurrence_kind] in *.
  destruct v; try discriminate H. reflexivity.
Qed.
Lemma kind_view_typename : forall o, occurrence_kind o = TypeNameKind -> exists ts, view_typename o = Some ts.
Proof.
  intros [k v par role sub] H. cbn [occurrence_kind] in H. subst k.
  cbn [view_typename occurrence_view].
  refine (match v as v0 in View k0
          return (match k0 return Prop with
                  | TypeNameKind => exists tx, (match v0 with TypeNameView ts => Some ts | _ => None end) = Some tx
                  | _ => True end)
          with
          | TypeNameView ts => ex_intro _ ts eq_refl
          | FileView _ => I | PackageClauseView _ => I | TopLevelView _ => I | DeclarationView _ => I
          | SpecView _ => I | BindingNameView _ => I | ExpressionView _ => I | StatementView _ => I | BlockView _ => I
          end).
Qed.

Definition view_binding_name (o : Occurrence) : option Syntax.BindingName :=
  match occurrence_view o with BindingNameView b => Some b | _ => None end.
Lemma view_binding_name_kind : forall o b, view_binding_name o = Some b -> occurrence_kind o = BindingNameKind.
Proof.
  intros [k v par role sub] b H. cbn [view_binding_name occurrence_view occurrence_kind] in *.
  destruct v; try discriminate H. reflexivity.
Qed.

Definition view_toplevel (o : Occurrence) : option Syntax.TopLevelDecl :=
  match occurrence_view o with TopLevelView d => Some d | _ => None end.
Lemma view_toplevel_kind : forall o d, view_toplevel o = Some d -> occurrence_kind o = TopLevelKind.
Proof.
  intros [k v par role sub] d H. cbn [view_toplevel occurrence_view occurrence_kind] in *.
  destruct v; try discriminate H. reflexivity.
Qed.

Definition view_stmt (o : Occurrence) : option Syntax.Stmt :=
  match occurrence_view o with StatementView s => Some s | _ => None end.
Lemma view_stmt_kind : forall o s, view_stmt o = Some s -> occurrence_kind o = StatementKind.
Proof.
  intros [k v par role sub] s H. cbn [view_stmt occurrence_view occurrence_kind] in *.
  destruct v; try discriminate H. reflexivity.
Qed.

(*  generic point lookup over a sibling run  *)

Fixpoint occurrence_seq' {X}
  (ox : nat -> positive -> X -> positive -> option Occurrence)
  (endx : positive -> X -> positive)
  (i0 : nat) (me0 : positive) (xs : list X) (target : positive) : option Occurrence :=
  match xs with
  | [] => None
  | x :: rest =>
      if Pos.leb target (endx me0 x)
      then ox i0 me0 x target
      else occurrence_seq' ox endx (S i0) (Pos.succ (endx me0 x)) rest target
  end.

Lemma occurrence_seq'_below {X}
  (ox : nat -> positive -> X -> positive -> option Occurrence) (endx : positive -> X -> positive)
  (xs : list X) :
  (forall me x, (me <= endx me x)%positive) ->
  (forall x, In x xs -> forall i me target, (target < me)%positive -> ox i me x target = None) ->
  forall i me target, (target < me)%positive -> occurrence_seq' ox endx i me xs target = None.
Proof.
  intros Hge. induction xs as [|x rest IH]; intros Hbelow i me target Hlt; cbn [occurrence_seq']; [reflexivity|].
  destruct (Pos.leb_spec target (endx me x)).
  - apply (Hbelow x (or_introl eq_refl)). exact Hlt.
  - apply IH; [intros y Hy; apply Hbelow; right; exact Hy|]. pose proof (Hge me x). lia.
Qed.

Lemma occurrence_seq'_above {X}
  (ox : nat -> positive -> X -> positive -> option Occurrence) (endx : positive -> X -> positive)
  (xs : list X) :
  (forall me x, (me <= endx me x)%positive) ->
  (forall x, In x xs -> forall i me target, (endx me x < target)%positive -> ox i me x target = None) ->
  forall i me target, (next_seq endx me xs <= target)%positive -> occurrence_seq' ox endx i me xs target = None.
Proof.
  intros Hge. induction xs as [|x rest IH]; intros Habove i me target Hge2; cbn [occurrence_seq' next_seq] in *; [reflexivity|].
  destruct (Pos.leb_spec target (endx me x)).
  - exfalso. pose proof (next_seq_ge endx Hge rest (Pos.succ (endx me x))). lia.
  - apply IH; [intros y Hy; apply Habove; right; exact Hy|]. exact Hge2.
Qed.

Lemma build_seq_get {X}
  (bx : positive -> nat -> positive -> X -> Table.table Meta -> Table.table Meta * positive)
  (endx : positive -> X -> positive)
  (ox : nat -> positive -> X -> positive -> option Occurrence) (parent : positive) (xs : list X) :
  (forall me x, (me <= endx me x)%positive) ->
  (forall x, In x xs -> forall i me t, snd (bx parent i me x t) = endx me x) ->
  (forall x, In x xs -> forall i me t target, Table.get target (fst (bx parent i me x t)) =
     match ox i me x target with Some o => Some (occurrence_meta o) | None => Table.get target t end) ->
  (forall x, In x xs -> forall i me target, (endx me x < target)%positive -> ox i me x target = None) ->
  (forall x, In x xs -> forall i me target, (target < me)%positive -> ox i me x target = None) ->
  forall i me t target,
    Table.get target (fst (build_seq bx parent i me xs t)) =
      match occurrence_seq' ox endx i me xs target with Some o => Some (occurrence_meta o) | None => Table.get target t end.
Proof.
  intros Hge. induction xs as [|x rest IH]; intros Hend Hget Habove Hbelow i me t target; cbn [build_seq occurrence_seq'].
  - reflexivity.
  - pose proof (Hend x (or_introl eq_refl) i me t) as He.
    destruct (bx parent i me x t) as [t1 se] eqn:E1. cbn [snd] in He. subst se. cbn [fst].
    pose proof (Hget x (or_introl eq_refl) i me t target) as HG. rewrite E1 in HG. cbn [fst] in HG.
    rewrite (IH (fun y Hy => Hend y (or_intror Hy)) (fun y Hy => Hget y (or_intror Hy))
                (fun y Hy => Habove y (or_intror Hy)) (fun y Hy => Hbelow y (or_intror Hy))
                (S i) (Pos.succ (endx me x)) t1 target).
    destruct (Pos.leb_spec target (endx me x)) as [Hle|Hgt].
    + rewrite (occurrence_seq'_below ox endx rest Hge (fun y Hy => Hbelow y (or_intror Hy))
                (S i) (Pos.succ (endx me x)) target ltac:(lia)). exact HG.
    + rewrite (Habove x (or_introl eq_refl) i me target ltac:(lia)) in HG.
      destruct (occurrence_seq' ox endx (S i) (Pos.succ (endx me x)) rest target); [reflexivity|exact HG].
Qed.
(*  the point-lookup single-node spec: one occurrence at a given id  *)

Definition occurrence_type_expr' (parent : positive) (role : Role) (me : positive) (ty : Syntax.TypeExpr) (target : positive)
  : option Occurrence :=
  if Pos.eqb target me then Some (MakeOccurrence TypeNameKind (TypeNameView ty) (Some parent) role me) else None.

Definition occurrence_binding_name' (parent : positive) (role : Role) (me : positive) (b : Syntax.BindingName) (target : positive)
  : option Occurrence :=
  if Pos.eqb target me then Some (MakeOccurrence BindingNameKind (BindingNameView b) (Some parent) role me) else None.

Fixpoint occurrence_expr' (parent : positive) (role : Role) (me : positive) (e : Syntax.Expr) (target : positive)
  : option Occurrence :=
  match e with
  | Syntax.Name _ | Syntax.LiteralExpr _ =>
      if Pos.eqb target me then Some (MakeOccurrence ExpressionKind (ExpressionView e) (Some parent) role me) else None
  | Syntax.Unary _ e' =>
      if Pos.eqb target me
      then Some (MakeOccurrence ExpressionKind (ExpressionView e) (Some parent) role (end_expr me e))
      else occurrence_expr' me UnaryOperand (Pos.succ me) e' target
  | Syntax.Application head args =>
      if Pos.eqb target me
      then Some (MakeOccurrence ExpressionKind (ExpressionView e) (Some parent) role (end_expr me e))
      else if Pos.leb target (end_expr (Pos.succ me) head)
      then occurrence_expr' me ApplicationHead (Pos.succ me) head target
      else (fix oa (i : nat) (mi : positive) (xs : list Syntax.Expr) : option Occurrence :=
              match xs with
              | []        => None
              | x :: rest =>
                  if Pos.leb target (end_expr mi x)
                  then occurrence_expr' me (ApplicationArgument i) mi x target
                  else oa (S i) (Pos.succ (end_expr mi x)) rest
              end) 0%nat (Pos.succ (end_expr (Pos.succ me) head)) args
  end.

Lemma occ_args_inner : forall me target args i start,
  (fix oa (i0 : nat) (mi : positive) (xs : list Syntax.Expr) : option Occurrence :=
     match xs with
     | [] => None
     | x :: rest =>
         if Pos.leb target (end_expr mi x)
         then occurrence_expr' me (ApplicationArgument i0) mi x target
         else oa (S i0) (Pos.succ (end_expr mi x)) rest
     end) i start args
  = occurrence_seq' (fun j m x tgt => occurrence_expr' me (ApplicationArgument j) m x tgt) end_expr i start args target.
Proof.
  intros me target args. induction args as [|x rest IH]; intros i start; [reflexivity|].
  simpl. destruct (Pos.leb target (end_expr start x)); [reflexivity | apply IH].
Qed.

Lemma occurrence_expr'_app : forall parent role me head args target,
  occurrence_expr' parent role me (Syntax.Application head args) target
  = if Pos.eqb target me
    then Some (MakeOccurrence ExpressionKind (ExpressionView (Syntax.Application head args)) (Some parent) role
                (end_expr me (Syntax.Application head args)))
    else if Pos.leb target (end_expr (Pos.succ me) head)
    then occurrence_expr' me ApplicationHead (Pos.succ me) head target
    else occurrence_seq' (fun i m x t => occurrence_expr' me (ApplicationArgument i) m x t) end_expr
           0 (Pos.succ (end_expr (Pos.succ me) head)) args target.
Proof.
  intros parent role me head args target.
  change (occurrence_expr' parent role me (Syntax.Application head args) target) with
    (if Pos.eqb target me
     then Some (MakeOccurrence ExpressionKind (ExpressionView (Syntax.Application head args)) (Some parent) role
                 (end_expr me (Syntax.Application head args)))
     else if Pos.leb target (end_expr (Pos.succ me) head)
     then occurrence_expr' me ApplicationHead (Pos.succ me) head target
     else (fix oa (i0 : nat) (mi : positive) (xs : list Syntax.Expr) : option Occurrence :=
             match xs with
             | [] => None
             | x :: rest =>
                 if Pos.leb target (end_expr mi x)
                 then occurrence_expr' me (ApplicationArgument i0) mi x target
                 else oa (S i0) (Pos.succ (end_expr mi x)) rest
             end) 0%nat (Pos.succ (end_expr (Pos.succ me) head)) args).
  rewrite occ_args_inner. reflexivity.
Qed.

Definition occurrence_opt_type' (parent : positive) (me : positive) (oty : option Syntax.TypeExpr) (target : positive)
  : option Occurrence :=
  match oty with Some ty => occurrence_type_expr' parent SpecTypeUse me ty target | None => None end.

Definition occurrence_const_spec' (parent : positive) (didx : nat) (me : positive) (s : Syntax.ConstSpec) (target : positive)
  : option Occurrence :=
  if Pos.eqb target me
  then Some (MakeOccurrence SpecKind (SpecView (ASConst s)) (Some parent) (DeclSpec didx) (end_const_spec me s))
  else
    let m1 := next_seq end_binding_name (Pos.succ me) (Collections.ne_to_list (Syntax.const_names s)) in
    match Syntax.const_init s with
    | Syntax.ExplicitConstInit oty vals =>
        match occurrence_seq' (fun i m x t => occurrence_expr' me (SpecValue i) m x t) end_expr
                0 (next_opt_type m1 oty) (Collections.ne_to_list vals) target with
        | Some o => Some o
        | None =>
          match occurrence_opt_type' me m1 oty target with
          | Some o => Some o
          | None => occurrence_seq' (fun i m x t => occurrence_binding_name' me (SpecName i) m x t) end_binding_name
                      0 (Pos.succ me) (Collections.ne_to_list (Syntax.const_names s)) target
          end
        end
    | Syntax.InheritedConstInit =>
        occurrence_seq' (fun i m x t => occurrence_binding_name' me (SpecName i) m x t) end_binding_name
          0 (Pos.succ me) (Collections.ne_to_list (Syntax.const_names s)) target
    end.

Definition occurrence_var_spec' (parent : positive) (didx : nat) (me : positive) (s : Syntax.VarSpec) (target : positive)
  : option Occurrence :=
  if Pos.eqb target me
  then Some (MakeOccurrence SpecKind (SpecView (ASVar s)) (Some parent) (DeclSpec didx) (end_var_spec me s))
  else
    let m1 := next_seq end_binding_name (Pos.succ me) (Collections.ne_to_list (Syntax.var_names s)) in
    match Syntax.var_init s with
    | Syntax.VarTypeOnly ty =>
        match occurrence_opt_type' me m1 (Some ty) target with
        | Some o => Some o
        | None => occurrence_seq' (fun i m x t => occurrence_binding_name' me (SpecName i) m x t) end_binding_name
                    0 (Pos.succ me) (Collections.ne_to_list (Syntax.var_names s)) target
        end
    | Syntax.VarValues oty vals =>
        match occurrence_seq' (fun i m x t => occurrence_expr' me (SpecValue i) m x t) end_expr
                0 (next_opt_type m1 oty) (Collections.ne_to_list vals) target with
        | Some o => Some o
        | None =>
          match occurrence_opt_type' me m1 oty target with
          | Some o => Some o
          | None => occurrence_seq' (fun i m x t => occurrence_binding_name' me (SpecName i) m x t) end_binding_name
                      0 (Pos.succ me) (Collections.ne_to_list (Syntax.var_names s)) target
          end
        end
    end.

Definition occurrence_type_spec' (parent : positive) (didx : nat) (me : positive) (s : Syntax.TypeSpec) (target : positive)
  : option Occurrence :=
  match s with
  | Syntax.AliasSpec nm ty | Syntax.DefSpec nm ty =>
      if Pos.eqb target me
      then Some (MakeOccurrence SpecKind (SpecView (ASType s)) (Some parent) (DeclSpec didx) (end_type_spec me s))
      else match occurrence_type_expr' me SpecTypeUse (Pos.succ (Pos.succ me)) ty target with
           | Some o => Some o
           | None => occurrence_binding_name' me (SpecName 0) (Pos.succ me) nm target
           end
  end.

Definition occurrence_declaration' (parent : positive) (role : Role) (me : positive) (d : Syntax.Declaration) (target : positive)
  : option Occurrence :=
  if Pos.eqb target me
  then Some (MakeOccurrence DeclarationKind (DeclarationView d) (Some parent) role (end_declaration me d))
  else match d with
       | Syntax.ConstDecl specs =>
           occurrence_seq' (fun i m x t => occurrence_const_spec' me i m x t) end_const_spec 0 (Pos.succ me) specs target
       | Syntax.VarDecl specs =>
           occurrence_seq' (fun i m x t => occurrence_var_spec' me i m x t) end_var_spec 0 (Pos.succ me) specs target
       | Syntax.TypeDecl specs =>
           occurrence_seq' (fun i m x t => occurrence_type_spec' me i m x t) end_type_spec 0 (Pos.succ me) specs target
       end.

Definition occurrence_stmt' (parent : positive) (sidx : nat) (me : positive) (s : Syntax.Stmt) (target : positive)
  : option Occurrence :=
  if Pos.eqb target me
  then Some (MakeOccurrence StatementKind (StatementView s) (Some parent) (BlockStatement sidx) (end_stmt me s))
  else match s with
       | Syntax.ExprStmt e => occurrence_expr' me ExprStatementExpr (Pos.succ me) e target
       | Syntax.DeclarationStmt d => occurrence_declaration' me DeclStatementDecl (Pos.succ me) d target
       | Syntax.ShortVarDecl names vals =>
           match occurrence_seq' (fun i m x t => occurrence_expr' me (ShortRhs i) m x t) end_expr 0
                   (next_seq end_binding_name (Pos.succ me) (Collections.ne_to_list names)) (Collections.ne_to_list vals) target with
           | Some o => Some o
           | None => occurrence_seq' (fun i m x t => occurrence_binding_name' me (ShortLhs i) m x t) end_binding_name
                       0 (Pos.succ me) (Collections.ne_to_list names) target
           end
       end.

Definition occurrence_block' (parent : positive) (role : Role) (me : positive) (b : Syntax.Block) (target : positive)
  : option Occurrence :=
  if Pos.eqb target me
  then Some (MakeOccurrence BlockKind (BlockView b) (Some parent) role (end_block me b))
  else match b with
       | Syntax.MakeBlock stmts =>
           occurrence_seq' (fun i m x t => occurrence_stmt' me i m x t) end_stmt 0 (Pos.succ me) stmts target
       end.

Definition occurrence_decl' (parent : positive) (didx : nat) (me : positive) (d : Syntax.TopLevelDecl) (target : positive)
  : option Occurrence :=
  if Pos.eqb target me
  then Some (MakeOccurrence TopLevelKind (TopLevelView d) (Some parent) (FileDeclaration didx) (end_decl me d))
  else match d with
       | Syntax.TopDeclaration dcl => occurrence_declaration' me (FileDeclaration didx) (Pos.succ me) dcl target
       | Syntax.Main body => occurrence_block' me MainBlock (Pos.succ me) body target
       end.

Definition source_occurrence_at (f : Syntax.File) (target : positive) : option Occurrence :=
  match Syntax.imports f with
  | i :: _ => match i with end
  | [] =>
      if Pos.eqb target root_id
      then Some (MakeOccurrence FileKind (FileView f) None FileRoot (count_file f))
      else if Pos.eqb target package_id
           then Some (MakeOccurrence PackageClauseKind (PackageClauseView (Syntax.package f)) (Some root_id) FilePackage package_id)
           else occurrence_seq' (fun i m x t => occurrence_decl' root_id i m x t) end_decl 0 (Pos.succ package_id) (Syntax.declarations f) target
  end.
(*  each lookup returns None strictly outside its subtree's id window  *)

Lemma pos_pred_lt_le : forall y t, (Pos.pred y < t)%positive -> (y <= t)%positive.
Proof.
  intros y t H. destruct (Pos.succ_pred_or y) as [Hy|Hy].
  - subst y. cbn in *. lia.
  - rewrite <- Hy. lia.
Qed.

Lemma next_seq_cons_gt {X} (endx : positive -> X -> positive) :
  (forall me x, (me <= endx me x)%positive) ->
  forall x rest start, (start < next_seq endx start (x :: rest))%positive.
Proof.
  intros Hge x rest start. cbn [next_seq].
  pose proof (next_seq_ge endx Hge rest (Pos.succ (endx start x))). pose proof (Hge start x). lia.
Qed.
Lemma next_seq_ne_gt {X} (endx : positive -> X -> positive) :
  (forall me x, (me <= endx me x)%positive) ->
  forall (ne : Collections.NonEmpty X) start, (start < next_seq endx start (Collections.ne_to_list ne))%positive.
Proof. intros Hge ne start. unfold Collections.ne_to_list. apply next_seq_cons_gt. exact Hge. Qed.

Lemma occurrence_type_expr'_below : forall ty parent role me target,
  (target < me)%positive -> occurrence_type_expr' parent role me ty target = None.
Proof. intros ty parent role me target H. unfold occurrence_type_expr'. destruct (Pos.eqb_spec target me); [lia|reflexivity]. Qed.
Lemma occurrence_type_expr'_above : forall ty parent role me target,
  (end_type_expr me ty < target)%positive -> occurrence_type_expr' parent role me ty target = None.
Proof. intros ty parent role me target H. unfold occurrence_type_expr', end_type_expr in *. destruct (Pos.eqb_spec target me); [lia|reflexivity]. Qed.
Lemma occurrence_binding_name'_below : forall b parent role me target,
  (target < me)%positive -> occurrence_binding_name' parent role me b target = None.
Proof. intros b parent role me target H. unfold occurrence_binding_name'. destruct (Pos.eqb_spec target me); [lia|reflexivity]. Qed.
Lemma occurrence_binding_name'_above : forall b parent role me target,
  (end_binding_name me b < target)%positive -> occurrence_binding_name' parent role me b target = None.
Proof. intros b parent role me target H. unfold occurrence_binding_name', end_binding_name in *. destruct (Pos.eqb_spec target me); [lia|reflexivity]. Qed.

Lemma occurrence_expr'_below : forall e parent role me target,
  (target < me)%positive -> occurrence_expr' parent role me e target = None.
Proof.
  induction e as [ n | l | op e' IH | head args IHhead IHargs ] using Syntax.Expr_ind'; intros parent role me target Hlt.
  - cbn [occurrence_expr']; destruct (Pos.eqb_spec target me); [lia|reflexivity].
  - cbn [occurrence_expr']; destruct (Pos.eqb_spec target me); [lia|reflexivity].
  - cbn [occurrence_expr']; destruct (Pos.eqb_spec target me); [lia|]. apply IH. lia.
  - rewrite occurrence_expr'_app. destruct (Pos.eqb_spec target me); [lia|].
    destruct (Pos.leb_spec target (end_expr (Pos.succ me) head)).
    + apply IHhead. lia.
    + exfalso. pose proof (end_expr_ge (Pos.succ me) head). lia.
Qed.

Lemma occurrence_expr'_above : forall e parent role me target,
  (end_expr me e < target)%positive -> occurrence_expr' parent role me e target = None.
Proof.
  induction e as [ n | l | op e' IH | head args IHhead IHargs ] using Syntax.Expr_ind'; intros parent role me target Hgt.
  - cbn [occurrence_expr' end_expr] in *; destruct (Pos.eqb_spec target me); [lia|reflexivity].
  - cbn [occurrence_expr' end_expr] in *; destruct (Pos.eqb_spec target me); [lia|reflexivity].
  - cbn [occurrence_expr' end_expr] in *. pose proof (end_expr_ge (Pos.succ me) e').
    destruct (Pos.eqb_spec target me); [lia|]. apply IH. exact Hgt.
  - rewrite occurrence_expr'_app.
    pose proof (end_expr_ge me (Syntax.Application head args)) as Hge_e.
    destruct (Pos.eqb_spec target me); [lia|].
    rewrite end_expr_app in Hgt. unfold next_exprs in Hgt.
    pose proof (next_seq_ge end_expr end_expr_ge args (Pos.succ (end_expr (Pos.succ me) head))) as Hn.
    apply pos_pred_lt_le in Hgt.
    destruct (Pos.leb_spec target (end_expr (Pos.succ me) head)).
    + exfalso. lia.
    + apply (occurrence_seq'_above (fun i m x t => occurrence_expr' me (ApplicationArgument i) m x t) end_expr
              args end_expr_ge).
      * intros x Hx i m tgt Hgt2. rewrite Forall_forall in IHargs. exact (IHargs x Hx me (ApplicationArgument i) m tgt Hgt2).
      * exact Hgt.
Qed.
Lemma occurrence_const_spec'_below : forall s parent didx me target,
  (target < me)%positive -> occurrence_const_spec' parent didx me s target = None.
Proof.
  intros s parent didx me target Hlt. unfold occurrence_const_spec'.
  destruct (Pos.eqb_spec target me); [lia|]. cbv zeta.
  set (m1 := next_seq end_binding_name (Pos.succ me) (Collections.ne_to_list (Syntax.const_names s))).
  assert (Hm1 : (Pos.succ me <= m1)%positive) by (apply next_seq_ge; apply end_binding_name_ge).
  assert (Hnames : occurrence_seq' (fun i m x t => occurrence_binding_name' me (SpecName i) m x t) end_binding_name
                     0 (Pos.succ me) (Collections.ne_to_list (Syntax.const_names s)) target = None).
  { apply (occurrence_seq'_below (fun i m x t => occurrence_binding_name' me (SpecName i) m x t) end_binding_name
             (Collections.ne_to_list (Syntax.const_names s)) end_binding_name_ge);
      [ intros x Hx i m tgt Hlt2; apply occurrence_binding_name'_below; exact Hlt2 | lia ]. }
  destruct (Syntax.const_init s) as [oty vals|]; [| exact Hnames].
  assert (Hvals : occurrence_seq' (fun i m x t => occurrence_expr' me (SpecValue i) m x t) end_expr
                    0 (next_opt_type m1 oty) (Collections.ne_to_list vals) target = None).
  { apply (occurrence_seq'_below (fun i m x t => occurrence_expr' me (SpecValue i) m x t) end_expr
             (Collections.ne_to_list vals) end_expr_ge);
      [ intros x Hx i m tgt Hlt2; apply occurrence_expr'_below; exact Hlt2
      | unfold next_opt_type; destruct oty; lia ]. }
  rewrite Hvals.
  assert (Hopt : occurrence_opt_type' me m1 oty target = None).
  { unfold occurrence_opt_type'. destruct oty as [ty|]; [|reflexivity]. apply occurrence_type_expr'_below. lia. }
  rewrite Hopt. exact Hnames.
Qed.

Lemma occurrence_const_spec'_above : forall s parent didx me target,
  (end_const_spec me s < target)%positive -> occurrence_const_spec' parent didx me s target = None.
Proof.
  intros s parent didx me target Hgt. pose proof (end_const_spec_ge me s) as Hge0.
  unfold occurrence_const_spec'. destruct (Pos.eqb_spec target me); [exfalso; lia|]. cbv zeta.
  set (m1 := next_seq end_binding_name (Pos.succ me) (Collections.ne_to_list (Syntax.const_names s))).
  assert (Hm1 : (Pos.succ me <= m1)%positive) by (apply next_seq_ge; apply end_binding_name_ge).
  unfold end_const_spec in Hgt. fold m1 in Hgt.
  destruct (Syntax.const_init s) as [oty vals|].
  - apply pos_pred_lt_le in Hgt.
    set (vstart := next_opt_type m1 oty) in *.
    assert (Hvs : (m1 <= vstart)%positive) by (unfold vstart, next_opt_type; destruct oty; lia).
    pose proof (next_seq_ge end_expr end_expr_ge (Collections.ne_to_list vals) vstart) as Hve.
    assert (Hvals : occurrence_seq' (fun i m x t => occurrence_expr' me (SpecValue i) m x t) end_expr
                      0 vstart (Collections.ne_to_list vals) target = None).
    { apply (occurrence_seq'_above (fun i m x t => occurrence_expr' me (SpecValue i) m x t) end_expr
               (Collections.ne_to_list vals) end_expr_ge);
        [ intros x Hx i m tgt Hgt2; apply occurrence_expr'_above; exact Hgt2 | exact Hgt ]. }
    rewrite Hvals.
    pose proof (next_seq_ne_gt end_expr end_expr_ge vals vstart) as Hvgt.
    assert (Hopt : occurrence_opt_type' me m1 oty target = None).
    { unfold occurrence_opt_type'. destruct oty as [ty|]; [|reflexivity]. apply occurrence_type_expr'_above.
      unfold end_type_expr, vstart, next_opt_type in *. lia. }
    rewrite Hopt.
    apply (occurrence_seq'_above (fun i m x t => occurrence_binding_name' me (SpecName i) m x t) end_binding_name
             (Collections.ne_to_list (Syntax.const_names s)) end_binding_name_ge);
      [ intros x Hx i m tgt Hgt2; apply occurrence_binding_name'_above; exact Hgt2 | fold m1; lia ].
  - apply pos_pred_lt_le in Hgt.
    apply (occurrence_seq'_above (fun i m x t => occurrence_binding_name' me (SpecName i) m x t) end_binding_name
             (Collections.ne_to_list (Syntax.const_names s)) end_binding_name_ge);
      [ intros x Hx i m tgt Hgt2; apply occurrence_binding_name'_above; exact Hgt2 | fold m1; exact Hgt ].
Qed.

Lemma occurrence_var_spec'_below : forall s parent didx me target,
  (target < me)%positive -> occurrence_var_spec' parent didx me s target = None.
Proof.
  intros s parent didx me target Hlt. unfold occurrence_var_spec'.
  destruct (Pos.eqb_spec target me); [lia|]. cbv zeta.
  set (m1 := next_seq end_binding_name (Pos.succ me) (Collections.ne_to_list (Syntax.var_names s))).
  assert (Hm1 : (Pos.succ me <= m1)%positive) by (apply next_seq_ge; apply end_binding_name_ge).
  assert (Hnames : occurrence_seq' (fun i m x t => occurrence_binding_name' me (SpecName i) m x t) end_binding_name
                     0 (Pos.succ me) (Collections.ne_to_list (Syntax.var_names s)) target = None).
  { apply (occurrence_seq'_below (fun i m x t => occurrence_binding_name' me (SpecName i) m x t) end_binding_name
             (Collections.ne_to_list (Syntax.var_names s)) end_binding_name_ge);
      [ intros x Hx i m tgt Hlt2; apply occurrence_binding_name'_below; exact Hlt2 | lia ]. }
  destruct (Syntax.var_init s) as [ty|oty vals].
  - assert (Hopt : occurrence_opt_type' me m1 (Some ty) target = None).
    { unfold occurrence_opt_type'. apply occurrence_type_expr'_below. lia. }
    rewrite Hopt. exact Hnames.
  - assert (Hvals : occurrence_seq' (fun i m x t => occurrence_expr' me (SpecValue i) m x t) end_expr
                      0 (next_opt_type m1 oty) (Collections.ne_to_list vals) target = None).
    { apply (occurrence_seq'_below (fun i m x t => occurrence_expr' me (SpecValue i) m x t) end_expr
               (Collections.ne_to_list vals) end_expr_ge);
        [ intros x Hx i m tgt Hlt2; apply occurrence_expr'_below; exact Hlt2
        | unfold next_opt_type; destruct oty; lia ]. }
    rewrite Hvals.
    assert (Hopt : occurrence_opt_type' me m1 oty target = None).
    { unfold occurrence_opt_type'. destruct oty as [ty|]; [|reflexivity]. apply occurrence_type_expr'_below. lia. }
    rewrite Hopt. exact Hnames.
Qed.

Lemma occurrence_var_spec'_above : forall s parent didx me target,
  (end_var_spec me s < target)%positive -> occurrence_var_spec' parent didx me s target = None.
Proof.
  intros s parent didx me target Hgt. pose proof (end_var_spec_ge me s) as Hge0.
  unfold occurrence_var_spec'. destruct (Pos.eqb_spec target me); [exfalso; lia|]. cbv zeta.
  set (m1 := next_seq end_binding_name (Pos.succ me) (Collections.ne_to_list (Syntax.var_names s))).
  assert (Hm1 : (Pos.succ me <= m1)%positive) by (apply next_seq_ge; apply end_binding_name_ge).
  unfold end_var_spec in Hgt. fold m1 in Hgt.
  destruct (Syntax.var_init s) as [ty|oty vals].
  - unfold next_opt_type in Hgt. apply pos_pred_lt_le in Hgt.
    assert (Hopt : occurrence_opt_type' me m1 (Some ty) target = None).
    { unfold occurrence_opt_type'. apply occurrence_type_expr'_above. unfold end_type_expr. lia. }
    rewrite Hopt.
    apply (occurrence_seq'_above (fun i m x t => occurrence_binding_name' me (SpecName i) m x t) end_binding_name
             (Collections.ne_to_list (Syntax.var_names s)) end_binding_name_ge);
      [ intros x Hx i m tgt Hgt2; apply occurrence_binding_name'_above; exact Hgt2 | fold m1; lia ].
  - apply pos_pred_lt_le in Hgt.
    set (vstart := next_opt_type m1 oty) in *.
    assert (Hvs : (m1 <= vstart)%positive) by (unfold vstart, next_opt_type; destruct oty; lia).
    pose proof (next_seq_ge end_expr end_expr_ge (Collections.ne_to_list vals) vstart) as Hve.
    assert (Hvals : occurrence_seq' (fun i m x t => occurrence_expr' me (SpecValue i) m x t) end_expr
                      0 vstart (Collections.ne_to_list vals) target = None).
    { apply (occurrence_seq'_above (fun i m x t => occurrence_expr' me (SpecValue i) m x t) end_expr
               (Collections.ne_to_list vals) end_expr_ge);
        [ intros x Hx i m tgt Hgt2; apply occurrence_expr'_above; exact Hgt2 | exact Hgt ]. }
    rewrite Hvals.
    pose proof (next_seq_ne_gt end_expr end_expr_ge vals vstart) as Hvgt.
    assert (Hopt : occurrence_opt_type' me m1 oty target = None).
    { unfold occurrence_opt_type'. destruct oty as [ty|]; [|reflexivity]. apply occurrence_type_expr'_above.
      unfold end_type_expr, vstart, next_opt_type in *. lia. }
    rewrite Hopt.
    apply (occurrence_seq'_above (fun i m x t => occurrence_binding_name' me (SpecName i) m x t) end_binding_name
             (Collections.ne_to_list (Syntax.var_names s)) end_binding_name_ge);
      [ intros x Hx i m tgt Hgt2; apply occurrence_binding_name'_above; exact Hgt2 | fold m1; lia ].
Qed.

Lemma occurrence_type_spec'_below : forall s parent didx me target,
  (target < me)%positive -> occurrence_type_spec' parent didx me s target = None.
Proof.
  intros s parent didx me target Hlt. unfold occurrence_type_spec'.
  destruct s as [nm ty|nm ty]; destruct (Pos.eqb_spec target me); try lia;
    (assert (Htv : occurrence_type_expr' me SpecTypeUse (Pos.succ (Pos.succ me)) ty target = None)
       by (apply occurrence_type_expr'_below; lia);
     rewrite Htv; apply occurrence_binding_name'_below; lia).
Qed.

Lemma occurrence_type_spec'_above : forall s parent didx me target,
  (end_type_spec me s < target)%positive -> occurrence_type_spec' parent didx me s target = None.
Proof.
  intros s parent didx me target Hgt. unfold occurrence_type_spec', end_type_spec in *.
  destruct s as [nm ty|nm ty]; destruct (Pos.eqb_spec target me); try lia;
    (assert (Htv : occurrence_type_expr' me SpecTypeUse (Pos.succ (Pos.succ me)) ty target = None)
       by (apply occurrence_type_expr'_above; unfold end_type_expr; lia);
     rewrite Htv; apply occurrence_binding_name'_above; unfold end_binding_name; lia).
Qed.

Lemma occurrence_declaration'_below : forall d parent role me target,
  (target < me)%positive -> occurrence_declaration' parent role me d target = None.
Proof.
  intros d parent role me target Hlt. unfold occurrence_declaration'.
  destruct (Pos.eqb_spec target me); [lia|].
  destruct d as [specs|specs|specs].
  - apply (occurrence_seq'_below (fun i m x t => occurrence_const_spec' me i m x t) end_const_spec specs end_const_spec_ge);
      [ intros x Hx i m tgt Hlt2; apply occurrence_const_spec'_below; exact Hlt2 | lia ].
  - apply (occurrence_seq'_below (fun i m x t => occurrence_var_spec' me i m x t) end_var_spec specs end_var_spec_ge);
      [ intros x Hx i m tgt Hlt2; apply occurrence_var_spec'_below; exact Hlt2 | lia ].
  - apply (occurrence_seq'_below (fun i m x t => occurrence_type_spec' me i m x t) end_type_spec specs end_type_spec_ge);
      [ intros x Hx i m tgt Hlt2; apply occurrence_type_spec'_below; exact Hlt2 | lia ].
Qed.

Lemma occurrence_declaration'_above : forall d parent role me target,
  (end_declaration me d < target)%positive -> occurrence_declaration' parent role me d target = None.
Proof.
  intros d parent role me target Hgt. pose proof (end_declaration_ge me d) as Hge0.
  unfold occurrence_declaration'. destruct (Pos.eqb_spec target me); [exfalso; lia|].
  unfold end_declaration in Hgt.
  destruct d as [specs|specs|specs]; apply pos_pred_lt_le in Hgt.
  - apply (occurrence_seq'_above (fun i m x t => occurrence_const_spec' me i m x t) end_const_spec specs end_const_spec_ge);
      [ intros x Hx i m tgt Hgt2; apply occurrence_const_spec'_above; exact Hgt2 | exact Hgt ].
  - apply (occurrence_seq'_above (fun i m x t => occurrence_var_spec' me i m x t) end_var_spec specs end_var_spec_ge);
      [ intros x Hx i m tgt Hgt2; apply occurrence_var_spec'_above; exact Hgt2 | exact Hgt ].
  - apply (occurrence_seq'_above (fun i m x t => occurrence_type_spec' me i m x t) end_type_spec specs end_type_spec_ge);
      [ intros x Hx i m tgt Hgt2; apply occurrence_type_spec'_above; exact Hgt2 | exact Hgt ].
Qed.

Lemma occurrence_stmt'_below : forall s parent sidx me target,
  (target < me)%positive -> occurrence_stmt' parent sidx me s target = None.
Proof.
  intros s parent sidx me target Hlt. unfold occurrence_stmt'.
  destruct (Pos.eqb_spec target me); [lia|].
  destruct s as [e|d|names vals].
  - apply occurrence_expr'_below. lia.
  - apply occurrence_declaration'_below. lia.
  - assert (Hm1 : (Pos.succ me <= next_seq end_binding_name (Pos.succ me) (Collections.ne_to_list names))%positive)
      by (apply next_seq_ge; apply end_binding_name_ge).
    assert (Hvals : occurrence_seq' (fun i m x t => occurrence_expr' me (ShortRhs i) m x t) end_expr 0
              (next_seq end_binding_name (Pos.succ me) (Collections.ne_to_list names)) (Collections.ne_to_list vals) target = None).
    { apply (occurrence_seq'_below (fun i m x t => occurrence_expr' me (ShortRhs i) m x t) end_expr
               (Collections.ne_to_list vals) end_expr_ge);
        [ intros x Hx i m tgt Hlt2; apply occurrence_expr'_below; exact Hlt2 | lia ]. }
    rewrite Hvals.
    apply (occurrence_seq'_below (fun i m x t => occurrence_binding_name' me (ShortLhs i) m x t) end_binding_name
             (Collections.ne_to_list names) end_binding_name_ge);
      [ intros x Hx i m tgt Hlt2; apply occurrence_binding_name'_below; exact Hlt2 | lia ].
Qed.

Lemma occurrence_stmt'_above : forall s parent sidx me target,
  (end_stmt me s < target)%positive -> occurrence_stmt' parent sidx me s target = None.
Proof.
  intros s parent sidx me target Hgt. pose proof (end_stmt_ge me s) as Hge0.
  unfold occurrence_stmt'. destruct (Pos.eqb_spec target me); [exfalso; lia|].
  destruct s as [e|d|names vals]; cbn [end_stmt] in Hgt.
  - apply occurrence_expr'_above. exact Hgt.
  - apply occurrence_declaration'_above. exact Hgt.
  - set (m1 := next_seq end_binding_name (Pos.succ me) (Collections.ne_to_list names)) in *.
    assert (Hm1 : (Pos.succ me <= m1)%positive) by (apply next_seq_ge; apply end_binding_name_ge).
    apply pos_pred_lt_le in Hgt.
    pose proof (next_seq_ge end_expr end_expr_ge (Collections.ne_to_list vals) m1) as Hve.
    assert (Hvals : occurrence_seq' (fun i m x t => occurrence_expr' me (ShortRhs i) m x t) end_expr 0
              m1 (Collections.ne_to_list vals) target = None).
    { apply (occurrence_seq'_above (fun i m x t => occurrence_expr' me (ShortRhs i) m x t) end_expr
               (Collections.ne_to_list vals) end_expr_ge);
        [ intros x Hx i m tgt Hgt2; apply occurrence_expr'_above; exact Hgt2 | exact Hgt ]. }
    rewrite Hvals.
    apply (occurrence_seq'_above (fun i m x t => occurrence_binding_name' me (ShortLhs i) m x t) end_binding_name
             (Collections.ne_to_list names) end_binding_name_ge);
      [ intros x Hx i m tgt Hgt2; apply occurrence_binding_name'_above; exact Hgt2 | fold m1; lia ].
Qed.

Lemma occurrence_block'_below : forall b parent role me target,
  (target < me)%positive -> occurrence_block' parent role me b target = None.
Proof.
  intros b parent role me target Hlt. unfold occurrence_block'.
  destruct (Pos.eqb_spec target me); [lia|]. destruct b as [stmts].
  apply (occurrence_seq'_below (fun i m x t => occurrence_stmt' me i m x t) end_stmt stmts end_stmt_ge);
    [ intros x Hx i m tgt Hlt2; apply occurrence_stmt'_below; exact Hlt2 | lia ].
Qed.
Lemma occurrence_block'_above : forall b parent role me target,
  (end_block me b < target)%positive -> occurrence_block' parent role me b target = None.
Proof.
  intros b parent role me target Hgt. pose proof (end_block_ge me b) as Hge0.
  unfold occurrence_block'. destruct (Pos.eqb_spec target me); [exfalso; lia|]. destruct b as [stmts].
  cbn [end_block] in Hgt. apply pos_pred_lt_le in Hgt.
  apply (occurrence_seq'_above (fun i m x t => occurrence_stmt' me i m x t) end_stmt stmts end_stmt_ge);
    [ intros x Hx i m tgt Hgt2; apply occurrence_stmt'_above; exact Hgt2 | exact Hgt ].
Qed.

Lemma occurrence_decl'_below : forall d parent didx me target,
  (target < me)%positive -> occurrence_decl' parent didx me d target = None.
Proof.
  intros d parent didx me target Hlt. unfold occurrence_decl'.
  destruct (Pos.eqb_spec target me); [lia|]. destruct d as [dcl|body].
  - apply occurrence_declaration'_below. lia.
  - apply occurrence_block'_below. lia.
Qed.
Lemma occurrence_decl'_above : forall d parent didx me target,
  (end_decl me d < target)%positive -> occurrence_decl' parent didx me d target = None.
Proof.
  intros d parent didx me target Hgt. pose proof (end_decl_ge me d) as Hge0.
  unfold occurrence_decl'. destruct (Pos.eqb_spec target me); [exfalso; lia|]. destruct d as [dcl|body]; cbn [end_decl] in Hgt.
  - apply occurrence_declaration'_above. exact Hgt.
  - apply occurrence_block'_above. exact Hgt.
Qed.
(*  the table read equals the source spec at every id  *)

Lemma build_type_expr_get : forall ty parent role me t target,
  Table.get target (fst (build_type_expr parent role me ty t)) =
    match occurrence_type_expr' parent role me ty target with Some o => Some (occurrence_meta o) | None => Table.get target t end.
Proof.
  intros ty parent role me t target. unfold build_type_expr, occurrence_type_expr'. cbn [fst].
  destruct (Pos.eqb_spec target me).
  - subst. rewrite Table.get_set_same. reflexivity.
  - rewrite Table.get_set_other by congruence. reflexivity.
Qed.
Lemma build_binding_name_get : forall b parent role me t target,
  Table.get target (fst (build_binding_name parent role me b t)) =
    match occurrence_binding_name' parent role me b target with Some o => Some (occurrence_meta o) | None => Table.get target t end.
Proof.
  intros b parent role me t target. unfold build_binding_name, occurrence_binding_name'. cbn [fst].
  destruct (Pos.eqb_spec target me).
  - subst. rewrite Table.get_set_same. reflexivity.
  - rewrite Table.get_set_other by congruence. reflexivity.
Qed.

Lemma build_expr_get : forall e parent role me t target,
  Table.get target (fst (build_expr parent role me e t)) =
    match occurrence_expr' parent role me e target with Some o => Some (occurrence_meta o) | None => Table.get target t end.
Proof.
  induction e as [ n | l | op e' IH | head args IHhead IHargs ] using Syntax.Expr_ind'; intros parent role me t target.
  - cbn [build_expr occurrence_expr' fst]. destruct (Pos.eqb_spec target me).
    + subst. rewrite Table.get_set_same. reflexivity.
    + rewrite Table.get_set_other by congruence. reflexivity.
  - cbn [build_expr occurrence_expr' fst]. destruct (Pos.eqb_spec target me).
    + subst. rewrite Table.get_set_same. reflexivity.
    + rewrite Table.get_set_other by congruence. reflexivity.
  - cbn [build_expr occurrence_expr' fst].
    pose proof (build_expr_end e' me UnaryOperand (Pos.succ me) t) as He1.
    destruct (build_expr me UnaryOperand (Pos.succ me) e' t) as [t1 e1] eqn:E1. cbn [snd] in He1. subst e1. cbn [fst].
    destruct (Pos.eqb_spec target me).
    + subst. rewrite Table.get_set_same. reflexivity.
    + rewrite Table.get_set_other by congruence.
      pose proof (IH me UnaryOperand (Pos.succ me) t target) as HI. rewrite E1 in HI. cbn [fst] in HI. exact HI.
  - rewrite build_expr_app, occurrence_expr'_app. rewrite Forall_forall in IHargs.
    pose proof (build_expr_end head me ApplicationHead (Pos.succ me) t) as Heh.
    destruct (build_expr me ApplicationHead (Pos.succ me) head t) as [th eh] eqn:Eh. cbn [snd] in Heh. subst eh.
    pose proof (build_seq_get (fun _ i m x tt => build_expr me (ApplicationArgument i) m x tt) end_expr
                  (fun i m x tgt => occurrence_expr' me (ApplicationArgument i) m x tgt) me
                  args end_expr_ge
                  (fun x _ i m tt => build_expr_end x me (ApplicationArgument i) m tt)
                  (fun x Hx i m tt tgt => IHargs x Hx me (ApplicationArgument i) m tt tgt)
                  (fun x _ i m tgt H => occurrence_expr'_above x me (ApplicationArgument i) m tgt H)
                  (fun x _ i m tgt H => occurrence_expr'_below x me (ApplicationArgument i) m tgt H)
                  0 (Pos.succ (end_expr (Pos.succ me) head)) th target) as Hseq.
    pose proof (build_seq_end (fun _ i m x tt => build_expr me (ApplicationArgument i) m x tt) end_expr me args
                  (fun x _ i m tt => build_expr_end x me (ApplicationArgument i) m tt) 0
                  (Pos.succ (end_expr (Pos.succ me) head)) th) as Hnx.
    revert Hseq Hnx.
    destruct (build_seq (fun _ i m x tt => build_expr me (ApplicationArgument i) m x tt) me 0
                (Pos.succ (end_expr (Pos.succ me) head)) args th) as [ta nx].
    intros Hseq Hnx. cbn [fst snd] in Hseq, Hnx. cbn [fst].
    destruct (Pos.eqb_spec target me).
    + subst target. rewrite Table.get_set_same. rewrite end_expr_app. unfold next_exprs. rewrite Hnx. reflexivity.
    + rewrite Table.get_set_other by congruence.
      destruct (Pos.leb_spec target (end_expr (Pos.succ me) head)) as [Hle|Hgt].
      * assert (Eseq : occurrence_seq' (fun i m x t0 => occurrence_expr' me (ApplicationArgument i) m x t0) end_expr 0
                         (Pos.succ (end_expr (Pos.succ me) head)) args target = None).
        { apply (occurrence_seq'_below (fun i m x t0 => occurrence_expr' me (ApplicationArgument i) m x t0) end_expr args end_expr_ge);
            [ intros x Hx i m tgt Hlt; apply occurrence_expr'_below; exact Hlt | lia ]. }
        rewrite Eseq in Hseq. rewrite Hseq.
        pose proof (IHhead me ApplicationHead (Pos.succ me) t target) as HIh. rewrite Eh in HIh. cbn [fst] in HIh. exact HIh.
      * rewrite Hseq.
        assert (Ehead : occurrence_expr' me ApplicationHead (Pos.succ me) head target = None) by (apply occurrence_expr'_above; lia).
        pose proof (IHhead me ApplicationHead (Pos.succ me) t target) as HIh. rewrite Eh in HIh. cbn [fst] in HIh. rewrite Ehead in HIh.
        destruct (occurrence_seq' (fun i m x t0 => occurrence_expr' me (ApplicationArgument i) m x t0) end_expr 0
                    (Pos.succ (end_expr (Pos.succ me) head)) args target); [reflexivity|exact HIh].
Qed.

Lemma build_opt_type_get : forall oty parent me t target,
  Table.get target (fst (build_opt_type parent me oty t)) =
    match occurrence_opt_type' parent me oty target with Some o => Some (occurrence_meta o) | None => Table.get target t end.
Proof.
  intros oty parent me t target. unfold build_opt_type, occurrence_opt_type'. destruct oty as [ty|].
  - pose proof (build_type_expr_get ty parent SpecTypeUse me t target) as H.
    destruct (build_type_expr parent SpecTypeUse me ty t) as [t1 e1] eqn:E1. cbn [fst] in H |- *. exact H.
  - cbn [fst]. reflexivity.
Qed.

(* the shared reasoning for a names run and a values run, over a generic sibling role function *)
Lemma build_binding_seq_get : forall role_of parent0 xs me t target,
  Table.get target (fst (build_seq (fun p i m x tt => build_binding_name p (role_of i) m x tt) parent0 0 me xs t)) =
    match occurrence_seq' (fun i m x tgt => occurrence_binding_name' parent0 (role_of i) m x tgt) end_binding_name 0 me xs target with
    | Some o => Some (occurrence_meta o) | None => Table.get target t end.
Proof.
  intros role_of parent0 xs me t target.
  apply (build_seq_get (fun p i m x tt => build_binding_name p (role_of i) m x tt) end_binding_name
           (fun i m x tgt => occurrence_binding_name' parent0 (role_of i) m x tgt) parent0
           xs end_binding_name_ge);
    [ intros x _ i m tt; reflexivity
    | intros x _ i m tt tgt; apply build_binding_name_get
    | intros x _ i m tgt H; apply occurrence_binding_name'_above; exact H
    | intros x _ i m tgt H; apply occurrence_binding_name'_below; exact H ].
Qed.
Lemma build_expr_seq_get : forall role_of parent0 xs me t target,
  Table.get target (fst (build_seq (fun p i m x tt => build_expr p (role_of i) m x tt) parent0 0 me xs t)) =
    match occurrence_seq' (fun i m x tgt => occurrence_expr' parent0 (role_of i) m x tgt) end_expr 0 me xs target with
    | Some o => Some (occurrence_meta o) | None => Table.get target t end.
Proof.
  intros role_of parent0 xs me t target.
  apply (build_seq_get (fun p i m x tt => build_expr p (role_of i) m x tt) end_expr
           (fun i m x tgt => occurrence_expr' parent0 (role_of i) m x tgt) parent0
           xs end_expr_ge);
    [ intros x _ i m tt; apply build_expr_end
    | intros x _ i m tt tgt; apply build_expr_get
    | intros x _ i m tgt H; apply occurrence_expr'_above; exact H
    | intros x _ i m tgt H; apply occurrence_expr'_below; exact H ].
Qed.

Lemma build_names_get : forall parent me ns t target,
  Table.get target (fst (build_names parent me ns t)) =
    match occurrence_seq' (fun i m x tgt => occurrence_binding_name' parent (SpecName i) m x tgt) end_binding_name 0 me (Collections.ne_to_list ns) target with
    | Some o => Some (occurrence_meta o) | None => Table.get target t end.
Proof. intros parent me ns t target. unfold build_names. apply build_binding_seq_get. Qed.
Lemma build_values_get : forall parent me vs t target,
  Table.get target (fst (build_values parent me vs t)) =
    match occurrence_seq' (fun i m x tgt => occurrence_expr' parent (SpecValue i) m x tgt) end_expr 0 me (Collections.ne_to_list vs) target with
    | Some o => Some (occurrence_meta o) | None => Table.get target t end.
Proof. intros parent me vs t target. unfold build_values. apply build_expr_seq_get. Qed.

Lemma build_const_spec_get : forall s parent didx me t target,
  Table.get target (fst (build_const_spec parent didx me s t)) =
    match occurrence_const_spec' parent didx me s target with Some o => Some (occurrence_meta o) | None => Table.get target t end.
Proof.
  intros s parent didx me t target.
  unfold build_const_spec.
  pose proof (build_names_next (Syntax.const_names s) me (Pos.succ me) t) as Hn.
  pose proof (build_names_get me (Pos.succ me) (Syntax.const_names s) t target) as HgN.
  revert Hn HgN. destruct (build_names me (Pos.succ me) (Syntax.const_names s) t) as [tn m1]. intros Hn HgN.
  cbn [fst snd] in Hn, HgN.
  unfold occurrence_const_spec'. cbv zeta. rewrite <- Hn.
  destruct (Syntax.const_init s) as [oty vals|] eqn:Ecinit.
  - pose proof (build_opt_type_get oty me m1 tn target) as HgO.
    pose proof (build_opt_type_next oty me m1 tn) as Hm2.
    revert HgO Hm2. destruct (build_opt_type me m1 oty tn) as [t1 m2]. intros HgO Hm2.
    cbn [fst snd] in HgO, Hm2.
    pose proof (build_values_get me m2 vals t1 target) as HgV.
    pose proof (build_values_next vals me m2 t1) as Hvn.
    revert HgV Hvn. destruct (build_values me m2 vals t1) as [tv nx]. intros HgV Hvn.
    cbn [fst snd] in HgV, Hvn.
    rewrite Hm2 in HgV.
    assert (Hpe : Pos.pred nx = end_const_spec me s).
    { unfold end_const_spec. rewrite Ecinit. cbn iota. rewrite <- Hn, <- Hm2, Hvn. reflexivity. }
    cbn [fst]. destruct (Pos.eqb_spec target me).
    + subst target. rewrite Table.get_set_same. rewrite Hpe. reflexivity.
    + rewrite Table.get_set_other by congruence. rewrite HgV.
      match goal with |- match ?X with _ => _ end = _ => destruct X as [o|] end; [reflexivity|].
      rewrite HgO.
      match goal with |- match ?X with _ => _ end = _ => destruct X as [o|] end; [reflexivity|].
      exact HgN.
  - assert (Hpe : Pos.pred m1 = end_const_spec me s).
    { unfold end_const_spec. rewrite Ecinit. cbn iota. rewrite <- Hn. reflexivity. }
    cbn [fst]. destruct (Pos.eqb_spec target me).
    + subst target. rewrite Table.get_set_same. rewrite Hpe. reflexivity.
    + rewrite Table.get_set_other by congruence. exact HgN.
Qed.

Lemma build_var_spec_get : forall s parent didx me t target,
  Table.get target (fst (build_var_spec parent didx me s t)) =
    match occurrence_var_spec' parent didx me s target with Some o => Some (occurrence_meta o) | None => Table.get target t end.
Proof.
  intros s parent didx me t target.
  unfold build_var_spec.
  pose proof (build_names_next (Syntax.var_names s) me (Pos.succ me) t) as Hn.
  pose proof (build_names_get me (Pos.succ me) (Syntax.var_names s) t target) as HgN.
  revert Hn HgN. destruct (build_names me (Pos.succ me) (Syntax.var_names s) t) as [tn m1]. intros Hn HgN.
  cbn [fst snd] in Hn, HgN.
  unfold occurrence_var_spec'. cbv zeta. rewrite <- Hn.
  destruct (Syntax.var_init s) as [ty|oty vals] eqn:Evinit.
  - pose proof (build_opt_type_get (Some ty) me m1 tn target) as HgO.
    pose proof (build_opt_type_next (Some ty) me m1 tn) as Hm2.
    revert HgO Hm2. destruct (build_opt_type me m1 (Some ty) tn) as [t1 m2]. intros HgO Hm2.
    cbn [fst snd] in HgO, Hm2.
    assert (Hpe : Pos.pred m2 = end_var_spec me s).
    { unfold end_var_spec. rewrite Evinit. cbn iota. rewrite <- Hn, Hm2. reflexivity. }
    cbn [fst]. destruct (Pos.eqb_spec target me).
    + subst target. rewrite Table.get_set_same. rewrite Hpe. reflexivity.
    + rewrite Table.get_set_other by congruence. rewrite HgO.
      match goal with |- match ?X with _ => _ end = _ => destruct X as [o|] end; [reflexivity|].
      exact HgN.
  - pose proof (build_opt_type_get oty me m1 tn target) as HgO.
    pose proof (build_opt_type_next oty me m1 tn) as Hm2.
    revert HgO Hm2. destruct (build_opt_type me m1 oty tn) as [t1 m2]. intros HgO Hm2.
    cbn [fst snd] in HgO, Hm2.
    pose proof (build_values_get me m2 vals t1 target) as HgV.
    pose proof (build_values_next vals me m2 t1) as Hvn.
    revert HgV Hvn. destruct (build_values me m2 vals t1) as [tv nx]. intros HgV Hvn.
    cbn [fst snd] in HgV, Hvn.
    rewrite Hm2 in HgV.
    assert (Hpe : Pos.pred nx = end_var_spec me s).
    { unfold end_var_spec. rewrite Evinit. cbn iota. rewrite <- Hn, <- Hm2, Hvn. reflexivity. }
    cbn [fst]. destruct (Pos.eqb_spec target me).
    + subst target. rewrite Table.get_set_same. rewrite Hpe. reflexivity.
    + rewrite Table.get_set_other by congruence. rewrite HgV.
      match goal with |- match ?X with _ => _ end = _ => destruct X as [o|] end; [reflexivity|].
      rewrite HgO.
      match goal with |- match ?X with _ => _ end = _ => destruct X as [o|] end; [reflexivity|].
      exact HgN.
Qed.

Lemma build_type_spec_get : forall s parent didx me t target,
  Table.get target (fst (build_type_spec parent didx me s t)) =
    match occurrence_type_spec' parent didx me s target with Some o => Some (occurrence_meta o) | None => Table.get target t end.
Proof.
  intros s parent didx me t target.
  destruct s as [nm ty|nm ty];
    (unfold build_type_spec, build_binding_name, build_type_expr, occurrence_type_spec',
            occurrence_type_expr', occurrence_binding_name', end_type_spec;
     cbn [fst snd];
     destruct (Pos.eqb_spec target me) as [->|Hnme];
       [ rewrite Table.get_set_same; reflexivity
       | rewrite Table.get_set_other by congruence;
         destruct (Pos.eqb_spec target (Pos.succ (Pos.succ me))) as [->|Hne2];
           [ rewrite Table.get_set_same; reflexivity
           | rewrite Table.get_set_other by congruence;
             destruct (Pos.eqb_spec target (Pos.succ me)) as [->|Hne1];
               [ rewrite Table.get_set_same; reflexivity
               | rewrite Table.get_set_other by congruence; reflexivity ] ] ]).
Qed.

Lemma build_declaration_get : forall d parent role me t target,
  Table.get target (fst (build_declaration parent role me d t)) =
    match occurrence_declaration' parent role me d target with Some o => Some (occurrence_meta o) | None => Table.get target t end.
Proof.
  intros d parent role me t target.
  destruct d as [specs|specs|specs]; unfold build_declaration, occurrence_declaration'; cbn [fst snd].
  - pose proof (build_seq_get build_const_spec end_const_spec (fun i m x tgt => occurrence_const_spec' me i m x tgt) me specs end_const_spec_ge
                  (fun x _ i m tt => build_const_spec_end x me i m tt)
                  (fun x _ i m tt tgt => build_const_spec_get x me i m tt tgt)
                  (fun x _ i m tgt H => occurrence_const_spec'_above x me i m tgt H)
                  (fun x _ i m tgt H => occurrence_const_spec'_below x me i m tgt H)
                  0 (Pos.succ me) t target) as Hg.
    pose proof (build_seq_end build_const_spec end_const_spec me specs (fun x _ i m tt => build_const_spec_end x me i m tt) 0 (Pos.succ me) t) as Hnx.
    revert Hg Hnx. destruct (build_seq build_const_spec me 0 (Pos.succ me) specs t) as [t1 nx]. intros Hg Hnx. cbn [fst snd] in Hg, Hnx. cbn [fst].
    destruct (Pos.eqb_spec target me).
    + subst target. rewrite Table.get_set_same. unfold end_declaration. rewrite <- Hnx. reflexivity.
    + rewrite Table.get_set_other by congruence. exact Hg.
  - pose proof (build_seq_get build_var_spec end_var_spec (fun i m x tgt => occurrence_var_spec' me i m x tgt) me specs end_var_spec_ge
                  (fun x _ i m tt => build_var_spec_end x me i m tt)
                  (fun x _ i m tt tgt => build_var_spec_get x me i m tt tgt)
                  (fun x _ i m tgt H => occurrence_var_spec'_above x me i m tgt H)
                  (fun x _ i m tgt H => occurrence_var_spec'_below x me i m tgt H)
                  0 (Pos.succ me) t target) as Hg.
    pose proof (build_seq_end build_var_spec end_var_spec me specs (fun x _ i m tt => build_var_spec_end x me i m tt) 0 (Pos.succ me) t) as Hnx.
    revert Hg Hnx. destruct (build_seq build_var_spec me 0 (Pos.succ me) specs t) as [t1 nx]. intros Hg Hnx. cbn [fst snd] in Hg, Hnx. cbn [fst].
    destruct (Pos.eqb_spec target me).
    + subst target. rewrite Table.get_set_same. unfold end_declaration. rewrite <- Hnx. reflexivity.
    + rewrite Table.get_set_other by congruence. exact Hg.
  - pose proof (build_seq_get build_type_spec end_type_spec (fun i m x tgt => occurrence_type_spec' me i m x tgt) me specs end_type_spec_ge
                  (fun x _ i m tt => build_type_spec_end x me i m tt)
                  (fun x _ i m tt tgt => build_type_spec_get x me i m tt tgt)
                  (fun x _ i m tgt H => occurrence_type_spec'_above x me i m tgt H)
                  (fun x _ i m tgt H => occurrence_type_spec'_below x me i m tgt H)
                  0 (Pos.succ me) t target) as Hg.
    pose proof (build_seq_end build_type_spec end_type_spec me specs (fun x _ i m tt => build_type_spec_end x me i m tt) 0 (Pos.succ me) t) as Hnx.
    revert Hg Hnx. destruct (build_seq build_type_spec me 0 (Pos.succ me) specs t) as [t1 nx]. intros Hg Hnx. cbn [fst snd] in Hg, Hnx. cbn [fst].
    destruct (Pos.eqb_spec target me).
    + subst target. rewrite Table.get_set_same. unfold end_declaration. rewrite <- Hnx. reflexivity.
    + rewrite Table.get_set_other by congruence. exact Hg.
Qed.

Lemma build_stmt_get : forall s parent sidx me t target,
  Table.get target (fst (build_stmt parent sidx me s t)) =
    match occurrence_stmt' parent sidx me s target with Some o => Some (occurrence_meta o) | None => Table.get target t end.
Proof.
  intros s parent sidx me t target.
  destruct s as [e|d|names vals]; unfold build_stmt, occurrence_stmt'; cbn [fst snd].
  - pose proof (build_expr_get e me ExprStatementExpr (Pos.succ me) t target) as Hg.
    pose proof (build_expr_end e me ExprStatementExpr (Pos.succ me) t) as Hnx.
    revert Hg Hnx. destruct (build_expr me ExprStatementExpr (Pos.succ me) e t) as [t1 e1]. intros Hg Hnx. cbn [fst snd] in Hg, Hnx. cbn [fst].
    destruct (Pos.eqb_spec target me).
    + subst target. rewrite Table.get_set_same. cbn [end_stmt]. rewrite <- Hnx. reflexivity.
    + rewrite Table.get_set_other by congruence. exact Hg.
  - pose proof (build_declaration_get d me DeclStatementDecl (Pos.succ me) t target) as Hg.
    pose proof (build_declaration_end d me DeclStatementDecl (Pos.succ me) t) as Hnx.
    revert Hg Hnx. destruct (build_declaration me DeclStatementDecl (Pos.succ me) d t) as [t1 e1]. intros Hg Hnx. cbn [fst snd] in Hg, Hnx. cbn [fst].
    destruct (Pos.eqb_spec target me).
    + subst target. rewrite Table.get_set_same. cbn [end_stmt]. rewrite <- Hnx. reflexivity.
    + rewrite Table.get_set_other by congruence. exact Hg.
  - pose proof (build_binding_seq_get ShortLhs me (Collections.ne_to_list names) (Pos.succ me) t target) as HgN.
    pose proof (build_seq_end (fun p i m x tt => build_binding_name p (ShortLhs i) m x tt) end_binding_name me
                  (Collections.ne_to_list names) (fun x _ i m tt => eq_refl) 0 (Pos.succ me) t) as Hn.
    revert HgN Hn.
    destruct (build_seq (fun p i m x tt => build_binding_name p (ShortLhs i) m x tt) me 0 (Pos.succ me) (Collections.ne_to_list names) t) as [tn m1].
    intros HgN Hn. cbn [fst snd] in HgN, Hn.
    pose proof (build_expr_seq_get ShortRhs me (Collections.ne_to_list vals) m1 tn target) as HgV.
    pose proof (build_seq_end (fun p i m x tt => build_expr p (ShortRhs i) m x tt) end_expr me
                  (Collections.ne_to_list vals) (fun x _ i m tt => build_expr_end x me (ShortRhs i) m tt) 0 m1 tn) as Hvn.
    revert HgV Hvn.
    destruct (build_seq (fun p i m x tt => build_expr p (ShortRhs i) m x tt) me 0 m1 (Collections.ne_to_list vals) tn) as [tv nx].
    intros HgV Hvn. cbn [fst snd] in HgV, Hvn.
    assert (Hpe : Pos.pred nx = end_stmt me (Syntax.ShortVarDecl names vals)).
    { cbn [end_stmt]. rewrite <- Hn, <- Hvn. reflexivity. }
    rewrite <- Hn. cbn [fst].
    destruct (Pos.eqb_spec target me).
    + subst target. rewrite Table.get_set_same. rewrite Hpe. reflexivity.
    + rewrite Table.get_set_other by congruence. rewrite HgV.
      match goal with |- match ?X with _ => _ end = _ => destruct X as [o|] end; [reflexivity|].
      exact HgN.
Qed.

Lemma build_block_get : forall b parent role me t target,
  Table.get target (fst (build_block parent role me b t)) =
    match occurrence_block' parent role me b target with Some o => Some (occurrence_meta o) | None => Table.get target t end.
Proof.
  intros b parent role me t target. destruct b as [stmts]; unfold build_block, occurrence_block'; cbn [fst snd].
  pose proof (build_seq_get build_stmt end_stmt (fun i m x tgt => occurrence_stmt' me i m x tgt) me stmts end_stmt_ge
                (fun x _ i m tt => build_stmt_end x me i m tt)
                (fun x _ i m tt tgt => build_stmt_get x me i m tt tgt)
                (fun x _ i m tgt H => occurrence_stmt'_above x me i m tgt H)
                (fun x _ i m tgt H => occurrence_stmt'_below x me i m tgt H)
                0 (Pos.succ me) t target) as Hg.
  pose proof (build_seq_end build_stmt end_stmt me stmts (fun x _ i m tt => build_stmt_end x me i m tt) 0 (Pos.succ me) t) as Hnx.
  revert Hg Hnx. destruct (build_seq build_stmt me 0 (Pos.succ me) stmts t) as [t1 nx]. intros Hg Hnx. cbn [fst snd] in Hg, Hnx. cbn [fst].
  destruct (Pos.eqb_spec target me).
  - subst target. rewrite Table.get_set_same. cbn [end_block]. rewrite <- Hnx. reflexivity.
  - rewrite Table.get_set_other by congruence. exact Hg.
Qed.

Lemma build_decl_get : forall d parent didx me t target,
  Table.get target (fst (build_decl parent didx me d t)) =
    match occurrence_decl' parent didx me d target with Some o => Some (occurrence_meta o) | None => Table.get target t end.
Proof.
  intros d parent didx me t target. destruct d as [dcl|body]; unfold build_decl, occurrence_decl'; cbn [fst snd].
  - pose proof (build_declaration_get dcl me (FileDeclaration didx) (Pos.succ me) t target) as Hg.
    pose proof (build_declaration_end dcl me (FileDeclaration didx) (Pos.succ me) t) as Hnx.
    revert Hg Hnx. destruct (build_declaration me (FileDeclaration didx) (Pos.succ me) dcl t) as [t1 e1]. intros Hg Hnx. cbn [fst snd] in Hg, Hnx. cbn [fst].
    destruct (Pos.eqb_spec target me).
    + subst target. rewrite Table.get_set_same. cbn [end_decl]. rewrite <- Hnx. reflexivity.
    + rewrite Table.get_set_other by congruence. exact Hg.
  - pose proof (build_block_get body me MainBlock (Pos.succ me) t target) as Hg.
    pose proof (build_block_end body me MainBlock (Pos.succ me) t) as Hnx.
    revert Hg Hnx. destruct (build_block me MainBlock (Pos.succ me) body t) as [t1 e1]. intros Hg Hnx. cbn [fst snd] in Hg, Hnx. cbn [fst].
    destruct (Pos.eqb_spec target me).
    + subst target. rewrite Table.get_set_same. cbn [end_decl]. rewrite <- Hnx. reflexivity.
    + rewrite Table.get_set_other by congruence. exact Hg.
Qed.

Theorem build_file_source_exact : forall f local,
  Table.get local (table (build_file f)) = option_map occurrence_meta (source_occurrence_at f local).
Proof.
  intros f local. unfold build_file, source_occurrence_at.
  destruct (Syntax.imports f) as [|i ?]; [| destruct i].
  set (tp := Table.set package_id (MakeMeta PackageClauseKind (Some root_id) FilePackage package_id) Table.empty).
  pose proof (build_seq_get build_decl end_decl (fun i m x tgt => occurrence_decl' root_id i m x tgt) root_id
                (Syntax.declarations f) end_decl_ge
                (fun x _ i m tt => build_decl_end x root_id i m tt)
                (fun x _ i m tt tgt => build_decl_get x root_id i m tt tgt)
                (fun x _ i m tgt H => occurrence_decl'_above x root_id i m tgt H)
                (fun x _ i m tgt H => occurrence_decl'_below x root_id i m tgt H)
                0 (Pos.succ package_id) tp local) as HG.
  pose proof (build_seq_end build_decl end_decl root_id (Syntax.declarations f)
                (fun x _ i m tt => build_decl_end x root_id i m tt) 0 (Pos.succ package_id) tp) as Hnx.
  revert HG Hnx. destruct (build_seq build_decl root_id 0 (Pos.succ package_id) (Syntax.declarations f) tp) as [t1 nx]. intros HG Hnx. cbn [fst snd] in HG, Hnx. cbn [table].
  destruct (Pos.eqb_spec local root_id).
  - subst local. rewrite Table.get_set_same.
    cbn [option_map occurrence_meta occurrence_kind occurrence_parent occurrence_role occurrence_subtree_end].
    unfold count_file. unfold next_decls. rewrite <- Hnx. reflexivity.
  - rewrite Table.get_set_other by congruence. rewrite HG.
    destruct (Pos.eqb_spec local package_id).
    + subst local.
      rewrite (occurrence_seq'_below (fun i m x t => occurrence_decl' root_id i m x t) end_decl (Syntax.declarations f) end_decl_ge
                 (fun x _ i m tgt H => occurrence_decl'_below x root_id i m tgt H) 0 (Pos.succ package_id) package_id
                 ltac:(unfold package_id; lia)).
      unfold tp. rewrite Table.get_set_same.
      cbn [option_map occurrence_meta occurrence_kind occurrence_parent occurrence_role occurrence_subtree_end].
      reflexivity.
    + unfold tp. rewrite Table.get_set_other by congruence. rewrite Table.get_empty.
      destruct (occurrence_seq' (fun i m x t => occurrence_decl' root_id i m x t) end_decl 0 (Pos.succ package_id) (Syntax.declarations f) local) as [o|];
        cbn [option_map]; reflexivity.
Qed.
Theorem source_occurrence_meta : forall f local o,
  source_occurrence_at f local = Some o ->
  Table.get local (table (build_file f)) = Some (occurrence_meta o).
Proof. intros f local o H. rewrite build_file_source_exact, H. reflexivity. Qed.

Theorem meta_source_occurrence : forall f local m,
  Table.get local (table (build_file f)) = Some m ->
  exists o, source_occurrence_at f local = Some o /\ m = occurrence_meta o.
Proof.
  intros f local m H. rewrite build_file_source_exact in H.
  destruct (source_occurrence_at f local) as [o|] eqn:Eo; cbn [option_map] in H; [|discriminate].
  injection H as <-. exists o. split; reflexivity.
Qed.

Theorem source_absence : forall f local,
  source_occurrence_at f local = None <->
  Table.get local (table (build_file f)) = None.
Proof.
  intros f local. rewrite build_file_source_exact.
  destruct (source_occurrence_at f local); cbn [option_map]; split; intro H; congruence.
Qed.

Theorem source_occurrence_unique : forall f local o1 o2,
  source_occurrence_at f local = Some o1 -> source_occurrence_at f local = Some o2 -> o1 = o2.
Proof. intros f local o1 o2 H1 H2. rewrite H1 in H2. injection H2 as <-. reflexivity. Qed.

Theorem source_kind_exact : forall f local o,
  source_occurrence_at f local = Some o ->
  exists m, Table.get local (table (build_file f)) = Some m /\ kind m = occurrence_kind o.
Proof. intros f local o H. exists (occurrence_meta o). split; [apply source_occurrence_meta; exact H | reflexivity]. Qed.

Theorem source_role_exact : forall f local o,
  source_occurrence_at f local = Some o ->
  exists m, Table.get local (table (build_file f)) = Some m /\ role m = occurrence_role o.
Proof. intros f local o H. exists (occurrence_meta o). split; [apply source_occurrence_meta; exact H | reflexivity]. Qed.

Theorem source_parent_exact : forall f local o,
  source_occurrence_at f local = Some o ->
  exists m, Table.get local (table (build_file f)) = Some m /\ parent m = occurrence_parent o.
Proof. intros f local o H. exists (occurrence_meta o). split; [apply source_occurrence_meta; exact H | reflexivity]. Qed.

Theorem source_subtree_end_exact : forall f local o,
  source_occurrence_at f local = Some o ->
  exists m, Table.get local (table (build_file f)) = Some m /\ subtree_end m = occurrence_subtree_end o.
Proof. intros f local o H. exists (occurrence_meta o). split; [apply source_occurrence_meta; exact H | reflexivity]. Qed.

(* the flat enumeration is the point spec read at every id in range: one traversal authority, no second walk *)

Fixpoint pos_seq (start : positive) (len : nat) : list positive :=
  match len with O => [] | S n => start :: pos_seq (Pos.succ start) n end.

Lemma pos_seq_in : forall len start c,
  In c (pos_seq start len) <-> (Pos.to_nat start <= Pos.to_nat c < Pos.to_nat start + len)%nat.
Proof.
  induction len as [|n IH]; intros start c; simpl.
  - split; [intros H; destruct H | intros H; exfalso; lia].
  - rewrite IH. split.
    + intros [<- | H]; [lia|]. rewrite Pos2Nat.inj_succ in H. lia.
    + intros H. destruct (Pos.eq_dec c start) as [->|Hne]; [left; reflexivity|].
      right. rewrite Pos2Nat.inj_succ.
      assert (Pos.to_nat c <> Pos.to_nat start) by (intro Hc; apply Hne; apply Pos2Nat.inj; exact Hc).
      lia.
Qed.

Lemma count_file_succ : forall f,
  Pos.succ (count_file f) = next_decls (Pos.succ package_id) (Syntax.declarations f).
Proof.
  intros f. unfold count_file, next_decls.
  set (N := next_seq end_decl (Pos.succ package_id) (Syntax.declarations f)).
  assert (HN : (Pos.succ package_id <= N)%positive) by (apply (next_seq_ge end_decl end_decl_ge)).
  destruct (Pos.succ_pred_or N) as [HN1|HN1]; [ unfold package_id in HN; lia | exact HN1 ].
Qed.

Lemma count_file_ge2 : forall f, (package_id <= count_file f)%positive.
Proof.
  intros f. pose proof (count_file_succ f) as H.
  assert (HN : (Pos.succ package_id <= next_decls (Pos.succ package_id) (Syntax.declarations f))%positive)
    by (apply (next_seq_ge end_decl end_decl_ge)).
  rewrite <- H in HN. lia.
Qed.

Lemma source_le_count : forall f target o,
  source_occurrence_at f target = Some o -> (target <= count_file f)%positive.
Proof.
  intros f target o H. unfold source_occurrence_at in H.
  destruct (Syntax.imports f) as [|i ?]; [|destruct i].
  destruct (Pos.eqb_spec target root_id) as [->|Hr].
  { pose proof (count_file_ge2 f). unfold root_id, package_id in *. lia. }
  destruct (Pos.eqb_spec target package_id) as [->|Hp].
  { apply count_file_ge2. }
  destruct (Pos.leb_spec target (count_file f)) as [Hle|Hgt]; [exact Hle|].
  exfalso.
  assert (Habove : (next_seq end_decl (Pos.succ package_id) (Syntax.declarations f) <= target)%positive).
  { pose proof (count_file_succ f) as Hs. unfold next_decls in Hs. rewrite <- Hs. lia. }
  rewrite (occurrence_seq'_above (fun i m x t => occurrence_decl' root_id i m x t) end_decl
             (Syntax.declarations f) end_decl_ge
             (fun x _ i m tgt Hh => occurrence_decl'_above x root_id i m tgt Hh)
             0 (Pos.succ package_id) target Habove) in H.
  discriminate.
Qed.

Definition all_ids (f : Syntax.File) : list positive := pos_seq root_id (Pos.to_nat (count_file f)).

Lemma in_all_ids : forall f k,
  In k (all_ids f) <-> (root_id <= k <= count_file f)%positive.
Proof.
  intros f k. unfold all_ids. rewrite pos_seq_in. unfold root_id. rewrite Pos2Nat.inj_1.
  pose proof (Pos2Nat.is_pos k) as Hk. split.
  - intros [Hlo Hhi]. split; [lia|]. apply Pos2Nat.inj_le. lia.
  - intros [Hlo Hhi]. apply Pos2Nat.inj_le in Hhi. lia.
Qed.

Definition occurrences_file (f : Syntax.File) : list (positive * Occurrence) :=
  flat_map (fun id => match source_occurrence_at f id with Some o => [(id, o)] | None => [] end) (all_ids f).

Lemma occurrences_file_sound : forall f id o,
  In (id, o) (occurrences_file f) -> source_occurrence_at f id = Some o.
Proof.
  intros f id o H. unfold occurrences_file in H. apply in_flat_map in H.
  destruct H as [k [Hk Hin]]. destruct (source_occurrence_at f k) as [o'|] eqn:E; cbn [In] in Hin; [|contradiction].
  destruct Hin as [Heq|[]]. injection Heq as <- <-. exact E.
Qed.

Lemma occurrences_file_complete : forall f id o,
  source_occurrence_at f id = Some o -> In (id, o) (occurrences_file f).
Proof.
  intros f id o H. unfold occurrences_file. apply in_flat_map. exists id. split.
  - apply in_all_ids. split; [unfold root_id; lia | apply (source_le_count f id o H)].
  - rewrite H. left. reflexivity.
Qed.

Lemma occurrences_file_exact : forall f id o,
  In (id, o) (occurrences_file f) <-> source_occurrence_at f id = Some o.
Proof. intros; split; [apply occurrences_file_sound | apply occurrences_file_complete]. Qed.

(* a local id is valid in a file exactly when the point spec places an occurrence there *)
Definition valid_localb (f : Syntax.File) (local : positive) : bool :=
  match source_occurrence_at f local with Some _ => true | None => false end.

Lemma valid_localb_some : forall f local,
  valid_localb f local = true -> source_occurrence_at f local <> None.
Proof. intros f local H. unfold valid_localb in H. destruct (source_occurrence_at f local); [discriminate | discriminate H]. Qed.

Lemma valid_localb_true : forall f local o,
  source_occurrence_at f local = Some o -> valid_localb f local = true.
Proof. intros f local o H. unfold valid_localb. rewrite H. reflexivity. Qed.

(* A program-global occurrence identity: the file path and the file-local id. *)
Lemma file_path_eq_dec (a b : FilePath.T) : {a = b} + {a <> b}.
Proof.
  destruct (FilePath.equalb a b) eqn:E; [left; apply FilePath.equalb_spec; exact E|].
  right; intro Heq; subst; rewrite (proj2 (FilePath.equalb_spec b b) eq_refl) in E; discriminate.
Qed.

Record Key := MakeKey { key_path : FilePath.T ; key_local : positive }.
Definition key_equalb (a b : Key) : bool :=
  FilePath.equalb (key_path a) (key_path b) && Pos.eqb (key_local a) (key_local b).

Theorem key_eq_dec (a b : Key) : {a = b} + {a <> b}.
Proof.
  destruct a as [fa la], b as [fb lb].
  destruct (file_path_eq_dec fa fb) as [->|Hf]; [| right; intro H; injection H as <- <-; apply Hf; reflexivity].
  destruct (Pos.eq_dec la lb) as [->|Hl]; [left; reflexivity|].
  right; intro H; injection H as <-; apply Hl; reflexivity.
Qed.

Theorem key_equalb_spec (a b : Key) : key_equalb a b = true <-> a = b.
Proof.
  unfold key_equalb. rewrite andb_true_iff. split.
  - intros [Hf Hl]. apply FilePath.equalb_spec in Hf. apply Pos.eqb_eq in Hl.
    destruct a, b; simpl in *; subst; reflexivity.
  - intros ->. split; [apply FilePath.equalb_spec; reflexivity | apply Pos.eqb_eq; reflexivity].
Qed.

(* The program-level reference API: a validated (path, local) pair, its validity carried as a proof field. *)
Module Snapshot.

(* A file handle: a path with a boolean membership proof; its source is read from the program map. *)
Record FileRef (p : Syntax.Program) : Type := MakeFileRef {
  fr_path : FilePath.T;
  fr_memb : Syntax.file_mem fr_path (Syntax.files p) = true
}.
Arguments MakeFileRef {p}. Arguments fr_path {p}. Arguments fr_memb {p}.

Lemma file_mem_find_some : forall fp (fm : Syntax.Files),
  Syntax.file_mem fp fm = true -> Syntax.find_file fp fm <> None.
Proof.
  intros fp fm H. unfold Syntax.find_file.
  apply Collections.FileFacts.in_find_iff. apply Collections.FileFacts.mem_in_iff. exact H.
Qed.

Definition fr_source {p} (fr : FileRef p) : Syntax.File :=
  option_get (Syntax.find_file (fr_path fr) (Syntax.files p)) (file_mem_find_some _ _ (fr_memb fr)).

Definition file_ref_path {p} (fr : FileRef p) : FilePath.T := fr_path fr.
Definition file_ref_source {p} (fr : FileRef p) : Syntax.File := fr_source fr.

Lemma file_ref_find {p} (fr : FileRef p) :
  Syntax.find_file (fr_path fr) (Syntax.files p) = Some (fr_source fr).
Proof. unfold fr_source. apply option_get_some. Qed.

Lemma file_ref_ext {p} (fr1 fr2 : FileRef p) : fr_path fr1 = fr_path fr2 -> fr1 = fr2.
Proof.
  destruct fr1 as [p1 m1], fr2 as [p2 m2]; cbn; intros Hp; subst p2.
  f_equal. apply Eqdep_dec.UIP_dec, Bool.bool_dec.
Qed.

Record NodeRef (p : Syntax.Program) : Type := MakeNodeRef {
  nr_file  : FileRef p;
  nr_local : positive;
  nr_valid : valid_localb (fr_source nr_file) nr_local = true
}.
Arguments MakeNodeRef {p}. Arguments nr_file {p}. Arguments nr_local {p}. Arguments nr_valid {p}.

(* The index carries no stored table: every fact is read from the source the reference already retains. *)
Definition Syntax (p : Syntax.Program) : Type := unit.
Definition index_program (p : Syntax.Program) : Syntax p := tt.

Definition node_ref_file {p} (r : NodeRef p) : FileRef p := nr_file r.
Definition node_ref_local {p} (r : NodeRef p) : positive := nr_local r.
Definition node_ref_source {p} (r : NodeRef p) : Syntax.File := fr_source (nr_file r).
Definition node_ref_key {p} (r : NodeRef p) : Key := MakeKey (fr_path (nr_file r)) (nr_local r).

Lemma node_ref_valid {p} (r : NodeRef p) :
  valid_localb (node_ref_source r) (node_ref_local r) = true.
Proof. destruct r as [fr l v]; exact v. Qed.

(* The one retained occurrence a reference designates, total by its validity proof. *)
Definition source_occurrence_of_ref {p} (r : NodeRef p) : Occurrence :=
  option_get (source_occurrence_at (node_ref_source r) (node_ref_local r))
             (valid_localb_some _ _ (node_ref_valid r)).

Lemma source_occ_of_ref_eq {p} (r : NodeRef p) :
  source_occurrence_at (node_ref_source r) (node_ref_local r) = Some (source_occurrence_of_ref r).
Proof. unfold source_occurrence_of_ref. apply option_get_some. Qed.

Definition ref_meta {p} (r : NodeRef p) : Meta := occurrence_meta (source_occurrence_of_ref r).
Definition node_kind {p} (r : NodeRef p) : Kind := occurrence_kind (source_occurrence_of_ref r).
Definition node_role {p} (r : NodeRef p) : Role := occurrence_role (source_occurrence_of_ref r).
Definition node_subtree_end {p} (r : NodeRef p) : positive := occurrence_subtree_end (source_occurrence_of_ref r).
Definition node_at {p} (r : NodeRef p) : option Syntax.Expr := view_expr (source_occurrence_of_ref r).
Definition type_name_ref_syntax {p} (r : NodeRef p) : option Syntax.TypeExpr := view_typename (source_occurrence_of_ref r).

Lemma node_ref_key_eq {p} (r : NodeRef p) :
  node_ref_key r = MakeKey (file_ref_path (node_ref_file r)) (node_ref_local r).
Proof. reflexivity. Qed.

(* Two references with equal file and equal local id are equal (validity is proof-irrelevant here). *)
Lemma node_ref_ext {p} (r1 r2 : NodeRef p) :
  nr_file r1 = nr_file r2 -> nr_local r1 = nr_local r2 -> r1 = r2.
Proof.
  destruct r1 as [f1 l1 v1], r2 as [f2 l2 v2]; cbn; intros Hf Hl; subst f2 l2.
  f_equal. apply Eqdep_dec.UIP_dec, Bool.bool_dec.
Qed.

Lemma node_ref_key_inj {p} (r1 r2 : NodeRef p) : node_ref_key r1 = node_ref_key r2 -> r1 = r2.
Proof.
  unfold node_ref_key. intros H. injection H as Hp Hl.
  apply node_ref_ext; [ apply file_ref_ext; exact Hp | exact Hl ].
Qed.

(* Locate a file by its path, retaining the membership proof. *)
Definition file_of_path (p : Syntax.Program) (fp : FilePath.T) : option (FileRef p) :=
  match Syntax.file_mem fp (Syntax.files p) as b
        return Syntax.file_mem fp (Syntax.files p) = b -> option (FileRef p) with
  | true  => fun H => Some (MakeFileRef fp H)
  | false => fun _ => None
  end eq_refl.

Lemma file_of_path_sound : forall p fp fr,
  file_of_path p fp = Some fr -> file_ref_path fr = fp.
Proof.
  intros p fp fr. unfold file_of_path.
  generalize (@eq_refl bool (Syntax.file_mem fp (Syntax.files p))).
  destruct (Syntax.file_mem fp (Syntax.files p)) at 2 3; intros e H; [|discriminate H].
  injection H as <-. reflexivity.
Qed.

Lemma file_of_path_complete : forall p fr,
  file_of_path p (fr_path fr) = Some fr.
Proof.
  intros p fr. unfold file_of_path.
  generalize (@eq_refl bool (Syntax.file_mem (fr_path fr) (Syntax.files p))).
  destruct (Syntax.file_mem (fr_path fr) (Syntax.files p)) at 2 3; intros e.
  - f_equal. apply file_ref_ext. reflexivity.
  - exfalso. rewrite (fr_memb fr) in e. discriminate e.
Qed.

Lemma file_of_path_source : forall p fp fr,
  file_of_path p fp = Some fr -> Syntax.find_file fp (Syntax.files p) = Some (file_ref_source fr).
Proof.
  intros p fp fr H. pose proof (file_of_path_sound p fp fr H) as Hp.
  unfold file_ref_path in Hp. unfold file_ref_source. rewrite <- Hp. apply file_ref_find.
Qed.

(* Resolve a key to the reference it names, when both its file and local id are real. *)
Definition ref_of_key (p : Syntax.Program) (k : Key) : option (NodeRef p) :=
  match file_of_path p (key_path k) with
  | Some fr =>
      match valid_localb (fr_source fr) (key_local k) as b
            return valid_localb (fr_source fr) (key_local k) = b -> option (NodeRef p) with
      | true  => fun H => Some (MakeNodeRef fr (key_local k) H)
      | false => fun _ => None
      end eq_refl
  | None => None
  end.

Lemma ref_of_key_sound : forall p k r, ref_of_key p k = Some r -> node_ref_key r = k.
Proof.
  intros p k r. unfold ref_of_key. destruct (file_of_path p (key_path k)) as [fr|] eqn:Efr; [|discriminate].
  generalize (@eq_refl bool (valid_localb (fr_source fr) (key_local k))).
  destruct (valid_localb (fr_source fr) (key_local k)) at 2 3; intros e H; [|discriminate H].
  injection H as <-. unfold node_ref_key. cbn.
  apply file_of_path_sound in Efr. unfold file_ref_path in Efr.
  destruct k as [kp kl]; cbn in *. rewrite Efr. reflexivity.
Qed.

Lemma ref_of_key_complete : forall p r, ref_of_key p (node_ref_key r) = Some r.
Proof.
  intros p r. unfold ref_of_key, node_ref_key. cbn [key_path key_local].
  rewrite (file_of_path_complete p (nr_file r)).
  generalize (@eq_refl bool (valid_localb (fr_source (nr_file r)) (nr_local r))).
  destruct (valid_localb (fr_source (nr_file r)) (nr_local r)) at 2 3; intros e.
  - f_equal. apply node_ref_ext; reflexivity.
  - exfalso. rewrite (nr_valid r) in e. discriminate e.
Qed.

End Snapshot.
