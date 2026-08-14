
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


(* total extraction from a provably-present option, the basis for the total reference API *)
Definition option_get {A} (o : option A) : o <> None -> A :=
  match o with Some a => fun _ => a | None => fun H => False_rect A (H eq_refl) end.
Lemma option_get_some {A} (o : option A) : forall (H : o <> None), o = Some (option_get o H).
Proof. destruct o as [a|]; intro H; [reflexivity | exfalso; exact (H eq_refl)]. Qed.

(* total positional access into a list; the in-range proof makes it a projection of a member, never a fallback *)
Fixpoint nth_lt {A} (l : list A) : forall n, Nat.lt n (length l) -> A :=
  match l with
  | [] => fun n H => False_rect A (Nat.nlt_0_r n H)
  | x :: xs => fun n =>
      match n with
      | O => fun _ => x
      | S k => fun H => nth_lt xs k (proj2 (Nat.succ_lt_mono k (length xs)) H)
      end
  end.

(* the bound is a mere proposition, so a reference's identity is its file and position, not which proof it carries *)
Lemma lt_unique (n m : nat) (p q : Nat.lt n m) : p = q.
Proof. apply Peano_dec.le_unique. Qed.

(* the total access agrees with the partial one: it returns exactly the retained member at that position *)
Lemma nth_lt_nth_error {A} (l : list A) : forall n H, nth_error l n = Some (nth_lt l n H).
Proof.
  induction l as [|x xs IH]; intros [|k] H; cbn in *.
  - exfalso; exact (Nat.nlt_0_r 0 H).
  - exfalso; exact (Nat.nlt_0_r (S k) H).
  - reflexivity.
  - apply IH.
Qed.

(* map over a list with each element's membership proof in hand — builds handles with no None fallback *)
Fixpoint map_in {A B} (l : list A) : (forall x, In x l -> B) -> list B :=
  match l with
  | [] => fun _ => []
  | x :: xs => fun f => f x (or_introl eq_refl) :: map_in xs (fun y Hy => f y (or_intror Hy))
  end.

(* the three spec shapes share one occurrence kind; this is the retained spec payload *)
Inductive AnySpec : Type :=
| ASConst : Syntax.ConstSpec -> AnySpec
| ASVar   : Syntax.VarSpec  -> AnySpec
| ASType  : Syntax.TypeSpec -> AnySpec.

(* Intrinsic cursors: a transparent selector into the source tree; each inhabitant denotes one real node. *)
Inductive CList {A} {C : A -> Type} : list A -> Type :=
| CL_head : forall (x : A) (xs : list A), C x -> CList (x :: xs)
| CL_tail : forall (x : A) (xs : list A), CList xs -> CList (x :: xs).

Inductive CExpr : Syntax.Expr -> Type :=
| CE_here  : forall e, CExpr e
| CE_unary : forall op e, CExpr e -> CExpr (Syntax.Unary op e)
| CE_head  : forall h a, CExpr h -> CExpr (Syntax.Application h a)
| CE_arg   : forall h a, @CList _ CExpr a -> CExpr (Syntax.Application h a).

(* the exact source expression the cursor selects *)
Fixpoint cexpr_view {e : Syntax.Expr} (c : CExpr e) {struct c} : Syntax.Expr :=
  match c with
  | CE_here e0 => e0
  | CE_unary _ _ c' => cexpr_view c'
  | CE_head _ _ c' => cexpr_view c'
  | CE_arg _ a cl =>
      (fix clv (xs : list Syntax.Expr) (cl0 : @CList _ CExpr xs) {struct cl0} : Syntax.Expr :=
         match cl0 with
         | CL_head _ _ c0 => cexpr_view c0
         | CL_tail _ _ cl1 => clv _ cl1
         end) a cl
  end.

(* every expression cursor: the node itself before its children, in source order *)
Fixpoint cexpr_cursors (e : Syntax.Expr) {struct e} : list (CExpr e) :=
  match e as e0 return list (CExpr e0) with
  | Syntax.Name _ | Syntax.LiteralExpr _ => [CE_here _]
  | Syntax.Unary op e' => CE_here _ :: List.map (CE_unary op e') (cexpr_cursors e')
  | Syntax.Application h a =>
      let argcs :=
        (fix argc (xs : list Syntax.Expr) {struct xs} : list (@CList _ CExpr xs) :=
           match xs as xs0 return list (@CList _ CExpr xs0) with
           | [] => []
           | x :: rest =>
               List.map (fun c0 => CL_head x rest c0) (cexpr_cursors x)
               ++ List.map (fun cl0 => CL_tail x rest cl0) (argc rest)
           end) a in
      CE_here _ :: (List.map (CE_head h a) (cexpr_cursors h) ++ List.map (CE_arg h a) argcs)
  end.

(* R1 (chunk 2): the rest of the cursor family, one inductive per grammar node, each inhabitant one real node. *)
Inductive CTypeExpr : Syntax.TypeExpr -> Type := CT_here : forall t, CTypeExpr t.
Inductive CBindingName : Syntax.BindingName -> Type := CBN_here : forall b, CBindingName b.

Inductive CConstSpec : Syntax.ConstSpec -> Type :=
| CCS_here : forall s, CConstSpec s
| CCS_name : forall names init, @CList _ CBindingName (Collections.ne_to_list names) ->
    CConstSpec (Syntax.MakeConstSpec names init)
| CCS_type : forall names oty vals, CTypeExpr oty ->
    CConstSpec (Syntax.MakeConstSpec names (Syntax.ExplicitConstInit (Some oty) vals))
| CCS_val  : forall names oty vals, @CList _ CExpr (Collections.ne_to_list vals) ->
    CConstSpec (Syntax.MakeConstSpec names (Syntax.ExplicitConstInit oty vals)).

Inductive CVarSpec : Syntax.VarSpec -> Type :=
| CVS_here : forall s, CVarSpec s
| CVS_name : forall names init, @CList _ CBindingName (Collections.ne_to_list names) ->
    CVarSpec (Syntax.MakeVarSpec names init)
| CVS_type_only : forall names ty, CTypeExpr ty ->
    CVarSpec (Syntax.MakeVarSpec names (Syntax.VarTypeOnly ty))
| CVS_type_vals : forall names ty vals, CTypeExpr ty ->
    CVarSpec (Syntax.MakeVarSpec names (Syntax.VarValues (Some ty) vals))
| CVS_val  : forall names oty vals, @CList _ CExpr (Collections.ne_to_list vals) ->
    CVarSpec (Syntax.MakeVarSpec names (Syntax.VarValues oty vals)).

Inductive CTypeSpec : Syntax.TypeSpec -> Type :=
| CTS_here : forall s, CTypeSpec s
| CTS_alias_name : forall nm ty, CBindingName nm -> CTypeSpec (Syntax.AliasSpec nm ty)
| CTS_alias_type : forall nm ty, CTypeExpr ty -> CTypeSpec (Syntax.AliasSpec nm ty)
| CTS_def_name : forall nm ty, CBindingName nm -> CTypeSpec (Syntax.DefSpec nm ty)
| CTS_def_type : forall nm ty, CTypeExpr ty -> CTypeSpec (Syntax.DefSpec nm ty).

Inductive CDecl : Syntax.Declaration -> Type :=
| CD_here : forall d, CDecl d
| CD_const : forall specs, @CList _ CConstSpec specs -> CDecl (Syntax.ConstDecl specs)
| CD_var   : forall specs, @CList _ CVarSpec specs -> CDecl (Syntax.VarDecl specs)
| CD_type  : forall specs, @CList _ CTypeSpec specs -> CDecl (Syntax.TypeDecl specs).

Inductive CStmt : Syntax.Stmt -> Type :=
| CST_here : forall s, CStmt s
| CST_expr : forall e, CExpr e -> CStmt (Syntax.ExprStmt e)
| CST_decl : forall d, CDecl d -> CStmt (Syntax.DeclarationStmt d)
| CST_lhs  : forall names vals, @CList _ CBindingName (Collections.ne_to_list names) ->
    CStmt (Syntax.ShortVarDecl names vals)
| CST_rhs  : forall names vals, @CList _ CExpr (Collections.ne_to_list vals) ->
    CStmt (Syntax.ShortVarDecl names vals).

Inductive CBlock : Syntax.Block -> Type :=
| CBL_here : forall b, CBlock b
| CBL_stmt : forall stmts, @CList _ CStmt stmts -> CBlock (Syntax.MakeBlock stmts).

Inductive CTop : Syntax.TopLevelDecl -> Type :=
| CTP_here : forall d, CTop d
| CTP_decl : forall dcl, CDecl dcl -> CTop (Syntax.TopDeclaration dcl)
| CTP_main : forall body, CBlock body -> CTop (Syntax.Main body).

Inductive CFile : Syntax.File -> Type :=
| CF_here    : forall f, CFile f
| CF_package : forall f, CFile f
| CF_decl    : forall f, @CList _ CTop (Syntax.declarations f) -> CFile f.

(* R1 (chunk 3): the node the cursor selects, as a tagged source view, and the kind/view accessors over it. *)
Fixpoint clist_proj {A} {C : A -> Type} {R} (proj : forall x, C x -> R) {xs} (cl : @CList A C xs) {struct cl} : R :=
  match cl with CL_head _ _ c => proj _ c | CL_tail _ _ cl' => clist_proj proj cl' end.

Definition ctypeexpr_view {t} (c : CTypeExpr t) : Syntax.TypeExpr := match c with CT_here t0 => t0 end.
Definition cbindingname_view {b} (c : CBindingName b) : Syntax.BindingName := match c with CBN_here b0 => b0 end.

Inductive NodeView : Type :=
| VFile        : Syntax.File          -> NodeView
| VPackage     : Syntax.PackageClause -> NodeView
| VTop         : Syntax.TopLevelDecl  -> NodeView
| VDecl        : Syntax.Declaration   -> NodeView
| VSpec        : AnySpec              -> NodeView
| VBindingName : Syntax.BindingName   -> NodeView
| VTypeExpr    : Syntax.TypeExpr      -> NodeView
| VStmt        : Syntax.Stmt          -> NodeView
| VBlock       : Syntax.Block         -> NodeView
| VExpr        : Syntax.Expr          -> NodeView.

Definition cexpr_nodeview {e} (c : CExpr e) : NodeView := VExpr (cexpr_view c).
Definition ctypeexpr_nodeview {t} (c : CTypeExpr t) : NodeView := VTypeExpr (ctypeexpr_view c).
Definition cbindingname_nodeview {b} (c : CBindingName b) : NodeView := VBindingName (cbindingname_view c).

Definition cconstspec_nodeview {s} (c : CConstSpec s) : NodeView :=
  match c with
  | CCS_here s0 => VSpec (ASConst s0)
  | CCS_name _ _ cl => clist_proj (fun _ sc => cbindingname_nodeview sc) cl
  | CCS_type _ _ _ tc => ctypeexpr_nodeview tc
  | CCS_val _ _ _ cl => clist_proj (fun _ sc => cexpr_nodeview sc) cl
  end.
Definition cvarspec_nodeview {s} (c : CVarSpec s) : NodeView :=
  match c with
  | CVS_here s0 => VSpec (ASVar s0)
  | CVS_name _ _ cl => clist_proj (fun _ sc => cbindingname_nodeview sc) cl
  | CVS_type_only _ _ tc => ctypeexpr_nodeview tc
  | CVS_type_vals _ _ _ tc => ctypeexpr_nodeview tc
  | CVS_val _ _ _ cl => clist_proj (fun _ sc => cexpr_nodeview sc) cl
  end.
Definition ctypespec_nodeview {s} (c : CTypeSpec s) : NodeView :=
  match c with
  | CTS_here s0 => VSpec (ASType s0)
  | CTS_alias_name _ _ bc => cbindingname_nodeview bc
  | CTS_alias_type _ _ tc => ctypeexpr_nodeview tc
  | CTS_def_name _ _ bc => cbindingname_nodeview bc
  | CTS_def_type _ _ tc => ctypeexpr_nodeview tc
  end.
Definition cdecl_nodeview {d} (c : CDecl d) : NodeView :=
  match c with
  | CD_here d0 => VDecl d0
  | CD_const _ cl => clist_proj (fun _ sc => cconstspec_nodeview sc) cl
  | CD_var _ cl => clist_proj (fun _ sc => cvarspec_nodeview sc) cl
  | CD_type _ cl => clist_proj (fun _ sc => ctypespec_nodeview sc) cl
  end.
Definition cstmt_nodeview {s} (c : CStmt s) : NodeView :=
  match c with
  | CST_here s0 => VStmt s0
  | CST_expr _ ec => cexpr_nodeview ec
  | CST_decl _ dc => cdecl_nodeview dc
  | CST_lhs _ _ cl => clist_proj (fun _ sc => cbindingname_nodeview sc) cl
  | CST_rhs _ _ cl => clist_proj (fun _ sc => cexpr_nodeview sc) cl
  end.
Definition cblock_nodeview {b} (c : CBlock b) : NodeView :=
  match c with
  | CBL_here b0 => VBlock b0
  | CBL_stmt _ cl => clist_proj (fun _ sc => cstmt_nodeview sc) cl
  end.
Definition ctop_nodeview {d} (c : CTop d) : NodeView :=
  match c with
  | CTP_here d0 => VTop d0
  | CTP_decl _ dc => cdecl_nodeview dc
  | CTP_main _ bc => cblock_nodeview bc
  end.
Definition cfile_nodeview {f} (c : CFile f) : NodeView :=
  match c with
  | CF_here f0 => VFile f0
  | CF_package f0 => VPackage (Syntax.package f0)
  | CF_decl f0 cl => clist_proj (fun _ tc => ctop_nodeview tc) cl
  end.

Definition node_kind (nv : NodeView) : Kind :=
  match nv with
  | VFile _ => FileKind | VPackage _ => PackageClauseKind | VTop _ => TopLevelKind
  | VDecl _ => DeclarationKind | VSpec _ => SpecKind | VBindingName _ => BindingNameKind
  | VTypeExpr _ => TypeNameKind | VStmt _ => StatementKind | VBlock _ => BlockKind | VExpr _ => ExpressionKind
  end.
Definition node_view_expr (nv : NodeView) : option Syntax.Expr := match nv with VExpr e => Some e | _ => None end.
Definition node_view_stmt (nv : NodeView) : option Syntax.Stmt := match nv with VStmt s => Some s | _ => None end.
Definition node_view_toplevel (nv : NodeView) : option Syntax.TopLevelDecl := match nv with VTop t => Some t | _ => None end.

Definition cfile_kind {f} (c : CFile f) : Kind := node_kind (cfile_nodeview c).
Definition cfile_view_expr {f} (c : CFile f) : option Syntax.Expr := node_view_expr (cfile_nodeview c).
Definition cfile_view_stmt {f} (c : CFile f) : option Syntax.Stmt := node_view_stmt (cfile_nodeview c).
Definition cfile_view_toplevel {f} (c : CFile f) : option Syntax.TopLevelDecl := node_view_toplevel (cfile_nodeview c).

(* The role the selected node plays in its parent, threaded down the path; list depth gives the position. *)
Fixpoint clist_proj_i {A} {C : A -> Type} {R} (proj : nat -> forall x, C x -> R) (base : nat) {xs}
                      (cl : @CList A C xs) {struct cl} : R :=
  match cl with CL_head _ _ c => proj base _ c | CL_tail _ _ cl' => clist_proj_i proj (S base) cl' end.

Fixpoint cexpr_role (incoming : Role) {e} (c : CExpr e) {struct c} : Role :=
  match c with
  | CE_here _ => incoming
  | CE_unary _ _ c' => cexpr_role UnaryOperand c'
  | CE_head _ _ c' => cexpr_role ApplicationHead c'
  | CE_arg _ a cl =>
      (fix argr (i : nat) (xs : list Syntax.Expr) (cl0 : @CList _ CExpr xs) {struct cl0} : Role :=
         match cl0 with
         | CL_head _ _ c0 => cexpr_role (ApplicationArgument i) c0
         | CL_tail _ _ cl1 => argr (S i) _ cl1
         end) 0%nat a cl
  end.

Definition ctypeexpr_role (incoming : Role) {t} (_ : CTypeExpr t) : Role := incoming.
Definition cbindingname_role (incoming : Role) {b} (_ : CBindingName b) : Role := incoming.

Definition cconstspec_role (incoming : Role) {s} (c : CConstSpec s) : Role :=
  match c with
  | CCS_here _ => incoming
  | CCS_name _ _ cl => clist_proj_i (fun i _ sc => cbindingname_role (SpecName i) sc) 0 cl
  | CCS_type _ _ _ tc => ctypeexpr_role SpecTypeUse tc
  | CCS_val _ _ _ cl => clist_proj_i (fun i _ sc => cexpr_role (SpecValue i) sc) 0 cl
  end.
Definition cvarspec_role (incoming : Role) {s} (c : CVarSpec s) : Role :=
  match c with
  | CVS_here _ => incoming
  | CVS_name _ _ cl => clist_proj_i (fun i _ sc => cbindingname_role (SpecName i) sc) 0 cl
  | CVS_type_only _ _ tc => ctypeexpr_role SpecTypeUse tc
  | CVS_type_vals _ _ _ tc => ctypeexpr_role SpecTypeUse tc
  | CVS_val _ _ _ cl => clist_proj_i (fun i _ sc => cexpr_role (SpecValue i) sc) 0 cl
  end.
Definition ctypespec_role (incoming : Role) {s} (c : CTypeSpec s) : Role :=
  match c with
  | CTS_here _ => incoming
  | CTS_alias_name _ _ bc => cbindingname_role (SpecName 0) bc
  | CTS_alias_type _ _ tc => ctypeexpr_role SpecTypeUse tc
  | CTS_def_name _ _ bc => cbindingname_role (SpecName 0) bc
  | CTS_def_type _ _ tc => ctypeexpr_role SpecTypeUse tc
  end.
Definition cdecl_role (incoming : Role) {d} (c : CDecl d) : Role :=
  match c with
  | CD_here _ => incoming
  | CD_const _ cl => clist_proj_i (fun i _ sc => cconstspec_role (DeclSpec i) sc) 0 cl
  | CD_var _ cl => clist_proj_i (fun i _ sc => cvarspec_role (DeclSpec i) sc) 0 cl
  | CD_type _ cl => clist_proj_i (fun i _ sc => ctypespec_role (DeclSpec i) sc) 0 cl
  end.
Definition cstmt_role (incoming : Role) {s} (c : CStmt s) : Role :=
  match c with
  | CST_here _ => incoming
  | CST_expr _ ec => cexpr_role ExprStatementExpr ec
  | CST_decl _ dc => cdecl_role DeclStatementDecl dc
  | CST_lhs _ _ cl => clist_proj_i (fun i _ sc => cbindingname_role (ShortLhs i) sc) 0 cl
  | CST_rhs _ _ cl => clist_proj_i (fun i _ sc => cexpr_role (ShortRhs i) sc) 0 cl
  end.
Definition cblock_role (incoming : Role) {b} (c : CBlock b) : Role :=
  match c with
  | CBL_here _ => incoming
  | CBL_stmt _ cl => clist_proj_i (fun i _ sc => cstmt_role (BlockStatement i) sc) 0 cl
  end.
Definition ctop_role (incoming : Role) {d} (c : CTop d) : Role :=
  match c with
  | CTP_here _ => incoming
  | CTP_decl _ dc => cdecl_role incoming dc
  | CTP_main _ bc => cblock_role MainBlock bc
  end.
Definition cfile_role {f} (c : CFile f) : Role :=
  match c with
  | CF_here _ => FileRoot
  | CF_package _ => FilePackage
  | CF_decl _ cl => clist_proj_i (fun i _ tc => ctop_role (FileDeclaration i) tc) 0 cl
  end.

(* The parent node as a projection: each descend carries the current node down as its children's parent. *)
Fixpoint cexpr_parentview (parent : option NodeView) {e} (c : CExpr e) {struct c} : option NodeView :=
  match c with
  | CE_here _ => parent
  | CE_unary op e0 c' => cexpr_parentview (Some (VExpr (Syntax.Unary op e0))) c'
  | CE_head h a c' => cexpr_parentview (Some (VExpr (Syntax.Application h a))) c'
  | CE_arg h a cl =>
      (fix argp (xs : list Syntax.Expr) (cl0 : @CList _ CExpr xs) {struct cl0} : option NodeView :=
         match cl0 with
         | CL_head _ _ c0 => cexpr_parentview (Some (VExpr (Syntax.Application h a))) c0
         | CL_tail _ _ cl1 => argp _ cl1
         end) a cl
  end.

Definition ctypeexpr_parentview (parent : option NodeView) {t} (_ : CTypeExpr t) : option NodeView := parent.
Definition cbindingname_parentview (parent : option NodeView) {b} (_ : CBindingName b) : option NodeView := parent.

Definition cconstspec_parentview (parent : option NodeView) {s} (c : CConstSpec s) : option NodeView :=
  match c with
  | CCS_here _ => parent
  | CCS_name _ _ cl => clist_proj (fun _ sc => cbindingname_parentview (Some (VSpec (ASConst s))) sc) cl
  | CCS_type _ _ _ tc => ctypeexpr_parentview (Some (VSpec (ASConst s))) tc
  | CCS_val _ _ _ cl => clist_proj (fun _ sc => cexpr_parentview (Some (VSpec (ASConst s))) sc) cl
  end.
Definition cvarspec_parentview (parent : option NodeView) {s} (c : CVarSpec s) : option NodeView :=
  match c with
  | CVS_here _ => parent
  | CVS_name _ _ cl => clist_proj (fun _ sc => cbindingname_parentview (Some (VSpec (ASVar s))) sc) cl
  | CVS_type_only _ _ tc => ctypeexpr_parentview (Some (VSpec (ASVar s))) tc
  | CVS_type_vals _ _ _ tc => ctypeexpr_parentview (Some (VSpec (ASVar s))) tc
  | CVS_val _ _ _ cl => clist_proj (fun _ sc => cexpr_parentview (Some (VSpec (ASVar s))) sc) cl
  end.
Definition ctypespec_parentview (parent : option NodeView) {s} (c : CTypeSpec s) : option NodeView :=
  match c with
  | CTS_here _ => parent
  | CTS_alias_name _ _ bc => cbindingname_parentview (Some (VSpec (ASType s))) bc
  | CTS_alias_type _ _ tc => ctypeexpr_parentview (Some (VSpec (ASType s))) tc
  | CTS_def_name _ _ bc => cbindingname_parentview (Some (VSpec (ASType s))) bc
  | CTS_def_type _ _ tc => ctypeexpr_parentview (Some (VSpec (ASType s))) tc
  end.
Definition cdecl_parentview (parent : option NodeView) {d} (c : CDecl d) : option NodeView :=
  match c with
  | CD_here _ => parent
  | CD_const _ cl => clist_proj (fun _ sc => cconstspec_parentview (Some (VDecl d)) sc) cl
  | CD_var _ cl => clist_proj (fun _ sc => cvarspec_parentview (Some (VDecl d)) sc) cl
  | CD_type _ cl => clist_proj (fun _ sc => ctypespec_parentview (Some (VDecl d)) sc) cl
  end.
Definition cstmt_parentview (parent : option NodeView) {s} (c : CStmt s) : option NodeView :=
  match c with
  | CST_here _ => parent
  | CST_expr _ ec => cexpr_parentview (Some (VStmt s)) ec
  | CST_decl _ dc => cdecl_parentview (Some (VStmt s)) dc
  | CST_lhs _ _ cl => clist_proj (fun _ sc => cbindingname_parentview (Some (VStmt s)) sc) cl
  | CST_rhs _ _ cl => clist_proj (fun _ sc => cexpr_parentview (Some (VStmt s)) sc) cl
  end.
Definition cblock_parentview (parent : option NodeView) {b} (c : CBlock b) : option NodeView :=
  match c with
  | CBL_here _ => parent
  | CBL_stmt _ cl => clist_proj (fun _ sc => cstmt_parentview (Some (VBlock b)) sc) cl
  end.
Definition ctop_parentview (parent : option NodeView) {d} (c : CTop d) : option NodeView :=
  match c with
  | CTP_here _ => parent
  | CTP_decl _ dc => cdecl_parentview (Some (VTop d)) dc
  | CTP_main _ bc => cblock_parentview (Some (VTop d)) bc
  end.
Definition cfile_parentview {f} (c : CFile f) : option NodeView :=
  match c with
  | CF_here _ => None
  | CF_package f0 => Some (VFile f0)
  | CF_decl f0 cl => clist_proj (fun _ tc => ctop_parentview (Some (VFile f0)) tc) cl
  end.

(* Ordered enumeration of every cursor, preorder, matching the old fold so the generated bytes are unchanged. *)
Fixpoint clist_cursors {A} {C : A -> Type} (all : forall x, list (C x)) (xs : list A) {struct xs}
  : list (@CList A C xs) :=
  match xs as xs0 return list (@CList A C xs0) with
  | [] => []
  | x :: rest => List.map (fun c => CL_head x rest c) (all x)
                 ++ List.map (fun cl => CL_tail x rest cl) (clist_cursors all rest)
  end.

Definition ctypeexpr_cursors (t : Syntax.TypeExpr) : list (CTypeExpr t) := [CT_here t].
Definition cbindingname_cursors (b : Syntax.BindingName) : list (CBindingName b) := [CBN_here b].

Definition cconstspec_cursors (s : Syntax.ConstSpec) : list (CConstSpec s) :=
  match s as s0 return list (CConstSpec s0) with
  | Syntax.MakeConstSpec names init =>
      CCS_here (Syntax.MakeConstSpec names init)
      :: (List.map (CCS_name names init) (clist_cursors cbindingname_cursors (Collections.ne_to_list names))
          ++ (match init as init0 return list (CConstSpec (Syntax.MakeConstSpec names init0)) with
              | Syntax.ExplicitConstInit oty vals =>
                  (match oty as oty0
                         return list (CConstSpec (Syntax.MakeConstSpec names (Syntax.ExplicitConstInit oty0 vals))) with
                   | Some ty => List.map (CCS_type names ty vals) (ctypeexpr_cursors ty)
                   | None => []
                   end)
                  ++ List.map (CCS_val names oty vals) (clist_cursors cexpr_cursors (Collections.ne_to_list vals))
              | Syntax.InheritedConstInit => []
              end))
  end.

Definition cvarspec_cursors (s : Syntax.VarSpec) : list (CVarSpec s) :=
  match s as s0 return list (CVarSpec s0) with
  | Syntax.MakeVarSpec names init =>
      CVS_here (Syntax.MakeVarSpec names init)
      :: (List.map (CVS_name names init) (clist_cursors cbindingname_cursors (Collections.ne_to_list names))
          ++ (match init as init0 return list (CVarSpec (Syntax.MakeVarSpec names init0)) with
              | Syntax.VarTypeOnly ty => List.map (CVS_type_only names ty) (ctypeexpr_cursors ty)
              | Syntax.VarValues oty vals =>
                  (match oty as oty0
                         return list (CVarSpec (Syntax.MakeVarSpec names (Syntax.VarValues oty0 vals))) with
                   | Some ty => List.map (CVS_type_vals names ty vals) (ctypeexpr_cursors ty)
                   | None => []
                   end)
                  ++ List.map (CVS_val names oty vals) (clist_cursors cexpr_cursors (Collections.ne_to_list vals))
              end))
  end.

Definition ctypespec_cursors (s : Syntax.TypeSpec) : list (CTypeSpec s) :=
  match s as s0 return list (CTypeSpec s0) with
  | Syntax.AliasSpec nm ty =>
      CTS_here (Syntax.AliasSpec nm ty)
      :: (List.map (CTS_alias_name nm ty) (cbindingname_cursors nm)
          ++ List.map (CTS_alias_type nm ty) (ctypeexpr_cursors ty))
  | Syntax.DefSpec nm ty =>
      CTS_here (Syntax.DefSpec nm ty)
      :: (List.map (CTS_def_name nm ty) (cbindingname_cursors nm)
          ++ List.map (CTS_def_type nm ty) (ctypeexpr_cursors ty))
  end.

(* R1 (chunk 5b): the remaining enumeration levels up to the composite per-file cursor list. *)
Definition cdecl_cursors (d : Syntax.Declaration) : list (CDecl d) :=
  match d as d0 return list (CDecl d0) with
  | Syntax.ConstDecl specs =>
      CD_here (Syntax.ConstDecl specs) :: List.map (CD_const specs) (clist_cursors cconstspec_cursors specs)
  | Syntax.VarDecl specs =>
      CD_here (Syntax.VarDecl specs) :: List.map (CD_var specs) (clist_cursors cvarspec_cursors specs)
  | Syntax.TypeDecl specs =>
      CD_here (Syntax.TypeDecl specs) :: List.map (CD_type specs) (clist_cursors ctypespec_cursors specs)
  end.

Definition cstmt_cursors (s : Syntax.Stmt) : list (CStmt s) :=
  match s as s0 return list (CStmt s0) with
  | Syntax.ExprStmt e => CST_here (Syntax.ExprStmt e) :: List.map (CST_expr e) (cexpr_cursors e)
  | Syntax.DeclarationStmt d => CST_here (Syntax.DeclarationStmt d) :: List.map (CST_decl d) (cdecl_cursors d)
  | Syntax.ShortVarDecl names vals =>
      CST_here (Syntax.ShortVarDecl names vals)
      :: (List.map (CST_lhs names vals) (clist_cursors cbindingname_cursors (Collections.ne_to_list names))
          ++ List.map (CST_rhs names vals) (clist_cursors cexpr_cursors (Collections.ne_to_list vals)))
  end.

Definition cblock_cursors (b : Syntax.Block) : list (CBlock b) :=
  match b as b0 return list (CBlock b0) with
  | Syntax.MakeBlock stmts =>
      CBL_here (Syntax.MakeBlock stmts) :: List.map (CBL_stmt stmts) (clist_cursors cstmt_cursors stmts)
  end.

Definition ctop_cursors (d : Syntax.TopLevelDecl) : list (CTop d) :=
  match d as d0 return list (CTop d0) with
  | Syntax.TopDeclaration dcl => CTP_here (Syntax.TopDeclaration dcl) :: List.map (CTP_decl dcl) (cdecl_cursors dcl)
  | Syntax.Main body => CTP_here (Syntax.Main body) :: List.map (CTP_main body) (cblock_cursors body)
  end.

Definition cfile_cursors (f : Syntax.File) : list (CFile f) :=
  CF_here f :: CF_package f :: List.map (CF_decl f) (clist_cursors ctop_cursors (Syntax.declarations f)).

(* Consumer bridge: binding-name view, subtree size, and the indexed enumeration (id/subtree_end erased views). *)
Definition node_view_binding_name (nv : NodeView) : option Syntax.BindingName :=
  match nv with VBindingName b => Some b | _ => None end.
Definition cfile_view_binding_name {f} (c : CFile f) : option Syntax.BindingName := node_view_binding_name (cfile_nodeview c).

Definition cfile_subtree_size {f} (c : CFile f) : nat :=
  match cfile_nodeview c with
  | VFile f0 => List.length (cfile_cursors f0)
  | VPackage _ => 1
  | VTop t => List.length (ctop_cursors t)
  | VDecl d => List.length (cdecl_cursors d)
  | VSpec (ASConst s) => List.length (cconstspec_cursors s)
  | VSpec (ASVar s) => List.length (cvarspec_cursors s)
  | VSpec (ASType s) => List.length (ctypespec_cursors s)
  | VBindingName b => List.length (cbindingname_cursors b)
  | VTypeExpr t => List.length (ctypeexpr_cursors t)
  | VStmt s => List.length (cstmt_cursors s)
  | VBlock b => List.length (cblock_cursors b)
  | VExpr e => List.length (cexpr_cursors e)
  end.

Fixpoint occ_index_aux {f} (i : nat) (cs : list (CFile f)) : list (positive * positive * CFile f) :=
  match cs with
  | [] => []
  | c :: rest =>
      (Pos.of_succ_nat i, Pos.of_succ_nat (i + cfile_subtree_size c - 1), c) :: occ_index_aux (S i) rest
  end.
Definition occ_index (f : Syntax.File) : list (positive * positive * CFile f) := occ_index_aux 0 (cfile_cursors f).

(* the index preserves its length: one entry per enumerated cursor, ids assigned by position *)
Lemma occ_index_aux_length {f} : forall (cs : list (CFile f)) base, length (occ_index_aux base cs) = length cs.
Proof. induction cs as [|x xs IH]; intros base; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.

(* position i carries the id of_succ_nat (base+i) over exactly the cursor found at position i of the enumeration *)
Lemma occ_index_aux_nth {f} : forall (cs : list (CFile f)) base i c,
  nth_error cs i = Some c ->
  exists se, nth_error (occ_index_aux base cs) i = Some (Pos.of_succ_nat (base + i), se, c).
Proof.
  induction cs as [|x xs IH]; intros base i c Hc.
  - destruct i; cbn in Hc; discriminate.
  - destruct i as [|k]; cbn in Hc.
    + injection Hc as <-. cbn. eexists. rewrite Nat.add_0_r. reflexivity.
    + cbn [occ_index_aux]. cbn [nth_error].
      destruct (IH (S base) k c Hc) as [se Hse].
      exists se. rewrite Hse. rewrite Nat.add_succ_comm. reflexivity.
Qed.

(* R1 totality: the index has exactly one entry per enumerated cursor — no occurrence is dropped or invented *)
Theorem occ_index_length (f : Syntax.File) : length (occ_index f) = length (cfile_cursors f).
Proof. unfold occ_index. apply occ_index_aux_length. Qed.

(* R1 ordering/id uniqueness: position i carries id of_succ_nat i over the cursor at position i — a bijection *)
Theorem occ_index_id_at (f : Syntax.File) : forall i c,
  nth_error (cfile_cursors f) i = Some c ->
  exists se, nth_error (occ_index f) i = Some (Pos.of_succ_nat i, se, c).
Proof.
  intros i c H. unfold occ_index.
  destruct (occ_index_aux_nth (cfile_cursors f) 0 i c H) as [se Hse]. exists se. exact Hse.
Qed.

(* The retained per-file result: the source and its ordered cursor index, built once from the one fold. *)
Record File := MakeFile { fi_source : Syntax.File ; fi_index : list (positive * positive * CFile fi_source) }.
Definition index_file (f : Syntax.File) : File := MakeFile f (occ_index f).

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

(* the retained program-indexed metadata object: one single-pass per-file table, built once from the program *)
Record ProgramIndex (p : Syntax.Program) : Type := MakeIndex {
  idx_files : Collections.FileMap.t File ;
  idx_built : idx_files = Collections.FileMap.map index_file (Syntax.files p)
}.
Arguments MakeIndex {p}. Arguments idx_files {p}. Arguments idx_built {p}.

Definition index_program (p : Syntax.Program) : ProgramIndex p :=
  MakeIndex (Collections.FileMap.map index_file (Syntax.files p)) eq_refl.

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

(* the retained per-file index the built map holds for a handle — the exact object a reference selects into *)
Lemma local_find_some {p} (idx : ProgramIndex p) (fr : FileRef p) :
  Collections.FileMap.find (fr_path fr) (idx_files idx) <> None.
Proof.
  rewrite (idx_built idx), Collections.FileFacts.map_o.
  destruct (Collections.FileMap.find (fr_path fr) (Syntax.files p)) eqn:E; cbn; [discriminate|].
  exfalso. apply (file_mem_find_some (fr_path fr) (Syntax.files p) (fr_memb fr)).
  unfold Syntax.find_file. exact E.
Qed.

Definition local_entry {p} (idx : ProgramIndex p) (fr : FileRef p) : File :=
  option_get (Collections.FileMap.find (fr_path fr) (idx_files idx)) (local_find_some idx fr).

(* the retained source this handle names — read from the built entry, not recomputed from the program *)
Definition local_source {p} (idx : ProgramIndex p) (fr : FileRef p) : Syntax.File := fi_source (local_entry idx fr).

Definition local_index {p} (idx : ProgramIndex p) (fr : FileRef p)
  : list (positive * positive * CFile (fi_source (local_entry idx fr))) := fi_index (local_entry idx fr).

(* a reference is a dependent selector: a file handle plus a proved-in-range position into that retained index *)
Record NodeRef {p : Syntax.Program} (idx : ProgramIndex p) : Type := MakeNodeRef {
  nr_file : FileRef p;
  nr_pos  : nat;
  nr_lt   : Nat.lt nr_pos (length (local_index idx nr_file))
}.
Arguments MakeNodeRef {p idx}. Arguments nr_file {p idx}. Arguments nr_pos {p idx}. Arguments nr_lt {p idx}.

(* the member the selector projects: exactly the retained occurrence at that position, total and without fallback *)
Definition node_ref_elt {p} {idx : ProgramIndex p} (r : NodeRef idx)
  : positive * positive * CFile (fi_source (local_entry idx (nr_file r)))
  := nth_lt (local_index idx (nr_file r)) (nr_pos r) (nr_lt r).
Definition node_ref_cursor {p} {idx : ProgramIndex p} (r : NodeRef idx)
  : CFile (fi_source (local_entry idx (nr_file r))) := snd (node_ref_elt r).

Definition node_ref_file {p} {idx : ProgramIndex p} (r : NodeRef idx) : FileRef p := nr_file r.
Definition node_ref_local {p} {idx : ProgramIndex p} (r : NodeRef idx) : positive := Pos.of_succ_nat (nr_pos r).
Definition node_ref_key {p} {idx : ProgramIndex p} (r : NodeRef idx) : Key :=
  MakeKey (fr_path (nr_file r)) (node_ref_local r).

Lemma node_ref_key_eq {p} {idx : ProgramIndex p} (r : NodeRef idx) :
  node_ref_key r = MakeKey (file_ref_path (node_ref_file r)) (node_ref_local r).
Proof. reflexivity. Qed.

(* two references with equal handle and equal position are equal — the range proof is a mere proposition *)
Lemma node_ref_ext {p} {idx : ProgramIndex p} (r1 r2 : NodeRef idx) :
  nr_file r1 = nr_file r2 -> nr_pos r1 = nr_pos r2 -> r1 = r2.
Proof.
  destruct r1 as [f1 n1 h1], r2 as [f2 n2 h2]; cbn; intros Hf Hn; subst f2 n2.
  f_equal. apply lt_unique.
Qed.

Lemma node_ref_key_inj {p} {idx : ProgramIndex p} (r1 r2 : NodeRef idx) : node_ref_key r1 = node_ref_key r2 -> r1 = r2.
Proof.
  unfold node_ref_key, node_ref_local. intros H. injection H as Hp Hl.
  apply (f_equal Pos.to_nat) in Hl. rewrite 2 SuccNat2Pos.id_succ in Hl. injection Hl as Hl.
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

(* a listed file binding is a real file, so its path is a member — the basis for a fallback-free handle list *)
Lemma binding_mem (p : Syntax.Program) (b : FilePath.T * Syntax.File) :
  In b (Syntax.file_bindings (Syntax.files p)) -> Syntax.file_mem (fst b) (Syntax.files p) = true.
Proof.
  intros Hin. apply Syntax.file_bindings_find in Hin. unfold Syntax.find_file in Hin.
  apply Collections.FileFacts.mem_in_iff. apply Collections.FileFacts.in_find_iff.
  rewrite Hin. discriminate.
Qed.

(* the retained files as handles: every file, once, with its membership — the enumeration consumers read *)
Definition file_refs (p : Syntax.Program) : list (FileRef p) :=
  map_in (Syntax.file_bindings (Syntax.files p)) (fun b Hin => MakeFileRef (fst b) (binding_mem p b Hin)).

(* q >= 1 for a positive q, so encoding a position as of_succ_nat and decoding by pred . to_nat round-trips *)
Lemma of_succ_pred_to_nat (q : positive) : Pos.of_succ_nat (Nat.pred (Pos.to_nat q)) = q.
Proof.
  apply Pos2Nat.inj. rewrite SuccNat2Pos.id_succ.
  pose proof (Pos2Nat.is_pos q) as H. destruct (Pos.to_nat q) as [|n] eqn:E; [ lia | reflexivity ].
Qed.

(* resolve a key to the reference it names: locate the file, then take the position its id encodes, in range *)
Definition ref_of_key {p : Syntax.Program} (idx : ProgramIndex p) (k : Key) : option (NodeRef idx) :=
  match file_of_path p (key_path k) with
  | Some fr =>
      match lt_dec (Nat.pred (Pos.to_nat (key_local k))) (length (local_index idx fr)) with
      | left H  => Some (MakeNodeRef fr (Nat.pred (Pos.to_nat (key_local k))) H)
      | right _ => None
      end
  | None => None
  end.

Lemma ref_of_key_sound : forall p (idx : ProgramIndex p) k r, ref_of_key idx k = Some r -> node_ref_key r = k.
Proof.
  intros p idx k r. unfold ref_of_key. destruct (file_of_path p (key_path k)) as [fr|] eqn:Efr; [|discriminate].
  destruct (lt_dec (Nat.pred (Pos.to_nat (key_local k))) (length (local_index idx fr))) as [H|H]; [|discriminate].
  intros HH. injection HH as <-. unfold node_ref_key, node_ref_local. cbn [nr_file nr_pos].
  apply file_of_path_sound in Efr. unfold file_ref_path in Efr.
  destruct k as [kp kl]; cbn [key_path key_local] in *.
  rewrite of_succ_pred_to_nat. rewrite Efr. reflexivity.
Qed.

Lemma ref_of_key_complete : forall p (idx : ProgramIndex p) r, ref_of_key idx (node_ref_key r) = Some r.
Proof.
  intros p idx r. unfold ref_of_key, node_ref_key, node_ref_local. cbn [key_path key_local].
  rewrite (file_of_path_complete p (nr_file r)).
  rewrite SuccNat2Pos.id_succ. cbn [Nat.pred].
  destruct (lt_dec (nr_pos r) (length (local_index idx (nr_file r)))) as [H|H].
  - f_equal. apply node_ref_ext; reflexivity.
  - exfalso. exact (H (nr_lt r)).
Qed.

End Snapshot.
