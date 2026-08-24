(* Index.Build — the one canonical executable source-to-shallow-occurrence numbering/build algorithm. *)
From Stdlib Require Import List Bool Arith PeanoNat Lia Eqdep_dec PArith FSets.FMapFacts.
From Fido Require Import Collections Syntax Index.Model.
Import ListNotations.

(* number a list of items left to right, threading the next free position and collecting each item's root *)
Fixpoint number_list {A} (f : nat -> A -> list (nat * Cell) * nat) (b : nat) (xs : list A)
  : list (nat * Cell) * nat * list nat :=
  match xs with
  | [] => ([], b, [])
  | x :: rest =>
      let '(xc, b') := f b x in
      let '(rc, b'', roots) := number_list f b' rest in
      (xc ++ rc, b'', b :: roots)
  end.

Definition number_leaf (v : NodeView) (par : option nat) (role : Role) (b : nat) : list (nat * Cell) * nat :=
  ([(b, mkCell v role par b [])], S b).

(* the shallow shape of each composite occurrence: its head constructor and immediate scalar flags only *)
Definition constspec_shape (cs : Syntax.ConstSpec) : ConstShape :=
  match Syntax.const_init cs with
  | Syntax.ExplicitConstInit ot vals =>
      CSExplicit (match ot with Some _ => true | None => false end)
                 (List.length (Collections.ne_to_list (Syntax.const_names cs)))
                 (List.length (Collections.ne_to_list vals))
  | Syntax.InheritedConstInit => CSInherited (List.length (Collections.ne_to_list (Syntax.const_names cs)))
  end.
Definition varspec_shape (vs : Syntax.VarSpec) : VarShape :=
  match Syntax.var_init vs with
  | Syntax.VarTypeOnly _ => VSTypeOnly (List.length (Collections.ne_to_list (Syntax.var_names vs)))
  | Syntax.VarValues ot vals => VSValues (match ot with Some _ => true | None => false end)
                                         (List.length (Collections.ne_to_list (Syntax.var_names vs)))
                                         (List.length (Collections.ne_to_list vals))
  end.
Definition typespec_shape (ts : Syntax.TypeSpec) : TypeSpecShape :=
  match ts with Syntax.AliasSpec _ _ => TSAlias | Syntax.DefSpec _ _ => TSDef end.
Definition decl_flavor (d : Syntax.Declaration) : SpecFlavor :=
  match d with Syntax.ConstDecl _ => ConstSpecF | Syntax.VarDecl _ => VarSpecF | Syntax.TypeDecl _ => TypeSpecF end.
Definition stmt_shape (s : Syntax.Stmt) : StmtShape :=
  match s with Syntax.ExprStmt _ => SSExpr | Syntax.DeclarationStmt _ => SSDecl
             | Syntax.ShortVarDecl names vals => SSShort (List.length (Collections.ne_to_list names))
                                                        (List.length (Collections.ne_to_list vals)) end.
Definition top_shape (td : Syntax.TopLevelDecl) : TopShape :=
  match td with Syntax.TopDeclaration _ => TSTopDecl | Syntax.Main _ => TSMain end.

(* an expression subtree; the arg list uses an inlined nested fixpoint so the guard checker accepts each arg *)
Fixpoint number_expr (par : option nat) (role : Role) (b : nat) (e : Syntax.Expr) {struct e}
  : list (nat * Cell) * nat :=
  match e with
  | Syntax.Name n => number_leaf (VName n) par role b
  | Syntax.LiteralExpr lit => number_leaf (VLiteral lit) par role b
  | Syntax.Unary op e' =>
      let '(kc, nxt) := number_expr (Some b) RUnaryOperand (S b) e' in
      ((b, mkCell (VUnary op) role par (nxt - 1) [S b]) :: kc, nxt)
  | Syntax.Application head args =>
      let '(hc, b1) := number_expr (Some b) RApplicationHead (S b) head in
      let fix do_args (i : nat) (bi : nat) (es : list Syntax.Expr) {struct es}
        : list (nat * Cell) * nat * list nat :=
        match es with
        | [] => ([], bi, [])
        | a :: rest =>
            let '(ac, bi') := number_expr (Some b) (RApplicationArg i) bi a in
            let '(rc, bf, roots) := do_args (S i) bi' rest in
            (ac ++ rc, bf, bi :: roots)
        end in
      let '(ac, bfin, aroots) := do_args 0 b1 args in
      ((b, mkCell VApplication role par (bfin - 1) (S b :: aroots)) :: (hc ++ ac), bfin)
  end.


(* the shallow view each expression head presents as its own root cell *)
Definition expr_view (e : Syntax.Expr) : NodeView :=
  match e with
  | Syntax.Name n => VName n
  | Syntax.LiteralExpr l => VLiteral l
  | Syntax.Unary op _ => VUnary op
  | Syntax.Application _ _ => VApplication
  end.


Definition number_typeexpr (par : option nat) (role : Role) (b : nat) (t : Syntax.TypeExpr) : list (nat * Cell) * nat :=
  number_leaf (VTypeExpr t) par role b.
Definition number_bindingname (par : option nat) (role : Role) (b : nat) (bn : Syntax.BindingName) : list (nat * Cell) * nat :=
  number_leaf (VBindingName bn) par role b.

Definition number_opttype (par : option nat) (b : nat) (ot : option Syntax.TypeExpr) : list (nat * Cell) * nat * list nat :=
  match ot with
  | Some t => let '(c, b') := number_typeexpr par RTypeUse b t in (c, b', [b])
  | None => ([], b, [])
  end.

Definition number_constspec (par : option nat) (role : Role) (b : nat) (cs : Syntax.ConstSpec) : list (nat * Cell) * nat :=
  let self := b in
  let '(nc, b1, nroots) := number_list (number_bindingname (Some self) (RSpecName ConstSpecF))
                                        (S self) (Collections.ne_to_list (Syntax.const_names cs)) in
  let '(ic, bfin, iroots) :=
    match Syntax.const_init cs with
    | Syntax.ExplicitConstInit ot vals =>
        let '(oc, b2, oroots) := number_opttype (Some self) b1 ot in
        let '(vc, b3, vroots) := number_list (number_expr (Some self) RPlain) b2 (Collections.ne_to_list vals) in
        (oc ++ vc, b3, oroots ++ vroots)
    | Syntax.InheritedConstInit => ([], b1, [])
    end in
  ((self, mkCell (VConstSpec (constspec_shape cs)) role par (bfin - 1) (nroots ++ iroots)) :: (nc ++ ic), bfin).

Definition number_varspec (par : option nat) (role : Role) (b : nat) (vs : Syntax.VarSpec) : list (nat * Cell) * nat :=
  let self := b in
  let '(nc, b1, nroots) := number_list (number_bindingname (Some self) (RSpecName VarSpecF))
                                        (S self) (Collections.ne_to_list (Syntax.var_names vs)) in
  let '(ic, bfin, iroots) :=
    match Syntax.var_init vs with
    | Syntax.VarTypeOnly t => let '(c, b2) := number_typeexpr (Some self) RTypeUse b1 t in (c, b2, [b1])
    | Syntax.VarValues ot vals =>
        let '(oc, b2, oroots) := number_opttype (Some self) b1 ot in
        let '(vc, b3, vroots) := number_list (number_expr (Some self) RPlain) b2 (Collections.ne_to_list vals) in
        (oc ++ vc, b3, oroots ++ vroots)
    end in
  ((self, mkCell (VVarSpec (varspec_shape vs)) role par (bfin - 1) (nroots ++ iroots)) :: (nc ++ ic), bfin).

Definition number_typespec (par : option nat) (role : Role) (b : nat) (ts : Syntax.TypeSpec) : list (nat * Cell) * nat :=
  let self := b in
  let '(bn, t) := match ts with Syntax.AliasSpec bn t | Syntax.DefSpec bn t => (bn, t) end in
  let '(bc, b1) := number_bindingname (Some self) (RSpecName TypeSpecF) (S self) bn in
  let '(tc, bfin) := number_typeexpr (Some self) RTypeUse b1 t in
  ((self, mkCell (VTypeSpec (typespec_shape ts)) role par (bfin - 1) [S self; b1]) :: (bc ++ tc), bfin).

Definition number_decl (par : option nat) (role : Role) (b : nat) (d : Syntax.Declaration) : list (nat * Cell) * nat :=
  let self := b in
  let '(kc, bfin, roots) :=
    match d with
    | Syntax.ConstDecl cs => number_list (number_constspec (Some self) RPlain) (S self) cs
    | Syntax.VarDecl vs   => number_list (number_varspec (Some self) RPlain) (S self) vs
    | Syntax.TypeDecl ts  => number_list (number_typespec (Some self) RPlain) (S self) ts
    end in
  ((self, mkCell (VDecl (decl_flavor d)) role par (bfin - 1) roots) :: kc, bfin).

Definition number_stmt (par : option nat) (role : Role) (b : nat) (s : Syntax.Stmt) : list (nat * Cell) * nat :=
  let self := b in
  let '(kc, bfin, roots) :=
    match s with
    | Syntax.ExprStmt e => let '(c, b') := number_expr (Some self) RExprStatementExpr (S self) e in (c, b', [S self])
    | Syntax.DeclarationStmt d => let '(c, b') := number_decl (Some self) RPlain (S self) d in (c, b', [S self])
    | Syntax.ShortVarDecl names vals =>
        let '(nc, b1, nroots) := number_list (number_bindingname (Some self) RShortLhs)
                                              (S self) (Collections.ne_to_list names) in
        let '(vc, b2, vroots) := number_list (number_expr (Some self) RPlain) b1 (Collections.ne_to_list vals) in
        (nc ++ vc, b2, nroots ++ vroots)
    end in
  ((self, mkCell (VStmt (stmt_shape s)) role par (bfin - 1) roots) :: kc, bfin).

Definition number_block (par : option nat) (role : Role) (b : nat) (blk : Syntax.Block) : list (nat * Cell) * nat :=
  let self := b in
  let stmts := match blk with Syntax.MakeBlock stmts => stmts end in
  let '(kc, bfin, roots) := number_list (number_stmt (Some self) RPlain) (S self) stmts in
  ((self, mkCell VBlock role par (bfin - 1) roots) :: kc, bfin).

Definition number_toplevel (par : option nat) (role : Role) (b : nat) (td : Syntax.TopLevelDecl) : list (nat * Cell) * nat :=
  let self := b in
  let '(kc, bfin, roots) :=
    match td with
    | Syntax.TopDeclaration d => let '(c, b') := number_decl (Some self) RPlain (S self) d in (c, b', [S self])
    | Syntax.Main blk         => let '(c, b') := number_block (Some self) RPlain (S self) blk in (c, b', [S self])
    end in
  ((self, mkCell (VTop (top_shape td)) role par (bfin - 1) roots) :: kc, bfin).

(* the file occurrence at position 0, its children the top-level declarations, in one preorder pass *)
Definition number_file (f : Syntax.File) : list (nat * Cell) :=
  let '(dc, bfin, droots) := number_list (number_toplevel (Some 0) RPlain) 1 (Syntax.declarations f) in
  (0, mkCell VFile RPlain None (bfin - 1) droots) :: dc.
(* one per-file finite structure: the position map keyed by occurrence position, and the occurrence count *)
Definition posmap_of (occs : list (nat * Cell)) : Collections.NodeMap.t Cell :=
  fold_right (fun kv m => Collections.NodeMap.add (Pos.of_succ_nat (fst kv)) (snd kv) m)
             (Collections.NodeMap.empty Cell) occs.

Record FileInfo : Type := mkFileInfo { fi_cells : Collections.NodeMap.t Cell ; fi_count : nat }.

(* one structural traversal: [number_file] is evaluated once and its result reused for the map and the count *)
Definition build_fileinfo (f : Syntax.File) : FileInfo :=
  let occs := number_file f in mkFileInfo (posmap_of occs) (List.length occs).

Definition raw_index (p : Syntax.Program) : Collections.FileMap.t FileInfo :=
  Collections.FileMap.map build_fileinfo (Syntax.files p).
