(* One direct shallow occurrence authority: a finite file map of finite position maps of shallow cells. *)

From Stdlib Require Import List Bool Arith PeanoNat Lia Eqdep_dec PArith FSets.FMapFacts.
From Fido Require Import FilePath Collections Names Syntax.
Import ListNotations.

Inductive SpecFlavor := ConstSpecF | VarSpecF | TypeSpecF.

(* shallow local shapes: the immediate constructor and its scalar payload only; substructure is child cells *)
Inductive ConstShape    := CSExplicit (has_type : bool) | CSInherited.
Inductive VarShape       := VSTypeOnly | VSValues (has_type : bool).
Inductive TypeSpecShape  := TSAlias | TSDef.
Inductive StmtShape      := SSExpr | SSDecl | SSShort.
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

(* one shallow cell: view, role, parent position, subtree extent, ordered direct-child positions *)
Record Cell : Type := mkCell {
  c_view     : NodeView ;
  c_role     : Role ;
  c_parent   : option nat ;
  c_extent   : nat ;
  c_children : list nat
}.

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
  | Syntax.ExplicitConstInit ot _ => CSExplicit (match ot with Some _ => true | None => false end)
  | Syntax.InheritedConstInit => CSInherited
  end.
Definition varspec_shape (vs : Syntax.VarSpec) : VarShape :=
  match Syntax.var_init vs with
  | Syntax.VarTypeOnly _ => VSTypeOnly
  | Syntax.VarValues ot _ => VSValues (match ot with Some _ => true | None => false end)
  end.
Definition typespec_shape (ts : Syntax.TypeSpec) : TypeSpecShape :=
  match ts with Syntax.AliasSpec _ _ => TSAlias | Syntax.DefSpec _ _ => TSDef end.
Definition decl_flavor (d : Syntax.Declaration) : SpecFlavor :=
  match d with Syntax.ConstDecl _ => ConstSpecF | Syntax.VarDecl _ => VarSpecF | Syntax.TypeDecl _ => TypeSpecF end.
Definition stmt_shape (s : Syntax.Stmt) : StmtShape :=
  match s with Syntax.ExprStmt _ => SSExpr | Syntax.DeclarationStmt _ => SSDecl | Syntax.ShortVarDecl _ _ => SSShort end.
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

(* every number_expr call emits its cells at exactly the consecutive positions [b, b+n), advancing to b+n, n>0 *)
Lemma number_expr_span : forall e par role b,
  exists n, map fst (fst (number_expr par role b e)) = seq b n
            /\ snd (number_expr par role b e) = b + n /\ 0 < n.
Proof.
  intro e; induction e using Syntax.Expr_ind'; intros par role b.
  - exists 1; cbn [number_expr number_leaf fst snd map seq]; split; [ reflexivity | split; lia ].
  - exists 1; cbn [number_expr number_leaf fst snd map seq]; split; [ reflexivity | split; lia ].
  - cbn [number_expr]. specialize (IHe (Some b) RUnaryOperand (S b)).
    destruct (number_expr (Some b) RUnaryOperand (S b) e) as [kc nxt].
    cbn [fst snd] in IHe. destruct IHe as [m [Hkc [Hnxt Hm]]].
    exists (S m). split; [| split].
    + cbn [fst snd map seq]. rewrite Hkc. reflexivity.
    + cbn [snd]. lia.
    + lia.
  - (* Application (head e) args *)
    cbn [number_expr]. specialize (IHe (Some b) RApplicationHead (S b)).
    destruct (number_expr (Some b) RApplicationHead (S b) e) as [hc b1].
    cbn [fst snd] in IHe. destruct IHe as [m1 [Hhc [Hb1 Hm1]]].
    assert (Hda : forall (es : list Syntax.Expr),
      Forall (fun a => forall par role bb,
        exists n, map fst (fst (number_expr par role bb a)) = seq bb n
                  /\ snd (number_expr par role bb a) = bb + n /\ 0 < n) es ->
      forall i0 bi,
        (let '(ac, bf, _) := (fix do_args (i bi : nat) (es : list Syntax.Expr) {struct es}
              : list (nat * Cell) * nat * list nat :=
              match es with
              | [] => ([], bi, [])
              | a :: rest =>
                  let '(ac, bi') := number_expr (Some b) (RApplicationArg i) bi a in
                  let '(rc, bf, roots) := do_args (S i) bi' rest in
                  (ac ++ rc, bf, bi :: roots)
              end) i0 bi es in exists k, map fst ac = seq bi k /\ bf = bi + k)).
    { intros es Hall; induction Hall as [| a rest Ha Hrest IHrest]; intros i0 bi.
      - cbn [fst snd map seq]. exists 0. split; [ reflexivity | lia ].
      - cbn [fst snd]. specialize (Ha (Some b) (RApplicationArg i0) bi).
        destruct (number_expr (Some b) (RApplicationArg i0) bi a) as [ac1 bi'].
        cbn [fst snd] in Ha. destruct Ha as [k1 [Hac1 [Hbi' _]]].
        specialize (IHrest (S i0) bi').
        destruct ((fix do_args (i bi : nat) (es : list Syntax.Expr) {struct es} := _) (S i0) bi' rest)
          as [[rc bf] roots]. destruct IHrest as [k2 [Hrc Hbf]].
        cbn [fst snd]. exists (k1 + k2). split.
        * rewrite map_app, Hac1, Hrc, seq_app, <- Hbi'. reflexivity.
        * lia. }
    specialize (Hda args H 0 b1).
    destruct ((fix do_args (i bi : nat) (es : list Syntax.Expr) {struct es} := _) 0 b1 args)
      as [[ac bfin] aroots]. destruct Hda as [k [Hac Hbf]].
    exists (S (m1 + k)). split; [| split].
    + cbn [fst snd map seq]. rewrite map_app, Hhc, Hac, seq_app, <- Hb1. reflexivity.
    + cbn [snd]. lia.
    + lia.
Qed.

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

(* coverage foundation: [spans out b] says a numbering call filled exactly the contiguous positions [b, b+n) *)
Definition spans (out : list (nat * Cell) * nat) (b : nat) : Prop :=
  exists n, map fst (fst out) = seq b n /\ snd out = b + n.

Lemma spans_app : forall c1 b1 c2 b2 b,
  spans (c1, b1) b -> spans (c2, b2) b1 -> spans (c1 ++ c2, b2) b.
Proof.
  intros c1 b1 c2 b2 b [n1 [H1 E1]] [n2 [H2 E2]]; cbn [fst snd] in H1, E1, H2, E2.
  exists (n1 + n2); cbn [fst snd]; split;
    [ rewrite map_app, H1, H2, seq_app; subst b1; reflexivity | lia ].
Qed.

Lemma spans_node : forall self (cell : Cell) kids bfin,
  spans (kids, bfin) (S self) -> spans ((self, cell) :: kids, bfin) self.
Proof.
  intros self cell kids bfin [m [H E]]; cbn [fst snd] in H, E.
  exists (S m); cbn [fst snd map seq]; split; [ rewrite H; reflexivity | lia ].
Qed.

Lemma spans_leaf : forall v par role b, spans (number_leaf v par role b) b.
Proof. intros; exists 1; cbn [number_leaf fst snd map seq]; split; [ reflexivity | lia ]. Qed.

Lemma number_expr_spans : forall e par role b, spans (number_expr par role b e) b.
Proof. intros e par role b; destruct (number_expr_span e par role b) as [n [H1 [H2 _]]]; now exists n. Qed.

Lemma number_list_span {A} (f : nat -> A -> list (nat * Cell) * nat) :
  (forall b x, spans (f b x) b) ->
  forall xs b, spans (let '(c, b', _) := number_list f b xs in (c, b')) b.
Proof.
  intros Hf xs; induction xs as [|x rest IH]; intro b.
  - exists 0; cbn [number_list fst snd map seq]; split; [ reflexivity | lia ].
  - cbn [number_list]. specialize (Hf b x); destruct (f b x) as [xc b'].
    specialize (IH b'); destruct (number_list f b' rest) as [[rc b''] roots].
    cbn [fst snd] in *. exact (spans_app xc b' rc b'' b Hf IH).
Qed.

Lemma number_typeexpr_spans : forall par role b t, spans (number_typeexpr par role b t) b.
Proof. intros; apply spans_leaf. Qed.
Lemma number_bindingname_spans : forall par role b bn, spans (number_bindingname par role b bn) b.
Proof. intros; apply spans_leaf. Qed.

Lemma number_opttype_span : forall par b ot, spans (let '(c, b', _) := number_opttype par b ot in (c, b')) b.
Proof.
  intros par b [t|].
  - cbn [number_opttype]. pose proof (number_typeexpr_spans par RTypeUse b t) as Hs.
    destruct (number_typeexpr par RTypeUse b t) as [c b']. cbn [fst snd] in Hs |- *. exact Hs.
  - exists 0. cbn [number_opttype fst snd map seq]. split; [ reflexivity | lia ].
Qed.

Lemma number_constspec_span : forall par role b cs, spans (number_constspec par role b cs) b.
Proof.
  intros par role b cs. unfold number_constspec.
  pose proof (number_list_span (number_bindingname (Some b) (RSpecName ConstSpecF))
                (fun bb x => number_bindingname_spans (Some b) (RSpecName ConstSpecF) bb x)
                (Collections.ne_to_list (Syntax.const_names cs)) (S b)) as Hn.
  destruct (number_list (number_bindingname (Some b) (RSpecName ConstSpecF)) (S b)
              (Collections.ne_to_list (Syntax.const_names cs))) as [[nc b1] nroots].
  cbn [fst snd] in Hn.
  destruct (Syntax.const_init cs) as [ot vals|].
  - pose proof (number_opttype_span (Some b) b1 ot) as Ho.
    destruct (number_opttype (Some b) b1 ot) as [[oc b2] oroots]. cbn [fst snd] in Ho.
    pose proof (number_list_span (number_expr (Some b) RPlain)
                  (fun bb x => number_expr_spans x (Some b) RPlain bb)
                  (Collections.ne_to_list vals) b2) as Hv.
    destruct (number_list (number_expr (Some b) RPlain) b2 (Collections.ne_to_list vals)) as [[vc b3] vroots].
    cbn [fst snd] in Hv |- *. apply spans_node.
    exact (spans_app nc b1 (oc ++ vc) b3 (S b) Hn (spans_app oc b2 vc b3 b1 Ho Hv)).
  - cbn [fst snd]. apply spans_node. rewrite app_nil_r. exact Hn.
Qed.

Lemma number_varspec_span : forall par role b vs, spans (number_varspec par role b vs) b.
Proof.
  intros par role b vs. unfold number_varspec.
  pose proof (number_list_span (number_bindingname (Some b) (RSpecName VarSpecF))
                (fun bb x => number_bindingname_spans (Some b) (RSpecName VarSpecF) bb x)
                (Collections.ne_to_list (Syntax.var_names vs)) (S b)) as Hn.
  destruct (number_list (number_bindingname (Some b) (RSpecName VarSpecF)) (S b)
              (Collections.ne_to_list (Syntax.var_names vs))) as [[nc b1] nroots].
  cbn [fst snd] in Hn.
  destruct (Syntax.var_init vs) as [t | ot vals].
  - pose proof (number_typeexpr_spans (Some b) RTypeUse b1 t) as Ht.
    destruct (number_typeexpr (Some b) RTypeUse b1 t) as [c b2]. cbn [fst snd] in Ht |- *.
    apply spans_node. exact (spans_app nc b1 c b2 (S b) Hn Ht).
  - pose proof (number_opttype_span (Some b) b1 ot) as Ho.
    destruct (number_opttype (Some b) b1 ot) as [[oc b2] oroots]. cbn [fst snd] in Ho.
    pose proof (number_list_span (number_expr (Some b) RPlain)
                  (fun bb x => number_expr_spans x (Some b) RPlain bb)
                  (Collections.ne_to_list vals) b2) as Hv.
    destruct (number_list (number_expr (Some b) RPlain) b2 (Collections.ne_to_list vals)) as [[vc b3] vroots].
    cbn [fst snd] in Hv |- *. apply spans_node.
    exact (spans_app nc b1 (oc ++ vc) b3 (S b) Hn (spans_app oc b2 vc b3 b1 Ho Hv)).
Qed.

Lemma number_typespec_span : forall par role b ts, spans (number_typespec par role b ts) b.
Proof.
  intros par role b ts. unfold number_typespec.
  destruct ts as [bn t|bn t]; cbn [fst snd];
    ( pose proof (number_bindingname_spans (Some b) (RSpecName TypeSpecF) (S b) bn) as Hb;
      destruct (number_bindingname (Some b) (RSpecName TypeSpecF) (S b) bn) as [bc b1];
      pose proof (number_typeexpr_spans (Some b) RTypeUse b1 t) as Ht;
      destruct (number_typeexpr (Some b) RTypeUse b1 t) as [tc bfin];
      cbn [fst snd] in Hb, Ht |- *;
      apply spans_node; exact (spans_app bc b1 tc bfin (S b) Hb Ht) ).
Qed.

Lemma number_decl_span : forall par role b d, spans (number_decl par role b d) b.
Proof.
  intros par role b d. unfold number_decl. destruct d as [cs|vs|ts];
  [ pose proof (number_list_span (number_constspec (Some b) RPlain) (fun bb x => number_constspec_span (Some b) RPlain bb x) cs (S b)) as Hs;
    destruct (number_list (number_constspec (Some b) RPlain) (S b) cs) as [[kc bfin] roots]
  | pose proof (number_list_span (number_varspec (Some b) RPlain) (fun bb x => number_varspec_span (Some b) RPlain bb x) vs (S b)) as Hs;
    destruct (number_list (number_varspec (Some b) RPlain) (S b) vs) as [[kc bfin] roots]
  | pose proof (number_list_span (number_typespec (Some b) RPlain) (fun bb x => number_typespec_span (Some b) RPlain bb x) ts (S b)) as Hs;
    destruct (number_list (number_typespec (Some b) RPlain) (S b) ts) as [[kc bfin] roots] ];
  cbn [fst snd] in Hs |- *; apply spans_node; exact Hs.
Qed.

Lemma number_stmt_span : forall par role b s, spans (number_stmt par role b s) b.
Proof.
  intros par role b s. unfold number_stmt. destruct s as [e | d | names vals].
  - pose proof (number_expr_spans e (Some b) RExprStatementExpr (S b)) as He.
    destruct (number_expr (Some b) RExprStatementExpr (S b) e) as [c b'].
    cbn [fst snd] in He |- *. apply spans_node. exact He.
  - pose proof (number_decl_span (Some b) RPlain (S b) d) as Hd.
    destruct (number_decl (Some b) RPlain (S b) d) as [c b'].
    cbn [fst snd] in Hd |- *. apply spans_node. exact Hd.
  - pose proof (number_list_span (number_bindingname (Some b) RShortLhs) (fun bb x => number_bindingname_spans (Some b) RShortLhs bb x) (Collections.ne_to_list names) (S b)) as Hn.
    destruct (number_list (number_bindingname (Some b) RShortLhs) (S b) (Collections.ne_to_list names)) as [[nc b1] nroots]. cbn [fst snd] in Hn.
    pose proof (number_list_span (number_expr (Some b) RPlain) (fun bb x => number_expr_spans x (Some b) RPlain bb) (Collections.ne_to_list vals) b1) as Hv.
    destruct (number_list (number_expr (Some b) RPlain) b1 (Collections.ne_to_list vals)) as [[vc b2] vroots]. cbn [fst snd] in Hv |- *.
    apply spans_node. exact (spans_app nc b1 vc b2 (S b) Hn Hv).
Qed.

Lemma number_block_span : forall par role b blk, spans (number_block par role b blk) b.
Proof.
  intros par role b blk. unfold number_block. destruct blk as [stmts].
  pose proof (number_list_span (number_stmt (Some b) RPlain) (fun bb x => number_stmt_span (Some b) RPlain bb x) stmts (S b)) as Hs.
  destruct (number_list (number_stmt (Some b) RPlain) (S b) stmts) as [[kc bfin] roots].
  cbn [fst snd] in Hs |- *. apply spans_node. exact Hs.
Qed.

Lemma number_toplevel_span : forall par role b td, spans (number_toplevel par role b td) b.
Proof.
  intros par role b td. unfold number_toplevel. destruct td as [d | blk].
  - pose proof (number_decl_span (Some b) RPlain (S b) d) as Hd.
    destruct (number_decl (Some b) RPlain (S b) d) as [c b']. cbn [fst snd] in Hd |- *.
    apply spans_node. exact Hd.
  - pose proof (number_block_span (Some b) RPlain (S b) blk) as Hb.
    destruct (number_block (Some b) RPlain (S b) blk) as [c b']. cbn [fst snd] in Hb |- *.
    apply spans_node. exact Hb.
Qed.

(* file coverage: occurrence positions are exactly the contiguous source-preorder block [0, n) from the file root *)
Lemma number_file_positions : forall f, exists n, map fst (number_file f) = seq 0 n.
Proof.
  intro f. unfold number_file.
  pose proof (number_list_span (number_toplevel (Some 0) RPlain) (fun bb x => number_toplevel_span (Some 0) RPlain bb x) (Syntax.declarations f) 1) as Hs.
  destruct (number_list (number_toplevel (Some 0) RPlain) 1 (Syntax.declarations f)) as [[dc bfin] droots].
  cbn [fst snd] in Hs. destruct Hs as [m [Hdc Hbfin]]. cbn [fst snd] in Hdc.
  exists (S m). cbn [map fst seq]. rewrite Hdc. reflexivity.
Qed.

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

(* ProgramIndex is sealed to the one canonical index, so every idx is raw_index p and refs cannot be foreign *)
Definition ProgramIndex (p : Syntax.Program) : Type := { m : Collections.FileMap.t FileInfo | m = raw_index p }.
Definition index_program (p : Syntax.Program) : ProgramIndex p := exist _ (raw_index p) eq_refl.
Definition prog_map {p} (idx : ProgramIndex p) : Collections.FileMap.t FileInfo := proj1_sig idx.

Definition file_has {p} (idx : ProgramIndex p) (path : FilePath.T) : bool :=
  Collections.FileMap.mem path (prog_map idx).

Lemma file_find_some {p} (idx : ProgramIndex p) (path : FilePath.T) :
  file_has idx path = true -> exists fi, Collections.FileMap.find path (prog_map idx) = Some fi.
Proof.
  unfold file_has; intro H. apply Collections.FileFacts.mem_in_iff in H. destruct H as [fi Hmt].
  exists fi. apply Collections.FileFacts.find_mapsto_iff; exact Hmt.
Qed.

(* a file reference is its path plus the proof it is a member; membership makes lookup total *)
Record FileRef {p} (idx : ProgramIndex p) : Type := mkFileRef {
  fr_path : FilePath.T ;
  fr_in   : file_has idx fr_path = true
}.
Arguments mkFileRef {p idx} _ _.
Arguments fr_path {p idx} _.
Arguments fr_in {p idx} _.

Lemma file_find_not_none {p} {idx : ProgramIndex p} (fr : FileRef idx) :
  Collections.FileMap.find (fr_path fr) (prog_map idx) = None -> False.
Proof.
  intro Hn. destruct (file_find_some idx (fr_path fr) (fr_in fr)) as [fi Hfi]. rewrite Hfi in Hn; discriminate.
Qed.

Definition file_info_of {p} {idx : ProgramIndex p} (fr : FileRef idx) : FileInfo :=
  (match Collections.FileMap.find (fr_path fr) (prog_map idx) as o
     return Collections.FileMap.find (fr_path fr) (prog_map idx) = o -> FileInfo with
   | Some fi => fun _ => fi
   | None => fun Hn => False_rect FileInfo (file_find_not_none fr Hn)
   end) eq_refl.

Definition occ_count {p} {idx : ProgramIndex p} (fr : FileRef idx) : nat := fi_count (file_info_of fr).

Module NodeFacts := FMapFacts.WFacts_fun Collections.NodeMap.E Collections.NodeMap.

Definition cell_map {p} {idx : ProgramIndex p} (fr : FileRef idx) : Collections.NodeMap.t Cell :=
  fi_cells (file_info_of fr).

(* a node reference: a file, its position key, and proof of membership, so occ_at is a total projection *)
Record NodeRef {p} (idx : ProgramIndex p) : Type := mkNodeRef {
  nr_file : FileRef idx ;
  nr_key  : positive ;
  nr_in   : Collections.NodeMap.mem nr_key (cell_map nr_file) = true
}.
Arguments mkNodeRef {p idx} _ _ _.
Arguments nr_file {p idx} _.
Arguments nr_key {p idx} _.
Arguments nr_in {p idx} _.

Definition occ_at {p} {idx : ProgramIndex p} (r : NodeRef idx) : Cell :=
  (match Collections.NodeMap.find (nr_key r) (cell_map (nr_file r)) as o
     return Collections.NodeMap.find (nr_key r) (cell_map (nr_file r)) = o -> Cell with
   | Some c => fun _ => c
   | None => fun Hn => False_rect Cell
       (proj1 (NodeFacts.in_find_iff _ _) (proj2 (NodeFacts.mem_in_iff _ _) (nr_in r)) Hn)
   end) eq_refl.

Definition nr_pos {p} {idx : ProgramIndex p} (r : NodeRef idx) : nat := Nat.pred (Pos.to_nat (nr_key r)).
Definition node_view {p} {idx : ProgramIndex p} (r : NodeRef idx) : NodeView := c_view (occ_at r).
Definition node_role {p} {idx : ProgramIndex p} (r : NodeRef idx) : Role := c_role (occ_at r).
Definition node_kind {p} {idx : ProgramIndex p} (r : NodeRef idx) : Kind := kind_of_view (node_view r).
Definition node_extent {p} {idx : ProgramIndex p} (r : NodeRef idx) : nat := c_extent (occ_at r).

Definition mk_noderef {p} {idx : ProgramIndex p} (fr : FileRef idx) (k : positive) : option (NodeRef idx) :=
  (match Collections.NodeMap.mem k (cell_map fr) as b
     return Collections.NodeMap.mem k (cell_map fr) = b -> option (NodeRef idx) with
   | true => fun H => Some (mkNodeRef fr k H)
   | false => fun _ => None
   end) eq_refl.

Lemma mk_noderef_file {p} {idx : ProgramIndex p} (fr : FileRef idx) (k : positive) (r : NodeRef idx) :
  mk_noderef fr k = Some r -> nr_file r = fr.
Proof.
  unfold mk_noderef. generalize (@eq_refl bool (Collections.NodeMap.mem k (cell_map fr))).
  destruct (Collections.NodeMap.mem k (cell_map fr)) at 2 3; intro H;
    [ intro E; injection E as <-; reflexivity | discriminate ].
Qed.

Definition node_parent {p} {idx : ProgramIndex p} (r : NodeRef idx) : option (NodeRef idx) :=
  match c_parent (occ_at r) with Some pp => mk_noderef (nr_file r) (Pos.of_succ_nat pp) | None => None end.

Definition node_children {p} {idx : ProgramIndex p} (r : NodeRef idx) : list (NodeRef idx) :=
  fold_right (fun pp acc => match mk_noderef (nr_file r) (Pos.of_succ_nat pp) with Some c => c :: acc | None => acc end)
             [] (c_children (occ_at r)).

Definition file_nodes {p} {idx : ProgramIndex p} (fr : FileRef idx) : list (NodeRef idx) :=
  flat_map (fun kv => match mk_noderef fr (fst kv) with Some r => [r] | None => [] end)
           (Collections.NodeMap.elements (cell_map fr)).

Lemma file_nodes_file {p} {idx : ProgramIndex p} (fr : FileRef idx) (r : NodeRef idx) :
  In r (file_nodes fr) -> nr_file r = fr.
Proof.
  unfold file_nodes. intro Hin. apply in_flat_map in Hin. destruct Hin as [kv [_ Hin]].
  destruct (mk_noderef fr (fst kv)) as [r'|] eqn:E; try rewrite E in Hin; cbn in Hin.
  - destruct Hin as [Heq|[]]. subst r'. exact (mk_noderef_file fr (fst kv) r E).
  - destruct Hin.
Qed.

(* fixed-main occurrence identity: one exact Syntax.Main occurrence; its body is the sibling shallow block *)
Definition is_main_view (v : NodeView) : bool := match v with VTop TSMain => true | _ => false end.
Definition is_block_view (v : NodeView) : bool := match v with VBlock => true | _ => false end.

Record MainOccurrenceRef {p} (idx : ProgramIndex p) : Type := mkMainOccurrenceRef {
  mo_node : NodeRef idx ;
  mo_ok   : is_main_view (node_view mo_node) = true
}.
Arguments mkMainOccurrenceRef {p idx} _ _.
Arguments mo_node {p idx} _.
Arguments mo_ok {p idx} _.

Record BlockRef {p} (idx : ProgramIndex p) : Type := mkBlockRef {
  bl_node : NodeRef idx ;
  bl_ok   : is_block_view (node_view bl_node) = true
}.
Arguments mkBlockRef {p idx} _ _.
Arguments bl_node {p idx} _.
Arguments bl_ok {p idx} _.

Lemma mainocc_positional {p} {idx : ProgramIndex p} (a b : MainOccurrenceRef idx) :
  mo_node a = mo_node b -> a = b.
Proof. destruct a as [na Ha], b as [nb Hb]; cbn; intro E; subst nb; f_equal; apply (UIP_dec Bool.bool_dec). Qed.

Lemma blockref_positional {p} {idx : ProgramIndex p} (a b : BlockRef idx) :
  bl_node a = bl_node b -> a = b.
Proof. destruct a as [na Ha], b as [nb Hb]; cbn; intro E; subst nb; f_equal; apply (UIP_dec Bool.bool_dec). Qed.

(* a node is identified by its file and position; the membership proof is irrelevant (bool has unique proofs) *)
Lemma noderef_positional {p} {idx : ProgramIndex p} (a b : NodeRef idx) :
  nr_file a = nr_file b -> nr_pos a = nr_pos b -> a = b.
Proof.
  destruct a as [fa ka Ha], b as [fb kb Hb]; unfold nr_pos; simpl; intros Ef Ep; subst fb.
  assert (ka = kb) as Ek.
  { apply Pos2Nat.inj. pose proof (Pos2Nat.is_pos ka); pose proof (Pos2Nat.is_pos kb); lia. }
  subst kb. f_equal. apply (UIP_dec Bool.bool_dec).
Qed.

Lemma mk_noderef_self {p} {idx : ProgramIndex p} (r : NodeRef idx) :
  mk_noderef (nr_file r) (nr_key r) = Some r.
Proof.
  unfold mk_noderef. generalize (@eq_refl bool (Collections.NodeMap.mem (nr_key r) (cell_map (nr_file r)))).
  destruct (Collections.NodeMap.mem (nr_key r) (cell_map (nr_file r))) at 2 3; intro H.
  - f_equal. apply noderef_positional; reflexivity.
  - exfalso; pose proof (nr_in r) as Hin; congruence.
Qed.

Lemma fileref_positional {p} {idx : ProgramIndex p} (a b : FileRef idx) :
  fr_path a = fr_path b -> a = b.
Proof.
  destruct a as [pa Ha], b as [pb Hb]; simpl; intro E; subst pb; f_equal; apply (UIP_dec Bool.bool_dec).
Qed.

Definition mk_fileref {p} (idx : ProgramIndex p) (path : FilePath.T) : option (FileRef idx) :=
  (match file_has idx path as b return file_has idx path = b -> option (FileRef idx) with
   | true => fun H => Some (mkFileRef path H)
   | false => fun _ => None
   end) eq_refl.

Lemma mk_fileref_path {p} (idx : ProgramIndex p) (path : FilePath.T) (fr : FileRef idx) :
  mk_fileref idx path = Some fr -> fr_path fr = path.
Proof.
  unfold mk_fileref. generalize (@eq_refl bool (file_has idx path)).
  destruct (file_has idx path) at 2 3; intro H; [ intro E; injection E as <-; reflexivity | discriminate ].
Qed.

Lemma mk_fileref_none {p} (idx : ProgramIndex p) (path : FilePath.T) :
  mk_fileref idx path = None -> file_has idx path = false.
Proof.
  unfold mk_fileref. generalize (@eq_refl bool (file_has idx path)).
  destruct (file_has idx path) at 2 3; intro H; [ intro E; discriminate E | intros _; exact H ].
Qed.

Lemma mk_fileref_some {p} (idx : ProgramIndex p) (path : FilePath.T) :
  file_has idx path = true -> exists fr, mk_fileref idx path = Some fr.
Proof.
  intro Hfh. destruct (mk_fileref idx path) as [fr|] eqn:E.
  - exists fr; reflexivity.
  - exfalso. pose proof (mk_fileref_none idx path E) as H. rewrite Hfh in H; discriminate.
Qed.

(* every member file, enumerated as a FileRef, in the finite map's key order *)
Definition all_files {p} (idx : ProgramIndex p) : list (FileRef idx) :=
  flat_map (fun kv => match mk_fileref idx (fst kv) with Some fr => [fr] | None => [] end)
           (Collections.FileMap.elements (prog_map idx)).

Definition fileref_eqb {p} {idx : ProgramIndex p} (a b : FileRef idx) : bool :=
  FilePath.equalb (fr_path a) (fr_path b).
Lemma fileref_eqb_spec {p} {idx : ProgramIndex p} (a b : FileRef idx) : fileref_eqb a b = true <-> a = b.
Proof.
  unfold fileref_eqb; split.
  - intro H; apply FilePath.equalb_spec in H; apply fileref_positional; exact H.
  - intro H; subst b; apply FilePath.equalb_spec; reflexivity.
Qed.
