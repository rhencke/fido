(* One direct shallow occurrence authority: a finite file map of finite position maps of shallow cells. *)

From Stdlib Require Import List Bool Arith PeanoNat Lia Eqdep_dec PArith FSets.FMapFacts.
From Fido Require Import FilePath Collections Names Syntax.
Import ListNotations.

Inductive SpecFlavor := ConstSpecF | VarSpecF | TypeSpecF.

(* shallow local shapes: the immediate constructor and its scalar payload only; substructure is child cells *)
Inductive ConstShape    := CSExplicit (has_type : bool) (n_names n_values : nat) | CSInherited.
Inductive VarShape       := VSTypeOnly | VSValues (has_type : bool).
Inductive TypeSpecShape  := TSAlias | TSDef.
Inductive StmtShape      := SSExpr | SSDecl | SSShort (n_names : nat).
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
  | Syntax.ExplicitConstInit ot vals =>
      CSExplicit (match ot with Some _ => true | None => false end)
                 (List.length (Collections.ne_to_list (Syntax.const_names cs)))
                 (List.length (Collections.ne_to_list vals))
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
  match s with Syntax.ExprStmt _ => SSExpr | Syntax.DeclarationStmt _ => SSDecl
             | Syntax.ShortVarDecl names _ => SSShort (List.length (Collections.ne_to_list names)) end.
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

(* the shallow view each expression head presents as its own root cell *)
Definition expr_view (e : Syntax.Expr) : NodeView :=
  match e with
  | Syntax.Name n => VName n
  | Syntax.LiteralExpr l => VLiteral l
  | Syntax.Unary op _ => VUnary op
  | Syntax.Application _ _ => VApplication
  end.

(* number_expr's first emitted cell is the occurrence's own root at b, carrying the passed role, view, and parent *)
Lemma number_expr_root : forall e par role b,
  exists rest rc, fst (number_expr par role b e) = (b, rc) :: rest
                  /\ c_role rc = role /\ c_view rc = expr_view e /\ c_parent rc = par.
Proof.
  intros e par role b. destruct e as [n|l|op e'|hd args]; cbn [number_expr].
  - do 2 eexists; cbn [number_leaf fst]; repeat split; reflexivity.
  - do 2 eexists; cbn [number_leaf fst]; repeat split; reflexivity.
  - destruct (number_expr (Some b) RUnaryOperand (S b) e') as [kc nxt].
    do 2 eexists; cbn [fst]; repeat split; reflexivity.
  - destruct (number_expr (Some b) RApplicationHead (S b) hd) as [hc b1].
    destruct ((fix do_args (i bi : nat) (es : list Syntax.Expr) {struct es} := _) 0 b1 args)
      as [[ac bfin] aroots].
    do 2 eexists; cbn [fst]; repeat split; reflexivity.
Qed.

(* the parent inverse: every child position resolves to a member whose parent edge points back to the cell *)
Definition child_parent_ok (occs : list (nat * Cell)) : Prop :=
  forall pos cell, In (pos, cell) occs ->
    forall cp, In cp (c_children cell) ->
      exists ccell, In (cp, ccell) occs /\ c_parent ccell = Some pos.

Lemma child_parent_ok_app : forall c1 c2,
  child_parent_ok c1 -> child_parent_ok c2 -> child_parent_ok (c1 ++ c2).
Proof.
  intros c1 c2 H1 H2 pos cell Hin cp Hcp. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  - destruct (H1 pos cell Hin cp Hcp) as [cc [Hc Hp]]. exists cc. split; [ apply in_or_app; left; exact Hc | exact Hp ].
  - destruct (H2 pos cell Hin cp Hcp) as [cc [Hc Hp]]. exists cc. split; [ apply in_or_app; right; exact Hc | exact Hp ].
Qed.

Lemma child_parent_ok_node : forall self cell kids,
  (forall cp, In cp (c_children cell) ->
     exists cc, In (cp, cc) ((self, cell) :: kids) /\ c_parent cc = Some self) ->
  child_parent_ok kids -> child_parent_ok ((self, cell) :: kids).
Proof.
  intros self cell kids Hself Hkids pos c Hin cp Hcp. destruct Hin as [Heq|Hin].
  - inversion Heq; subst. destruct (Hself cp Hcp) as [cc [Hc Hp]]. exists cc. split; [ exact Hc | exact Hp ].
  - destruct (Hkids pos c Hin cp Hcp) as [cc [Hc Hp]]. exists cc. split; [ right; exact Hc | exact Hp ].
Qed.

(* the exact first-child edge law: a view carrying a required first edge has that edge at S pos, in range *)
Definition requires_first_edge (v : NodeView) : bool :=
  match v with VApplication | VUnary _ | VStmt SSExpr => true | _ => false end.
Definition first_child_wf (children : list nat) (pos bnd : nat) : Prop :=
  match children with hp :: _ => hp = S pos /\ hp < bnd | [] => False end.
Definition edge_wf (pos : nat) (cell : Cell) (bnd : nat) : Prop :=
  if requires_first_edge (c_view cell) then first_child_wf (c_children cell) pos bnd else True.
Definition ewf (occs : list (nat * Cell)) (bnd : nat) : Prop :=
  Forall (fun kv => edge_wf (fst kv) (snd kv) bnd) occs.

Lemma first_child_wf_mono : forall ch pos m M, m <= M -> first_child_wf ch pos m -> first_child_wf ch pos M.
Proof.
  intros [|hp tl] pos m M Hle; unfold first_child_wf;
    [ exact (fun H => H) | intros [Heq Hlt]; exact (conj Heq (Nat.lt_le_trans _ _ _ Hlt Hle)) ].
Qed.
Lemma edge_wf_mono : forall pos cell m M, m <= M -> edge_wf pos cell m -> edge_wf pos cell M.
Proof.
  intros pos cell m M Hle. unfold edge_wf.
  destruct (requires_first_edge (c_view cell)); [ apply first_child_wf_mono; exact Hle | exact (fun H => H) ].
Qed.
Lemma ewf_weaken : forall occs m M, m <= M -> ewf occs m -> ewf occs M.
Proof.
  intros occs m M Hle H. unfold ewf in *. eapply Forall_impl; [| exact H ].
  intros kv Hkv. eapply edge_wf_mono; [ exact Hle | exact Hkv ].
Qed.

Lemma number_expr_edge_wf : forall e par role b,
  ewf (fst (number_expr par role b e)) (snd (number_expr par role b e)).
Proof.
  intro e; induction e using Syntax.Expr_ind'; intros par role b; cbn [number_expr].
  - cbn [number_leaf fst snd]; constructor; [ cbn [edge_wf requires_first_edge c_view]; exact I | constructor ].
  - cbn [number_leaf fst snd]; constructor; [ cbn [edge_wf requires_first_edge c_view]; exact I | constructor ].
  - specialize (IHe (Some b) RUnaryOperand (S b)).
    pose proof (number_expr_span e (Some b) RUnaryOperand (S b)) as Hsp.
    destruct (number_expr (Some b) RUnaryOperand (S b) e) as [kc nxt].
    destruct Hsp as [n1 [_ [Hnxt Hn1pos]]]. cbn [fst snd] in IHe, Hnxt |- *.
    constructor.
    + cbn [fst snd edge_wf requires_first_edge c_view c_children first_child_wf]. split; [ reflexivity | lia ].
    + exact IHe.
  - specialize (IHe (Some b) RApplicationHead (S b)).
    pose proof (number_expr_span e (Some b) RApplicationHead (S b)) as Hsph.
    destruct (number_expr (Some b) RApplicationHead (S b) e) as [hc b1].
    destruct Hsph as [nh [_ [Hb1 Hnhpos]]]. cbn [fst snd] in IHe, Hb1.
    assert (Hda : forall es, Forall (fun a => forall par role bb,
                     ewf (fst (number_expr par role bb a)) (snd (number_expr par role bb a))) es ->
      forall i0 bi, (let '(ac, bf, _) := (fix do_args (i bi : nat) (es : list Syntax.Expr) {struct es}
              : list (nat * Cell) * nat * list nat :=
              match es with
              | [] => ([], bi, [])
              | a :: rest =>
                  let '(ac, bi') := number_expr (Some b) (RApplicationArg i) bi a in
                  let '(rc, bf, roots) := do_args (S i) bi' rest in
                  (ac ++ rc, bf, bi :: roots)
              end) i0 bi es in ewf ac bf /\ bi <= bf)).
    { intros es Hall; induction Hall as [| a rest Ha Hrest IHrest]; intros i0 bi.
      - split; [ constructor | lia ].
      - pose proof (number_expr_span a (Some b) (RApplicationArg i0) bi) as [na [_ [Hbi' Hnapos]]].
        specialize (Ha (Some b) (RApplicationArg i0) bi).
        destruct (number_expr (Some b) (RApplicationArg i0) bi a) as [ac1 bi'].
        cbn [fst snd] in Ha, Hbi'.
        specialize (IHrest (S i0) bi').
        destruct ((fix do_args (i bi : nat) (es : list Syntax.Expr) {struct es} := _) (S i0) bi' rest)
          as [[rc bf] roots].
        destruct IHrest as [Hrcwf Hle2]. cbn [fst snd] in Hrcwf, Hle2 |- *.
        split.
        + apply Forall_app; split; [ eapply ewf_weaken; [ | exact Ha ]; lia | exact Hrcwf ].
        + lia. }
    specialize (Hda args H 0 b1).
    destruct ((fix do_args (i bi : nat) (es : list Syntax.Expr) {struct es} := _) 0 b1 args)
      as [[ac bfin] aroots].
    destruct Hda as [Hacwf Hble]. cbn [fst snd] in Hacwf, Hble |- *.
    constructor.
    + cbn [fst snd edge_wf requires_first_edge c_view c_children first_child_wf]. split; [ reflexivity | lia ].
    + apply Forall_app; split; [ eapply ewf_weaken; [ | exact IHe ]; lia | exact Hacwf ].
Qed.

(* every expression's children resolve back: each child position is a member whose parent edge is this cell *)
Lemma number_expr_cpo : forall e par role b, child_parent_ok (fst (number_expr par role b e)).
Proof.
  intro e; induction e using Syntax.Expr_ind'; intros par role b; cbn [number_expr].
  - cbn [number_leaf fst]. intros pos c Hin cp Hcp.
    destruct Hin as [Heq|[]]; inversion Heq; subst; cbn [c_children] in Hcp; destruct Hcp.
  - cbn [number_leaf fst]. intros pos c Hin cp Hcp.
    destruct Hin as [Heq|[]]; inversion Heq; subst; cbn [c_children] in Hcp; destruct Hcp.
  - specialize (IHe (Some b) RUnaryOperand (S b)).
    pose proof (number_expr_root e (Some b) RUnaryOperand (S b)) as [urest [urc [Huroot [_ [_ Hupar]]]]].
    destruct (number_expr (Some b) RUnaryOperand (S b) e) as [kc nxt].
    cbn [fst] in IHe, Huroot |- *.
    apply child_parent_ok_node.
    + cbn [c_children]. intros cp [Hcp|[]]; subst cp.
      exists urc. split; [ right; rewrite Huroot; left; reflexivity | exact Hupar ].
    + exact IHe.
  - specialize (IHe (Some b) RApplicationHead (S b)).
    pose proof (number_expr_root e (Some b) RApplicationHead (S b)) as [hrest [hrc [Hhroot [_ [_ Hhpar]]]]].
    destruct (number_expr (Some b) RApplicationHead (S b) e) as [hc b1].
    cbn [fst] in IHe, Hhroot.
    assert (Hda : forall es, Forall (fun a => forall par role bb,
                     child_parent_ok (fst (number_expr par role bb a))) es ->
      forall i0 bi, (let '(ac, _, roots) := (fix do_args (i bi : nat) (es : list Syntax.Expr) {struct es}
              : list (nat * Cell) * nat * list nat :=
              match es with
              | [] => ([], bi, [])
              | a :: rest =>
                  let '(ac, bi') := number_expr (Some b) (RApplicationArg i) bi a in
                  let '(rc, bf, roots) := do_args (S i) bi' rest in
                  (ac ++ rc, bf, bi :: roots)
              end) i0 bi es in
        child_parent_ok ac /\
        (forall ar, In ar roots -> exists cc, In (ar, cc) ac /\ c_parent cc = Some b))).
    { intros es Hall; induction Hall as [| a rest Ha Hrest IHrest]; intros i0 bi.
      - split; [ intros pos c Hin; destruct Hin | intros ar Har; destruct Har ].
      - pose proof (number_expr_root a (Some b) (RApplicationArg i0) bi) as [arest [arc [Haroot [_ [_ Hapar]]]]].
        specialize (Ha (Some b) (RApplicationArg i0) bi).
        destruct (number_expr (Some b) (RApplicationArg i0) bi a) as [ac1 bi'].
        cbn [fst] in Ha, Haroot.
        specialize (IHrest (S i0) bi').
        destruct ((fix do_args (i bi : nat) (es : list Syntax.Expr) {struct es} := _) (S i0) bi' rest)
          as [[rc bf] roots].
        destruct IHrest as [Hrcok Hroots]. cbn [fst snd] in Hrcok, Hroots |- *.
        split.
        + apply child_parent_ok_app; [ exact Ha | exact Hrcok ].
        + intros ar [Har|Har].
          * subst ar. exists arc.
            split; [ apply in_or_app; left; rewrite Haroot; left; reflexivity | exact Hapar ].
          * destruct (Hroots ar Har) as [cc [Hcc Hccpar]]. exists cc.
            split; [ apply in_or_app; right; exact Hcc | exact Hccpar ]. }
    specialize (Hda args H 0 b1).
    destruct ((fix do_args (i bi : nat) (es : list Syntax.Expr) {struct es} := _) 0 b1 args)
      as [[ac bfin] aroots].
    destruct Hda as [Hacok Haroots]. cbn [fst snd] in Hacok, Haroots |- *.
    apply child_parent_ok_node.
    + cbn [c_children]. intros cp [Hcp|Hcp].
      * subst cp. exists hrc.
        split; [ right; apply in_or_app; left; rewrite Hhroot; left; reflexivity | exact Hhpar ].
      * destruct (Haroots cp Hcp) as [cc [Hcc Hccpar]]. exists cc.
        split; [ right; apply in_or_app; right; exact Hcc | exact Hccpar ].
    + apply child_parent_ok_app; [ exact IHe | exact Hacok ].
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

(* the exact first-edge law over a whole file numbering: each required first edge is S-of-its-position, in range *)
Lemma span_final_ge : forall out b, spans out b -> b <= snd out.
Proof. intros out b [n [_ H]]; lia. Qed.

Lemma ewf_node : forall self cell kids bnd, edge_wf self cell bnd -> ewf kids bnd -> ewf ((self, cell) :: kids) bnd.
Proof. intros; constructor; assumption. Qed.

Lemma number_list_edge_wf {A} (f : nat -> A -> list (nat * Cell) * nat) :
  (forall b x, ewf (fst (f b x)) (snd (f b x))) ->
  (forall b x, b <= snd (f b x)) ->
  forall b xs, ewf (fst (fst (number_list f b xs))) (snd (fst (number_list f b xs)))
               /\ b <= snd (fst (number_list f b xs)).
Proof.
  intros Hf Hmono b xs; revert b; induction xs as [|x rest IH]; intro b.
  - cbn [number_list fst snd]. split; [ constructor | lia ].
  - cbn [number_list]. specialize (Hf b x); specialize (Hmono b x).
    destruct (f b x) as [xc b']. cbn [fst snd] in Hf, Hmono.
    specialize (IH b'). destruct (number_list f b' rest) as [[rc b''] roots].
    destruct IH as [Hrc Hle]. cbn [fst snd] in Hrc, Hle |- *.
    split; [ apply Forall_app; split; [ eapply ewf_weaken; [ | exact Hf ]; lia | exact Hrc ] | lia ].
Qed.

Lemma number_typeexpr_edge_wf : forall par role b t,
  ewf (fst (number_typeexpr par role b t)) (snd (number_typeexpr par role b t)).
Proof. intros; cbn [number_typeexpr number_leaf fst snd]; apply ewf_node;
  [ cbn [edge_wf requires_first_edge c_view]; exact I | constructor ]. Qed.
Lemma number_bindingname_edge_wf : forall par role b bn,
  ewf (fst (number_bindingname par role b bn)) (snd (number_bindingname par role b bn)).
Proof. intros; cbn [number_bindingname number_leaf fst snd]; apply ewf_node;
  [ cbn [edge_wf requires_first_edge c_view]; exact I | constructor ]. Qed.

Lemma number_opttype_edge_wf : forall par b ot,
  ewf (fst (fst (number_opttype par b ot))) (snd (fst (number_opttype par b ot))).
Proof.
  intros par b [t|]; cbn [number_opttype].
  - pose proof (number_typeexpr_edge_wf par RTypeUse b t) as Ht.
    destruct (number_typeexpr par RTypeUse b t) as [c b']. cbn [fst snd] in Ht |- *. exact Ht.
  - cbn [fst snd]. constructor.
Qed.

Lemma number_constspec_edge_wf : forall par role b cs,
  ewf (fst (number_constspec par role b cs)) (snd (number_constspec par role b cs)).
Proof.
  intros par role b cs. unfold number_constspec.
  destruct (number_list_edge_wf (number_bindingname (Some b) (RSpecName ConstSpecF))
        (fun bb x => number_bindingname_edge_wf (Some b) (RSpecName ConstSpecF) bb x)
        (fun bb x => span_final_ge _ _ (number_bindingname_spans (Some b) (RSpecName ConstSpecF) bb x))
        (S b) (Collections.ne_to_list (Syntax.const_names cs))) as [Hnc Hncle].
  destruct (number_list (number_bindingname (Some b) (RSpecName ConstSpecF)) (S b)
             (Collections.ne_to_list (Syntax.const_names cs))) as [[nc b1] nroots].
  cbn [fst snd] in Hnc, Hncle. destruct (Syntax.const_init cs) as [ot vals | ].
  - pose proof (number_opttype_edge_wf (Some b) b1 ot) as Hoc.
    pose proof (span_final_ge _ _ (number_opttype_span (Some b) b1 ot)) as Hocle.
    destruct (number_opttype (Some b) b1 ot) as [[oc b2] oroots]. cbn [fst snd] in Hoc, Hocle.
    destruct (number_list_edge_wf (number_expr (Some b) RPlain)
        (fun bb x => number_expr_edge_wf x (Some b) RPlain bb)
        (fun bb x => span_final_ge _ _ (number_expr_spans x (Some b) RPlain bb))
        b2 (Collections.ne_to_list vals)) as [Hvc Hvcle].
    destruct (number_list (number_expr (Some b) RPlain) b2 (Collections.ne_to_list vals)) as [[vc b3] vroots].
    cbn [fst snd] in Hvc, Hvcle |- *.
    apply ewf_node; [ cbn [edge_wf requires_first_edge c_view]; exact I | ].
    apply Forall_app; split; [ eapply ewf_weaken; [ | exact Hnc ]; lia
      | apply Forall_app; split; [ eapply ewf_weaken; [ | exact Hoc ]; lia | exact Hvc ] ].
  - cbn [fst snd] in *. apply ewf_node; [ cbn [edge_wf requires_first_edge c_view]; exact I | ].
    apply Forall_app; split; [ exact Hnc | constructor ].
Qed.

Lemma number_varspec_edge_wf : forall par role b vs,
  ewf (fst (number_varspec par role b vs)) (snd (number_varspec par role b vs)).
Proof.
  intros par role b vs. unfold number_varspec.
  destruct (number_list_edge_wf (number_bindingname (Some b) (RSpecName VarSpecF))
        (fun bb x => number_bindingname_edge_wf (Some b) (RSpecName VarSpecF) bb x)
        (fun bb x => span_final_ge _ _ (number_bindingname_spans (Some b) (RSpecName VarSpecF) bb x))
        (S b) (Collections.ne_to_list (Syntax.var_names vs))) as [Hnc Hncle].
  destruct (number_list (number_bindingname (Some b) (RSpecName VarSpecF)) (S b)
             (Collections.ne_to_list (Syntax.var_names vs))) as [[nc b1] nroots].
  cbn [fst snd] in Hnc, Hncle. destruct (Syntax.var_init vs) as [t | ot vals].
  - pose proof (number_typeexpr_edge_wf (Some b) RTypeUse b1 t) as Ht.
    pose proof (span_final_ge _ _ (number_typeexpr_spans (Some b) RTypeUse b1 t)) as Htle.
    destruct (number_typeexpr (Some b) RTypeUse b1 t) as [c b2]. cbn [fst snd] in Ht, Htle |- *.
    apply ewf_node; [ cbn [edge_wf requires_first_edge c_view]; exact I | ].
    apply Forall_app; split; [ eapply ewf_weaken; [ | exact Hnc ]; lia | exact Ht ].
  - pose proof (number_opttype_edge_wf (Some b) b1 ot) as Hoc.
    pose proof (span_final_ge _ _ (number_opttype_span (Some b) b1 ot)) as Hocle.
    destruct (number_opttype (Some b) b1 ot) as [[oc b2] oroots]. cbn [fst snd] in Hoc, Hocle.
    destruct (number_list_edge_wf (number_expr (Some b) RPlain)
        (fun bb x => number_expr_edge_wf x (Some b) RPlain bb)
        (fun bb x => span_final_ge _ _ (number_expr_spans x (Some b) RPlain bb))
        b2 (Collections.ne_to_list vals)) as [Hvc Hvcle].
    destruct (number_list (number_expr (Some b) RPlain) b2 (Collections.ne_to_list vals)) as [[vc b3] vroots].
    cbn [fst snd] in Hvc, Hvcle |- *.
    apply ewf_node; [ cbn [edge_wf requires_first_edge c_view]; exact I | ].
    apply Forall_app; split; [ eapply ewf_weaken; [ | exact Hnc ]; lia
      | apply Forall_app; split; [ eapply ewf_weaken; [ | exact Hoc ]; lia | exact Hvc ] ].
Qed.

Lemma number_typespec_edge_wf : forall par role b ts,
  ewf (fst (number_typespec par role b ts)) (snd (number_typespec par role b ts)).
Proof.
  intros par role b ts. unfold number_typespec; destruct ts as [bn t | bn t];
  ( pose proof (number_bindingname_edge_wf (Some b) (RSpecName TypeSpecF) (S b) bn) as Hbc;
    pose proof (span_final_ge _ _ (number_bindingname_spans (Some b) (RSpecName TypeSpecF) (S b) bn)) as Hbcle;
    destruct (number_bindingname (Some b) (RSpecName TypeSpecF) (S b) bn) as [bc b1]; cbn [fst snd] in Hbc, Hbcle;
    pose proof (number_typeexpr_edge_wf (Some b) RTypeUse b1 t) as Htc;
    pose proof (span_final_ge _ _ (number_typeexpr_spans (Some b) RTypeUse b1 t)) as Htcle;
    destruct (number_typeexpr (Some b) RTypeUse b1 t) as [tc bfin]; cbn [fst snd] in Htc, Htcle |- *;
    apply ewf_node; [ cbn [edge_wf requires_first_edge c_view]; exact I | ];
    apply Forall_app; split; [ eapply ewf_weaken; [ | exact Hbc ]; lia | exact Htc ] ).
Qed.

Lemma number_decl_edge_wf : forall par role b d,
  ewf (fst (number_decl par role b d)) (snd (number_decl par role b d)).
Proof.
  intros par role b d. unfold number_decl; destruct d as [cs | vs | ts].
  - destruct (number_list_edge_wf (number_constspec (Some b) RPlain)
        (fun bb x => number_constspec_edge_wf (Some b) RPlain bb x)
        (fun bb x => span_final_ge _ _ (number_constspec_span (Some b) RPlain bb x)) (S b) cs) as [Hk _].
    destruct (number_list (number_constspec (Some b) RPlain) (S b) cs) as [[kc bfin] roots].
    cbn [fst snd] in Hk |- *. apply ewf_node; [ cbn [edge_wf requires_first_edge c_view]; exact I | exact Hk ].
  - destruct (number_list_edge_wf (number_varspec (Some b) RPlain)
        (fun bb x => number_varspec_edge_wf (Some b) RPlain bb x)
        (fun bb x => span_final_ge _ _ (number_varspec_span (Some b) RPlain bb x)) (S b) vs) as [Hk _].
    destruct (number_list (number_varspec (Some b) RPlain) (S b) vs) as [[kc bfin] roots].
    cbn [fst snd] in Hk |- *. apply ewf_node; [ cbn [edge_wf requires_first_edge c_view]; exact I | exact Hk ].
  - destruct (number_list_edge_wf (number_typespec (Some b) RPlain)
        (fun bb x => number_typespec_edge_wf (Some b) RPlain bb x)
        (fun bb x => span_final_ge _ _ (number_typespec_span (Some b) RPlain bb x)) (S b) ts) as [Hk _].
    destruct (number_list (number_typespec (Some b) RPlain) (S b) ts) as [[kc bfin] roots].
    cbn [fst snd] in Hk |- *. apply ewf_node; [ cbn [edge_wf requires_first_edge c_view]; exact I | exact Hk ].
Qed.

Lemma number_stmt_edge_wf : forall par role b s,
  ewf (fst (number_stmt par role b s)) (snd (number_stmt par role b s)).
Proof.
  intros par role b s. unfold number_stmt; destruct s as [e | d | names vals].
  - pose proof (number_expr_edge_wf e (Some b) RExprStatementExpr (S b)) as He.
    pose proof (number_expr_span e (Some b) RExprStatementExpr (S b)) as [ne [_ [Hb' Hnepos]]].
    destruct (number_expr (Some b) RExprStatementExpr (S b) e) as [c b']. cbn [fst snd] in He, Hb' |- *.
    apply ewf_node; [ cbn [fst snd edge_wf requires_first_edge c_view c_children first_child_wf];
      split; [ reflexivity | lia ] | exact He ].
  - pose proof (number_decl_edge_wf (Some b) RPlain (S b) d) as Hd.
    destruct (number_decl (Some b) RPlain (S b) d) as [c b']. cbn [fst snd] in Hd |- *.
    apply ewf_node; [ cbn [edge_wf requires_first_edge c_view]; exact I | exact Hd ].
  - destruct (number_list_edge_wf (number_bindingname (Some b) RShortLhs)
        (fun bb x => number_bindingname_edge_wf (Some b) RShortLhs bb x)
        (fun bb x => span_final_ge _ _ (number_bindingname_spans (Some b) RShortLhs bb x))
        (S b) (Collections.ne_to_list names)) as [Hnc Hncle].
    destruct (number_list (number_bindingname (Some b) RShortLhs) (S b) (Collections.ne_to_list names)) as [[nc b1] nroots].
    cbn [fst snd] in Hnc, Hncle.
    destruct (number_list_edge_wf (number_expr (Some b) RPlain)
        (fun bb x => number_expr_edge_wf x (Some b) RPlain bb)
        (fun bb x => span_final_ge _ _ (number_expr_spans x (Some b) RPlain bb))
        b1 (Collections.ne_to_list vals)) as [Hvc Hvcle].
    destruct (number_list (number_expr (Some b) RPlain) b1 (Collections.ne_to_list vals)) as [[vc b2] vroots].
    cbn [fst snd] in Hvc, Hvcle |- *.
    apply ewf_node; [ cbn [edge_wf requires_first_edge c_view]; exact I | ].
    apply Forall_app; split; [ eapply ewf_weaken; [ | exact Hnc ]; lia | exact Hvc ].
Qed.

Lemma number_block_edge_wf : forall par role b blk,
  ewf (fst (number_block par role b blk)) (snd (number_block par role b blk)).
Proof.
  intros par role b [stmts]. unfold number_block.
  destruct (number_list_edge_wf (number_stmt (Some b) RPlain)
      (fun bb x => number_stmt_edge_wf (Some b) RPlain bb x)
      (fun bb x => span_final_ge _ _ (number_stmt_span (Some b) RPlain bb x)) (S b) stmts) as [Hk _].
  destruct (number_list (number_stmt (Some b) RPlain) (S b) stmts) as [[kc bfin] roots].
  cbn [fst snd] in Hk |- *. apply ewf_node; [ cbn [edge_wf requires_first_edge c_view]; exact I | exact Hk ].
Qed.

Lemma number_toplevel_edge_wf : forall par role b td,
  ewf (fst (number_toplevel par role b td)) (snd (number_toplevel par role b td)).
Proof.
  intros par role b td. unfold number_toplevel; destruct td as [d | blk].
  - pose proof (number_decl_edge_wf (Some b) RPlain (S b) d) as Hd.
    destruct (number_decl (Some b) RPlain (S b) d) as [c b']. cbn [fst snd] in Hd |- *.
    apply ewf_node; [ cbn [edge_wf requires_first_edge c_view]; exact I | exact Hd ].
  - pose proof (number_block_edge_wf (Some b) RPlain (S b) blk) as Hb.
    destruct (number_block (Some b) RPlain (S b) blk) as [c b']. cbn [fst snd] in Hb |- *.
    apply ewf_node; [ cbn [edge_wf requires_first_edge c_view]; exact I | exact Hb ].
Qed.

Lemma number_file_edge_wf : forall f, ewf (number_file f) (length (number_file f)).
Proof.
  intro f. unfold number_file.
  destruct (number_list_edge_wf (number_toplevel (Some 0) RPlain)
      (fun bb x => number_toplevel_edge_wf (Some 0) RPlain bb x)
      (fun bb x => span_final_ge _ _ (number_toplevel_span (Some 0) RPlain bb x)) 1 (Syntax.declarations f)) as [Hd _].
  pose proof (number_list_span (number_toplevel (Some 0) RPlain)
      (fun bb x => number_toplevel_span (Some 0) RPlain bb x) (Syntax.declarations f) 1) as Hsp.
  destruct (number_list (number_toplevel (Some 0) RPlain) 1 (Syntax.declarations f)) as [[dc bfin] droots].
  cbn [fst snd] in Hd, Hsp. destruct Hsp as [ntop [Hmap Hbfin]]. cbn [fst snd] in Hmap, Hbfin.
  assert (Hlen : length dc = ntop).
  { apply (f_equal (@length nat)) in Hmap.
    first [ rewrite length_map in Hmap | rewrite map_length in Hmap ];
    first [ rewrite length_seq in Hmap | rewrite seq_length in Hmap ]; exact Hmap. }
  cbn [length]. apply ewf_node; [ cbn [edge_wf requires_first_edge c_view]; exact I | ].
  eapply ewf_weaken; [ | exact Hd ]. lia.
Qed.

(* [roots_resolve occs self roots]: every root position is a member of [occs] whose parent edge is [self] *)
Definition roots_resolve (occs : list (nat * Cell)) (self : nat) (roots : list nat) : Prop :=
  forall ar, In ar roots -> exists cc, In (ar, cc) occs /\ c_parent cc = Some self.

Lemma roots_resolve_app_l : forall occs extra self roots,
  roots_resolve occs self roots -> roots_resolve (occs ++ extra) self roots.
Proof.
  intros occs extra self roots H ar Har. destruct (H ar Har) as [cc [Hin Hpar]].
  exists cc. split; [ apply in_or_app; left; exact Hin | exact Hpar ].
Qed.

Lemma roots_resolve_app_r : forall occs extra self roots,
  roots_resolve occs self roots -> roots_resolve (extra ++ occs) self roots.
Proof.
  intros occs extra self roots H ar Har. destruct (H ar Har) as [cc [Hin Hpar]].
  exists cc. split; [ apply in_or_app; right; exact Hin | exact Hpar ].
Qed.

Lemma roots_resolve_concat : forall occs self r1 r2,
  roots_resolve occs self r1 -> roots_resolve occs self r2 -> roots_resolve occs self (r1 ++ r2).
Proof.
  intros occs self r1 r2 H1 H2 ar Har. apply in_app_or in Har.
  destruct Har as [Har|Har]; [ apply H1 | apply H2 ]; exact Har.
Qed.

Lemma cpo_node : forall self cell kids,
  roots_resolve kids self (c_children cell) ->
  child_parent_ok kids -> child_parent_ok ((self, cell) :: kids).
Proof.
  intros self cell kids Hres Hkids. apply child_parent_ok_node; [ | exact Hkids ].
  intros cp Hcp. destruct (Hres cp Hcp) as [cc [Hin Hpar]]. exists cc. split; [ right; exact Hin | exact Hpar ].
Qed.

(* one sublist numbered by [g]: its cells resolve internally and its roots point back to the shared parent *)
Lemma number_list_cpo {A} (g : nat -> A -> list (nat * Cell) * nat) (par : nat) :
  (forall b x, child_parent_ok (fst (g b x))) ->
  (forall b x, exists cc rest, fst (g b x) = (b, cc) :: rest /\ c_parent cc = Some par) ->
  forall b xs,
    child_parent_ok (fst (fst (number_list g b xs))) /\
    roots_resolve (fst (fst (number_list g b xs))) par (snd (number_list g b xs)).
Proof.
  intros Hcpo Hroot b xs; revert b; induction xs as [|x rest IH]; intro b.
  - cbn [number_list fst snd]. split; [ intros pos c Hin; destruct Hin | intros ar Har; destruct Har ].
  - cbn [number_list].
    pose proof (Hroot b x) as [rc [rest' [Hgx Hrcpar]]].
    specialize (Hcpo b x). destruct (g b x) as [xc b']. cbn [fst] in Hcpo, Hgx.
    specialize (IH b'). destruct (number_list g b' rest) as [[rcl b''] roots].
    destruct IH as [Hcpol Hresl]. cbn [fst snd] in Hcpol, Hresl |- *.
    split.
    + apply child_parent_ok_app; [ exact Hcpo | exact Hcpol ].
    + intros ar [Har|Har].
      * subst ar. exists rc. split; [ apply in_or_app; left; rewrite Hgx; left; reflexivity | exact Hrcpar ].
      * destruct (Hresl ar Har) as [cc [Hin Hpar]].
        exists cc. split; [ apply in_or_app; right; exact Hin | exact Hpar ].
Qed.

(* each composite occurrence begins with its own cell, carrying the passed parent edge — the root fact *)
Lemma number_expr_root' : forall par role b e,
  exists cc rest, fst (number_expr par role b e) = (b, cc) :: rest /\ c_parent cc = par.
Proof.
  intros. destruct (number_expr_root e par role b) as [rest [rc [H [_ [_ Hpar]]]]].
  exists rc, rest. split; [ exact H | exact Hpar ].
Qed.

Lemma number_typeexpr_root : forall par role b t,
  exists cc rest, fst (number_typeexpr par role b t) = (b, cc) :: rest /\ c_parent cc = par.
Proof. intros. cbn [number_typeexpr number_leaf fst]. do 2 eexists; split; reflexivity. Qed.

Lemma number_bindingname_root : forall par role b bn,
  exists cc rest, fst (number_bindingname par role b bn) = (b, cc) :: rest /\ c_parent cc = par.
Proof. intros. cbn [number_bindingname number_leaf fst]. do 2 eexists; split; reflexivity. Qed.

Lemma number_constspec_root : forall par role b cs,
  exists cc rest, fst (number_constspec par role b cs) = (b, cc) :: rest /\ c_parent cc = par.
Proof.
  intros par role b cs. unfold number_constspec.
  destruct (number_list (number_bindingname (Some b) (RSpecName ConstSpecF)) (S b)
             (Collections.ne_to_list (Syntax.const_names cs))) as [[nc b1] nroots].
  destruct (Syntax.const_init cs) as [ot vals|].
  - destruct (number_opttype (Some b) b1 ot) as [[oc b2] oroots].
    destruct (number_list (number_expr (Some b) RPlain) b2 (Collections.ne_to_list vals)) as [[vc b3] vroots].
    cbn [fst]. do 2 eexists; split; reflexivity.
  - cbn [fst]. do 2 eexists; split; reflexivity.
Qed.

Lemma number_varspec_root : forall par role b vs,
  exists cc rest, fst (number_varspec par role b vs) = (b, cc) :: rest /\ c_parent cc = par.
Proof.
  intros par role b vs. unfold number_varspec.
  destruct (number_list (number_bindingname (Some b) (RSpecName VarSpecF)) (S b)
             (Collections.ne_to_list (Syntax.var_names vs))) as [[nc b1] nroots].
  destruct (Syntax.var_init vs) as [t | ot vals].
  - destruct (number_typeexpr (Some b) RTypeUse b1 t) as [tc b2].
    cbn [fst]. do 2 eexists; split; reflexivity.
  - destruct (number_opttype (Some b) b1 ot) as [[oc b2] oroots].
    destruct (number_list (number_expr (Some b) RPlain) b2 (Collections.ne_to_list vals)) as [[vc b3] vroots].
    cbn [fst]. do 2 eexists; split; reflexivity.
Qed.

Lemma number_typespec_root : forall par role b ts,
  exists cc rest, fst (number_typespec par role b ts) = (b, cc) :: rest /\ c_parent cc = par.
Proof.
  intros par role b ts. unfold number_typespec; destruct ts as [bn t|bn t];
    (destruct (number_bindingname (Some b) (RSpecName TypeSpecF) (S b) bn) as [bc b1];
     destruct (number_typeexpr (Some b) RTypeUse b1 t) as [tc bfin];
     cbn [fst]; do 2 eexists; split; reflexivity).
Qed.

Lemma number_decl_root : forall par role b d,
  exists cc rest, fst (number_decl par role b d) = (b, cc) :: rest /\ c_parent cc = par.
Proof.
  intros par role b d. unfold number_decl.
  destruct d as [cs|vs|ts];
    [ destruct (number_list (number_constspec (Some b) RPlain) (S b) cs) as [[kc bfin] roots]
    | destruct (number_list (number_varspec (Some b) RPlain) (S b) vs) as [[kc bfin] roots]
    | destruct (number_list (number_typespec (Some b) RPlain) (S b) ts) as [[kc bfin] roots] ];
    cbn [fst]; do 2 eexists; split; reflexivity.
Qed.

Lemma number_stmt_root : forall par role b s,
  exists cc rest, fst (number_stmt par role b s) = (b, cc) :: rest /\ c_parent cc = par.
Proof.
  intros par role b s. unfold number_stmt.
  destruct s as [e|d|names vals];
    [ destruct (number_expr (Some b) RExprStatementExpr (S b) e) as [c b']
    | destruct (number_decl (Some b) RPlain (S b) d) as [c b']
    | destruct (number_list (number_bindingname (Some b) RShortLhs) (S b) (Collections.ne_to_list names)) as [[nc b1] nroots];
      destruct (number_list (number_expr (Some b) RPlain) b1 (Collections.ne_to_list vals)) as [[vc b2] vroots] ];
    cbn [fst]; do 2 eexists; split; reflexivity.
Qed.

Lemma number_block_root : forall par role b blk,
  exists cc rest, fst (number_block par role b blk) = (b, cc) :: rest /\ c_parent cc = par.
Proof.
  intros par role b [stmts]. unfold number_block.
  destruct (number_list (number_stmt (Some b) RPlain) (S b) stmts) as [[kc bfin] roots].
  cbn [fst]. do 2 eexists; split; reflexivity.
Qed.

Lemma number_toplevel_root : forall par role b td,
  exists cc rest, fst (number_toplevel par role b td) = (b, cc) :: rest /\ c_parent cc = par.
Proof.
  intros par role b td. unfold number_toplevel.
  destruct td as [d|blk];
    [ destruct (number_decl (Some b) RPlain (S b) d) as [c b']
    | destruct (number_block (Some b) RPlain (S b) blk) as [c b'] ];
    cbn [fst]; do 2 eexists; split; reflexivity.
Qed.

Lemma number_typeexpr_cpo : forall par role b t, child_parent_ok (fst (number_typeexpr par role b t)).
Proof.
  intros. cbn [number_typeexpr number_leaf fst]. intros pos c Hin cp Hcp.
  destruct Hin as [Heq|[]]; inversion Heq; subst; cbn [c_children] in Hcp; destruct Hcp.
Qed.

Lemma number_bindingname_cpo : forall par role b bn, child_parent_ok (fst (number_bindingname par role b bn)).
Proof.
  intros. cbn [number_bindingname number_leaf fst]. intros pos c Hin cp Hcp.
  destruct Hin as [Heq|[]]; inversion Heq; subst; cbn [c_children] in Hcp; destruct Hcp.
Qed.

Lemma number_opttype_cpo : forall self b ot,
  child_parent_ok (fst (fst (number_opttype (Some self) b ot))) /\
  roots_resolve (fst (fst (number_opttype (Some self) b ot))) self (snd (number_opttype (Some self) b ot)).
Proof.
  intros self b ot. destruct ot as [t|].
  - cbn [number_opttype].
    pose proof (number_typeexpr_cpo (Some self) RTypeUse b t) as Hc.
    pose proof (number_typeexpr_root (Some self) RTypeUse b t) as [rc [rest [Hr Hpar]]].
    destruct (number_typeexpr (Some self) RTypeUse b t) as [tc b'].
    cbn [fst snd] in Hc, Hr |- *. split.
    + exact Hc.
    + intros ar [Har|[]]. subst ar. exists rc. split; [ rewrite Hr; left; reflexivity | exact Hpar ].
  - cbn [number_opttype fst snd]. split; [ intros pos c Hin; destruct Hin | intros ar Har; destruct Har ].
Qed.

Lemma number_constspec_cpo : forall par role b cs, child_parent_ok (fst (number_constspec par role b cs)).
Proof.
  intros par role b cs. unfold number_constspec.
  destruct (number_list_cpo (number_bindingname (Some b) (RSpecName ConstSpecF)) b
             (fun bb x => number_bindingname_cpo (Some b) (RSpecName ConstSpecF) bb x)
             (fun bb x => number_bindingname_root (Some b) (RSpecName ConstSpecF) bb x)
             (S b) (Collections.ne_to_list (Syntax.const_names cs))) as [Hnc_cpo Hnc_res].
  destruct (number_list (number_bindingname (Some b) (RSpecName ConstSpecF)) (S b)
             (Collections.ne_to_list (Syntax.const_names cs))) as [[nc b1] nroots].
  cbn [fst snd] in Hnc_cpo, Hnc_res.
  destruct (Syntax.const_init cs) as [ot vals|].
  - pose proof (number_opttype_cpo b b1 ot) as [Hoc_cpo Hoc_res].
    destruct (number_opttype (Some b) b1 ot) as [[oc b2] oroots]. cbn [fst snd] in Hoc_cpo, Hoc_res.
    destruct (number_list_cpo (number_expr (Some b) RPlain) b
               (fun bb x => number_expr_cpo x (Some b) RPlain bb)
               (fun bb x => number_expr_root' (Some b) RPlain bb x)
               b2 (Collections.ne_to_list vals)) as [Hvc_cpo Hvc_res].
    destruct (number_list (number_expr (Some b) RPlain) b2 (Collections.ne_to_list vals)) as [[vc b3] vroots].
    cbn [fst snd] in Hvc_cpo, Hvc_res. cbn [fst]. apply cpo_node.
    + cbn [c_children]. apply roots_resolve_concat.
      * apply roots_resolve_app_l. exact Hnc_res.
      * apply roots_resolve_app_r. apply roots_resolve_concat;
          [ apply roots_resolve_app_l; exact Hoc_res | apply roots_resolve_app_r; exact Hvc_res ].
    + apply child_parent_ok_app; [ exact Hnc_cpo | apply child_parent_ok_app; [ exact Hoc_cpo | exact Hvc_cpo ] ].
  - cbn [fst]. apply cpo_node.
    + cbn [c_children]. rewrite !app_nil_r. exact Hnc_res.
    + rewrite app_nil_r. exact Hnc_cpo.
Qed.

Lemma number_varspec_cpo : forall par role b vs, child_parent_ok (fst (number_varspec par role b vs)).
Proof.
  intros par role b vs. unfold number_varspec.
  destruct (number_list_cpo (number_bindingname (Some b) (RSpecName VarSpecF)) b
             (fun bb x => number_bindingname_cpo (Some b) (RSpecName VarSpecF) bb x)
             (fun bb x => number_bindingname_root (Some b) (RSpecName VarSpecF) bb x)
             (S b) (Collections.ne_to_list (Syntax.var_names vs))) as [Hnc_cpo Hnc_res].
  destruct (number_list (number_bindingname (Some b) (RSpecName VarSpecF)) (S b)
             (Collections.ne_to_list (Syntax.var_names vs))) as [[nc b1] nroots].
  cbn [fst snd] in Hnc_cpo, Hnc_res.
  destruct (Syntax.var_init vs) as [t | ot vals].
  - pose proof (number_typeexpr_cpo (Some b) RTypeUse b1 t) as Htc_cpo.
    pose proof (number_typeexpr_root (Some b) RTypeUse b1 t) as [tc0 [trest [Htr Htpar]]].
    destruct (number_typeexpr (Some b) RTypeUse b1 t) as [tc b2].
    cbn [fst] in Htc_cpo, Htr. cbn [fst]. apply cpo_node.
    + cbn [c_children]. apply roots_resolve_concat.
      * apply roots_resolve_app_l. exact Hnc_res.
      * apply roots_resolve_app_r. intros ar [Har|[]]. subst ar. exists tc0.
        split; [ rewrite Htr; left; reflexivity | exact Htpar ].
    + apply child_parent_ok_app; [ exact Hnc_cpo | exact Htc_cpo ].
  - pose proof (number_opttype_cpo b b1 ot) as [Hoc_cpo Hoc_res].
    destruct (number_opttype (Some b) b1 ot) as [[oc b2] oroots]. cbn [fst snd] in Hoc_cpo, Hoc_res.
    destruct (number_list_cpo (number_expr (Some b) RPlain) b
               (fun bb x => number_expr_cpo x (Some b) RPlain bb)
               (fun bb x => number_expr_root' (Some b) RPlain bb x)
               b2 (Collections.ne_to_list vals)) as [Hvc_cpo Hvc_res].
    destruct (number_list (number_expr (Some b) RPlain) b2 (Collections.ne_to_list vals)) as [[vc b3] vroots].
    cbn [fst snd] in Hvc_cpo, Hvc_res. cbn [fst]. apply cpo_node.
    + cbn [c_children]. apply roots_resolve_concat.
      * apply roots_resolve_app_l. exact Hnc_res.
      * apply roots_resolve_app_r. apply roots_resolve_concat;
          [ apply roots_resolve_app_l; exact Hoc_res | apply roots_resolve_app_r; exact Hvc_res ].
    + apply child_parent_ok_app; [ exact Hnc_cpo | apply child_parent_ok_app; [ exact Hoc_cpo | exact Hvc_cpo ] ].
Qed.

Lemma number_typespec_cpo : forall par role b ts, child_parent_ok (fst (number_typespec par role b ts)).
Proof.
  intros par role b ts. unfold number_typespec; destruct ts as [bn t|bn t];
  ( pose proof (number_bindingname_cpo (Some b) (RSpecName TypeSpecF) (S b) bn) as Hbc_cpo;
    pose proof (number_bindingname_root (Some b) (RSpecName TypeSpecF) (S b) bn) as [bc0 [brest [Hbr Hbpar]]];
    destruct (number_bindingname (Some b) (RSpecName TypeSpecF) (S b) bn) as [bc b1];
    cbn [fst] in Hbc_cpo, Hbr;
    pose proof (number_typeexpr_cpo (Some b) RTypeUse b1 t) as Htc_cpo;
    pose proof (number_typeexpr_root (Some b) RTypeUse b1 t) as [tc0 [trest [Htr Htpar]]];
    destruct (number_typeexpr (Some b) RTypeUse b1 t) as [tc bfin];
    cbn [fst] in Htc_cpo, Htr; cbn [fst]; apply cpo_node;
    [ cbn [c_children]; intros ar Har; destruct Har as [Har|[Har|[]]];
      [ subst ar; exists bc0; split; [ apply in_or_app; left; rewrite Hbr; left; reflexivity | exact Hbpar ]
      | subst ar; exists tc0; split; [ apply in_or_app; right; rewrite Htr; left; reflexivity | exact Htpar ] ]
    | apply child_parent_ok_app; [ exact Hbc_cpo | exact Htc_cpo ] ] ).
Qed.

Lemma number_decl_cpo : forall par role b d, child_parent_ok (fst (number_decl par role b d)).
Proof.
  intros par role b d. unfold number_decl. destruct d as [cs|vs|ts].
  - destruct (number_list_cpo (number_constspec (Some b) RPlain) b
        (fun bb x => number_constspec_cpo (Some b) RPlain bb x)
        (fun bb x => number_constspec_root (Some b) RPlain bb x) (S b) cs) as [Hk_cpo Hk_res].
    destruct (number_list (number_constspec (Some b) RPlain) (S b) cs) as [[kc bfin] roots].
    cbn [fst snd] in Hk_cpo, Hk_res. cbn [fst]. apply cpo_node; [ cbn [c_children]; exact Hk_res | exact Hk_cpo ].
  - destruct (number_list_cpo (number_varspec (Some b) RPlain) b
        (fun bb x => number_varspec_cpo (Some b) RPlain bb x)
        (fun bb x => number_varspec_root (Some b) RPlain bb x) (S b) vs) as [Hk_cpo Hk_res].
    destruct (number_list (number_varspec (Some b) RPlain) (S b) vs) as [[kc bfin] roots].
    cbn [fst snd] in Hk_cpo, Hk_res. cbn [fst]. apply cpo_node; [ cbn [c_children]; exact Hk_res | exact Hk_cpo ].
  - destruct (number_list_cpo (number_typespec (Some b) RPlain) b
        (fun bb x => number_typespec_cpo (Some b) RPlain bb x)
        (fun bb x => number_typespec_root (Some b) RPlain bb x) (S b) ts) as [Hk_cpo Hk_res].
    destruct (number_list (number_typespec (Some b) RPlain) (S b) ts) as [[kc bfin] roots].
    cbn [fst snd] in Hk_cpo, Hk_res. cbn [fst]. apply cpo_node; [ cbn [c_children]; exact Hk_res | exact Hk_cpo ].
Qed.

Lemma number_stmt_cpo : forall par role b s, child_parent_ok (fst (number_stmt par role b s)).
Proof.
  intros par role b s. unfold number_stmt. destruct s as [e|d|names vals].
  - pose proof (number_expr_cpo e (Some b) RExprStatementExpr (S b)) as Hc_cpo.
    pose proof (number_expr_root' (Some b) RExprStatementExpr (S b) e) as [c0 [crest [Hcr Hcpar]]].
    destruct (number_expr (Some b) RExprStatementExpr (S b) e) as [c b'].
    cbn [fst] in Hc_cpo, Hcr. cbn [fst]. apply cpo_node.
    + cbn [c_children]. intros ar [Har|[]]. subst ar. exists c0.
      split; [ rewrite Hcr; left; reflexivity | exact Hcpar ].
    + exact Hc_cpo.
  - pose proof (number_decl_cpo (Some b) RPlain (S b) d) as Hc_cpo.
    pose proof (number_decl_root (Some b) RPlain (S b) d) as [c0 [crest [Hcr Hcpar]]].
    destruct (number_decl (Some b) RPlain (S b) d) as [c b'].
    cbn [fst] in Hc_cpo, Hcr. cbn [fst]. apply cpo_node.
    + cbn [c_children]. intros ar [Har|[]]. subst ar. exists c0.
      split; [ rewrite Hcr; left; reflexivity | exact Hcpar ].
    + exact Hc_cpo.
  - destruct (number_list_cpo (number_bindingname (Some b) RShortLhs) b
        (fun bb x => number_bindingname_cpo (Some b) RShortLhs bb x)
        (fun bb x => number_bindingname_root (Some b) RShortLhs bb x)
        (S b) (Collections.ne_to_list names)) as [Hnc_cpo Hnc_res].
    destruct (number_list (number_bindingname (Some b) RShortLhs) (S b) (Collections.ne_to_list names)) as [[nc b1] nroots].
    cbn [fst snd] in Hnc_cpo, Hnc_res.
    destruct (number_list_cpo (number_expr (Some b) RPlain) b
        (fun bb x => number_expr_cpo x (Some b) RPlain bb)
        (fun bb x => number_expr_root' (Some b) RPlain bb x)
        b1 (Collections.ne_to_list vals)) as [Hvc_cpo Hvc_res].
    destruct (number_list (number_expr (Some b) RPlain) b1 (Collections.ne_to_list vals)) as [[vc b2] vroots].
    cbn [fst snd] in Hvc_cpo, Hvc_res. cbn [fst]. apply cpo_node.
    + cbn [c_children]. apply roots_resolve_concat;
        [ apply roots_resolve_app_l; exact Hnc_res | apply roots_resolve_app_r; exact Hvc_res ].
    + apply child_parent_ok_app; [ exact Hnc_cpo | exact Hvc_cpo ].
Qed.

Lemma number_block_cpo : forall par role b blk, child_parent_ok (fst (number_block par role b blk)).
Proof.
  intros par role b [stmts]. unfold number_block.
  destruct (number_list_cpo (number_stmt (Some b) RPlain) b
      (fun bb x => number_stmt_cpo (Some b) RPlain bb x)
      (fun bb x => number_stmt_root (Some b) RPlain bb x) (S b) stmts) as [Hk_cpo Hk_res].
  destruct (number_list (number_stmt (Some b) RPlain) (S b) stmts) as [[kc bfin] roots].
  cbn [fst snd] in Hk_cpo, Hk_res. cbn [fst]. apply cpo_node; [ cbn [c_children]; exact Hk_res | exact Hk_cpo ].
Qed.

Lemma number_toplevel_cpo : forall par role b td, child_parent_ok (fst (number_toplevel par role b td)).
Proof.
  intros par role b td. unfold number_toplevel. destruct td as [d|blk].
  - pose proof (number_decl_cpo (Some b) RPlain (S b) d) as Hc_cpo.
    pose proof (number_decl_root (Some b) RPlain (S b) d) as [c0 [crest [Hcr Hcpar]]].
    destruct (number_decl (Some b) RPlain (S b) d) as [c b'].
    cbn [fst] in Hc_cpo, Hcr. cbn [fst]. apply cpo_node.
    + cbn [c_children]. intros ar [Har|[]]. subst ar. exists c0.
      split; [ rewrite Hcr; left; reflexivity | exact Hcpar ].
    + exact Hc_cpo.
  - pose proof (number_block_cpo (Some b) RPlain (S b) blk) as Hc_cpo.
    pose proof (number_block_root (Some b) RPlain (S b) blk) as [c0 [crest [Hcr Hcpar]]].
    destruct (number_block (Some b) RPlain (S b) blk) as [c b'].
    cbn [fst] in Hc_cpo, Hcr. cbn [fst]. apply cpo_node.
    + cbn [c_children]. intros ar [Har|[]]. subst ar. exists c0.
      split; [ rewrite Hcr; left; reflexivity | exact Hcpar ].
    + exact Hc_cpo.
Qed.

(* the whole-file parent inverse: every child position resolves to a member whose parent edge points back *)
Lemma number_file_cpo : forall f, child_parent_ok (number_file f).
Proof.
  intro f. unfold number_file.
  destruct (number_list_cpo (number_toplevel (Some 0) RPlain) 0
      (fun bb x => number_toplevel_cpo (Some 0) RPlain bb x)
      (fun bb x => number_toplevel_root (Some 0) RPlain bb x) 1 (Syntax.declarations f)) as [Hd_cpo Hd_res].
  destruct (number_list (number_toplevel (Some 0) RPlain) 1 (Syntax.declarations f)) as [[dc bfin] droots].
  cbn [fst snd] in Hd_cpo, Hd_res |- *. apply cpo_node; [ cbn [c_children]; exact Hd_res | exact Hd_cpo ].
Qed.

(* one root position per numbered element — the enumeration is a bijection onto the source list *)
Lemma number_list_roots_length {A} (g : nat -> A -> list (nat * Cell) * nat) :
  forall b xs, length (snd (number_list g b xs)) = length xs.
Proof.
  intros b xs; revert b; induction xs as [|x rest IH]; intro b; [ reflexivity | ].
  cbn [number_list]. destruct (g b x) as [xc b']. specialize (IH b').
  destruct (number_list g b' rest) as [[rc b''] roots]. cbn [snd length] in IH |- *.
  rewrite IH. reflexivity.
Qed.

(* file roots are exact: the file cell heads the traversal and lists exactly one child per top-level decl *)
Lemma number_file_roots_exact : forall f,
  exists filecell dc, number_file f = (0, filecell) :: dc
    /\ length (c_children filecell) = length (Syntax.declarations f).
Proof.
  intro f. unfold number_file.
  pose proof (number_list_roots_length (number_toplevel (Some 0) RPlain) 1 (Syntax.declarations f)) as Hlen.
  destruct (number_list (number_toplevel (Some 0) RPlain) 1 (Syntax.declarations f)) as [[dc bfin] droots].
  cbn [snd] in Hlen. exists (mkCell VFile RPlain None (bfin - 1) droots), dc.
  split; [ reflexivity | cbn [c_children]; exact Hlen ].
Qed.

(* every parent edge lands inside the block: [lo, pos) — no edge escapes below lo or forward past its child *)
Definition pbounds (lo : nat) (occs : list (nat * Cell)) : Prop :=
  forall pos cell, In (pos, cell) occs -> forall pp, c_parent cell = Some pp -> lo <= pp /\ pp < pos.

Lemma pbounds_app : forall lo c1 c2, pbounds lo c1 -> pbounds lo c2 -> pbounds lo (c1 ++ c2).
Proof.
  intros lo c1 c2 H1 H2 pos cell Hin pp Hpp. apply in_app_or in Hin.
  destruct Hin as [Hin|Hin]; [ apply (H1 pos cell Hin pp Hpp) | apply (H2 pos cell Hin pp Hpp) ].
Qed.

Lemma pbounds_weaken : forall lo hi occs, lo <= hi -> pbounds hi occs -> pbounds lo occs.
Proof.
  intros lo hi occs Hle H pos cell Hin pp Hpp. destruct (H pos cell Hin pp Hpp) as [Ha Hb]. split; [ lia | exact Hb ].
Qed.

Lemma pbounds_node : forall lo b rootcell subforest,
  c_parent rootcell = Some lo -> lo < b ->
  pbounds lo subforest -> pbounds lo ((b, rootcell) :: subforest).
Proof.
  intros lo b rootcell sf Hrp Hlt Hsf pos cell Hin pp Hpp. destruct Hin as [Heq|Hin].
  - inversion Heq; subst. rewrite Hrp in Hpp. inversion Hpp; subst. split; [ lia | exact Hlt ].
  - apply (Hsf pos cell Hin pp Hpp).
Qed.

(* the shared sublist form: with the parent below its first element, every element edge stays in [lo, pos) *)
Lemma number_list_pbounds {A} (g : nat -> A -> list (nat * Cell) * nat) (lo : nat) :
  (forall b x, lo < b -> pbounds lo (fst (g b x))) ->
  (forall b x, b <= snd (g b x)) ->
  forall b xs, lo < b -> pbounds lo (fst (fst (number_list g b xs))).
Proof.
  intros Hg Hmono b xs; revert b; induction xs as [|x rest IH]; intros b Hlt.
  - cbn [number_list fst snd]. intros pos cell Hin; destruct Hin.
  - cbn [number_list]. specialize (Hg b x Hlt). pose proof (Hmono b x) as Hm.
    destruct (g b x) as [xc b']. cbn [fst snd] in Hg, Hm.
    assert (Hlt' : lo < b') by lia.
    specialize (IH b' Hlt'). destruct (number_list g b' rest) as [[rc b''] roots].
    cbn [fst snd] in IH |- *. apply pbounds_app; [ exact Hg | exact IH ].
Qed.

Lemma number_expr_pbounds : forall e pv role b,
  pv < b -> pbounds pv (fst (number_expr (Some pv) role b e)).
Proof.
  intro e; induction e using Syntax.Expr_ind'; intros pv role b Hlt; cbn [number_expr].
  - cbn [number_leaf fst]. apply pbounds_node; [ reflexivity | exact Hlt | intros pos cell Hin; destruct Hin ].
  - cbn [number_leaf fst]. apply pbounds_node; [ reflexivity | exact Hlt | intros pos cell Hin; destruct Hin ].
  - specialize (IHe b RUnaryOperand (S b) (Nat.lt_succ_diag_r b)).
    destruct (number_expr (Some b) RUnaryOperand (S b) e) as [kc nxt]. cbn [fst] in IHe |- *.
    apply pbounds_node; [ reflexivity | exact Hlt | eapply pbounds_weaken; [ | exact IHe ]; lia ].
  - specialize (IHe b RApplicationHead (S b) (Nat.lt_succ_diag_r b)).
    pose proof (number_expr_span e (Some b) RApplicationHead (S b)) as [nh [_ [Hb1 _]]].
    destruct (number_expr (Some b) RApplicationHead (S b) e) as [hc b1]. cbn [fst snd] in IHe, Hb1.
    assert (Hda : forall es, Forall (fun a => forall pv role bb, pv < bb ->
                     pbounds pv (fst (number_expr (Some pv) role bb a))) es ->
      forall i0 bi, b < bi -> pbounds b (fst (fst ((fix do_args (i bi : nat) (es : list Syntax.Expr) {struct es}
              : list (nat * Cell) * nat * list nat :=
              match es with
              | [] => ([], bi, [])
              | a :: rest =>
                  let '(ac, bi') := number_expr (Some b) (RApplicationArg i) bi a in
                  let '(rc, bf, roots) := do_args (S i) bi' rest in
                  (ac ++ rc, bf, bi :: roots)
              end) i0 bi es)))).
    { intros es Hall; induction Hall as [| a rest Ha Hrest IHrest]; intros i0 bi Hbi.
      - cbn [number_list fst snd]. intros pos cell Hin; destruct Hin.
      - specialize (Ha b (RApplicationArg i0) bi Hbi).
        pose proof (number_expr_span a (Some b) (RApplicationArg i0) bi) as [na [_ [Hbi' _]]].
        destruct (number_expr (Some b) (RApplicationArg i0) bi a) as [ac1 bi'].
        cbn [fst snd] in Ha, Hbi'.
        assert (Hbi2 : b < bi') by lia.
        specialize (IHrest (S i0) bi' Hbi2).
        destruct ((fix do_args (i bi : nat) (es : list Syntax.Expr) {struct es} := _) (S i0) bi' rest)
          as [[rc bf] roots].
        cbn [fst snd] in IHrest |- *. apply pbounds_app; [ exact Ha | exact IHrest ]. }
    assert (Hb1' : b < b1) by lia.
    specialize (Hda args H 0 b1 Hb1').
    destruct ((fix do_args (i bi : nat) (es : list Syntax.Expr) {struct es} := _) 0 b1 args)
      as [[ac bfin] aroots].
    cbn [fst snd] in Hda |- *.
    apply pbounds_node; [ reflexivity | exact Hlt | ].
    apply pbounds_app; [ eapply pbounds_weaken; [ | exact IHe ]; lia
      | eapply pbounds_weaken; [ | exact Hda ]; lia ].
Qed.

Lemma number_typeexpr_pbounds : forall t pv role b, pv < b -> pbounds pv (fst (number_typeexpr (Some pv) role b t)).
Proof.
  intros t pv role b Hlt. cbn [number_typeexpr number_leaf fst].
  apply pbounds_node; [ reflexivity | exact Hlt | intros pos cell Hin; destruct Hin ].
Qed.

Lemma number_bindingname_pbounds : forall bn pv role b, pv < b -> pbounds pv (fst (number_bindingname (Some pv) role b bn)).
Proof.
  intros bn pv role b Hlt. cbn [number_bindingname number_leaf fst].
  apply pbounds_node; [ reflexivity | exact Hlt | intros pos cell Hin; destruct Hin ].
Qed.

Lemma number_opttype_pbounds : forall ot pv b, pv < b -> pbounds pv (fst (fst (number_opttype (Some pv) b ot))).
Proof.
  intros ot pv b Hlt. destruct ot as [t|].
  - cbn [number_opttype].
    pose proof (number_typeexpr_pbounds t pv RTypeUse b Hlt) as Ht.
    destruct (number_typeexpr (Some pv) RTypeUse b t) as [tc b']. cbn [fst] in Ht |- *. exact Ht.
  - cbn [number_opttype fst snd]. intros pos cell Hin; destruct Hin.
Qed.

Lemma number_constspec_pbounds : forall cs pv role b, pv < b -> pbounds pv (fst (number_constspec (Some pv) role b cs)).
Proof.
  intros cs pv role b Hlt. unfold number_constspec.
  pose proof (number_list_pbounds (number_bindingname (Some b) (RSpecName ConstSpecF)) b
      (fun bb x Hbb => number_bindingname_pbounds x b (RSpecName ConstSpecF) bb Hbb)
      (fun bb x => span_final_ge _ _ (number_bindingname_spans (Some b) (RSpecName ConstSpecF) bb x))
      (S b) (Collections.ne_to_list (Syntax.const_names cs)) (Nat.lt_succ_diag_r b)) as Hnc.
  pose proof (span_final_ge _ _ (number_list_span (number_bindingname (Some b) (RSpecName ConstSpecF))
      (fun bb x => number_bindingname_spans (Some b) (RSpecName ConstSpecF) bb x)
      (Collections.ne_to_list (Syntax.const_names cs)) (S b))) as Hb1.
  destruct (number_list (number_bindingname (Some b) (RSpecName ConstSpecF)) (S b)
      (Collections.ne_to_list (Syntax.const_names cs))) as [[nc b1] nroots].
  cbn [fst snd] in Hnc, Hb1.
  destruct (Syntax.const_init cs) as [ot vals|].
  - assert (Hb1lt : b < b1) by lia.
    pose proof (number_opttype_pbounds ot b b1 Hb1lt) as Hoc.
    pose proof (span_final_ge _ _ (number_opttype_span (Some b) b1 ot)) as Hb2.
    destruct (number_opttype (Some b) b1 ot) as [[oc b2] oroots]. cbn [fst snd] in Hoc, Hb2.
    assert (Hb2lt : b < b2) by lia.
    pose proof (number_list_pbounds (number_expr (Some b) RPlain) b
        (fun bb x Hbb => number_expr_pbounds x b RPlain bb Hbb)
        (fun bb x => span_final_ge _ _ (number_expr_spans x (Some b) RPlain bb))
        b2 (Collections.ne_to_list vals) Hb2lt) as Hvc.
    destruct (number_list (number_expr (Some b) RPlain) b2 (Collections.ne_to_list vals)) as [[vc b3] vroots].
    cbn [fst snd] in Hvc. cbn [fst]. apply pbounds_node; [ reflexivity | exact Hlt |
      apply (pbounds_weaken pv b); [ lia | apply pbounds_app; [ exact Hnc | apply pbounds_app; [ exact Hoc | exact Hvc ] ] ] ].
  - cbn [fst]. apply pbounds_node; [ reflexivity | exact Hlt |
      rewrite app_nil_r; apply (pbounds_weaken pv b); [ lia | exact Hnc ] ].
Qed.

Lemma number_varspec_pbounds : forall vs pv role b, pv < b -> pbounds pv (fst (number_varspec (Some pv) role b vs)).
Proof.
  intros vs pv role b Hlt. unfold number_varspec.
  pose proof (number_list_pbounds (number_bindingname (Some b) (RSpecName VarSpecF)) b
      (fun bb x Hbb => number_bindingname_pbounds x b (RSpecName VarSpecF) bb Hbb)
      (fun bb x => span_final_ge _ _ (number_bindingname_spans (Some b) (RSpecName VarSpecF) bb x))
      (S b) (Collections.ne_to_list (Syntax.var_names vs)) (Nat.lt_succ_diag_r b)) as Hnc.
  pose proof (span_final_ge _ _ (number_list_span (number_bindingname (Some b) (RSpecName VarSpecF))
      (fun bb x => number_bindingname_spans (Some b) (RSpecName VarSpecF) bb x)
      (Collections.ne_to_list (Syntax.var_names vs)) (S b))) as Hb1.
  destruct (number_list (number_bindingname (Some b) (RSpecName VarSpecF)) (S b)
      (Collections.ne_to_list (Syntax.var_names vs))) as [[nc b1] nroots].
  cbn [fst snd] in Hnc, Hb1.
  destruct (Syntax.var_init vs) as [t | ot vals].
  - assert (Hb1lt : b < b1) by lia.
    pose proof (number_typeexpr_pbounds t b RTypeUse b1 Hb1lt) as Htc.
    destruct (number_typeexpr (Some b) RTypeUse b1 t) as [tc b2]. cbn [fst] in Htc.
    cbn [fst]. apply pbounds_node; [ reflexivity | exact Hlt |
      apply (pbounds_weaken pv b); [ lia | apply pbounds_app; [ exact Hnc | exact Htc ] ] ].
  - assert (Hb1lt : b < b1) by lia.
    pose proof (number_opttype_pbounds ot b b1 Hb1lt) as Hoc.
    pose proof (span_final_ge _ _ (number_opttype_span (Some b) b1 ot)) as Hb2.
    destruct (number_opttype (Some b) b1 ot) as [[oc b2] oroots]. cbn [fst snd] in Hoc, Hb2.
    assert (Hb2lt : b < b2) by lia.
    pose proof (number_list_pbounds (number_expr (Some b) RPlain) b
        (fun bb x Hbb => number_expr_pbounds x b RPlain bb Hbb)
        (fun bb x => span_final_ge _ _ (number_expr_spans x (Some b) RPlain bb))
        b2 (Collections.ne_to_list vals) Hb2lt) as Hvc.
    destruct (number_list (number_expr (Some b) RPlain) b2 (Collections.ne_to_list vals)) as [[vc b3] vroots].
    cbn [fst snd] in Hvc. cbn [fst]. apply pbounds_node; [ reflexivity | exact Hlt |
      apply (pbounds_weaken pv b); [ lia | apply pbounds_app; [ exact Hnc | apply pbounds_app; [ exact Hoc | exact Hvc ] ] ] ].
Qed.

Lemma number_typespec_pbounds : forall ts pv role b, pv < b -> pbounds pv (fst (number_typespec (Some pv) role b ts)).
Proof.
  intros ts pv role b Hlt. unfold number_typespec; destruct ts as [bn t|bn t];
  ( pose proof (number_bindingname_pbounds bn b (RSpecName TypeSpecF) (S b) (Nat.lt_succ_diag_r b)) as Hbc;
    pose proof (span_final_ge _ _ (number_bindingname_spans (Some b) (RSpecName TypeSpecF) (S b) bn)) as Hb1;
    destruct (number_bindingname (Some b) (RSpecName TypeSpecF) (S b) bn) as [bc b1];
    cbn [fst snd] in Hbc, Hb1;
    assert (Hb1lt : b < b1) by lia;
    pose proof (number_typeexpr_pbounds t b RTypeUse b1 Hb1lt) as Htc;
    destruct (number_typeexpr (Some b) RTypeUse b1 t) as [tc bfin]; cbn [fst] in Htc;
    cbn [fst]; apply pbounds_node; [ reflexivity | exact Hlt |
      apply (pbounds_weaken pv b); [ lia | apply pbounds_app; [ exact Hbc | exact Htc ] ] ] ).
Qed.

Lemma number_decl_pbounds : forall d pv role b, pv < b -> pbounds pv (fst (number_decl (Some pv) role b d)).
Proof.
  intros d pv role b Hlt. unfold number_decl. destruct d as [cs|vs|ts].
  - pose proof (number_list_pbounds (number_constspec (Some b) RPlain) b
        (fun bb x Hbb => number_constspec_pbounds x b RPlain bb Hbb)
        (fun bb x => span_final_ge _ _ (number_constspec_span (Some b) RPlain bb x)) (S b) cs (Nat.lt_succ_diag_r b)) as Hk.
    destruct (number_list (number_constspec (Some b) RPlain) (S b) cs) as [[kc bfin] roots].
    cbn [fst snd] in Hk. cbn [fst]. apply pbounds_node; [ reflexivity | exact Hlt |
      apply (pbounds_weaken pv b); [ lia | exact Hk ] ].
  - pose proof (number_list_pbounds (number_varspec (Some b) RPlain) b
        (fun bb x Hbb => number_varspec_pbounds x b RPlain bb Hbb)
        (fun bb x => span_final_ge _ _ (number_varspec_span (Some b) RPlain bb x)) (S b) vs (Nat.lt_succ_diag_r b)) as Hk.
    destruct (number_list (number_varspec (Some b) RPlain) (S b) vs) as [[kc bfin] roots].
    cbn [fst snd] in Hk. cbn [fst]. apply pbounds_node; [ reflexivity | exact Hlt |
      apply (pbounds_weaken pv b); [ lia | exact Hk ] ].
  - pose proof (number_list_pbounds (number_typespec (Some b) RPlain) b
        (fun bb x Hbb => number_typespec_pbounds x b RPlain bb Hbb)
        (fun bb x => span_final_ge _ _ (number_typespec_span (Some b) RPlain bb x)) (S b) ts (Nat.lt_succ_diag_r b)) as Hk.
    destruct (number_list (number_typespec (Some b) RPlain) (S b) ts) as [[kc bfin] roots].
    cbn [fst snd] in Hk. cbn [fst]. apply pbounds_node; [ reflexivity | exact Hlt |
      apply (pbounds_weaken pv b); [ lia | exact Hk ] ].
Qed.

Lemma number_stmt_pbounds : forall s pv role b, pv < b -> pbounds pv (fst (number_stmt (Some pv) role b s)).
Proof.
  intros s pv role b Hlt. unfold number_stmt. destruct s as [e|d|names vals].
  - pose proof (number_expr_pbounds e b RExprStatementExpr (S b) (Nat.lt_succ_diag_r b)) as Hc.
    destruct (number_expr (Some b) RExprStatementExpr (S b) e) as [c b']. cbn [fst] in Hc.
    cbn [fst]. apply pbounds_node; [ reflexivity | exact Hlt | apply (pbounds_weaken pv b); [ lia | exact Hc ] ].
  - pose proof (number_decl_pbounds d b RPlain (S b) (Nat.lt_succ_diag_r b)) as Hc.
    destruct (number_decl (Some b) RPlain (S b) d) as [c b']. cbn [fst] in Hc.
    cbn [fst]. apply pbounds_node; [ reflexivity | exact Hlt | apply (pbounds_weaken pv b); [ lia | exact Hc ] ].
  - pose proof (number_list_pbounds (number_bindingname (Some b) RShortLhs) b
        (fun bb x Hbb => number_bindingname_pbounds x b RShortLhs bb Hbb)
        (fun bb x => span_final_ge _ _ (number_bindingname_spans (Some b) RShortLhs bb x))
        (S b) (Collections.ne_to_list names) (Nat.lt_succ_diag_r b)) as Hnc.
    pose proof (span_final_ge _ _ (number_list_span (number_bindingname (Some b) RShortLhs)
        (fun bb x => number_bindingname_spans (Some b) RShortLhs bb x) (Collections.ne_to_list names) (S b))) as Hb1.
    destruct (number_list (number_bindingname (Some b) RShortLhs) (S b) (Collections.ne_to_list names)) as [[nc b1] nroots].
    cbn [fst snd] in Hnc, Hb1. assert (Hb1lt : b < b1) by lia.
    pose proof (number_list_pbounds (number_expr (Some b) RPlain) b
        (fun bb x Hbb => number_expr_pbounds x b RPlain bb Hbb)
        (fun bb x => span_final_ge _ _ (number_expr_spans x (Some b) RPlain bb))
        b1 (Collections.ne_to_list vals) Hb1lt) as Hvc.
    destruct (number_list (number_expr (Some b) RPlain) b1 (Collections.ne_to_list vals)) as [[vc b2] vroots].
    cbn [fst snd] in Hvc. cbn [fst]. apply pbounds_node; [ reflexivity | exact Hlt |
      apply (pbounds_weaken pv b); [ lia | apply pbounds_app; [ exact Hnc | exact Hvc ] ] ].
Qed.

Lemma number_block_pbounds : forall blk pv role b, pv < b -> pbounds pv (fst (number_block (Some pv) role b blk)).
Proof.
  intros [stmts] pv role b Hlt. unfold number_block.
  pose proof (number_list_pbounds (number_stmt (Some b) RPlain) b
      (fun bb x Hbb => number_stmt_pbounds x b RPlain bb Hbb)
      (fun bb x => span_final_ge _ _ (number_stmt_span (Some b) RPlain bb x)) (S b) stmts (Nat.lt_succ_diag_r b)) as Hk.
  destruct (number_list (number_stmt (Some b) RPlain) (S b) stmts) as [[kc bfin] roots].
  cbn [fst snd] in Hk. cbn [fst]. apply pbounds_node; [ reflexivity | exact Hlt |
    apply (pbounds_weaken pv b); [ lia | exact Hk ] ].
Qed.

Lemma number_toplevel_pbounds : forall td pv role b, pv < b -> pbounds pv (fst (number_toplevel (Some pv) role b td)).
Proof.
  intros td pv role b Hlt. unfold number_toplevel. destruct td as [d|blk].
  - pose proof (number_decl_pbounds d b RPlain (S b) (Nat.lt_succ_diag_r b)) as Hc.
    destruct (number_decl (Some b) RPlain (S b) d) as [c b']. cbn [fst] in Hc.
    cbn [fst]. apply pbounds_node; [ reflexivity | exact Hlt | apply (pbounds_weaken pv b); [ lia | exact Hc ] ].
  - pose proof (number_block_pbounds blk b RPlain (S b) (Nat.lt_succ_diag_r b)) as Hc.
    destruct (number_block (Some b) RPlain (S b) blk) as [c b']. cbn [fst] in Hc.
    cbn [fst]. apply pbounds_node; [ reflexivity | exact Hlt | apply (pbounds_weaken pv b); [ lia | exact Hc ] ].
Qed.

(* whole-file parent well-scoping: every parent edge points strictly earlier — the parent relation is acyclic *)
Lemma number_file_pbounds : forall f, pbounds 0 (number_file f).
Proof.
  intro f. unfold number_file.
  pose proof (number_list_pbounds (number_toplevel (Some 0) RPlain) 0
      (fun bb x Hbb => number_toplevel_pbounds x 0 RPlain bb Hbb)
      (fun bb x => span_final_ge _ _ (number_toplevel_span (Some 0) RPlain bb x))
      1 (Syntax.declarations f) (Nat.lt_0_succ 0)) as Hd.
  destruct (number_list (number_toplevel (Some 0) RPlain) 1 (Syntax.declarations f)) as [[dc bfin] droots].
  cbn [fst snd] in Hd |- *. intros pos cell Hin pp Hpp. destruct Hin as [Heq|Hin].
  - inversion Heq; subst. discriminate Hpp.
  - apply (Hd pos cell Hin pp Hpp).
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
Module NodeProperties := FMapFacts.WProperties_fun Collections.NodeMap.E Collections.NodeMap.

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

(* transport: a cell found in the position map is one of the numbering-list entries, at the same position *)
Lemma posmap_nil : posmap_of [] = Collections.NodeMap.empty Cell.
Proof. reflexivity. Qed.
Lemma posmap_cons : forall kv rest,
  posmap_of (kv :: rest)
  = Collections.NodeMap.add (Pos.of_succ_nat (fst kv)) (snd kv) (posmap_of rest).
Proof. reflexivity. Qed.

Lemma posmap_find_in : forall occs k cell,
  Collections.NodeMap.find k (posmap_of occs) = Some cell ->
  exists pos, k = Pos.of_succ_nat pos /\ In (pos, cell) occs.
Proof.
  induction occs as [|[pos0 c] rest IH]; intros k cell Hf.
  - rewrite posmap_nil, NodeFacts.empty_o in Hf. discriminate.
  - rewrite posmap_cons in Hf. cbn [fst snd] in Hf. rewrite NodeFacts.add_o in Hf.
    destruct (Collections.NodeMap.E.eq_dec (Pos.of_succ_nat pos0) k) as [Heq|Hneq].
    + injection Hf as Hc. exists pos0. split; [ symmetry; exact Heq | left; rewrite Hc; reflexivity ].
    + destruct (IH k cell Hf) as [pos [Hk Hin]]. exists pos. split; [ exact Hk | right; exact Hin ].
Qed.

(* distinct source positions give the position map exactly one binding each, so its cardinality is the count *)
Lemma posmap_cardinal : forall occs,
  NoDup (map fst occs) -> Collections.NodeMap.cardinal (posmap_of occs) = length occs.
Proof.
  induction occs as [|[pos0 c] rest IH]; intro Hnd.
  - reflexivity.
  - cbn [map fst] in Hnd. rewrite NoDup_cons_iff in Hnd. destruct Hnd as [Hnotin Hnd'].
    assert (Hni : ~ Collections.NodeMap.In (Pos.of_succ_nat pos0) (posmap_of rest)).
    { intro Hin. rewrite NodeFacts.in_find_iff in Hin.
      destruct (Collections.NodeMap.find (Pos.of_succ_nat pos0) (posmap_of rest)) as [cell|] eqn:E;
        [| exact (Hin eq_refl) ].
      destruct (posmap_find_in rest (Pos.of_succ_nat pos0) cell E) as [q [Hq Hinq]].
      apply (f_equal Pos.to_nat) in Hq. rewrite !SuccNat2Pos.id_succ in Hq.
      apply Hnotin. apply in_map_iff. exists (q, cell); split; [ cbn [fst]; lia | exact Hinq ]. }
    rewrite posmap_cons. cbn [fst snd].
    rewrite (NodeProperties.cardinal_2 (m := posmap_of rest)
             (m' := Collections.NodeMap.add (Pos.of_succ_nat pos0) c (posmap_of rest))
             Hni (fun y => eq_refl)).
    cbn [length]. f_equal. apply IH; exact Hnd'.
Qed.

(* the position map key of a node reference is exactly the successor-encoding of its ordinal position *)
Lemma nr_key_pos {p} {idx : ProgramIndex p} (r : NodeRef idx) :
  nr_key r = Pos.of_succ_nat (nr_pos r).
Proof.
  apply Pos2Nat.inj. unfold nr_pos. rewrite SuccNat2Pos.id_succ.
  pose proof (Pos2Nat.is_pos (nr_key r)). lia.
Qed.

(* occ_at is the value the position map actually stores for the node's key *)
Lemma occ_at_find_some {p} {idx : ProgramIndex p} (r : NodeRef idx) c :
  Collections.NodeMap.find (nr_key r) (cell_map (nr_file r)) = Some c -> occ_at r = c.
Proof.
  intro E. unfold occ_at.
  generalize (@eq_refl (option Cell) (Collections.NodeMap.find (nr_key r) (cell_map (nr_file r)))).
  destruct (Collections.NodeMap.find (nr_key r) (cell_map (nr_file r))) at 2 3; intro H; congruence.
Qed.

Lemma occ_at_find {p} {idx : ProgramIndex p} (r : NodeRef idx) :
  Collections.NodeMap.find (nr_key r) (cell_map (nr_file r)) = Some (occ_at r).
Proof.
  destruct (Collections.NodeMap.find (nr_key r) (cell_map (nr_file r))) as [c|] eqn:E.
  - rewrite (occ_at_find_some r c E). reflexivity.
  - exfalso. exact (proj1 (NodeFacts.in_find_iff _ _) (proj2 (NodeFacts.mem_in_iff _ _) (nr_in r)) E).
Qed.

(* the value file_info_of retrieves is exactly what the program map stores for the file's path *)
Lemma file_info_of_find {p} {idx : ProgramIndex p} (fr : FileRef idx) fi :
  Collections.FileMap.find (fr_path fr) (prog_map idx) = Some fi -> file_info_of fr = fi.
Proof.
  intro E. unfold file_info_of.
  generalize (@eq_refl (option FileInfo) (Collections.FileMap.find (fr_path fr) (prog_map idx))).
  destruct (Collections.FileMap.find (fr_path fr) (prog_map idx)) at 2 3; intro H; congruence.
Qed.

(* every file reference resolves to the single-pass numbering build of some source file *)
Lemma fileinfo_number_file {p} {idx : ProgramIndex p} (fr : FileRef idx) :
  exists f, file_info_of fr = build_fileinfo f.
Proof.
  destruct (file_find_some idx (fr_path fr) (fr_in fr)) as [fi Hfi].
  pose proof (file_info_of_find fr fi Hfi) as Hfio.
  unfold prog_map in Hfi. rewrite (proj2_sig idx) in Hfi. unfold raw_index in Hfi.
  rewrite Collections.FileFacts.map_o in Hfi.
  destruct (Collections.FileMap.find (fr_path fr) (Syntax.files p)) as [file|] eqn:Ef;
    cbn [option_map] in Hfi.
  - injection Hfi as <-. exists file. exact Hfio.
  - discriminate.
Qed.

Lemma cellmap_number_file {p} {idx : ProgramIndex p} (fr : FileRef idx) :
  exists f, cell_map fr = posmap_of (number_file f).
Proof. destruct (fileinfo_number_file fr) as [f Hf]. exists f. unfold cell_map; rewrite Hf; reflexivity. Qed.

(* the universal transport: any node's cell is a numbering-list entry of its file, at its ordinal position *)
Lemma occ_in_number_file {p} {idx : ProgramIndex p} (r : NodeRef idx) :
  exists f, In (nr_pos r, occ_at r) (number_file f) /\ occ_count (nr_file r) = length (number_file f).
Proof.
  destruct (fileinfo_number_file (nr_file r)) as [f Hf].
  assert (Hc : cell_map (nr_file r) = posmap_of (number_file f)) by (unfold cell_map; rewrite Hf; reflexivity).
  exists f. split; [| unfold occ_count; rewrite Hf; reflexivity ].
  pose proof (occ_at_find r) as Hfind. rewrite Hc in Hfind.
  destruct (posmap_find_in (number_file f) (nr_key r) (occ_at r) Hfind) as [pos [Hk Hin]].
  assert (Hpe : pos = nr_pos r).
  { pose proof (nr_key_pos r) as Hkp.
    assert (Pos.of_succ_nat (nr_pos r) = Pos.of_succ_nat pos) as Hpp by (rewrite <- Hkp; exact Hk).
    apply (f_equal Pos.to_nat) in Hpp. rewrite !SuccNat2Pos.id_succ in Hpp. lia. }
  rewrite Hpe in Hin. exact Hin.
Qed.

(* count equals domain cardinality: the retained occurrence count is exactly the position map's binding count *)
Lemma occ_count_cardinal {p} {idx : ProgramIndex p} (fr : FileRef idx) :
  occ_count fr = Collections.NodeMap.cardinal (cell_map fr).
Proof.
  destruct (fileinfo_number_file fr) as [f Hf].
  assert (Hc : cell_map fr = posmap_of (number_file f)) by (unfold cell_map; rewrite Hf; reflexivity).
  assert (Hcount : occ_count fr = length (number_file f)) by (unfold occ_count; rewrite Hf; reflexivity).
  rewrite Hc, Hcount. symmetry. apply posmap_cardinal.
  destruct (number_file_positions f) as [n Hn]. rewrite Hn. apply seq_NoDup.
Qed.

(* a source position present in the numbering list is a live key of the position map *)
Lemma posmap_mem_of_in : forall occs q,
  In q (map fst occs) -> Collections.NodeMap.mem (Pos.of_succ_nat q) (posmap_of occs) = true.
Proof.
  induction occs as [|[pos0 c] rest IH]; intros q Hin.
  - cbn in Hin. contradiction.
  - cbn [map fst] in Hin. rewrite posmap_cons. cbn [fst snd].
    apply NodeFacts.mem_in_iff, NodeFacts.add_in_iff. destruct Hin as [Heq | Hin].
    + subst pos0. left. reflexivity.
    + right. apply NodeFacts.mem_in_iff, IH. exact Hin.
Qed.

(* coverage lifts an in-range ordinal position to a live position-map key on the exact file *)
Lemma mem_at_pos {p} {idx : ProgramIndex p} (fr : FileRef idx) (pos : nat) :
  pos < occ_count fr -> Collections.NodeMap.mem (Pos.of_succ_nat pos) (cell_map fr) = true.
Proof.
  intro H. destruct (fileinfo_number_file fr) as [f Hf].
  assert (Hc : cell_map fr = posmap_of (number_file f)) by (unfold cell_map; rewrite Hf; reflexivity).
  assert (Hn0 : occ_count fr = length (number_file f)) by (unfold occ_count; rewrite Hf; reflexivity).
  rewrite Hc. apply posmap_mem_of_in.
  destruct (number_file_positions f) as [n Hn]. rewrite Hn. apply in_seq.
  rewrite Hn0 in H.
  assert (Hlen : length (number_file f) = n).
  { apply (f_equal (@length nat)) in Hn.
    first [ rewrite length_map in Hn | rewrite map_length in Hn ];
    first [ rewrite length_seq in Hn | rewrite seq_length in Hn ]; exact Hn. }
  lia.
Qed.

(* every represented source occurrence appears once: the ordinal positions of a file are pairwise distinct *)
Lemma occurrences_distinct : forall f, NoDup (map fst (number_file f)).
Proof. intro f. destruct (number_file_positions f) as [n Hn]. rewrite Hn. apply seq_NoDup. Qed.

(* the position map domain is exactly the source-occurrence domain: its keys are the in-range ordinals *)
Lemma domain_exact {p} {idx : ProgramIndex p} (fr : FileRef idx) (k : positive) :
  Collections.NodeMap.In k (cell_map fr) <-> exists pos, pos < occ_count fr /\ k = Pos.of_succ_nat pos.
Proof.
  destruct (fileinfo_number_file fr) as [f Hf].
  assert (Hc : cell_map fr = posmap_of (number_file f)) by (unfold cell_map; rewrite Hf; reflexivity).
  assert (Hcount : occ_count fr = length (number_file f)) by (unfold occ_count; rewrite Hf; reflexivity).
  destruct (number_file_positions f) as [n Hn].
  assert (Hlen : length (number_file f) = n).
  { apply (f_equal (@length nat)) in Hn.
    first [ rewrite length_map in Hn | rewrite map_length in Hn ];
    first [ rewrite length_seq in Hn | rewrite seq_length in Hn ]; exact Hn. }
  rewrite Hc, Hcount, Hlen. split.
  - intro Hin.
    destruct (Collections.NodeMap.find k (posmap_of (number_file f))) as [cell|] eqn:E;
      [| exfalso; rewrite NodeFacts.in_find_iff in Hin; apply Hin; exact E ].
    destruct (posmap_find_in (number_file f) k cell E) as [pos [Hk Hinpos]].
    exists pos. split; [| exact Hk].
    assert (Hinm : In pos (map fst (number_file f)))
      by (apply in_map_iff; exists (pos, cell); split; [ reflexivity | exact Hinpos ]).
    rewrite Hn in Hinm. apply in_seq in Hinm. lia.
  - intros [pos [Hlt Hk]]. subst k. rewrite NodeFacts.mem_in_iff. apply posmap_mem_of_in.
    rewrite Hn. apply in_seq. lia.
Qed.

(* the total position-indexed node reference: any in-range ordinal resolves without option or fallback *)
Definition noderef_at_pos {p} {idx : ProgramIndex p} (fr : FileRef idx) (pos : nat)
  (H : pos < occ_count fr) : NodeRef idx := mkNodeRef fr (Pos.of_succ_nat pos) (mem_at_pos fr pos H).

Lemma noderef_at_pos_file {p} {idx : ProgramIndex p} (fr : FileRef idx) (pos : nat)
  (H : pos < occ_count fr) : nr_file (noderef_at_pos fr pos H) = fr.
Proof. reflexivity. Qed.

Lemma noderef_at_pos_pos {p} {idx : ProgramIndex p} (fr : FileRef idx) (pos : nat)
  (H : pos < occ_count fr) : nr_pos (noderef_at_pos fr pos H) = pos.
Proof. unfold noderef_at_pos, nr_pos; cbn [nr_key]; rewrite SuccNat2Pos.id_succ; reflexivity. Qed.

(* every node's cell obeys the first-edge law with its own file's occurrence count as the range bound *)
Lemma occ_edge_wf {p} {idx : ProgramIndex p} (r : NodeRef idx) :
  edge_wf (nr_pos r) (occ_at r) (occ_count (nr_file r)).
Proof.
  destruct (occ_in_number_file r) as [f [Hin Hcount]].
  rewrite Hcount. pose proof (number_file_edge_wf f) as Hwf. unfold ewf in Hwf.
  rewrite Forall_forall in Hwf. exact (Hwf _ Hin).
Qed.

(* the exact first required child of any node that carries a required edge, in range on its own file *)
Lemma occ_first_child_wf {p} {idx : ProgramIndex p} (r : NodeRef idx) :
  requires_first_edge (node_view r) = true ->
  first_child_wf (c_children (occ_at r)) (nr_pos r) (occ_count (nr_file r)).
Proof.
  intro H. pose proof (occ_edge_wf r) as He. unfold edge_wf in He. unfold node_view in H.
  rewrite H in He. exact He.
Qed.

(* the total refined first-edge reference: no filter, no fallback — a required edge resolves exactly *)
Definition first_edge {p} {idx : ProgramIndex p} (r : NodeRef idx)
  (H : requires_first_edge (node_view r) = true) : NodeRef idx :=
  match c_children (occ_at r) as ch
    return first_child_wf ch (nr_pos r) (occ_count (nr_file r)) -> NodeRef idx with
  | [] => fun Hw => False_rect _ Hw
  | hp :: _ => fun Hw => noderef_at_pos (nr_file r) hp (proj2 Hw)
  end (occ_first_child_wf r H).

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
