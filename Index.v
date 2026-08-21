(* One direct shallow occurrence authority: a finite file map of finite position maps of shallow cells. *)

From Stdlib Require Import List Bool Arith PeanoNat Lia Eqdep_dec PArith FSets.FMapFacts.
From Fido Require Import FilePath Collections Names Syntax.
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

(* [covered occs q]: position q is listed among the children of some member cell — it is nobody's orphan *)
Definition covered (occs : list (nat * Cell)) (q : nat) : Prop :=
  exists r rcell, In (r, rcell) occs /\ In q (c_children rcell).

Lemma covered_app_l : forall c1 c2 q, covered c1 q -> covered (c1 ++ c2) q.
Proof.
  intros c1 c2 q [r [rcell [Hin Hq]]]. exists r, rcell. split; [ apply in_or_app; left; exact Hin | exact Hq ].
Qed.

Lemma covered_app_r : forall c1 c2 q, covered c2 q -> covered (c1 ++ c2) q.
Proof.
  intros c1 c2 q [r [rcell [Hin Hq]]]. exists r, rcell. split; [ apply in_or_app; right; exact Hin | exact Hq ].
Qed.

(* every position a sublist fills is either one of its element roots or already covered inside an element *)
Lemma number_list_cover {A} (g : nat -> A -> list (nat * Cell) * nat) :
  (forall b x q, b < q < snd (g b x) -> covered (fst (g b x)) q) ->
  (forall b x, b <= snd (g b x)) ->
  forall b xs q, b <= q < snd (fst (number_list g b xs)) ->
    In q (snd (number_list g b xs)) \/ covered (fst (fst (number_list g b xs))) q.
Proof.
  intros Hg Hmono b xs; revert b; induction xs as [|x rest IH]; intro b.
  - cbn [number_list fst snd]. intros q Hq. exfalso; lia.
  - cbn [number_list]. pose proof (Hmono b x) as Hm. pose proof (Hg b x) as Hgx.
    destruct (g b x) as [xc b']. cbn [fst snd] in Hm, Hgx.
    specialize (IH b'). destruct (number_list g b' rest) as [[rc bfin] roots].
    cbn [fst snd] in IH |- *. intros q [Hqlo Hqhi].
    destruct (le_lt_dec b' q) as [Hge|Hqlt].
    + destruct (IH q (conj Hge Hqhi)) as [Hin|Hcov];
        [ left; apply in_cons; exact Hin | right; apply covered_app_r; exact Hcov ].
    + destruct (Nat.eq_dec q b) as [->|Hne].
      * left; apply in_eq.
      * right. apply covered_app_l. apply Hgx. split; [ lia | exact Hqlt ].
Qed.

Lemma covered_cons : forall kv occs q, covered occs q -> covered (kv :: occs) q.
Proof. intros kv occs q [r [rcell [Hin Hq]]]. exists r, rcell. split; [ right; exact Hin | exact Hq ]. Qed.

Lemma covered_here : forall b rcell occs q, In q (c_children rcell) -> covered ((b, rcell) :: occs) q.
Proof. intros b rcell occs q Hq. exists b, rcell. split; [ left; reflexivity | exact Hq ]. Qed.

(* every interior position of an expression's block is covered — its own root lists it, or a sub-expression does *)
Lemma number_expr_cover : forall e par role b q,
  b < q < snd (number_expr par role b e) -> covered (fst (number_expr par role b e)) q.
Proof.
  intro e; induction e using Syntax.Expr_ind'; intros par role b; cbn [number_expr].
  - cbn [number_leaf fst snd]. intros q Hq. exfalso; lia.
  - cbn [number_leaf fst snd]. intros q Hq. exfalso; lia.
  - specialize (IHe (Some b) RUnaryOperand (S b)).
    destruct (number_expr (Some b) RUnaryOperand (S b) e) as [kc nxt].
    cbn [fst snd] in IHe |- *. intros q [Hqlo Hqhi].
    destruct (Nat.eq_dec q (S b)) as [->|Hne].
    + apply covered_here. cbn [c_children]. left; reflexivity.
    + apply covered_cons. apply IHe. split; [ lia | exact Hqhi ].
  - specialize (IHe (Some b) RApplicationHead (S b)).
    destruct (number_expr (Some b) RApplicationHead (S b) e) as [hc b1]. cbn [fst snd] in IHe.
    assert (Hda : forall es, Forall (fun a => forall par role bb q,
                     bb < q < snd (number_expr par role bb a) -> covered (fst (number_expr par role bb a)) q) es ->
      forall i0 bi, (let '(ac, bf, roots) := (fix do_args (i bi : nat) (es : list Syntax.Expr) {struct es}
              : list (nat * Cell) * nat * list nat :=
              match es with
              | [] => ([], bi, [])
              | a :: rest =>
                  let '(ac, bi') := number_expr (Some b) (RApplicationArg i) bi a in
                  let '(rc, bf, roots) := do_args (S i) bi' rest in
                  (ac ++ rc, bf, bi :: roots)
              end) i0 bi es in
        forall q, bi <= q < bf -> In q roots \/ covered ac q)).
    { intros es Hall; induction Hall as [| a rest Ha Hrest IHrest]; intros i0 bi.
      - intros q Hq. exfalso; lia.
      - specialize (Ha (Some b) (RApplicationArg i0) bi).
        destruct (number_expr (Some b) (RApplicationArg i0) bi a) as [ac1 bi']. cbn [fst snd] in Ha.
        specialize (IHrest (S i0) bi').
        destruct ((fix do_args (i bi : nat) (es : list Syntax.Expr) {struct es} := _) (S i0) bi' rest)
          as [[rc bf] roots].
        cbn [fst snd] in IHrest |- *. intros q [Hqlo Hqhi].
        destruct (le_lt_dec bi' q) as [Hge|Hqlt].
        + destruct (IHrest q (conj Hge Hqhi)) as [Hin|Hcov];
            [ left; apply in_cons; exact Hin | right; apply covered_app_r; exact Hcov ].
        + destruct (Nat.eq_dec q bi) as [->|Hne].
          * left; apply in_eq.
          * right. apply covered_app_l. apply Ha. split; [ lia | exact Hqlt ]. }
    specialize (Hda args H 0 b1).
    destruct ((fix do_args (i bi : nat) (es : list Syntax.Expr) {struct es} := _) 0 b1 args)
      as [[ac bfin] aroots].
    cbn [fst snd] in Hda |- *. intros q [Hqlo Hqhi].
    destruct (le_lt_dec b1 q) as [Hge|Hqlt].
    + destruct (Hda q (conj Hge Hqhi)) as [Hin|Hcov].
      * apply covered_here. cbn [c_children]. right; exact Hin.
      * apply covered_cons. apply covered_app_r. exact Hcov.
    + destruct (Nat.eq_dec q (S b)) as [->|Hne].
      * apply covered_here. cbn [c_children]. left; reflexivity.
      * apply covered_cons. apply covered_app_l. apply IHe. split; [ lia | exact Hqlt ].
Qed.

Lemma number_typeexpr_cover : forall t par role b q,
  b < q < snd (number_typeexpr par role b t) -> covered (fst (number_typeexpr par role b t)) q.
Proof. intros t par role b q Hq. cbn [number_typeexpr number_leaf snd] in Hq. exfalso; lia. Qed.

Lemma number_bindingname_cover : forall bn par role b q,
  b < q < snd (number_bindingname par role b bn) -> covered (fst (number_bindingname par role b bn)) q.
Proof. intros bn par role b q Hq. cbn [number_bindingname number_leaf snd] in Hq. exfalso; lia. Qed.

(* the optional type slot fills exactly [b] (its type) or nothing: any position it covers is its one root *)
Lemma number_opttype_cover : forall ot par b q,
  b <= q < snd (fst (number_opttype par b ot)) ->
    In q (snd (number_opttype par b ot)) \/ covered (fst (fst (number_opttype par b ot))) q.
Proof.
  intros ot par b q. destruct ot as [t|].
  - cbn [number_opttype number_typeexpr number_leaf fst snd]. intros [Hlo Hhi].
    assert (q = b) by lia. subst q. left; apply in_eq.
  - cbn [number_opttype fst snd]. intros [Hlo Hhi]. exfalso; lia.
Qed.

Lemma number_constspec_cover : forall cs par role b q,
  b < q < snd (number_constspec par role b cs) -> covered (fst (number_constspec par role b cs)) q.
Proof.
  intros cs par role b. unfold number_constspec.
  pose proof (number_list_cover (number_bindingname (Some b) (RSpecName ConstSpecF))
      (fun bb x q => number_bindingname_cover x (Some b) (RSpecName ConstSpecF) bb q)
      (fun bb x => span_final_ge _ _ (number_bindingname_spans (Some b) (RSpecName ConstSpecF) bb x))
      (S b) (Collections.ne_to_list (Syntax.const_names cs))) as Hnc.
  destruct (number_list (number_bindingname (Some b) (RSpecName ConstSpecF)) (S b)
      (Collections.ne_to_list (Syntax.const_names cs))) as [[nc b1] nroots].
  cbn [fst snd] in Hnc.
  destruct (Syntax.const_init cs) as [ot vals|].
  - pose proof (number_opttype_cover ot (Some b) b1) as Hoc.
    destruct (number_opttype (Some b) b1 ot) as [[oc b2] oroots]. cbn [fst snd] in Hoc.
    pose proof (number_list_cover (number_expr (Some b) RPlain)
        (fun bb x q => number_expr_cover x (Some b) RPlain bb q)
        (fun bb x => span_final_ge _ _ (number_expr_spans x (Some b) RPlain bb))
        b2 (Collections.ne_to_list vals)) as Hvc.
    destruct (number_list (number_expr (Some b) RPlain) b2 (Collections.ne_to_list vals)) as [[vc b3] vroots].
    cbn [fst snd] in Hvc. cbn [fst snd]. intros q [Hqlo Hqhi].
    destruct (le_lt_dec b1 q) as [Hb1|Hb1].
    + destruct (le_lt_dec b2 q) as [Hb2|Hb2].
      * destruct (Hvc q (conj Hb2 Hqhi)) as [Hin|Hcov].
        -- apply covered_here; cbn [c_children]; apply in_or_app; right; apply in_or_app; right; exact Hin.
        -- apply covered_cons; apply covered_app_r; apply covered_app_r; exact Hcov.
      * destruct (Hoc q (conj Hb1 Hb2)) as [Hin|Hcov].
        -- apply covered_here; cbn [c_children]; apply in_or_app; right; apply in_or_app; left; exact Hin.
        -- apply covered_cons; apply covered_app_r; apply covered_app_l; exact Hcov.
    + destruct (Hnc q (conj Hqlo Hb1)) as [Hin|Hcov].
      * apply covered_here; cbn [c_children]; apply in_or_app; left; exact Hin.
      * apply covered_cons; apply covered_app_l; exact Hcov.
  - cbn [fst snd]. intros q [Hqlo Hqhi].
    destruct (Hnc q (conj Hqlo Hqhi)) as [Hin|Hcov].
    + apply covered_here; cbn [c_children]; rewrite app_nil_r; exact Hin.
    + apply covered_cons; rewrite app_nil_r; exact Hcov.
Qed.

Lemma number_varspec_cover : forall vs par role b q,
  b < q < snd (number_varspec par role b vs) -> covered (fst (number_varspec par role b vs)) q.
Proof.
  intros vs par role b. unfold number_varspec.
  pose proof (number_list_cover (number_bindingname (Some b) (RSpecName VarSpecF))
      (fun bb x q => number_bindingname_cover x (Some b) (RSpecName VarSpecF) bb q)
      (fun bb x => span_final_ge _ _ (number_bindingname_spans (Some b) (RSpecName VarSpecF) bb x))
      (S b) (Collections.ne_to_list (Syntax.var_names vs))) as Hnc.
  destruct (number_list (number_bindingname (Some b) (RSpecName VarSpecF)) (S b)
      (Collections.ne_to_list (Syntax.var_names vs))) as [[nc b1] nroots].
  cbn [fst snd] in Hnc.
  destruct (Syntax.var_init vs) as [t | ot vals].
  - cbn [number_typeexpr number_leaf fst snd]. intros q [Hqlo Hqhi].
    destruct (le_lt_dec b1 q) as [Hb1|Hb1].
    + assert (q = b1) by lia. subst q.
      apply covered_here; cbn [c_children]; apply in_or_app; right; apply in_eq.
    + destruct (Hnc q (conj Hqlo Hb1)) as [Hin|Hcov].
      * apply covered_here; cbn [c_children]; apply in_or_app; left; exact Hin.
      * apply covered_cons; apply covered_app_l; exact Hcov.
  - pose proof (number_opttype_cover ot (Some b) b1) as Hoc.
    destruct (number_opttype (Some b) b1 ot) as [[oc b2] oroots]. cbn [fst snd] in Hoc.
    pose proof (number_list_cover (number_expr (Some b) RPlain)
        (fun bb x q => number_expr_cover x (Some b) RPlain bb q)
        (fun bb x => span_final_ge _ _ (number_expr_spans x (Some b) RPlain bb))
        b2 (Collections.ne_to_list vals)) as Hvc.
    destruct (number_list (number_expr (Some b) RPlain) b2 (Collections.ne_to_list vals)) as [[vc b3] vroots].
    cbn [fst snd] in Hvc. cbn [fst snd]. intros q [Hqlo Hqhi].
    destruct (le_lt_dec b1 q) as [Hb1|Hb1].
    + destruct (le_lt_dec b2 q) as [Hb2|Hb2].
      * destruct (Hvc q (conj Hb2 Hqhi)) as [Hin|Hcov].
        -- apply covered_here; cbn [c_children]; apply in_or_app; right; apply in_or_app; right; exact Hin.
        -- apply covered_cons; apply covered_app_r; apply covered_app_r; exact Hcov.
      * destruct (Hoc q (conj Hb1 Hb2)) as [Hin|Hcov].
        -- apply covered_here; cbn [c_children]; apply in_or_app; right; apply in_or_app; left; exact Hin.
        -- apply covered_cons; apply covered_app_r; apply covered_app_l; exact Hcov.
    + destruct (Hnc q (conj Hqlo Hb1)) as [Hin|Hcov].
      * apply covered_here; cbn [c_children]; apply in_or_app; left; exact Hin.
      * apply covered_cons; apply covered_app_l; exact Hcov.
Qed.

Lemma number_typespec_cover : forall ts par role b q,
  b < q < snd (number_typespec par role b ts) -> covered (fst (number_typespec par role b ts)) q.
Proof.
  intros ts par role b. unfold number_typespec; destruct ts as [bn t|bn t];
  ( cbn [number_bindingname number_typeexpr number_leaf fst snd]; intros q [Hqlo Hqhi];
    destruct (Nat.eq_dec q (S b)) as [->|Hne];
    [ apply covered_here; cbn [c_children]; apply in_eq
    | assert (q = S (S b)) by lia; subst q;
      apply covered_here; cbn [c_children]; apply in_cons; apply in_eq ] ).
Qed.

Lemma number_decl_cover : forall d par role b q,
  b < q < snd (number_decl par role b d) -> covered (fst (number_decl par role b d)) q.
Proof.
  intros d par role b. unfold number_decl. destruct d as [cs|vs|ts].
  - pose proof (number_list_cover (number_constspec (Some b) RPlain)
        (fun bb x q => number_constspec_cover x (Some b) RPlain bb q)
        (fun bb x => span_final_ge _ _ (number_constspec_span (Some b) RPlain bb x)) (S b) cs) as Hk.
    destruct (number_list (number_constspec (Some b) RPlain) (S b) cs) as [[kc bfin] roots].
    cbn [fst snd] in Hk. cbn [fst snd]. intros q [Hqlo Hqhi].
    destruct (Hk q (conj Hqlo Hqhi)) as [Hin|Hcov];
      [ apply covered_here; cbn [c_children]; exact Hin | apply covered_cons; exact Hcov ].
  - pose proof (number_list_cover (number_varspec (Some b) RPlain)
        (fun bb x q => number_varspec_cover x (Some b) RPlain bb q)
        (fun bb x => span_final_ge _ _ (number_varspec_span (Some b) RPlain bb x)) (S b) vs) as Hk.
    destruct (number_list (number_varspec (Some b) RPlain) (S b) vs) as [[kc bfin] roots].
    cbn [fst snd] in Hk. cbn [fst snd]. intros q [Hqlo Hqhi].
    destruct (Hk q (conj Hqlo Hqhi)) as [Hin|Hcov];
      [ apply covered_here; cbn [c_children]; exact Hin | apply covered_cons; exact Hcov ].
  - pose proof (number_list_cover (number_typespec (Some b) RPlain)
        (fun bb x q => number_typespec_cover x (Some b) RPlain bb q)
        (fun bb x => span_final_ge _ _ (number_typespec_span (Some b) RPlain bb x)) (S b) ts) as Hk.
    destruct (number_list (number_typespec (Some b) RPlain) (S b) ts) as [[kc bfin] roots].
    cbn [fst snd] in Hk. cbn [fst snd]. intros q [Hqlo Hqhi].
    destruct (Hk q (conj Hqlo Hqhi)) as [Hin|Hcov];
      [ apply covered_here; cbn [c_children]; exact Hin | apply covered_cons; exact Hcov ].
Qed.

Lemma number_stmt_cover : forall s par role b q,
  b < q < snd (number_stmt par role b s) -> covered (fst (number_stmt par role b s)) q.
Proof.
  intros s par role b. unfold number_stmt. destruct s as [e|d|names vals].
  - pose proof (number_expr_cover e (Some b) RExprStatementExpr (S b)) as Hc.
    pose proof (number_expr_spans e (Some b) RExprStatementExpr (S b)) as Hs.
    destruct (number_expr (Some b) RExprStatementExpr (S b) e) as [c b']. cbn [fst snd] in Hc, Hs.
    cbn [fst snd]. intros q [Hqlo Hqhi].
    destruct (Nat.eq_dec q (S b)) as [->|Hne].
    + apply covered_here; cbn [c_children]; left; reflexivity.
    + apply covered_cons. apply Hc. split; [ lia | exact Hqhi ].
  - pose proof (number_decl_cover d (Some b) RPlain (S b)) as Hc.
    destruct (number_decl (Some b) RPlain (S b) d) as [c b']. cbn [fst snd] in Hc.
    cbn [fst snd]. intros q [Hqlo Hqhi].
    destruct (Nat.eq_dec q (S b)) as [->|Hne].
    + apply covered_here; cbn [c_children]; left; reflexivity.
    + apply covered_cons. apply Hc. split; [ lia | exact Hqhi ].
  - pose proof (number_list_cover (number_bindingname (Some b) RShortLhs)
        (fun bb x q => number_bindingname_cover x (Some b) RShortLhs bb q)
        (fun bb x => span_final_ge _ _ (number_bindingname_spans (Some b) RShortLhs bb x))
        (S b) (Collections.ne_to_list names)) as Hnc.
    destruct (number_list (number_bindingname (Some b) RShortLhs) (S b) (Collections.ne_to_list names)) as [[nc b1] nroots].
    cbn [fst snd] in Hnc.
    pose proof (number_list_cover (number_expr (Some b) RPlain)
        (fun bb x q => number_expr_cover x (Some b) RPlain bb q)
        (fun bb x => span_final_ge _ _ (number_expr_spans x (Some b) RPlain bb))
        b1 (Collections.ne_to_list vals)) as Hvc.
    destruct (number_list (number_expr (Some b) RPlain) b1 (Collections.ne_to_list vals)) as [[vc b2] vroots].
    cbn [fst snd] in Hvc. cbn [fst snd]. intros q [Hqlo Hqhi].
    destruct (le_lt_dec b1 q) as [Hb1|Hb1].
    + destruct (Hvc q (conj Hb1 Hqhi)) as [Hin|Hcov].
      * apply covered_here; cbn [c_children]; apply in_or_app; right; exact Hin.
      * apply covered_cons; apply covered_app_r; exact Hcov.
    + destruct (Hnc q (conj Hqlo Hb1)) as [Hin|Hcov].
      * apply covered_here; cbn [c_children]; apply in_or_app; left; exact Hin.
      * apply covered_cons; apply covered_app_l; exact Hcov.
Qed.

Lemma number_block_cover : forall blk par role b q,
  b < q < snd (number_block par role b blk) -> covered (fst (number_block par role b blk)) q.
Proof.
  intros [stmts] par role b. unfold number_block.
  pose proof (number_list_cover (number_stmt (Some b) RPlain)
      (fun bb x q => number_stmt_cover x (Some b) RPlain bb q)
      (fun bb x => span_final_ge _ _ (number_stmt_span (Some b) RPlain bb x)) (S b) stmts) as Hk.
  destruct (number_list (number_stmt (Some b) RPlain) (S b) stmts) as [[kc bfin] roots].
  cbn [fst snd] in Hk. cbn [fst snd]. intros q [Hqlo Hqhi].
  destruct (Hk q (conj Hqlo Hqhi)) as [Hin|Hcov];
    [ apply covered_here; cbn [c_children]; exact Hin | apply covered_cons; exact Hcov ].
Qed.

Lemma number_toplevel_cover : forall td par role b q,
  b < q < snd (number_toplevel par role b td) -> covered (fst (number_toplevel par role b td)) q.
Proof.
  intros td par role b. unfold number_toplevel. destruct td as [d|blk].
  - pose proof (number_decl_cover d (Some b) RPlain (S b)) as Hc.
    destruct (number_decl (Some b) RPlain (S b) d) as [c b']. cbn [fst snd] in Hc.
    cbn [fst snd]. intros q [Hqlo Hqhi].
    destruct (Nat.eq_dec q (S b)) as [->|Hne].
    + apply covered_here; cbn [c_children]; left; reflexivity.
    + apply covered_cons. apply Hc. split; [ lia | exact Hqhi ].
  - pose proof (number_block_cover blk (Some b) RPlain (S b)) as Hc.
    destruct (number_block (Some b) RPlain (S b) blk) as [c b']. cbn [fst snd] in Hc.
    cbn [fst snd]. intros q [Hqlo Hqhi].
    destruct (Nat.eq_dec q (S b)) as [->|Hne].
    + apply covered_here; cbn [c_children]; left; reflexivity.
    + apply covered_cons. apply Hc. split; [ lia | exact Hqhi ].
Qed.

(* every non-file position in the file is listed as some occurrence's child — the forest has no orphans *)
Lemma number_file_cover : forall f q,
  0 < q < List.length (number_file f) -> covered (number_file f) q.
Proof.
  intros f q Hq. unfold number_file in *.
  pose proof (number_list_cover (number_toplevel (Some 0) RPlain)
      (fun bb x q => number_toplevel_cover x (Some 0) RPlain bb q)
      (fun bb x => span_final_ge _ _ (number_toplevel_span (Some 0) RPlain bb x)) 1 (Syntax.declarations f)) as Hd.
  pose proof (number_list_span (number_toplevel (Some 0) RPlain)
      (fun bb x => number_toplevel_span (Some 0) RPlain bb x) (Syntax.declarations f) 1) as Hsp.
  destruct (number_list (number_toplevel (Some 0) RPlain) 1 (Syntax.declarations f)) as [[dc bfin] droots].
  cbn [fst snd length] in Hd, Hsp, Hq |- *.
  destruct Hsp as [nd [Hmap Hbfin]]. cbn [fst snd] in Hmap, Hbfin. destruct Hq as [Hqlo Hqhi].
  assert (Hqb : q < bfin).
  { assert (Hlen : List.length dc = nd).
    { apply (f_equal (@length nat)) in Hmap.
      first [ rewrite length_map in Hmap | rewrite map_length in Hmap ];
      first [ rewrite length_seq in Hmap | rewrite seq_length in Hmap ]; exact Hmap. }
    lia. }
  destruct (Hd q (conj Hqlo Hqb)) as [Hin|Hcov];
    [ apply covered_here; cbn [c_children]; exact Hin | apply covered_cons; exact Hcov ].
Qed.

(* distinct positions ⇒ one cell per position: two members sharing a position are the same cell *)
Lemma occ_unique : forall (occs : list (nat * Cell)) p c1 c2,
  NoDup (map fst occs) -> In (p, c1) occs -> In (p, c2) occs -> c1 = c2.
Proof.
  induction occs as [|[k c] rest IH]; intros p c1 c2 Hnd Hin1 Hin2; [ destruct Hin1 | ].
  cbn [map] in Hnd. apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnotin Hnd'].
  destruct Hin1 as [E1|Hin1]; destruct Hin2 as [E2|Hin2].
  - inversion E1; inversion E2; subst; reflexivity.
  - inversion E1; subst. exfalso; apply Hnotin; apply in_map_iff; exists (p, c2); split; [ reflexivity | exact Hin2 ].
  - inversion E2; subst. exfalso; apply Hnotin; apply in_map_iff; exists (p, c1); split; [ reflexivity | exact Hin1 ].
  - exact (IH p c1 c2 Hnd' Hin1 Hin2).
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

(* §4:252 completeness/inverse: any cell whose parent edge names pp is itself listed among pp's children *)
Lemma number_file_complete : forall f cp ccell pp pcell,
  In (cp, ccell) (number_file f) -> In (pp, pcell) (number_file f) ->
  c_parent ccell = Some pp -> In cp (c_children pcell).
Proof.
  intros f cp ccell pp pcell Hinc Hinp Hpar.
  pose proof (occurrences_distinct f) as Hnd.
  pose proof (number_file_pbounds f cp ccell Hinc pp Hpar) as [Hpp Hcplt].
  pose proof (number_file_positions f) as [count Hpos].
  assert (Hcpin : In cp (map fst (number_file f)))
    by (apply in_map_iff; exists (cp, ccell); split; [ reflexivity | exact Hinc ]).
  rewrite Hpos in Hcpin. apply in_seq in Hcpin.
  assert (Hlen : List.length (number_file f) = count).
  { first [ rewrite <- (length_map fst (number_file f)) | rewrite <- (map_length fst (number_file f)) ].
    rewrite Hpos. first [ apply length_seq | apply seq_length ]. }
  destruct (number_file_cover f cp ltac:(lia)) as [r [rcell [Hinr Hchild]]].
  destruct (number_file_cpo f r rcell Hinr cp Hchild) as [ccell' [Hinc' Hpar']].
  assert (ccell' = ccell) by (apply (occ_unique (number_file f) cp); [ exact Hnd | exact Hinc' | exact Hinc ]).
  subst ccell'. rewrite Hpar in Hpar'. injection Hpar' as Hrpp. subst r.
  assert (rcell = pcell) by (apply (occ_unique (number_file f) pp); [ exact Hnd | exact Hinr | exact Hinp ]).
  subst rcell. exact Hchild.
Qed.

(* a listed child is a real position, so it falls below the block end that the span fixes *)
Lemma child_lt : forall occs n b pos cell r,
  map fst occs = seq b n -> child_parent_ok occs ->
  In (pos, cell) occs -> In r (c_children cell) -> r < b + n.
Proof.
  intros occs n b pos cell r Hmap Hcpo Hin Hr.
  destruct (Hcpo pos cell Hin r Hr) as [rc [Hinr _]].
  apply (in_map fst) in Hinr. cbn [fst] in Hinr. rewrite Hmap in Hinr. apply in_seq in Hinr. lia.
Qed.

(* the extent field exactly delimits each cell's block: its own position at or below it, its children within it *)
Definition ext_ok (bnd : nat) (occs : list (nat * Cell)) : Prop :=
  Forall (fun '(pos, cell) => pos <= c_extent cell < bnd /\
                              (forall r, In r (c_children cell) -> r <= c_extent cell)) occs.

Lemma ext_ok_weaken : forall bnd bnd' occs, bnd <= bnd' -> ext_ok bnd occs -> ext_ok bnd' occs.
Proof.
  intros bnd bnd' occs Hle. apply Forall_impl. intros [pos cell] [[H1 H2] H3]. split; [ split; [ exact H1 | lia ] | exact H3 ].
Qed.

Lemma ext_ok_app : forall bnd c1 c2, ext_ok bnd c1 -> ext_ok bnd c2 -> ext_ok bnd (c1 ++ c2).
Proof. intros bnd c1 c2 H1 H2. apply Forall_app; split; assumption. Qed.

Lemma number_expr_ext : forall e par role b,
  ext_ok (snd (number_expr par role b e)) (fst (number_expr par role b e)).
Proof.
  intro e; induction e using Syntax.Expr_ind'; intros par role b.
  - cbn [number_expr number_leaf fst snd]. constructor; [ | constructor ].
    cbn [c_extent c_children]. split; [ lia | intros r Hr; destruct Hr ].
  - cbn [number_expr number_leaf fst snd]. constructor; [ | constructor ].
    cbn [c_extent c_children]. split; [ lia | intros r Hr; destruct Hr ].
  - specialize (IHe (Some b) RUnaryOperand (S b)).
    pose proof (number_expr_cpo (Syntax.Unary op e) par role b) as Hcpo.
    pose proof (number_expr_spans (Syntax.Unary op e) par role b) as [n [Hmap Hnxt]].
    cbn [number_expr] in Hcpo, Hmap, Hnxt |- *.
    destruct (number_expr (Some b) RUnaryOperand (S b) e) as [kc nxt].
    cbn [fst snd] in IHe, Hcpo, Hmap, Hnxt |- *.
    assert (HSb : S b < b + n)
      by (eapply child_lt; [ exact Hmap | exact Hcpo | left; reflexivity | cbn [c_children]; left; reflexivity ]).
    constructor.
    + cbn [c_extent c_children]. split; [ lia | intros r [Hr|[]]; subst r; lia ].
    + exact IHe.
  - specialize (IHe (Some b) RApplicationHead (S b)).
    pose proof (number_expr_cpo (Syntax.Application e args) par role b) as Hcpo.
    pose proof (number_expr_spans (Syntax.Application e args) par role b) as [n [Hmap Hbfin]].
    cbn [number_expr] in Hcpo, Hmap, Hbfin |- *.
    destruct (number_expr (Some b) RApplicationHead (S b) e) as [hc b1]. cbn [fst snd] in IHe.
    assert (Hda : forall es, Forall (fun a => forall par role bb,
                     ext_ok (snd (number_expr par role bb a)) (fst (number_expr par role bb a))) es ->
      forall i0 bi, (let '(ac, bf, roots) := (fix do_args (i bi : nat) (es : list Syntax.Expr) {struct es}
              : list (nat * Cell) * nat * list nat :=
              match es with
              | [] => ([], bi, [])
              | a :: rest =>
                  let '(ac, bi') := number_expr (Some b) (RApplicationArg i) bi a in
                  let '(rc, bf, roots) := do_args (S i) bi' rest in
                  (ac ++ rc, bf, bi :: roots)
              end) i0 bi es in ext_ok bf ac /\ bi <= bf)).
    { intros es Hall; induction Hall as [| a rest Ha Hrest IHrest]; intros i0 bi.
      - split; [ constructor | lia ].
      - specialize (Ha (Some b) (RApplicationArg i0) bi).
        pose proof (number_expr_span a (Some b) (RApplicationArg i0) bi) as [na [_ [Hbi' _]]].
        destruct (number_expr (Some b) (RApplicationArg i0) bi a) as [ac1 bi'].
        cbn [fst snd] in Ha, Hbi'.
        specialize (IHrest (S i0) bi').
        destruct ((fix do_args (i bi : nat) (es : list Syntax.Expr) {struct es} := _) (S i0) bi' rest)
          as [[rc bf] roots].
        cbn [fst snd] in IHrest |- *. destruct IHrest as [IHrc IHle].
        split; [ apply ext_ok_app; [ eapply ext_ok_weaken; [ | exact Ha ]; lia | exact IHrc ] | lia ]. }
    specialize (Hda args H 0 b1).
    destruct ((fix do_args (i bi : nat) (es : list Syntax.Expr) {struct es} := _) 0 b1 args)
      as [[ac bfin] aroots].
    cbn [fst snd] in Hda, Hmap, Hbfin |- *. destruct Hda as [Hext Hble].
    assert (Hchild : forall r, In r (S b :: aroots) -> r < b + n).
    { intros r Hr. eapply child_lt; [ exact Hmap | exact Hcpo | left; reflexivity | cbn [c_children]; exact Hr ]. }
    constructor.
    + cbn [c_extent c_children]. split.
      * pose proof (Hchild (S b) (or_introl eq_refl)). lia.
      * intros r Hr. pose proof (Hchild r Hr). lia.
    + apply ext_ok_app; [ eapply ext_ok_weaken; [ | exact IHe ]; lia | exact Hext ].
Qed.

Lemma map_seq_pos : forall (occs : list (nat * Cell)) n b, map fst occs = seq b n -> occs <> [] -> 0 < n.
Proof.
  intros [|x l] n b Hmap Hne; [ contradiction | destruct n; [ cbn [map seq] in Hmap; discriminate | lia ] ].
Qed.

Lemma number_typeexpr_ext : forall t par role b,
  ext_ok (snd (number_typeexpr par role b t)) (fst (number_typeexpr par role b t)).
Proof.
  intros. cbn [number_typeexpr number_leaf fst snd]. constructor; [ | constructor ].
  cbn [c_extent c_children]. split; [ lia | intros r Hr; destruct Hr ].
Qed.

Lemma number_bindingname_ext : forall bn par role b,
  ext_ok (snd (number_bindingname par role b bn)) (fst (number_bindingname par role b bn)).
Proof.
  intros. cbn [number_bindingname number_leaf fst snd]. constructor; [ | constructor ].
  cbn [c_extent c_children]. split; [ lia | intros r Hr; destruct Hr ].
Qed.

Lemma number_opttype_ext : forall ot par b,
  ext_ok (snd (fst (number_opttype par b ot))) (fst (fst (number_opttype par b ot))).
Proof.
  intros ot par b. destruct ot as [t|].
  - cbn [number_opttype]. pose proof (number_typeexpr_ext t par RTypeUse b) as Ht.
    destruct (number_typeexpr par RTypeUse b t) as [tc b']. cbn [fst snd] in Ht |- *. exact Ht.
  - cbn [number_opttype fst snd]. constructor.
Qed.

Lemma number_list_ext {A} (g : nat -> A -> list (nat * Cell) * nat) :
  (forall b x, ext_ok (snd (g b x)) (fst (g b x))) ->
  (forall b x, b <= snd (g b x)) ->
  forall b xs, ext_ok (snd (fst (number_list g b xs))) (fst (fst (number_list g b xs))) /\
               b <= snd (fst (number_list g b xs)).
Proof.
  intros Hg Hmono b xs; revert b; induction xs as [|x rest IH]; intro b.
  - cbn [number_list fst snd]. split; [ constructor | lia ].
  - cbn [number_list]. pose proof (Hg b x) as Hgx. pose proof (Hmono b x) as Hm.
    destruct (g b x) as [xc b']. cbn [fst snd] in Hgx, Hm.
    specialize (IH b'). destruct (number_list g b' rest) as [[rc bfin] roots].
    cbn [fst snd] in IH |- *. destruct IH as [IHext IHle].
    split; [ apply ext_ok_app; [ eapply ext_ok_weaken; [ | exact Hgx ]; lia | exact IHext ] | lia ].
Qed.

Lemma number_constspec_ext : forall cs par role b,
  ext_ok (snd (number_constspec par role b cs)) (fst (number_constspec par role b cs)).
Proof.
  intros cs par role b.
  pose proof (number_constspec_cpo par role b cs) as Hcpo.
  pose proof (number_constspec_span par role b cs) as [n [Hmap Hsnd]].
  unfold number_constspec in Hcpo, Hmap, Hsnd |- *.
  destruct (number_list_ext (number_bindingname (Some b) (RSpecName ConstSpecF))
      (fun bb x => number_bindingname_ext x (Some b) (RSpecName ConstSpecF) bb)
      (fun bb x => span_final_ge _ _ (number_bindingname_spans (Some b) (RSpecName ConstSpecF) bb x))
      (S b) (Collections.ne_to_list (Syntax.const_names cs))) as [Hnc Hnc_le].
  destruct (number_list (number_bindingname (Some b) (RSpecName ConstSpecF)) (S b)
      (Collections.ne_to_list (Syntax.const_names cs))) as [[nc b1] nroots].
  cbn [fst snd] in Hnc, Hnc_le, Hcpo, Hmap, Hsnd.
  destruct (Syntax.const_init cs) as [ot vals|].
  - pose proof (number_opttype_ext ot (Some b) b1) as Hoc.
    pose proof (span_final_ge _ _ (number_opttype_span (Some b) b1 ot)) as Hb2.
    destruct (number_opttype (Some b) b1 ot) as [[oc b2] oroots]. cbn [fst snd] in Hoc, Hb2.
    destruct (number_list_ext (number_expr (Some b) RPlain)
        (fun bb x => number_expr_ext x (Some b) RPlain bb)
        (fun bb x => span_final_ge _ _ (number_expr_spans x (Some b) RPlain bb))
        b2 (Collections.ne_to_list vals)) as [Hvc Hvc_le].
    destruct (number_list (number_expr (Some b) RPlain) b2 (Collections.ne_to_list vals)) as [[vc b3] vroots].
    cbn [fst snd] in Hvc, Hvc_le, Hcpo, Hmap, Hsnd |- *.
    assert (Hn : 0 < n) by (apply (map_seq_pos _ n b Hmap); discriminate).
    assert (Hchild : forall r, In r (nroots ++ oroots ++ vroots) -> r < b + n)
      by (intros r Hr; eapply child_lt; [ exact Hmap | exact Hcpo | left; reflexivity | cbn [c_children]; exact Hr ]).
    constructor.
    + cbn [c_extent c_children]. split; [ lia | intros r Hr; pose proof (Hchild r Hr); lia ].
    + apply ext_ok_app; [ eapply ext_ok_weaken; [ | exact Hnc ]; lia
        | apply ext_ok_app; [ eapply ext_ok_weaken; [ | exact Hoc ]; lia | eapply ext_ok_weaken; [ | exact Hvc ]; lia ] ].
  - cbn [fst snd] in Hcpo, Hmap, Hsnd |- *.
    assert (Hn : 0 < n) by (apply (map_seq_pos _ n b Hmap); discriminate).
    assert (Hchild : forall r, In r (nroots ++ []) -> r < b + n)
      by (intros r Hr; eapply child_lt; [ exact Hmap | exact Hcpo | left; reflexivity | cbn [c_children]; exact Hr ]).
    constructor.
    + cbn [c_extent c_children]. split; [ lia | intros r Hr; pose proof (Hchild r Hr); lia ].
    + rewrite app_nil_r. eapply ext_ok_weaken; [ | exact Hnc ]. lia.
Qed.

Lemma number_varspec_ext : forall vs par role b,
  ext_ok (snd (number_varspec par role b vs)) (fst (number_varspec par role b vs)).
Proof.
  intros vs par role b.
  pose proof (number_varspec_cpo par role b vs) as Hcpo.
  pose proof (number_varspec_span par role b vs) as [n [Hmap Hsnd]].
  unfold number_varspec in Hcpo, Hmap, Hsnd |- *.
  destruct (number_list_ext (number_bindingname (Some b) (RSpecName VarSpecF))
      (fun bb x => number_bindingname_ext x (Some b) (RSpecName VarSpecF) bb)
      (fun bb x => span_final_ge _ _ (number_bindingname_spans (Some b) (RSpecName VarSpecF) bb x))
      (S b) (Collections.ne_to_list (Syntax.var_names vs))) as [Hnc Hnc_le].
  destruct (number_list (number_bindingname (Some b) (RSpecName VarSpecF)) (S b)
      (Collections.ne_to_list (Syntax.var_names vs))) as [[nc b1] nroots].
  cbn [fst snd] in Hnc, Hnc_le, Hcpo, Hmap, Hsnd.
  destruct (Syntax.var_init vs) as [t | ot vals].
  - pose proof (number_typeexpr_ext t (Some b) RTypeUse b1) as Htc.
    pose proof (span_final_ge _ _ (number_typeexpr_spans (Some b) RTypeUse b1 t)) as Hb2.
    destruct (number_typeexpr (Some b) RTypeUse b1 t) as [tc b2]. cbn [fst snd] in Htc, Hb2, Hcpo, Hmap, Hsnd |- *.
    assert (Hn : 0 < n) by (apply (map_seq_pos _ n b Hmap); discriminate).
    assert (Hchild : forall r, In r (nroots ++ b1 :: nil) -> r < b + n)
      by (intros r Hr; eapply child_lt; [ exact Hmap | exact Hcpo | left; reflexivity | cbn [c_children]; exact Hr ]).
    constructor.
    + cbn [c_extent c_children]. split; [ lia | intros r Hr; pose proof (Hchild r Hr); lia ].
    + apply ext_ok_app; [ eapply ext_ok_weaken; [ | exact Hnc ]; lia | eapply ext_ok_weaken; [ | exact Htc ]; lia ].
  - pose proof (number_opttype_ext ot (Some b) b1) as Hoc.
    pose proof (span_final_ge _ _ (number_opttype_span (Some b) b1 ot)) as Hb2.
    destruct (number_opttype (Some b) b1 ot) as [[oc b2] oroots]. cbn [fst snd] in Hoc, Hb2.
    destruct (number_list_ext (number_expr (Some b) RPlain)
        (fun bb x => number_expr_ext x (Some b) RPlain bb)
        (fun bb x => span_final_ge _ _ (number_expr_spans x (Some b) RPlain bb))
        b2 (Collections.ne_to_list vals)) as [Hvc Hvc_le].
    destruct (number_list (number_expr (Some b) RPlain) b2 (Collections.ne_to_list vals)) as [[vc b3] vroots].
    cbn [fst snd] in Hvc, Hvc_le, Hcpo, Hmap, Hsnd |- *.
    assert (Hn : 0 < n) by (apply (map_seq_pos _ n b Hmap); discriminate).
    assert (Hchild : forall r, In r (nroots ++ oroots ++ vroots) -> r < b + n)
      by (intros r Hr; eapply child_lt; [ exact Hmap | exact Hcpo | left; reflexivity | cbn [c_children]; exact Hr ]).
    constructor.
    + cbn [c_extent c_children]. split; [ lia | intros r Hr; pose proof (Hchild r Hr); lia ].
    + apply ext_ok_app; [ eapply ext_ok_weaken; [ | exact Hnc ]; lia
        | apply ext_ok_app; [ eapply ext_ok_weaken; [ | exact Hoc ]; lia | eapply ext_ok_weaken; [ | exact Hvc ]; lia ] ].
Qed.

Lemma number_typespec_ext : forall ts par role b,
  ext_ok (snd (number_typespec par role b ts)) (fst (number_typespec par role b ts)).
Proof.
  intros ts par role b.
  pose proof (number_typespec_cpo par role b ts) as Hcpo.
  pose proof (number_typespec_span par role b ts) as [n [Hmap Hsnd]].
  unfold number_typespec in Hcpo, Hmap, Hsnd |- *. destruct ts as [bn t|bn t];
  ( pose proof (number_bindingname_ext bn (Some b) (RSpecName TypeSpecF) (S b)) as Hbc;
    pose proof (span_final_ge _ _ (number_bindingname_spans (Some b) (RSpecName TypeSpecF) (S b) bn)) as Hb1;
    destruct (number_bindingname (Some b) (RSpecName TypeSpecF) (S b) bn) as [bc b1];
    pose proof (number_typeexpr_ext t (Some b) RTypeUse b1) as Htc;
    pose proof (span_final_ge _ _ (number_typeexpr_spans (Some b) RTypeUse b1 t)) as Hbfin;
    destruct (number_typeexpr (Some b) RTypeUse b1 t) as [tc bfin];
    cbn [fst snd] in Hbc, Hb1, Htc, Hbfin, Hcpo, Hmap, Hsnd |- *;
    assert (Hn : 0 < n) by (apply (map_seq_pos _ n b Hmap); discriminate);
    assert (Hchild : forall r, In r (S b :: b1 :: nil) -> r < b + n) by
      (intros r Hr; eapply child_lt; [ exact Hmap | exact Hcpo | left; reflexivity | cbn [c_children]; exact Hr ]);
    constructor;
    [ cbn [c_extent c_children]; split; [ lia | intros r Hr; pose proof (Hchild r Hr); lia ]
    | apply ext_ok_app; [ eapply ext_ok_weaken; [ | exact Hbc ]; lia | eapply ext_ok_weaken; [ | exact Htc ]; lia ] ] ).
Qed.

Lemma number_decl_ext : forall d par role b,
  ext_ok (snd (number_decl par role b d)) (fst (number_decl par role b d)).
Proof.
  intros d par role b.
  pose proof (number_decl_cpo par role b d) as Hcpo.
  pose proof (number_decl_span par role b d) as [n [Hmap Hsnd]].
  unfold number_decl in Hcpo, Hmap, Hsnd |- *. destruct d as [cs|vs|ts];
  [ destruct (number_list_ext (number_constspec (Some b) RPlain)
        (fun bb x => number_constspec_ext x (Some b) RPlain bb)
        (fun bb x => span_final_ge _ _ (number_constspec_span (Some b) RPlain bb x)) (S b) cs) as [Hk _];
    destruct (number_list (number_constspec (Some b) RPlain) (S b) cs) as [[kc bfin] roots]
  | destruct (number_list_ext (number_varspec (Some b) RPlain)
        (fun bb x => number_varspec_ext x (Some b) RPlain bb)
        (fun bb x => span_final_ge _ _ (number_varspec_span (Some b) RPlain bb x)) (S b) vs) as [Hk _];
    destruct (number_list (number_varspec (Some b) RPlain) (S b) vs) as [[kc bfin] roots]
  | destruct (number_list_ext (number_typespec (Some b) RPlain)
        (fun bb x => number_typespec_ext x (Some b) RPlain bb)
        (fun bb x => span_final_ge _ _ (number_typespec_span (Some b) RPlain bb x)) (S b) ts) as [Hk _];
    destruct (number_list (number_typespec (Some b) RPlain) (S b) ts) as [[kc bfin] roots] ];
  cbn [fst snd] in Hk, Hcpo, Hmap, Hsnd |- *;
  ( assert (Hn : 0 < n) by (apply (map_seq_pos _ n b Hmap); discriminate);
    assert (Hchild : forall r, In r roots -> r < b + n) by
      (intros r Hr; eapply child_lt; [ exact Hmap | exact Hcpo | left; reflexivity | cbn [c_children]; exact Hr ]);
    constructor;
    [ cbn [c_extent c_children]; split; [ lia | intros r Hr; pose proof (Hchild r Hr); lia ]
    | eapply ext_ok_weaken; [ | exact Hk ]; lia ] ).
Qed.

Lemma number_stmt_ext : forall s par role b,
  ext_ok (snd (number_stmt par role b s)) (fst (number_stmt par role b s)).
Proof.
  intros s par role b.
  pose proof (number_stmt_cpo par role b s) as Hcpo.
  pose proof (number_stmt_span par role b s) as [n [Hmap Hsnd]].
  unfold number_stmt in Hcpo, Hmap, Hsnd |- *. destruct s as [e|d|names vals].
  - pose proof (number_expr_ext e (Some b) RExprStatementExpr (S b)) as Hc.
    destruct (number_expr (Some b) RExprStatementExpr (S b) e) as [c b']. cbn [fst snd] in Hc, Hcpo, Hmap, Hsnd |- *.
    assert (Hn : 0 < n) by (apply (map_seq_pos _ n b Hmap); discriminate).
    assert (Hchild : forall r, In r (S b :: nil) -> r < b + n)
      by (intros r Hr; eapply child_lt; [ exact Hmap | exact Hcpo | left; reflexivity | cbn [c_children]; exact Hr ]).
    constructor.
    + cbn [c_extent c_children]. split; [ lia | intros r Hr; pose proof (Hchild r Hr); lia ].
    + eapply ext_ok_weaken; [ | exact Hc ]. lia.
  - pose proof (number_decl_ext d (Some b) RPlain (S b)) as Hc.
    destruct (number_decl (Some b) RPlain (S b) d) as [c b']. cbn [fst snd] in Hc, Hcpo, Hmap, Hsnd |- *.
    assert (Hn : 0 < n) by (apply (map_seq_pos _ n b Hmap); discriminate).
    assert (Hchild : forall r, In r (S b :: nil) -> r < b + n)
      by (intros r Hr; eapply child_lt; [ exact Hmap | exact Hcpo | left; reflexivity | cbn [c_children]; exact Hr ]).
    constructor.
    + cbn [c_extent c_children]. split; [ lia | intros r Hr; pose proof (Hchild r Hr); lia ].
    + eapply ext_ok_weaken; [ | exact Hc ]. lia.
  - destruct (number_list_ext (number_bindingname (Some b) RShortLhs)
        (fun bb x => number_bindingname_ext x (Some b) RShortLhs bb)
        (fun bb x => span_final_ge _ _ (number_bindingname_spans (Some b) RShortLhs bb x))
        (S b) (Collections.ne_to_list names)) as [Hnc Hnc_le].
    destruct (number_list (number_bindingname (Some b) RShortLhs) (S b) (Collections.ne_to_list names)) as [[nc b1] nroots].
    cbn [fst snd] in Hnc, Hnc_le.
    destruct (number_list_ext (number_expr (Some b) RPlain)
        (fun bb x => number_expr_ext x (Some b) RPlain bb)
        (fun bb x => span_final_ge _ _ (number_expr_spans x (Some b) RPlain bb))
        b1 (Collections.ne_to_list vals)) as [Hvc Hvc_le].
    destruct (number_list (number_expr (Some b) RPlain) b1 (Collections.ne_to_list vals)) as [[vc b2] vroots].
    cbn [fst snd] in Hvc, Hvc_le, Hcpo, Hmap, Hsnd |- *.
    assert (Hn : 0 < n) by (apply (map_seq_pos _ n b Hmap); discriminate).
    assert (Hchild : forall r, In r (nroots ++ vroots) -> r < b + n)
      by (intros r Hr; eapply child_lt; [ exact Hmap | exact Hcpo | left; reflexivity | cbn [c_children]; exact Hr ]).
    constructor.
    + cbn [c_extent c_children]. split; [ lia | intros r Hr; pose proof (Hchild r Hr); lia ].
    + apply ext_ok_app; [ eapply ext_ok_weaken; [ | exact Hnc ]; lia | eapply ext_ok_weaken; [ | exact Hvc ]; lia ].
Qed.

Lemma number_block_ext : forall blk par role b,
  ext_ok (snd (number_block par role b blk)) (fst (number_block par role b blk)).
Proof.
  intros [stmts] par role b.
  pose proof (number_block_cpo par role b (Syntax.MakeBlock stmts)) as Hcpo.
  pose proof (number_block_span par role b (Syntax.MakeBlock stmts)) as [n [Hmap Hsnd]].
  unfold number_block in Hcpo, Hmap, Hsnd |- *.
  destruct (number_list_ext (number_stmt (Some b) RPlain)
      (fun bb x => number_stmt_ext x (Some b) RPlain bb)
      (fun bb x => span_final_ge _ _ (number_stmt_span (Some b) RPlain bb x)) (S b) stmts) as [Hk _].
  destruct (number_list (number_stmt (Some b) RPlain) (S b) stmts) as [[kc bfin] roots].
  cbn [fst snd] in Hk, Hcpo, Hmap, Hsnd |- *.
  assert (Hn : 0 < n) by (apply (map_seq_pos _ n b Hmap); discriminate).
  assert (Hchild : forall r, In r roots -> r < b + n)
    by (intros r Hr; eapply child_lt; [ exact Hmap | exact Hcpo | left; reflexivity | cbn [c_children]; exact Hr ]).
  constructor.
  + cbn [c_extent c_children]. split; [ lia | intros r Hr; pose proof (Hchild r Hr); lia ].
  + eapply ext_ok_weaken; [ | exact Hk ]. lia.
Qed.

Lemma number_toplevel_ext : forall td par role b,
  ext_ok (snd (number_toplevel par role b td)) (fst (number_toplevel par role b td)).
Proof.
  intros td par role b.
  pose proof (number_toplevel_cpo par role b td) as Hcpo.
  pose proof (number_toplevel_span par role b td) as [n [Hmap Hsnd]].
  unfold number_toplevel in Hcpo, Hmap, Hsnd |- *. destruct td as [d|blk].
  - pose proof (number_decl_ext d (Some b) RPlain (S b)) as Hc.
    destruct (number_decl (Some b) RPlain (S b) d) as [c b']. cbn [fst snd] in Hc, Hcpo, Hmap, Hsnd |- *.
    assert (Hn : 0 < n) by (apply (map_seq_pos _ n b Hmap); discriminate).
    assert (Hchild : forall r, In r (S b :: nil) -> r < b + n)
      by (intros r Hr; eapply child_lt; [ exact Hmap | exact Hcpo | left; reflexivity | cbn [c_children]; exact Hr ]).
    constructor.
    + cbn [c_extent c_children]. split; [ lia | intros r Hr; pose proof (Hchild r Hr); lia ].
    + eapply ext_ok_weaken; [ | exact Hc ]. lia.
  - pose proof (number_block_ext blk (Some b) RPlain (S b)) as Hc.
    destruct (number_block (Some b) RPlain (S b) blk) as [c b']. cbn [fst snd] in Hc, Hcpo, Hmap, Hsnd |- *.
    assert (Hn : 0 < n) by (apply (map_seq_pos _ n b Hmap); discriminate).
    assert (Hchild : forall r, In r (S b :: nil) -> r < b + n)
      by (intros r Hr; eapply child_lt; [ exact Hmap | exact Hcpo | left; reflexivity | cbn [c_children]; exact Hr ]).
    constructor.
    + cbn [c_extent c_children]. split; [ lia | intros r Hr; pose proof (Hchild r Hr); lia ].
    + eapply ext_ok_weaken; [ | exact Hc ]. lia.
Qed.

Lemma number_file_ext : forall f, ext_ok (List.length (number_file f)) (number_file f).
Proof.
  intro f. pose proof (number_file_cpo f) as Hcpo.
  pose proof (number_file_positions f) as [n Hmap].
  unfold number_file in Hcpo, Hmap |- *.
  pose proof (number_list_span (number_toplevel (Some 0) RPlain)
      (fun bb x => number_toplevel_span (Some 0) RPlain bb x) (Syntax.declarations f) 1) as Hsp.
  destruct (number_list_ext (number_toplevel (Some 0) RPlain)
      (fun bb x => number_toplevel_ext x (Some 0) RPlain bb)
      (fun bb x => span_final_ge _ _ (number_toplevel_span (Some 0) RPlain bb x)) 1 (Syntax.declarations f)) as [Hd _].
  destruct (number_list (number_toplevel (Some 0) RPlain) 1 (Syntax.declarations f)) as [[dc bfin] droots].
  cbn [fst snd] in Hcpo, Hmap, Hd, Hsp. destruct Hsp as [nd [Hmapd Hbfin]]. cbn [fst snd] in Hmapd, Hbfin.
  assert (Hlend : List.length dc = nd).
  { first [ rewrite <- (length_map fst) | rewrite <- (map_length fst) ]; rewrite Hmapd; first [ apply length_seq | apply seq_length ]. }
  assert (Hnn : n = S nd).
  { apply (f_equal (@length _)) in Hmap. cbn [map length] in Hmap.
    first [ rewrite length_seq in Hmap | rewrite seq_length in Hmap ].
    first [ rewrite length_map in Hmap | rewrite map_length in Hmap ].
    rewrite Hlend in Hmap. lia. }
  cbn [length]. rewrite Hlend.
  assert (Hchild : forall r, In r droots -> r < 0 + n)
    by (intros r Hr; eapply child_lt; [ exact Hmap | exact Hcpo | left; reflexivity | cbn [c_children]; exact Hr ]).
  constructor.
  + cbn [c_extent c_children]. split; [ lia | intros r Hr; pose proof (Hchild r Hr); lia ].
  + eapply ext_ok_weaken; [ | exact Hd ]. lia.
Qed.

(* extent is exact: in range, at least the node's own position, and at or above every direct child *)
Lemma number_file_extent : forall f pos cell,
  In (pos, cell) (number_file f) ->
  pos <= c_extent cell < List.length (number_file f) /\
  (forall q qc, In (q, qc) (number_file f) -> c_parent qc = Some pos -> q <= c_extent cell).
Proof.
  intros f pos cell Hin. pose proof (number_file_ext f) as Hext.
  unfold ext_ok in Hext. rewrite Forall_forall in Hext.
  destruct (Hext (pos, cell) Hin) as [Hrange Hch]. split; [ exact Hrange | ].
  intros q qc Hinq Hpar. apply Hch. exact (number_file_complete f q qc pos cell Hinq Hin Hpar).
Qed.

(* the kind a structural role commits its node to; the generic RPlain commits to none *)
Definition role_kind_of (r : Role) : option Kind :=
  match r with
  | RApplicationHead | RApplicationArg _ | RUnaryOperand | RExprStatementExpr => Some ExprKind
  | RSpecName _ | RShortLhs => Some BindingNameKind
  | RTypeUse => Some TypeExprKind
  | RPlain => None
  end.

Definition rv_ok (cell : Cell) : Prop :=
  match role_kind_of (c_role cell) with Some k => kind_of_view (c_view cell) = k | None => True end.

Definition role_ok_for (k : Kind) (r : Role) : Prop :=
  match role_kind_of r with None => True | Some k' => k' = k end.

Definition class_ok (occs : list (nat * Cell)) : Prop := Forall (fun '(pos, cell) => rv_ok cell) occs.

Lemma class_ok_app : forall c1 c2, class_ok c1 -> class_ok c2 -> class_ok (c1 ++ c2).
Proof. intros c1 c2 H1 H2. apply Forall_app; split; assumption. Qed.

Lemma rv_ok_mk : forall v role par ext ch k,
  kind_of_view v = k -> role_ok_for k role -> rv_ok (mkCell v role par ext ch).
Proof.
  intros v role par ext ch k Hk Hr. unfold rv_ok, role_ok_for in *. cbn [c_role c_view].
  destruct (role_kind_of role) as [k'|]; [ congruence | exact I ].
Qed.

Lemma number_expr_class : forall e par role b,
  role_ok_for ExprKind role -> class_ok (fst (number_expr par role b e)).
Proof.
  intro e; induction e using Syntax.Expr_ind'; intros par role b Hr; cbn [number_expr].
  - cbn [number_leaf fst]. constructor; [ apply (rv_ok_mk _ _ _ _ _ ExprKind); [ reflexivity | exact Hr ] | constructor ].
  - cbn [number_leaf fst]. constructor; [ apply (rv_ok_mk _ _ _ _ _ ExprKind); [ reflexivity | exact Hr ] | constructor ].
  - specialize (IHe (Some b) RUnaryOperand (S b) ltac:(reflexivity)).
    destruct (number_expr (Some b) RUnaryOperand (S b) e) as [kc nxt]. cbn [fst] in IHe |- *.
    constructor; [ apply (rv_ok_mk _ _ _ _ _ ExprKind); [ reflexivity | exact Hr ] | exact IHe ].
  - specialize (IHe (Some b) RApplicationHead (S b) ltac:(reflexivity)).
    destruct (number_expr (Some b) RApplicationHead (S b) e) as [hc b1]. cbn [fst] in IHe.
    assert (Hda : forall es, Forall (fun a => forall par role bb, role_ok_for ExprKind role ->
                     class_ok (fst (number_expr par role bb a))) es ->
      forall i0 bi, (let '(ac, bf, roots) := (fix do_args (i bi : nat) (es : list Syntax.Expr) {struct es}
              : list (nat * Cell) * nat * list nat :=
              match es with
              | [] => ([], bi, [])
              | a :: rest =>
                  let '(ac, bi') := number_expr (Some b) (RApplicationArg i) bi a in
                  let '(rc, bf, roots) := do_args (S i) bi' rest in
                  (ac ++ rc, bf, bi :: roots)
              end) i0 bi es in class_ok ac)).
    { intros es Hall; induction Hall as [| a rest Ha Hrest IHrest]; intros i0 bi.
      - constructor.
      - specialize (Ha (Some b) (RApplicationArg i0) bi ltac:(reflexivity)).
        destruct (number_expr (Some b) (RApplicationArg i0) bi a) as [ac1 bi']. cbn [fst] in Ha.
        specialize (IHrest (S i0) bi').
        destruct ((fix do_args (i bi : nat) (es : list Syntax.Expr) {struct es} := _) (S i0) bi' rest)
          as [[rc bf] roots].
        cbn [fst snd] in IHrest |- *. apply class_ok_app; [ exact Ha | exact IHrest ]. }
    specialize (Hda args H 0 b1).
    destruct ((fix do_args (i bi : nat) (es : list Syntax.Expr) {struct es} := _) 0 b1 args)
      as [[ac bfin] aroots].
    cbn [fst snd] in Hda |- *.
    constructor; [ apply (rv_ok_mk _ _ _ _ _ ExprKind); [ reflexivity | exact Hr ]
      | apply class_ok_app; [ exact IHe | exact Hda ] ].
Qed.

Lemma number_list_class {A} (g : nat -> A -> list (nat * Cell) * nat) :
  (forall b x, class_ok (fst (g b x))) ->
  forall b xs, class_ok (fst (fst (number_list g b xs))).
Proof.
  intros Hg b xs; revert b; induction xs as [|x rest IH]; intro b.
  - cbn [number_list fst snd]. constructor.
  - cbn [number_list]. pose proof (Hg b x) as Hgx. destruct (g b x) as [xc b'].
    specialize (IH b'). destruct (number_list g b' rest) as [[rc bfin] roots].
    cbn [fst snd] in Hgx, IH |- *. apply class_ok_app; [ exact Hgx | exact IH ].
Qed.

Lemma number_bindingname_class : forall bn par role b,
  role_ok_for BindingNameKind role -> class_ok (fst (number_bindingname par role b bn)).
Proof.
  intros. cbn [number_bindingname number_leaf fst].
  constructor; [ apply (rv_ok_mk _ _ _ _ _ BindingNameKind); [ reflexivity | assumption ] | constructor ].
Qed.

Lemma number_typeexpr_class : forall t par role b,
  role_ok_for TypeExprKind role -> class_ok (fst (number_typeexpr par role b t)).
Proof.
  intros. cbn [number_typeexpr number_leaf fst].
  constructor; [ apply (rv_ok_mk _ _ _ _ _ TypeExprKind); [ reflexivity | assumption ] | constructor ].
Qed.

Lemma number_opttype_class : forall ot par b, class_ok (fst (fst (number_opttype par b ot))).
Proof.
  intros ot par b. destruct ot as [t|].
  - cbn [number_opttype]. pose proof (number_typeexpr_class t par RTypeUse b ltac:(first [ reflexivity | exact I ])) as Ht.
    destruct (number_typeexpr par RTypeUse b t) as [tc b']. cbn [fst] in Ht |- *. exact Ht.
  - cbn [number_opttype fst snd]. constructor.
Qed.

Lemma number_constspec_class : forall cs par role b,
  role_ok_for (SpecKind ConstSpecF) role -> class_ok (fst (number_constspec par role b cs)).
Proof.
  intros cs par role b Hr. unfold number_constspec.
  pose proof (number_list_class (number_bindingname (Some b) (RSpecName ConstSpecF))
      (fun bb x => number_bindingname_class x (Some b) (RSpecName ConstSpecF) bb ltac:(first [ reflexivity | exact I ]))
      (S b) (Collections.ne_to_list (Syntax.const_names cs))) as Hnc.
  destruct (number_list (number_bindingname (Some b) (RSpecName ConstSpecF)) (S b)
      (Collections.ne_to_list (Syntax.const_names cs))) as [[nc b1] nroots].
  cbn [fst snd] in Hnc.
  destruct (Syntax.const_init cs) as [ot vals|].
  - pose proof (number_opttype_class ot (Some b) b1) as Hoc.
    destruct (number_opttype (Some b) b1 ot) as [[oc b2] oroots]. cbn [fst snd] in Hoc.
    pose proof (number_list_class (number_expr (Some b) RPlain)
        (fun bb x => number_expr_class x (Some b) RPlain bb ltac:(first [ reflexivity | exact I ]))
        b2 (Collections.ne_to_list vals)) as Hvc.
    destruct (number_list (number_expr (Some b) RPlain) b2 (Collections.ne_to_list vals)) as [[vc b3] vroots].
    cbn [fst snd] in Hvc. cbn [fst].
    constructor; [ apply (rv_ok_mk _ _ _ _ _ (SpecKind ConstSpecF)); [ reflexivity | exact Hr ]
      | apply class_ok_app; [ exact Hnc | apply class_ok_app; [ exact Hoc | exact Hvc ] ] ].
  - cbn [fst].
    constructor; [ apply (rv_ok_mk _ _ _ _ _ (SpecKind ConstSpecF)); [ reflexivity | exact Hr ]
      | rewrite app_nil_r; exact Hnc ].
Qed.

Lemma number_varspec_class : forall vs par role b,
  role_ok_for (SpecKind VarSpecF) role -> class_ok (fst (number_varspec par role b vs)).
Proof.
  intros vs par role b Hr. unfold number_varspec.
  pose proof (number_list_class (number_bindingname (Some b) (RSpecName VarSpecF))
      (fun bb x => number_bindingname_class x (Some b) (RSpecName VarSpecF) bb ltac:(first [ reflexivity | exact I ]))
      (S b) (Collections.ne_to_list (Syntax.var_names vs))) as Hnc.
  destruct (number_list (number_bindingname (Some b) (RSpecName VarSpecF)) (S b)
      (Collections.ne_to_list (Syntax.var_names vs))) as [[nc b1] nroots].
  cbn [fst snd] in Hnc.
  destruct (Syntax.var_init vs) as [t | ot vals].
  - pose proof (number_typeexpr_class t (Some b) RTypeUse b1 ltac:(first [ reflexivity | exact I ])) as Htc.
    destruct (number_typeexpr (Some b) RTypeUse b1 t) as [tc b2]. cbn [fst] in Htc. cbn [fst].
    constructor; [ apply (rv_ok_mk _ _ _ _ _ (SpecKind VarSpecF)); [ reflexivity | exact Hr ]
      | apply class_ok_app; [ exact Hnc | exact Htc ] ].
  - pose proof (number_opttype_class ot (Some b) b1) as Hoc.
    destruct (number_opttype (Some b) b1 ot) as [[oc b2] oroots]. cbn [fst snd] in Hoc.
    pose proof (number_list_class (number_expr (Some b) RPlain)
        (fun bb x => number_expr_class x (Some b) RPlain bb ltac:(first [ reflexivity | exact I ]))
        b2 (Collections.ne_to_list vals)) as Hvc.
    destruct (number_list (number_expr (Some b) RPlain) b2 (Collections.ne_to_list vals)) as [[vc b3] vroots].
    cbn [fst snd] in Hvc. cbn [fst].
    constructor; [ apply (rv_ok_mk _ _ _ _ _ (SpecKind VarSpecF)); [ reflexivity | exact Hr ]
      | apply class_ok_app; [ exact Hnc | apply class_ok_app; [ exact Hoc | exact Hvc ] ] ].
Qed.

Lemma number_typespec_class : forall ts par role b,
  role_ok_for (SpecKind TypeSpecF) role -> class_ok (fst (number_typespec par role b ts)).
Proof.
  intros ts par role b Hr. unfold number_typespec; destruct ts as [bn t|bn t];
  ( pose proof (number_bindingname_class bn (Some b) (RSpecName TypeSpecF) (S b) ltac:(first [ reflexivity | exact I ])) as Hbc;
    destruct (number_bindingname (Some b) (RSpecName TypeSpecF) (S b) bn) as [bc b1]; cbn [fst] in Hbc;
    pose proof (number_typeexpr_class t (Some b) RTypeUse b1 ltac:(first [ reflexivity | exact I ])) as Htc;
    destruct (number_typeexpr (Some b) RTypeUse b1 t) as [tc bfin]; cbn [fst] in Htc; cbn [fst];
    constructor; [ apply (rv_ok_mk _ _ _ _ _ (SpecKind TypeSpecF)); [ reflexivity | exact Hr ]
      | apply class_ok_app; [ exact Hbc | exact Htc ] ] ).
Qed.

Lemma number_decl_class : forall d par role b,
  role_ok_for DeclKind role -> class_ok (fst (number_decl par role b d)).
Proof.
  intros d par role b Hr. unfold number_decl. destruct d as [cs|vs|ts];
  [ pose proof (number_list_class (number_constspec (Some b) RPlain)
        (fun bb x => number_constspec_class x (Some b) RPlain bb ltac:(first [ reflexivity | exact I ])) (S b) cs) as Hk;
    destruct (number_list (number_constspec (Some b) RPlain) (S b) cs) as [[kc bfin] roots]
  | pose proof (number_list_class (number_varspec (Some b) RPlain)
        (fun bb x => number_varspec_class x (Some b) RPlain bb ltac:(first [ reflexivity | exact I ])) (S b) vs) as Hk;
    destruct (number_list (number_varspec (Some b) RPlain) (S b) vs) as [[kc bfin] roots]
  | pose proof (number_list_class (number_typespec (Some b) RPlain)
        (fun bb x => number_typespec_class x (Some b) RPlain bb ltac:(first [ reflexivity | exact I ])) (S b) ts) as Hk;
    destruct (number_list (number_typespec (Some b) RPlain) (S b) ts) as [[kc bfin] roots] ];
  cbn [fst snd] in Hk; cbn [fst];
  ( constructor; [ apply (rv_ok_mk _ _ _ _ _ DeclKind); [ reflexivity | exact Hr ] | exact Hk ] ).
Qed.

Lemma number_stmt_class : forall s par role b,
  role_ok_for StmtKind role -> class_ok (fst (number_stmt par role b s)).
Proof.
  intros s par role b Hr. unfold number_stmt. destruct s as [e|d|names vals].
  - pose proof (number_expr_class e (Some b) RExprStatementExpr (S b) ltac:(first [ reflexivity | exact I ])) as Hc.
    destruct (number_expr (Some b) RExprStatementExpr (S b) e) as [c b']. cbn [fst] in Hc. cbn [fst].
    constructor; [ apply (rv_ok_mk _ _ _ _ _ StmtKind); [ reflexivity | exact Hr ] | exact Hc ].
  - pose proof (number_decl_class d (Some b) RPlain (S b) ltac:(first [ reflexivity | exact I ])) as Hc.
    destruct (number_decl (Some b) RPlain (S b) d) as [c b']. cbn [fst] in Hc. cbn [fst].
    constructor; [ apply (rv_ok_mk _ _ _ _ _ StmtKind); [ reflexivity | exact Hr ] | exact Hc ].
  - pose proof (number_list_class (number_bindingname (Some b) RShortLhs)
        (fun bb x => number_bindingname_class x (Some b) RShortLhs bb ltac:(first [ reflexivity | exact I ]))
        (S b) (Collections.ne_to_list names)) as Hnc.
    destruct (number_list (number_bindingname (Some b) RShortLhs) (S b) (Collections.ne_to_list names)) as [[nc b1] nroots].
    cbn [fst snd] in Hnc.
    pose proof (number_list_class (number_expr (Some b) RPlain)
        (fun bb x => number_expr_class x (Some b) RPlain bb ltac:(first [ reflexivity | exact I ]))
        b1 (Collections.ne_to_list vals)) as Hvc.
    destruct (number_list (number_expr (Some b) RPlain) b1 (Collections.ne_to_list vals)) as [[vc b2] vroots].
    cbn [fst snd] in Hvc. cbn [fst].
    constructor; [ apply (rv_ok_mk _ _ _ _ _ StmtKind); [ reflexivity | exact Hr ]
      | apply class_ok_app; [ exact Hnc | exact Hvc ] ].
Qed.

Lemma number_block_class : forall blk par role b,
  role_ok_for BlockKind role -> class_ok (fst (number_block par role b blk)).
Proof.
  intros [stmts] par role b Hr. unfold number_block.
  pose proof (number_list_class (number_stmt (Some b) RPlain)
      (fun bb x => number_stmt_class x (Some b) RPlain bb ltac:(first [ reflexivity | exact I ])) (S b) stmts) as Hk.
  destruct (number_list (number_stmt (Some b) RPlain) (S b) stmts) as [[kc bfin] roots].
  cbn [fst snd] in Hk. cbn [fst].
  constructor; [ apply (rv_ok_mk _ _ _ _ _ BlockKind); [ reflexivity | exact Hr ] | exact Hk ].
Qed.

Lemma number_toplevel_class : forall td par role b,
  role_ok_for TopKind role -> class_ok (fst (number_toplevel par role b td)).
Proof.
  intros td par role b Hr. unfold number_toplevel. destruct td as [d|blk].
  - pose proof (number_decl_class d (Some b) RPlain (S b) ltac:(first [ reflexivity | exact I ])) as Hc.
    destruct (number_decl (Some b) RPlain (S b) d) as [c b']. cbn [fst] in Hc. cbn [fst].
    constructor; [ apply (rv_ok_mk _ _ _ _ _ TopKind); [ reflexivity | exact Hr ] | exact Hc ].
  - pose proof (number_block_class blk (Some b) RPlain (S b) ltac:(first [ reflexivity | exact I ])) as Hc.
    destruct (number_block (Some b) RPlain (S b) blk) as [c b']. cbn [fst] in Hc. cbn [fst].
    constructor; [ apply (rv_ok_mk _ _ _ _ _ TopKind); [ reflexivity | exact Hr ] | exact Hc ].
Qed.

(* §4:255 role/kind exact: every cell whose role commits to a kind carries a view of exactly that kind *)
Lemma number_file_class : forall f, class_ok (number_file f).
Proof.
  intro f. unfold number_file.
  pose proof (number_list_class (number_toplevel (Some 0) RPlain)
      (fun bb x => number_toplevel_class x (Some 0) RPlain bb ltac:(first [ reflexivity | exact I ]))
      1 (Syntax.declarations f)) as Hd.
  destruct (number_list (number_toplevel (Some 0) RPlain) 1 (Syntax.declarations f)) as [[dc bfin] droots].
  cbn [fst snd] in Hd |- *.
  constructor; [ apply (rv_ok_mk _ _ _ _ _ FileKind); [ reflexivity | exact I ] | exact Hd ].
Qed.

(* round-trip (§4:251): each occurrence's tag is exactly its source construct's role and shallow view *)
Lemma number_bindingname_view : forall par role b bn,
  exists cell rest, fst (number_bindingname par role b bn) = (b, cell) :: rest
                    /\ c_role cell = role /\ c_view cell = VBindingName bn.
Proof. intros. cbn [number_bindingname number_leaf fst]. do 2 eexists; split; [ reflexivity | split; reflexivity ]. Qed.

Lemma number_typeexpr_view : forall par role b t,
  exists cell rest, fst (number_typeexpr par role b t) = (b, cell) :: rest
                    /\ c_role cell = role /\ c_view cell = VTypeExpr t.
Proof. intros. cbn [number_typeexpr number_leaf fst]. do 2 eexists; split; [ reflexivity | split; reflexivity ]. Qed.

Lemma number_constspec_view : forall par role b cs,
  exists cell rest, fst (number_constspec par role b cs) = (b, cell) :: rest
                    /\ c_role cell = role /\ c_view cell = VConstSpec (constspec_shape cs).
Proof.
  intros par role b cs. unfold number_constspec.
  destruct (number_list (number_bindingname (Some b) (RSpecName ConstSpecF)) (S b)
             (Collections.ne_to_list (Syntax.const_names cs))) as [[nc b1] nroots].
  destruct (Syntax.const_init cs) as [ot vals|].
  - destruct (number_opttype (Some b) b1 ot) as [[oc b2] oroots].
    destruct (number_list (number_expr (Some b) RPlain) b2 (Collections.ne_to_list vals)) as [[vc b3] vroots].
    cbn [fst]. do 2 eexists; split; [ reflexivity | split; reflexivity ].
  - cbn [fst]. do 2 eexists; split; [ reflexivity | split; reflexivity ].
Qed.

Lemma number_varspec_view : forall par role b vs,
  exists cell rest, fst (number_varspec par role b vs) = (b, cell) :: rest
                    /\ c_role cell = role /\ c_view cell = VVarSpec (varspec_shape vs).
Proof.
  intros par role b vs. unfold number_varspec.
  destruct (number_list (number_bindingname (Some b) (RSpecName VarSpecF)) (S b)
             (Collections.ne_to_list (Syntax.var_names vs))) as [[nc b1] nroots].
  destruct (Syntax.var_init vs) as [t | ot vals].
  - destruct (number_typeexpr (Some b) RTypeUse b1 t) as [tc b2].
    cbn [fst]. do 2 eexists; split; [ reflexivity | split; reflexivity ].
  - destruct (number_opttype (Some b) b1 ot) as [[oc b2] oroots].
    destruct (number_list (number_expr (Some b) RPlain) b2 (Collections.ne_to_list vals)) as [[vc b3] vroots].
    cbn [fst]. do 2 eexists; split; [ reflexivity | split; reflexivity ].
Qed.

Lemma number_typespec_view : forall par role b ts,
  exists cell rest, fst (number_typespec par role b ts) = (b, cell) :: rest
                    /\ c_role cell = role /\ c_view cell = VTypeSpec (typespec_shape ts).
Proof.
  intros par role b ts. unfold number_typespec; destruct ts as [bn t|bn t];
    (destruct (number_bindingname (Some b) (RSpecName TypeSpecF) (S b) bn) as [bc b1];
     destruct (number_typeexpr (Some b) RTypeUse b1 t) as [tc bfin];
     cbn [fst]; do 2 eexists; split; [ reflexivity | split; reflexivity ]).
Qed.

Lemma number_decl_view : forall par role b d,
  exists cell rest, fst (number_decl par role b d) = (b, cell) :: rest
                    /\ c_role cell = role /\ c_view cell = VDecl (decl_flavor d).
Proof.
  intros par role b d. unfold number_decl.
  destruct d as [cs|vs|ts];
    [ destruct (number_list (number_constspec (Some b) RPlain) (S b) cs) as [[kc bfin] roots]
    | destruct (number_list (number_varspec (Some b) RPlain) (S b) vs) as [[kc bfin] roots]
    | destruct (number_list (number_typespec (Some b) RPlain) (S b) ts) as [[kc bfin] roots] ];
    (cbn [fst]; do 2 eexists; split; [ reflexivity | split; reflexivity ]).
Qed.

Lemma number_stmt_view : forall par role b s,
  exists cell rest, fst (number_stmt par role b s) = (b, cell) :: rest
                    /\ c_role cell = role /\ c_view cell = VStmt (stmt_shape s).
Proof.
  intros par role b s. unfold number_stmt.
  destruct s as [e|d|names vals];
    [ destruct (number_expr (Some b) RExprStatementExpr (S b) e) as [c b']
    | destruct (number_decl (Some b) RPlain (S b) d) as [c b']
    | destruct (number_list (number_bindingname (Some b) RShortLhs) (S b) (Collections.ne_to_list names)) as [[nc b1] nroots];
      destruct (number_list (number_expr (Some b) RPlain) b1 (Collections.ne_to_list vals)) as [[vc b2] vroots] ];
    (cbn [fst]; do 2 eexists; split; [ reflexivity | split; reflexivity ]).
Qed.

Lemma number_block_view : forall par role b blk,
  exists cell rest, fst (number_block par role b blk) = (b, cell) :: rest
                    /\ c_role cell = role /\ c_view cell = VBlock.
Proof.
  intros par role b [stmts]. unfold number_block.
  destruct (number_list (number_stmt (Some b) RPlain) (S b) stmts) as [[kc bfin] roots].
  cbn [fst]. do 2 eexists; split; [ reflexivity | split; reflexivity ].
Qed.

Lemma number_toplevel_view : forall par role b td,
  exists cell rest, fst (number_toplevel par role b td) = (b, cell) :: rest
                    /\ c_role cell = role /\ c_view cell = VTop (top_shape td).
Proof.
  intros par role b td. unfold number_toplevel.
  destruct td as [d|blk];
    [ destruct (number_decl (Some b) RPlain (S b) d) as [c b']
    | destruct (number_block (Some b) RPlain (S b) blk) as [c b'] ];
    (cbn [fst]; do 2 eexists; split; [ reflexivity | split; reflexivity ]).
Qed.

(* main (§4:256): a Main top-level is tagged VTop TSMain and its one child is exactly the body block *)
Lemma number_main : forall par role b blk,
  exists cell bcell rest,
    fst (number_toplevel par role b (Syntax.Main blk)) = (b, cell) :: rest /\
    c_view cell = VTop TSMain /\ c_children cell = [S b] /\
    In (S b, bcell) rest /\ c_view bcell = VBlock.
Proof.
  intros par role b blk. unfold number_toplevel.
  destruct (number_block_view (Some b) RPlain (S b) blk) as [bcell [brest [Hb [_ Hbv]]]].
  destruct (number_block (Some b) RPlain (S b) blk) as [bc b']. cbn [fst] in Hb.
  cbn [fst]. exists (mkCell (VTop (top_shape (Syntax.Main blk))) role par (b' - 1) [S b]), bcell, bc.
  split; [ reflexivity | split; [ reflexivity | split; [ reflexivity | split; [ rewrite Hb; left; reflexivity | exact Hbv ] ] ] ].
Qed.

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

(* strictly ascending child positions: the ordinal order IS the source order *)
Fixpoint asc (l : list nat) : Prop :=
  match l with a :: ((b :: _) as t) => a < b /\ asc t | _ => True end.

Lemma asc_cons : forall a l, (match l with b :: _ => a < b | [] => True end) -> asc l -> asc (a :: l).
Proof. intros a [|b t] Hh Ht; cbn; [ exact I | exact (conj Hh Ht) ]. Qed.

Lemma asc_app : forall l1 l2, asc l1 -> asc l2 -> (forall x y, In x l1 -> In y l2 -> x < y) -> asc (l1 ++ l2).
Proof.
  induction l1 as [|a t IH]; intros l2 H1 H2 Hlt; cbn [app]; [ exact H2 |].
  apply asc_cons.
  - destruct t as [|b t']; cbn [app].
    + destruct l2 as [|y l2']; [ exact I | apply Hlt; [ left; reflexivity | left; reflexivity ] ].
    + exact (proj1 H1).
  - apply IH; [ destruct t as [|b t']; [ exact I | exact (proj2 H1) ] | exact H2 |].
    intros x y Hx Hy. apply Hlt; [ right; exact Hx | exact Hy ].
Qed.

Lemma asc_head_lt : forall t a j y, asc (a :: t) -> nth_error t j = Some y -> a < y.
Proof.
  induction t as [|b t' IH]; intros a j y Ha Hy; [ destruct j; discriminate Hy |].
  destruct Ha as [Hab Ht]. destruct j as [|j'].
  - injection Hy as <-. exact Hab.
  - cbn in Hy. specialize (IH b j' y Ht Hy). lia.
Qed.

Lemma asc_nth : forall l i j x y, asc l -> i < j -> nth_error l i = Some x -> nth_error l j = Some y -> x < y.
Proof.
  induction l as [|a t IH]; intros i j x y Ha Hij Hx Hy; [ destruct i; discriminate Hx |].
  destruct i as [|i'].
  - injection Hx as <-. destruct j as [|j']; [ lia |]. cbn in Hy. exact (asc_head_lt t a j' y Ha Hy).
  - destruct j as [|j']; [ lia |]. cbn in Hx, Hy.
    assert (Htasc : asc t) by (destruct t; [ exact I | exact (proj2 Ha) ]).
    exact (IH i' j' x y Htasc ltac:(lia) Hx Hy).
Qed.

(* each spec flavor's exact child view class: a declaration's children are exactly its flavor's specs *)
Definition spec_view_of_flavor (fl : SpecFlavor) (v : NodeView) : Prop :=
  match fl, v with
  | ConstSpecF, VConstSpec _ => True
  | VarSpecF, VVarSpec _ => True
  | TypeSpecF, VTypeSpec _ => True
  | _, _ => False
  end.

(* the reverse layout clauses: a spec, statement, or declaration child pins its parent's exact view class *)
Definition reverse_clauses (pv cv : NodeView) : Prop :=
  (forall fl, spec_view_of_flavor fl cv -> pv = VDecl fl)
  /\ (forall sh, cv = VStmt sh -> pv = VBlock)
  /\ (forall fl, cv = VDecl fl -> pv = VStmt SSDecl \/ pv = VTop TSTopDecl).

(* a child view that is no spec, statement, or declaration discharges every reverse clause *)
Definition no_reverse (v : NodeView) : Prop :=
  match v with VConstSpec _ | VVarSpec _ | VTypeSpec _ | VStmt _ | VDecl _ => False | _ => True end.

Lemma no_reverse_clauses : forall pv cv, no_reverse cv -> reverse_clauses pv cv.
Proof.
  intros pv cv H. destruct cv; try (exact (match H with end));
    (split; [ intros fl Hs; destruct fl; exact (match Hs with end)
            | split; intros ? He; discriminate He ]).
Qed.

Lemma stmt_reverse_clauses : forall sh, reverse_clauses VBlock (VStmt sh).
Proof.
  intro sh. split; [ intros fl Hs; destruct fl; exact (match Hs with end) |].
  split; [ intros ? _; reflexivity | intros ? He; discriminate He ].
Qed.

Lemma spec_reverse_clauses : forall fl0 v, spec_view_of_flavor fl0 v -> reverse_clauses (VDecl fl0) v.
Proof.
  intros fl0 v Hv. destruct fl0; destruct v; try (exact (match Hv with end));
    (split; [ intros fl Hs; destruct fl; try (exact (match Hs with end)); reflexivity
            | split; intros ? He; discriminate He ]).
Qed.

Lemma decl_stmt_reverse_clauses : forall fl, reverse_clauses (VStmt SSDecl) (VDecl fl).
Proof.
  intro fl. split; [ intros fl0 Hs; destruct fl0; exact (match Hs with end) |].
  split; [ intros ? He; discriminate He | intros ? _; left; reflexivity ].
Qed.

Lemma decl_top_reverse_clauses : forall fl, reverse_clauses (VTop TSTopDecl) (VDecl fl).
Proof.
  intro fl. split; [ intros fl0 Hs; destruct fl0; exact (match Hs with end) |].
  split; [ intros ? He; discriminate He | intros ? _; right; reflexivity ].
Qed.

(* per-parent layout: exact child roles; main, spec, statement and declaration adjacency in both directions *)
Definition child_layout_ok (occs : list (nat * Cell)) : Prop :=
  forall pos cell, In (pos, cell) occs ->
    forall k cp, nth_error (c_children cell) k = Some cp ->
      exists cc, In (cp, cc) occs
                 /\ c_role cc = layout_role (c_view cell) k
                 /\ (c_view cell = VTop TSMain -> c_view cc = VBlock)
                 /\ (forall fl, c_view cell = VDecl fl -> spec_view_of_flavor fl (c_view cc))
                 /\ reverse_clauses (c_view cell) (c_view cc).

Lemma child_layout_ok_app : forall c1 c2, child_layout_ok c1 -> child_layout_ok c2 -> child_layout_ok (c1 ++ c2).
Proof.
  intros c1 c2 H1 H2 pos cell Hin k cp Hcp. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  - destruct (H1 pos cell Hin k cp Hcp) as [cc [Hc Hp]]. exists cc.
    split; [ apply in_or_app; left; exact Hc | exact Hp ].
  - destruct (H2 pos cell Hin k cp Hcp) as [cc [Hc Hp]]. exists cc.
    split; [ apply in_or_app; right; exact Hc | exact Hp ].
Qed.

Lemma child_layout_ok_node : forall self cell kids,
  (forall k cp, nth_error (c_children cell) k = Some cp ->
     exists cc, In (cp, cc) ((self, cell) :: kids)
                /\ c_role cc = layout_role (c_view cell) k
                /\ (c_view cell = VTop TSMain -> c_view cc = VBlock)
                /\ (forall fl, c_view cell = VDecl fl -> spec_view_of_flavor fl (c_view cc))
                /\ reverse_clauses (c_view cell) (c_view cc)) ->
  child_layout_ok kids -> child_layout_ok ((self, cell) :: kids).
Proof.
  intros self cell kids Hself Hkids pos c Hin k cp Hcp. destruct Hin as [Heq|Hin].
  - inversion Heq; subst. exact (Hself k cp Hcp).
  - destruct (Hkids pos c Hin k cp Hcp) as [cc [Hc Hp]]. exists cc. split; [ right; exact Hc | exact Hp ].
Qed.

(* the per-cell shape law: children ascend in source order and match the count the shape fixes *)
Definition cell_shape_ok (cell : Cell) : Prop :=
  asc (c_children cell) /\
  match layout_count (c_view cell) with Some n => length (c_children cell) = n | None => True end.
Definition shape_ok (occs : list (nat * Cell)) : Prop := Forall (fun kv => cell_shape_ok (snd kv)) occs.

Lemma shape_ok_app : forall c1 c2, shape_ok c1 -> shape_ok c2 -> shape_ok (c1 ++ c2).
Proof. intros c1 c2 H1 H2. apply Forall_app; split; assumption. Qed.

(* one roots account for a numbered segment: count, ascent, bounds, and per-root cell resolution *)
Lemma number_list_roots {A} (g : nat -> A -> list (nat * Cell) * nat) (P : Cell -> Prop) :
  (forall b x, spans (g b x) b) ->
  (forall b x, exists cell rest, fst (g b x) = (b, cell) :: rest /\ P cell) ->
  forall xs b,
    let '(c, b', roots) := number_list g b xs in
    length roots = length xs
    /\ asc roots
    /\ (forall r0, In r0 roots -> b <= r0 < b')
    /\ (forall k r0, nth_error roots k = Some r0 -> exists cell, In (r0, cell) c /\ P cell).
Proof.
  intros Hspan Hroot xs; induction xs as [|x rest IH]; intro b.
  - cbn [number_list]. split; [ reflexivity | split; [ exact I | split ] ];
      [ intros r0 [] | intros k r0 Hk; destruct k; discriminate Hk ].
  - cbn [number_list].
    pose proof (Hspan b x) as Hsx. pose proof (Hroot b x) as [cell [crest [Hc HP]]].
    destruct (g b x) as [xc b1]. cbn [fst snd] in Hsx, Hc.
    destruct Hsx as [n1 [Hmap He]]. cbn [fst snd] in Hmap, He.
    assert (Hn1 : 0 < n1).
    { destruct n1; [ rewrite Hc in Hmap; discriminate Hmap | lia ]. }
    pose proof (number_list_span g Hspan rest b1) as Hsr.
    specialize (IH b1). destruct (number_list g b1 rest) as [[rc b2] roots1].
    destruct IH as [Hlen [Hasc [Hbnd Hnth]]].
    destruct Hsr as [n2 [_ Hb2]]. cbn [fst snd] in Hb2.
    split; [| split; [| split ]].
    + cbn [length]. rewrite Hlen. reflexivity.
    + apply asc_cons; [ destruct roots1 as [|r1 t1]; [ exact I | destruct (Hbnd r1 (or_introl eq_refl)); lia ] | exact Hasc ].
    + intros r0 [Hr0|Hr0]; [ subst r0; lia | destruct (Hbnd r0 Hr0); lia ].
    + intros k r0 Hk. destruct k as [|k'].
      * injection Hk as <-. exists cell. split; [ apply in_or_app; left; rewrite Hc; left; reflexivity | exact HP ].
      * cbn in Hk. destruct (Hnth k' r0 Hk) as [cc [Hcc HPc]]. exists cc.
        split; [ apply in_or_app; right; exact Hcc | exact HPc ].
Qed.

Lemma number_list_shape {A} (g : nat -> A -> list (nat * Cell) * nat) :
  (forall b x, shape_ok (fst (g b x))) ->
  forall b xs, shape_ok (fst (fst (number_list g b xs))).
Proof.
  intros Hg b xs; revert b; induction xs as [|x rest IH]; intro b.
  - constructor.
  - cbn [number_list]. pose proof (Hg b x) as Hgx. destruct (g b x) as [xc b'].
    specialize (IH b'). destruct (number_list g b' rest) as [[rc bfin] roots].
    cbn [fst snd] in Hgx, IH |- *. apply shape_ok_app; [ exact Hgx | exact IH ].
Qed.

Lemma number_list_layout {A} (g : nat -> A -> list (nat * Cell) * nat) :
  (forall b x, child_layout_ok (fst (g b x))) ->
  forall b xs, child_layout_ok (fst (fst (number_list g b xs))).
Proof.
  intros Hg b xs; revert b; induction xs as [|x rest IH]; intro b.
  - intros pos c Hin; destruct Hin.
  - cbn [number_list]. pose proof (Hg b x) as Hgx. destruct (g b x) as [xc b'].
    specialize (IH b'). destruct (number_list g b' rest) as [[rc bfin] roots].
    cbn [fst snd] in Hgx, IH |- *. apply child_layout_ok_app; [ exact Hgx | exact IH ].
Qed.

Lemma number_expr_shape : forall e par role b, shape_ok (fst (number_expr par role b e)).
Proof.
  intro e; induction e using Syntax.Expr_ind'; intros par role b; cbn [number_expr].
  - cbn [number_leaf fst]. constructor; [ cbn; split; [ exact I | reflexivity ] | constructor ].
  - cbn [number_leaf fst]. constructor; [ cbn; split; [ exact I | reflexivity ] | constructor ].
  - specialize (IHe (Some b) RUnaryOperand (S b)).
    destruct (number_expr (Some b) RUnaryOperand (S b) e) as [kc nxt]. cbn [fst] in IHe |- *.
    constructor; [ cbn; split; [ exact I | reflexivity ] | exact IHe ].
  - specialize (IHe (Some b) RApplicationHead (S b)).
    pose proof (number_expr_span e (Some b) RApplicationHead (S b)) as [m1 [_ [Hb1 Hm1]]].
    destruct (number_expr (Some b) RApplicationHead (S b) e) as [hc b1]. cbn [fst snd] in IHe, Hb1.
    assert (Hda : forall es, Forall (fun a => forall par role bb, shape_ok (fst (number_expr par role bb a))) es ->
      forall i0 bi, (let '(ac, bf, roots) := (fix do_args (i bi : nat) (es : list Syntax.Expr) {struct es}
              : list (nat * Cell) * nat * list nat :=
              match es with
              | [] => ([], bi, [])
              | a :: rest =>
                  let '(ac, bi') := number_expr (Some b) (RApplicationArg i) bi a in
                  let '(rc, bf, roots) := do_args (S i) bi' rest in
                  (ac ++ rc, bf, bi :: roots)
              end) i0 bi es in
        shape_ok ac /\ asc roots /\ bi <= bf /\ (forall r, In r roots -> bi <= r < bf))).
    { intros es Hall; induction Hall as [| a rest Ha Hrest IHrest]; intros i0 bi.
      - split; [ constructor | split; [ exact I | split; [ lia | intros r [] ] ] ].
      - pose proof (number_expr_span a (Some b) (RApplicationArg i0) bi) as [na [_ [Hbi' Hna]]].
        specialize (Ha (Some b) (RApplicationArg i0) bi).
        destruct (number_expr (Some b) (RApplicationArg i0) bi a) as [ac1 bi']. cbn [fst snd] in Ha, Hbi'.
        specialize (IHrest (S i0) bi').
        destruct ((fix do_args (i bi : nat) (es : list Syntax.Expr) {struct es} := _) (S i0) bi' rest)
          as [[rc bf] roots]. destruct IHrest as [Hrs [Hra [Hrb Hrbnd]]]. cbn [fst snd] in *.
        split; [ apply shape_ok_app; [ exact Ha | exact Hrs ] |].
        split; [ apply asc_cons; [ destruct roots as [|r1 t1]; [ exact I | destruct (Hrbnd r1 (or_introl eq_refl)); lia ] | exact Hra ] |].
        split; [ lia |].
        intros r [Hr|Hr]; [ subst r; lia | destruct (Hrbnd r Hr); lia ]. }
    specialize (Hda args H 0 b1).
    destruct ((fix do_args (i bi : nat) (es : list Syntax.Expr) {struct es} := _) 0 b1 args)
      as [[ac bfin] aroots]. destruct Hda as [Hacs [Haca [Hacb Hacbnd]]]. cbn [fst snd] in *.
    constructor.
    + cbn [snd]. split.
      * cbn [c_children]. apply asc_cons;
          [ destruct aroots as [|r1 t1]; [ exact I | destruct (Hacbnd r1 (or_introl eq_refl)); lia ] | exact Haca ].
      * cbn [c_view layout_count]. exact I.
    + apply shape_ok_app; [ exact IHe | exact Hacs ].
Qed.

Lemma number_typeexpr_shape : forall par role b t, shape_ok (fst (number_typeexpr par role b t)).
Proof. intros. cbn [number_typeexpr number_leaf fst]. constructor; [ cbn; split; [ exact I | reflexivity ] | constructor ]. Qed.
Lemma number_bindingname_shape : forall par role b bn, shape_ok (fst (number_bindingname par role b bn)).
Proof. intros. cbn [number_bindingname number_leaf fst]. constructor; [ cbn; split; [ exact I | reflexivity ] | constructor ]. Qed.

Lemma number_opttype_shape : forall self b ot, shape_ok (fst (fst (number_opttype (Some self) b ot))).
Proof.
  intros self b [t|]; cbn [number_opttype].
  - pose proof (number_typeexpr_shape (Some self) RTypeUse b t) as Hs.
    destruct (number_typeexpr (Some self) RTypeUse b t) as [c b']. cbn [fst snd] in Hs |- *. exact Hs.
  - constructor.
Qed.

(* the opttype roots: exactly one RTypeUse root when the type is present, none otherwise *)
Lemma number_opttype_roots : forall self b ot,
  let '(c, b', roots) := number_opttype (Some self) b ot in
  length roots = (match ot with Some _ => 1 | None => 0 end)
  /\ asc roots /\ b <= b' /\ (forall r, In r roots -> b <= r < b')
  /\ (forall k r0, nth_error roots k = Some r0 ->
        exists cell, In (r0, cell) c /\ c_role cell = RTypeUse
                     /\ no_reverse (c_view cell)).
Proof.
  intros self b [t|]; cbn [number_opttype].
  - destruct (number_typeexpr_view (Some self) RTypeUse b t) as [cell [rest [Hf [Hr Hv]]]].
    pose proof (number_typeexpr_spans (Some self) RTypeUse b t) as [n [Hm He]].
    destruct (number_typeexpr (Some self) RTypeUse b t) as [c b']. cbn [fst snd] in Hf, Hm, He.
    assert (Hn : 0 < n) by (destruct n; [ rewrite Hf in Hm; discriminate Hm | lia ]).
    split; [ reflexivity | split; [ exact I | split; [ lia | split ] ] ].
    + intros r [Hr0|[]]; subst r; lia.
    + intros k r0 Hk. destruct k as [|k']; [| destruct k'; discriminate Hk ].
      injection Hk as <-. exists cell. split; [ rewrite Hf; left; reflexivity |].
      split; [ exact Hr | rewrite Hv; exact I ].
  - split; [ reflexivity | split; [ exact I | split; [ lia | split; [ intros r [] | intros k r0 Hk; destruct k; discriminate Hk ] ] ] ].
Qed.

Lemma number_constspec_shape : forall par role b cs, shape_ok (fst (number_constspec par role b cs)).
Proof.
  intros par role b cs. unfold number_constspec.
  pose proof (number_list_roots (number_bindingname (Some b) (RSpecName ConstSpecF)) (fun _ => True)
                (fun bb x => number_bindingname_spans (Some b) (RSpecName ConstSpecF) bb x)
                (fun bb x => match number_bindingname_view (Some b) (RSpecName ConstSpecF) bb x with
                             | ex_intro _ cell (ex_intro _ rest (conj Hf _)) =>
                                 ex_intro _ cell (ex_intro _ rest (conj Hf I))
                             end)
                (Collections.ne_to_list (Syntax.const_names cs)) (S b)) as Hnr.
  pose proof (number_list_shape (number_bindingname (Some b) (RSpecName ConstSpecF))
                (fun bb x => number_bindingname_shape (Some b) (RSpecName ConstSpecF) bb x)
                (S b) (Collections.ne_to_list (Syntax.const_names cs))) as Hns.
  destruct (number_list (number_bindingname (Some b) (RSpecName ConstSpecF)) (S b)
             (Collections.ne_to_list (Syntax.const_names cs))) as [[nc b1] nroots].
  destruct Hnr as [Hnlen [Hnasc [Hnbnd _]]]. cbn [fst snd] in Hns.
  destruct (Syntax.const_init cs) as [ot vals|] eqn:E.
  - pose proof (number_opttype_roots b b1 ot) as Hor.
    pose proof (number_opttype_shape b b1 ot) as Hos.
    destruct (number_opttype (Some b) b1 ot) as [[oc b2] oroots].
    destruct Hor as [Holen [Hoasc [Hob [Hobnd _]]]]. cbn [fst snd] in Hos.
    pose proof (number_list_roots (number_expr (Some b) RPlain) (fun _ => True)
                  (fun bb x => number_expr_spans x (Some b) RPlain bb)
                  (fun bb x => match number_expr_root x (Some b) RPlain bb with
                               | ex_intro _ rest (ex_intro _ rc (conj Hf _)) =>
                                   ex_intro _ rc (ex_intro _ rest (conj Hf I))
                               end)
                  (Collections.ne_to_list vals) b2) as Hvr.
    pose proof (number_list_shape (number_expr (Some b) RPlain)
                  (fun bb x => number_expr_shape x (Some b) RPlain bb)
                  b2 (Collections.ne_to_list vals)) as Hvs.
    destruct (number_list (number_expr (Some b) RPlain) b2 (Collections.ne_to_list vals)) as [[vc b3] vroots].
    destruct Hvr as [Hvlen [Hvasc [Hvbnd _]]]. cbn [fst snd] in Hvs.
    cbn [fst]. constructor.
    + cbn [snd]. split.
      * cbn [c_children]. apply asc_app; [ exact Hnasc | apply asc_app; [ exact Hoasc | exact Hvasc |] |].
        { intros x y Hx Hy. destruct (Hobnd x Hx). destruct (Hvbnd y Hy). lia. }
        { intros x y Hx Hy. destruct (Hnbnd x Hx). apply in_app_or in Hy.
          destruct Hy as [Hy|Hy]; [ destruct (Hobnd y Hy) | destruct (Hvbnd y Hy) ]; lia. }
      * cbn [c_view]. unfold constspec_shape. rewrite E. cbn [layout_count].
        cbn [c_children]. rewrite !length_app, Hnlen, Hvlen, Holen.
        destruct ot; cbn [length]; lia.
    + apply shape_ok_app; [ exact Hns | apply shape_ok_app; [ exact Hos | exact Hvs ] ].
  - cbn [fst]. constructor.
    + cbn [snd]. split.
      * cbn [c_children]. rewrite app_nil_r. exact Hnasc.
      * cbn [c_view]. unfold constspec_shape. rewrite E. cbn [layout_count].
        cbn [c_children]. rewrite length_app, Hnlen. cbn [length]. lia.
    + rewrite app_nil_r. exact Hns.
Qed.

Lemma number_varspec_shape : forall par role b vs, shape_ok (fst (number_varspec par role b vs)).
Proof.
  intros par role b vs. unfold number_varspec.
  pose proof (number_list_roots (number_bindingname (Some b) (RSpecName VarSpecF)) (fun _ => True)
                (fun bb x => number_bindingname_spans (Some b) (RSpecName VarSpecF) bb x)
                (fun bb x => match number_bindingname_view (Some b) (RSpecName VarSpecF) bb x with
                             | ex_intro _ cell (ex_intro _ rest (conj Hf _)) =>
                                 ex_intro _ cell (ex_intro _ rest (conj Hf I))
                             end)
                (Collections.ne_to_list (Syntax.var_names vs)) (S b)) as Hnr.
  pose proof (number_list_shape (number_bindingname (Some b) (RSpecName VarSpecF))
                (fun bb x => number_bindingname_shape (Some b) (RSpecName VarSpecF) bb x)
                (S b) (Collections.ne_to_list (Syntax.var_names vs))) as Hns.
  destruct (number_list (number_bindingname (Some b) (RSpecName VarSpecF)) (S b)
             (Collections.ne_to_list (Syntax.var_names vs))) as [[nc b1] nroots].
  destruct Hnr as [Hnlen [Hnasc [Hnbnd _]]]. cbn [fst snd] in Hns.
  destruct (Syntax.var_init vs) as [t | ot vals] eqn:E.
  - pose proof (number_typeexpr_shape (Some b) RTypeUse b1 t) as Hts.
    destruct (number_typeexpr (Some b) RTypeUse b1 t) as [tc b2]. cbn [fst] in Hts.
    cbn [fst]. constructor.
    + cbn [snd]. split.
      * cbn [c_children]. apply asc_app; [ exact Hnasc | exact I |].
        intros x y Hx [Hy|[]]. destruct (Hnbnd x Hx). subst y. lia.
      * cbn [c_view]. unfold varspec_shape. rewrite E. cbn [layout_count].
        cbn [c_children]. rewrite length_app, Hnlen. cbn [length]. lia.
    + apply shape_ok_app; [ exact Hns | exact Hts ].
  - pose proof (number_opttype_roots b b1 ot) as Hor.
    pose proof (number_opttype_shape b b1 ot) as Hos.
    destruct (number_opttype (Some b) b1 ot) as [[oc b2] oroots].
    destruct Hor as [Holen [Hoasc [Hob [Hobnd _]]]]. cbn [fst snd] in Hos.
    pose proof (number_list_roots (number_expr (Some b) RPlain) (fun _ => True)
                  (fun bb x => number_expr_spans x (Some b) RPlain bb)
                  (fun bb x => match number_expr_root x (Some b) RPlain bb with
                               | ex_intro _ rest (ex_intro _ rc (conj Hf _)) =>
                                   ex_intro _ rc (ex_intro _ rest (conj Hf I))
                               end)
                  (Collections.ne_to_list vals) b2) as Hvr.
    pose proof (number_list_shape (number_expr (Some b) RPlain)
                  (fun bb x => number_expr_shape x (Some b) RPlain bb)
                  b2 (Collections.ne_to_list vals)) as Hvs.
    destruct (number_list (number_expr (Some b) RPlain) b2 (Collections.ne_to_list vals)) as [[vc b3] vroots].
    destruct Hvr as [Hvlen [Hvasc [Hvbnd _]]]. cbn [fst snd] in Hvs.
    cbn [fst]. constructor.
    + cbn [snd]. split.
      * cbn [c_children]. apply asc_app; [ exact Hnasc | apply asc_app; [ exact Hoasc | exact Hvasc |] |].
        { intros x y Hx Hy. destruct (Hobnd x Hx). destruct (Hvbnd y Hy). lia. }
        { intros x y Hx Hy. destruct (Hnbnd x Hx). apply in_app_or in Hy.
          destruct Hy as [Hy|Hy]; [ destruct (Hobnd y Hy) | destruct (Hvbnd y Hy) ]; lia. }
      * cbn [c_view]. unfold varspec_shape. rewrite E. cbn [layout_count].
        cbn [c_children]. rewrite !length_app, Hnlen, Hvlen, Holen.
        destruct ot; cbn [length]; lia.
    + apply shape_ok_app; [ exact Hns | apply shape_ok_app; [ exact Hos | exact Hvs ] ].
Qed.

Lemma number_typespec_shape : forall par role b ts, shape_ok (fst (number_typespec par role b ts)).
Proof.
  intros par role b ts. unfold number_typespec.
  destruct ts as [bn t|bn t];
    (cbn [number_bindingname number_leaf];
     pose proof (number_typeexpr_shape (Some b) RTypeUse (S (S b)) t) as Hts;
     destruct (number_typeexpr (Some b) RTypeUse (S (S b)) t) as [tc bfin]; cbn [fst] in Hts;
     cbn [fst app]; constructor;
     [ cbn; split; [ split; [ lia | exact I ] | reflexivity ]
     | constructor; [ cbn; split; [ exact I | reflexivity ] | exact Hts ] ]).
Qed.

Lemma number_decl_shape : forall par role b d, shape_ok (fst (number_decl par role b d)).
Proof.
  intros par role b d. unfold number_decl.
  destruct d as [cs|vs|ts].
  - pose proof (number_list_roots (number_constspec (Some b) RPlain) (fun _ => True)
                  (fun bb x => number_constspec_span (Some b) RPlain bb x)
                  (fun bb x => match number_constspec_view (Some b) RPlain bb x with
                               | ex_intro _ cell (ex_intro _ rest (conj Hf _)) =>
                                   ex_intro _ cell (ex_intro _ rest (conj Hf I))
                               end)
                  cs (S b)) as Hr.
    pose proof (number_list_shape (number_constspec (Some b) RPlain)
                  (fun bb x => number_constspec_shape (Some b) RPlain bb x) (S b) cs) as Hs.
    destruct (number_list (number_constspec (Some b) RPlain) (S b) cs) as [[kc bfin] roots].
    destruct Hr as [_ [Hasc _]]. cbn [fst snd] in Hs.
    cbn [fst]. constructor; [ cbn [snd]; split; [ exact Hasc | cbn; exact I ] | exact Hs ].
  - pose proof (number_list_roots (number_varspec (Some b) RPlain) (fun _ => True)
                  (fun bb x => number_varspec_span (Some b) RPlain bb x)
                  (fun bb x => match number_varspec_view (Some b) RPlain bb x with
                               | ex_intro _ cell (ex_intro _ rest (conj Hf _)) =>
                                   ex_intro _ cell (ex_intro _ rest (conj Hf I))
                               end)
                  vs (S b)) as Hr.
    pose proof (number_list_shape (number_varspec (Some b) RPlain)
                  (fun bb x => number_varspec_shape (Some b) RPlain bb x) (S b) vs) as Hs.
    destruct (number_list (number_varspec (Some b) RPlain) (S b) vs) as [[kc bfin] roots].
    destruct Hr as [_ [Hasc _]]. cbn [fst snd] in Hs.
    cbn [fst]. constructor; [ cbn [snd]; split; [ exact Hasc | cbn; exact I ] | exact Hs ].
  - pose proof (number_list_roots (number_typespec (Some b) RPlain) (fun _ => True)
                  (fun bb x => number_typespec_span (Some b) RPlain bb x)
                  (fun bb x => match number_typespec_view (Some b) RPlain bb x with
                               | ex_intro _ cell (ex_intro _ rest (conj Hf _)) =>
                                   ex_intro _ cell (ex_intro _ rest (conj Hf I))
                               end)
                  ts (S b)) as Hr.
    pose proof (number_list_shape (number_typespec (Some b) RPlain)
                  (fun bb x => number_typespec_shape (Some b) RPlain bb x) (S b) ts) as Hs.
    destruct (number_list (number_typespec (Some b) RPlain) (S b) ts) as [[kc bfin] roots].
    destruct Hr as [_ [Hasc _]]. cbn [fst snd] in Hs.
    cbn [fst]. constructor; [ cbn [snd]; split; [ exact Hasc | cbn; exact I ] | exact Hs ].
Qed.

Lemma number_stmt_shape : forall par role b s, shape_ok (fst (number_stmt par role b s)).
Proof.
  intros par role b s. unfold number_stmt.
  destruct s as [e|d|names vals].
  - pose proof (number_expr_shape e (Some b) RExprStatementExpr (S b)) as Hs.
    destruct (number_expr (Some b) RExprStatementExpr (S b) e) as [c b']. cbn [fst] in Hs.
    cbn [fst]. constructor; [ cbn; split; [ exact I | reflexivity ] | exact Hs ].
  - pose proof (number_decl_shape (Some b) RPlain (S b) d) as Hs.
    destruct (number_decl (Some b) RPlain (S b) d) as [c b']. cbn [fst] in Hs.
    cbn [fst]. constructor; [ cbn; split; [ exact I | reflexivity ] | exact Hs ].
  - pose proof (number_list_roots (number_bindingname (Some b) RShortLhs) (fun _ => True)
                  (fun bb x => number_bindingname_spans (Some b) RShortLhs bb x)
                  (fun bb x => match number_bindingname_view (Some b) RShortLhs bb x with
                               | ex_intro _ cell (ex_intro _ rest (conj Hf _)) =>
                                   ex_intro _ cell (ex_intro _ rest (conj Hf I))
                               end)
                  (Collections.ne_to_list names) (S b)) as Hnr.
    pose proof (number_list_shape (number_bindingname (Some b) RShortLhs)
                  (fun bb x => number_bindingname_shape (Some b) RShortLhs bb x)
                  (S b) (Collections.ne_to_list names)) as Hns.
    destruct (number_list (number_bindingname (Some b) RShortLhs) (S b) (Collections.ne_to_list names))
      as [[nc b1] nroots].
    destruct Hnr as [Hnlen [Hnasc [Hnbnd _]]]. cbn [fst snd] in Hns.
    pose proof (number_list_roots (number_expr (Some b) RPlain) (fun _ => True)
                  (fun bb x => number_expr_spans x (Some b) RPlain bb)
                  (fun bb x => match number_expr_root x (Some b) RPlain bb with
                               | ex_intro _ rest (ex_intro _ rc (conj Hf _)) =>
                                   ex_intro _ rc (ex_intro _ rest (conj Hf I))
                               end)
                  (Collections.ne_to_list vals) b1) as Hvr.
    pose proof (number_list_shape (number_expr (Some b) RPlain)
                  (fun bb x => number_expr_shape x (Some b) RPlain bb)
                  b1 (Collections.ne_to_list vals)) as Hvs.
    destruct (number_list (number_expr (Some b) RPlain) b1 (Collections.ne_to_list vals)) as [[vc b2] vroots].
    destruct Hvr as [Hvlen [Hvasc [Hvbnd _]]]. cbn [fst snd] in Hvs.
    cbn [fst]. constructor.
    + cbn [snd]. split.
      * cbn [c_children]. apply asc_app; [ exact Hnasc | exact Hvasc |].
        intros x y Hx Hy. destruct (Hnbnd x Hx). destruct (Hvbnd y Hy). lia.
      * cbn [c_view]. unfold stmt_shape. cbn [layout_count].
        cbn [c_children]. rewrite length_app, Hnlen, Hvlen. reflexivity.
    + apply shape_ok_app; [ exact Hns | exact Hvs ].
Qed.

Lemma number_block_shape : forall par role b blk, shape_ok (fst (number_block par role b blk)).
Proof.
  intros par role b [stmts]. unfold number_block.
  pose proof (number_list_roots (number_stmt (Some b) RPlain) (fun _ => True)
                (fun bb x => number_stmt_span (Some b) RPlain bb x)
                (fun bb x => match number_stmt_view (Some b) RPlain bb x with
                             | ex_intro _ cell (ex_intro _ rest (conj Hf _)) =>
                                 ex_intro _ cell (ex_intro _ rest (conj Hf I))
                             end)
                stmts (S b)) as Hr.
  pose proof (number_list_shape (number_stmt (Some b) RPlain)
                (fun bb x => number_stmt_shape (Some b) RPlain bb x) (S b) stmts) as Hs.
  destruct (number_list (number_stmt (Some b) RPlain) (S b) stmts) as [[kc bfin] roots].
  destruct Hr as [_ [Hasc _]]. cbn [fst snd] in Hs.
  cbn [fst]. constructor; [ cbn [snd]; split; [ exact Hasc | cbn; exact I ] | exact Hs ].
Qed.

Lemma number_toplevel_shape : forall par role b td, shape_ok (fst (number_toplevel par role b td)).
Proof.
  intros par role b td. unfold number_toplevel.
  destruct td as [d|blk].
  - pose proof (number_decl_shape (Some b) RPlain (S b) d) as Hs.
    destruct (number_decl (Some b) RPlain (S b) d) as [c b']. cbn [fst] in Hs.
    cbn [fst]. constructor; [ cbn; split; [ exact I | reflexivity ] | exact Hs ].
  - pose proof (number_block_shape (Some b) RPlain (S b) blk) as Hs.
    destruct (number_block (Some b) RPlain (S b) blk) as [c b']. cbn [fst] in Hs.
    cbn [fst]. constructor; [ cbn; split; [ exact I | reflexivity ] | exact Hs ].
Qed.

Lemma number_file_shape : forall f, shape_ok (number_file f).
Proof.
  intro f. unfold number_file.
  pose proof (number_list_roots (number_toplevel (Some 0) RPlain) (fun _ => True)
                (fun bb x => number_toplevel_span (Some 0) RPlain bb x)
                (fun bb x => match number_toplevel_view (Some 0) RPlain bb x with
                             | ex_intro _ cell (ex_intro _ rest (conj Hf _)) =>
                                 ex_intro _ cell (ex_intro _ rest (conj Hf I))
                             end)
                (Syntax.declarations f) 1) as Hr.
  pose proof (number_list_shape (number_toplevel (Some 0) RPlain)
                (fun bb x => number_toplevel_shape (Some 0) RPlain bb x) 1 (Syntax.declarations f)) as Hs.
  destruct (number_list (number_toplevel (Some 0) RPlain) 1 (Syntax.declarations f)) as [[dc bfin] droots].
  destruct Hr as [_ [Hasc _]]. cbn [fst snd] in Hs.
  constructor; [ cbn [snd]; split; [ exact Hasc | cbn; exact I ] | exact Hs ].
Qed.

Lemma expr_view_not_const : forall e sh, expr_view e = VConstSpec sh -> False.
Proof. intros e sh H; destruct e; cbn in H; discriminate H. Qed.

Lemma expr_view_no_reverse : forall e, no_reverse (expr_view e).
Proof. intro e; destruct e; exact I. Qed.

Lemma number_leaf_layout : forall v par role b, child_layout_ok (fst (number_leaf v par role b)).
Proof.
  intros v par role b pos c Hin k cp Hcp. destruct Hin as [Heq|[]].
  inversion Heq; subst. cbn [c_children] in Hcp. destruct k; discriminate Hcp.
Qed.

Lemma number_expr_layout : forall e par role b, child_layout_ok (fst (number_expr par role b e)).
Proof.
  intro e; induction e using Syntax.Expr_ind'; intros par role b; cbn [number_expr].
  - apply number_leaf_layout.
  - apply number_leaf_layout.
  - specialize (IHe (Some b) RUnaryOperand (S b)).
    pose proof (number_expr_root e (Some b) RUnaryOperand (S b)) as [urest [urc [Huroot [Hurole [Huview _]]]]].
    destruct (number_expr (Some b) RUnaryOperand (S b) e) as [kc nxt].
    cbn [fst] in IHe, Huroot |- *.
    apply child_layout_ok_node.
    + cbn [c_children c_view]. intros k cp Hcp. destruct k as [|k']; [| destruct k'; discriminate Hcp ].
      injection Hcp as <-. exists urc.
      split; [ right; rewrite Huroot; left; reflexivity |].
      split; [ rewrite Hurole; reflexivity |].
      split; [ intro He; discriminate He |].
      split; [ intros fl He; discriminate He |].
      rewrite Huview. apply no_reverse_clauses, expr_view_no_reverse.
    + exact IHe.
  - specialize (IHe (Some b) RApplicationHead (S b)).
    pose proof (number_expr_root e (Some b) RApplicationHead (S b)) as [hrest [hrc [Hhroot [Hhrole [Hhview _]]]]].
    destruct (number_expr (Some b) RApplicationHead (S b) e) as [hc b1].
    cbn [fst] in IHe, Hhroot.
    assert (Hda : forall es, Forall (fun a => forall par role bb,
                     child_layout_ok (fst (number_expr par role bb a))) es ->
      forall i0 bi, (let '(ac, _, roots) := (fix do_args (i bi : nat) (es : list Syntax.Expr) {struct es}
              : list (nat * Cell) * nat * list nat :=
              match es with
              | [] => ([], bi, [])
              | a :: rest =>
                  let '(ac, bi') := number_expr (Some b) (RApplicationArg i) bi a in
                  let '(rc, bf, roots) := do_args (S i) bi' rest in
                  (ac ++ rc, bf, bi :: roots)
              end) i0 bi es in
        child_layout_ok ac /\
        (forall k r0, nth_error roots k = Some r0 ->
           exists cc, In (r0, cc) ac /\ c_role cc = RApplicationArg (i0 + k)
                      /\ no_reverse (c_view cc)))).
    { intros es Hall; induction Hall as [| a rest Ha Hrest IHrest]; intros i0 bi.
      - split; [ intros pos c Hin; destruct Hin | intros k r0 Hk; destruct k; discriminate Hk ].
      - pose proof (number_expr_root a (Some b) (RApplicationArg i0) bi) as [arest [arc [Haroot [Harole [Haview _]]]]].
        specialize (Ha (Some b) (RApplicationArg i0) bi).
        destruct (number_expr (Some b) (RApplicationArg i0) bi a) as [ac1 bi'].
        cbn [fst] in Ha, Haroot.
        specialize (IHrest (S i0) bi').
        destruct ((fix do_args (i bi : nat) (es : list Syntax.Expr) {struct es} := _) (S i0) bi' rest)
          as [[rc bf] roots].
        destruct IHrest as [Hrcok Hroots]. cbn [fst snd] in Hrcok, Hroots |- *.
        split; [ apply child_layout_ok_app; [ exact Ha | exact Hrcok ] |].
        intros k r0 Hk. destruct k as [|k'].
        + injection Hk as <-. exists arc.
          split; [ apply in_or_app; left; rewrite Haroot; left; reflexivity |].
          split; [ rewrite Harole, Nat.add_0_r; reflexivity |].
          rewrite Haview. apply expr_view_no_reverse.
        + cbn in Hk. destruct (Hroots k' r0 Hk) as [cc [Hcc [Hccrole Hccnc]]]. exists cc.
          split; [ apply in_or_app; right; exact Hcc |].
          split; [ rewrite Hccrole; rewrite Nat.add_succ_comm; reflexivity | exact Hccnc ]. }
    specialize (Hda args H 0 b1).
    destruct ((fix do_args (i bi : nat) (es : list Syntax.Expr) {struct es} := _) 0 b1 args)
      as [[ac bfin] aroots].
    destruct Hda as [Hacok Haroots]. cbn [fst snd] in Hacok, Haroots |- *.
    apply child_layout_ok_node.
    + cbn [c_children c_view]. intros k cp Hcp. destruct k as [|i].
      * injection Hcp as <-. exists hrc.
        split; [ right; apply in_or_app; left; rewrite Hhroot; left; reflexivity |].
        split; [ rewrite Hhrole; reflexivity |].
        split; [ intro He; discriminate He |].
        split; [ intros fl He; discriminate He |].
        rewrite Hhview. apply no_reverse_clauses, expr_view_no_reverse.
      * cbn in Hcp. destruct (Haroots i cp Hcp) as [cc [Hcc [Hccrole Hccnc]]]. exists cc.
        split; [ right; apply in_or_app; right; exact Hcc |].
        split; [ rewrite Hccrole; reflexivity |].
        split; [ intro He; discriminate He |].
        split; [ intros fl He; discriminate He |].
        apply no_reverse_clauses, Hccnc.
    + apply child_layout_ok_app; [ exact IHe | exact Hacok ].
Qed.

Lemma number_typeexpr_layout : forall par role b t, child_layout_ok (fst (number_typeexpr par role b t)).
Proof. intros; apply number_leaf_layout. Qed.
Lemma number_bindingname_layout : forall par role b bn, child_layout_ok (fst (number_bindingname par role b bn)).
Proof. intros; apply number_leaf_layout. Qed.

Lemma number_opttype_layout : forall self b ot, child_layout_ok (fst (fst (number_opttype (Some self) b ot))).
Proof.
  intros self b [t|]; cbn [number_opttype].
  - pose proof (number_typeexpr_layout (Some self) RTypeUse b t) as Hc.
    destruct (number_typeexpr (Some self) RTypeUse b t) as [c b']. cbn [fst snd] in Hc |- *. exact Hc.
  - intros pos c Hin; destruct Hin.
Qed.

Lemma number_constspec_layout : forall par role b cs, child_layout_ok (fst (number_constspec par role b cs)).
Proof.
  intros par role b cs. unfold number_constspec.
  assert (Hnroot : forall bb x, exists cell rest,
            fst (number_bindingname (Some b) (RSpecName ConstSpecF) bb x) = (bb, cell) :: rest
            /\ (c_role cell = RSpecName ConstSpecF /\ no_reverse (c_view cell))).
  { intros bb x. destruct (number_bindingname_view (Some b) (RSpecName ConstSpecF) bb x)
      as [cell [rest [Hf [Hr Hv]]]].
    exists cell, rest. split; [ exact Hf |].
    split; [ exact Hr | rewrite Hv; exact I ]. }
  pose proof (number_list_roots (number_bindingname (Some b) (RSpecName ConstSpecF))
                (fun cell => c_role cell = RSpecName ConstSpecF /\ no_reverse (c_view cell))
                (fun bb x => number_bindingname_spans (Some b) (RSpecName ConstSpecF) bb x)
                Hnroot
                (Collections.ne_to_list (Syntax.const_names cs)) (S b)) as Hnr.
  pose proof (number_list_layout (number_bindingname (Some b) (RSpecName ConstSpecF))
                (fun bb x => number_bindingname_layout (Some b) (RSpecName ConstSpecF) bb x)
                (S b) (Collections.ne_to_list (Syntax.const_names cs))) as Hnl.
  destruct (number_list (number_bindingname (Some b) (RSpecName ConstSpecF)) (S b)
             (Collections.ne_to_list (Syntax.const_names cs))) as [[nc b1] nroots].
  destruct Hnr as [Hnlen [_ [_ Hnnth]]]. cbn [fst snd] in Hnl.
  destruct (Syntax.const_init cs) as [ot vals|] eqn:E.
  - assert (Hsh : constspec_shape cs
                  = CSExplicit (match ot with Some _ => true | None => false end)
                               (List.length (Collections.ne_to_list (Syntax.const_names cs)))
                               (List.length (Collections.ne_to_list vals)))
      by (unfold constspec_shape; rewrite E; reflexivity).
    pose proof (number_opttype_roots b b1 ot) as Hor.
    pose proof (number_opttype_layout b b1 ot) as Hol.
    destruct (number_opttype (Some b) b1 ot) as [[oc b2] oroots].
    destruct Hor as [Holen [_ [_ [_ Honth]]]]. cbn [fst snd] in Hol.
    assert (Hvroot : forall bb x, exists cell rest,
              fst (number_expr (Some b) RPlain bb x) = (bb, cell) :: rest
              /\ (c_role cell = RPlain /\ no_reverse (c_view cell))).
    { intros bb x. destruct (number_expr_root x (Some b) RPlain bb) as [rest [rc [Hf [Hr [Hv _]]]]].
      exists rc, rest. split; [ exact Hf |].
      split; [ exact Hr | rewrite Hv; apply expr_view_no_reverse ]. }
    pose proof (number_list_roots (number_expr (Some b) RPlain)
                  (fun cell => c_role cell = RPlain /\ no_reverse (c_view cell))
                  (fun bb x => number_expr_spans x (Some b) RPlain bb)
                  Hvroot
                  (Collections.ne_to_list vals) b2) as Hvr.
    pose proof (number_list_layout (number_expr (Some b) RPlain)
                  (fun bb x => number_expr_layout x (Some b) RPlain bb)
                  b2 (Collections.ne_to_list vals)) as Hvl.
    destruct (number_list (number_expr (Some b) RPlain) b2 (Collections.ne_to_list vals)) as [[vc b3] vroots].
    destruct Hvr as [Hvlen [_ [_ Hvnth]]]. cbn [fst snd] in Hvl.
    cbn [fst]. apply child_layout_ok_node.
    + cbn [c_children c_view]. rewrite Hsh. intros k cp Hcp.
      set (NN := List.length (Collections.ne_to_list (Syntax.const_names cs))) in *.
      destruct (Nat.lt_ge_cases k (length nroots)) as [Hk|Hk].
      * rewrite nth_error_app1 in Hcp by exact Hk.
        destruct (Hnnth k cp Hcp) as [cell [Hcell [Hrole Hnc]]].
        exists cell. split; [ right; apply in_or_app; left; exact Hcell |].
        split.
        { rewrite Hrole. cbn [layout_role].
          assert (Hlt : k <? NN = true) by (apply Nat.ltb_lt; rewrite <- Hnlen; exact Hk).
          rewrite Hlt. reflexivity. }
        split; [ intro He; discriminate He |].
        split; [ intros fl He; discriminate He |].
        apply no_reverse_clauses, Hnc.
      * rewrite nth_error_app2 in Hcp by exact Hk.
        destruct (Nat.lt_ge_cases (k - length nroots) (length oroots)) as [Hk2|Hk2].
        -- rewrite nth_error_app1 in Hcp by exact Hk2.
           destruct (Honth (k - length nroots) cp Hcp) as [cell [Hcell [Hrole Hnc]]].
           exists cell. split; [ right; apply in_or_app; right; apply in_or_app; left; exact Hcell |].
           split.
           { rewrite Hrole. cbn [layout_role].
             destruct ot as [t0|]; cbn in Holen; [| lia ].
             assert (Hke : k = NN) by (rewrite Holen in Hk2; rewrite Hnlen in Hk; lia).
             assert (Hltb : k <? NN = false) by (apply Nat.ltb_ge; lia).
             assert (Heqb : k =? NN = true) by (apply Nat.eqb_eq; exact Hke).
             rewrite Hltb, Heqb. reflexivity. }
           split; [ intro He; discriminate He |].
           split; [ intros fl He; discriminate He |].
           apply no_reverse_clauses, Hnc.
        -- rewrite nth_error_app2 in Hcp by exact Hk2.
           destruct (Hvnth (k - length nroots - length oroots) cp Hcp) as [cell [Hcell [Hrole Hnc]]].
           exists cell. split; [ right; apply in_or_app; right; apply in_or_app; right; exact Hcell |].
           split.
           { rewrite Hrole. cbn [layout_role].
             assert (Hltb : k <? NN = false) by (apply Nat.ltb_ge; rewrite <- Hnlen; lia).
             rewrite Hltb.
             destruct ot as [t0|]; cbn in Holen; [| reflexivity ].
             assert (Heqb : k =? NN = false)
               by (apply Nat.eqb_neq; rewrite <- Hnlen; lia).
             rewrite Heqb. cbn [andb]. destruct (k <? NN); reflexivity. }
           split; [ intro He; discriminate He |].
           split; [ intros fl He; discriminate He |].
           apply no_reverse_clauses, Hnc.
    + apply child_layout_ok_app; [ exact Hnl | apply child_layout_ok_app; [ exact Hol | exact Hvl ] ].
  - cbn [fst]. apply child_layout_ok_node.
    + cbn [c_children c_view].
      assert (Hsh : constspec_shape cs
                    = CSInherited (List.length (Collections.ne_to_list (Syntax.const_names cs))))
        by (unfold constspec_shape; rewrite E; reflexivity).
      rewrite Hsh. intros k cp Hcp. rewrite app_nil_r in Hcp.
      destruct (Hnnth k cp Hcp) as [cell [Hcell [Hrole Hnc]]].
      exists cell. split; [ right; rewrite app_nil_r; exact Hcell |].
      split; [ rewrite Hrole; reflexivity |].
      split; [ intro He; discriminate He |].
      split; [ intros fl He; discriminate He |].
      apply no_reverse_clauses, Hnc.
    + rewrite app_nil_r. exact Hnl.
Qed.

Lemma number_varspec_layout : forall par role b vs, child_layout_ok (fst (number_varspec par role b vs)).
Proof.
  intros par role b vs. unfold number_varspec.
  assert (Hnroot : forall bb x, exists cell rest,
            fst (number_bindingname (Some b) (RSpecName VarSpecF) bb x) = (bb, cell) :: rest
            /\ (c_role cell = RSpecName VarSpecF /\ no_reverse (c_view cell))).
  { intros bb x. destruct (number_bindingname_view (Some b) (RSpecName VarSpecF) bb x)
      as [cell [rest [Hf [Hr Hv]]]].
    exists cell, rest. split; [ exact Hf |].
    split; [ exact Hr | rewrite Hv; exact I ]. }
  pose proof (number_list_roots (number_bindingname (Some b) (RSpecName VarSpecF))
                (fun cell => c_role cell = RSpecName VarSpecF /\ no_reverse (c_view cell))
                (fun bb x => number_bindingname_spans (Some b) (RSpecName VarSpecF) bb x)
                Hnroot
                (Collections.ne_to_list (Syntax.var_names vs)) (S b)) as Hnr.
  pose proof (number_list_layout (number_bindingname (Some b) (RSpecName VarSpecF))
                (fun bb x => number_bindingname_layout (Some b) (RSpecName VarSpecF) bb x)
                (S b) (Collections.ne_to_list (Syntax.var_names vs))) as Hnl.
  destruct (number_list (number_bindingname (Some b) (RSpecName VarSpecF)) (S b)
             (Collections.ne_to_list (Syntax.var_names vs))) as [[nc b1] nroots].
  destruct Hnr as [Hnlen [_ [_ Hnnth]]]. cbn [fst snd] in Hnl.
  destruct (Syntax.var_init vs) as [t | ot vals] eqn:E.
  - assert (Hsh : varspec_shape vs
                  = VSTypeOnly (List.length (Collections.ne_to_list (Syntax.var_names vs))))
      by (unfold varspec_shape; rewrite E; reflexivity).
    pose proof (number_typeexpr_view (Some b) RTypeUse b1 t) as [tcell [trest [Htf [Htr Htv]]]].
    pose proof (number_typeexpr_layout (Some b) RTypeUse b1 t) as Htl.
    destruct (number_typeexpr (Some b) RTypeUse b1 t) as [tc b2]. cbn [fst] in Htf, Htl.
    cbn [fst]. apply child_layout_ok_node.
    + cbn [c_children c_view]. rewrite Hsh. intros k cp Hcp.
      set (NN := List.length (Collections.ne_to_list (Syntax.var_names vs))) in *.
      destruct (Nat.lt_ge_cases k (length nroots)) as [Hk|Hk].
      * rewrite nth_error_app1 in Hcp by exact Hk.
        destruct (Hnnth k cp Hcp) as [cell [Hcell [Hrole Hnc]]].
        exists cell. split; [ right; apply in_or_app; left; exact Hcell |].
        split.
        { rewrite Hrole. cbn [layout_role].
          assert (Hlt : k <? NN = true) by (apply Nat.ltb_lt; rewrite <- Hnlen; exact Hk).
          rewrite Hlt. reflexivity. }
        split; [ intro He; discriminate He |].
        split; [ intros fl He; discriminate He |].
        apply no_reverse_clauses, Hnc.
      * rewrite nth_error_app2 in Hcp by exact Hk.
        destruct (k - length nroots) as [|k2] eqn:Hk2; [| destruct k2; discriminate Hcp ].
        injection Hcp as <-. exists tcell.
        split; [ right; apply in_or_app; right; rewrite Htf; left; reflexivity |].
        split.
        { rewrite Htr. cbn [layout_role].
          assert (Hltb : k <? NN = false) by (apply Nat.ltb_ge; rewrite <- Hnlen; exact Hk).
          rewrite Hltb. reflexivity. }
        split; [ intro He; discriminate He |].
        split; [ intros fl He; discriminate He |].
        rewrite Htv. apply no_reverse_clauses. exact I.
    + apply child_layout_ok_app; [ exact Hnl | exact Htl ].
  - assert (Hsh : varspec_shape vs
                  = VSValues (match ot with Some _ => true | None => false end)
                             (List.length (Collections.ne_to_list (Syntax.var_names vs)))
                             (List.length (Collections.ne_to_list vals)))
      by (unfold varspec_shape; rewrite E; reflexivity).
    pose proof (number_opttype_roots b b1 ot) as Hor.
    pose proof (number_opttype_layout b b1 ot) as Hol.
    destruct (number_opttype (Some b) b1 ot) as [[oc b2] oroots].
    destruct Hor as [Holen [_ [_ [_ Honth]]]]. cbn [fst snd] in Hol.
    assert (Hvroot : forall bb x, exists cell rest,
              fst (number_expr (Some b) RPlain bb x) = (bb, cell) :: rest
              /\ (c_role cell = RPlain /\ no_reverse (c_view cell))).
    { intros bb x. destruct (number_expr_root x (Some b) RPlain bb) as [rest [rc [Hf [Hr [Hv _]]]]].
      exists rc, rest. split; [ exact Hf |].
      split; [ exact Hr | rewrite Hv; apply expr_view_no_reverse ]. }
    pose proof (number_list_roots (number_expr (Some b) RPlain)
                  (fun cell => c_role cell = RPlain /\ no_reverse (c_view cell))
                  (fun bb x => number_expr_spans x (Some b) RPlain bb)
                  Hvroot
                  (Collections.ne_to_list vals) b2) as Hvr.
    pose proof (number_list_layout (number_expr (Some b) RPlain)
                  (fun bb x => number_expr_layout x (Some b) RPlain bb)
                  b2 (Collections.ne_to_list vals)) as Hvl.
    destruct (number_list (number_expr (Some b) RPlain) b2 (Collections.ne_to_list vals)) as [[vc b3] vroots].
    destruct Hvr as [Hvlen [_ [_ Hvnth]]]. cbn [fst snd] in Hvl.
    cbn [fst]. apply child_layout_ok_node.
    + cbn [c_children c_view]. rewrite Hsh. intros k cp Hcp.
      set (NN := List.length (Collections.ne_to_list (Syntax.var_names vs))) in *.
      destruct (Nat.lt_ge_cases k (length nroots)) as [Hk|Hk].
      * rewrite nth_error_app1 in Hcp by exact Hk.
        destruct (Hnnth k cp Hcp) as [cell [Hcell [Hrole Hnc]]].
        exists cell. split; [ right; apply in_or_app; left; exact Hcell |].
        split.
        { rewrite Hrole. cbn [layout_role].
          assert (Hlt : k <? NN = true) by (apply Nat.ltb_lt; rewrite <- Hnlen; exact Hk).
          rewrite Hlt. reflexivity. }
        split; [ intro He; discriminate He |].
        split; [ intros fl He; discriminate He |].
        apply no_reverse_clauses, Hnc.
      * rewrite nth_error_app2 in Hcp by exact Hk.
        destruct (Nat.lt_ge_cases (k - length nroots) (length oroots)) as [Hk2|Hk2].
        -- rewrite nth_error_app1 in Hcp by exact Hk2.
           destruct (Honth (k - length nroots) cp Hcp) as [cell [Hcell [Hrole Hnc]]].
           exists cell. split; [ right; apply in_or_app; right; apply in_or_app; left; exact Hcell |].
           split.
           { rewrite Hrole. cbn [layout_role].
             destruct ot as [t0|]; cbn in Holen; [| lia ].
             assert (Hke : k = NN) by (rewrite Holen in Hk2; rewrite Hnlen in Hk; lia).
             assert (Hltb : k <? NN = false) by (apply Nat.ltb_ge; lia).
             assert (Heqb : k =? NN = true) by (apply Nat.eqb_eq; exact Hke).
             rewrite Hltb, Heqb. reflexivity. }
           split; [ intro He; discriminate He |].
           split; [ intros fl He; discriminate He |].
           apply no_reverse_clauses, Hnc.
        -- rewrite nth_error_app2 in Hcp by exact Hk2.
           destruct (Hvnth (k - length nroots - length oroots) cp Hcp) as [cell [Hcell [Hrole Hnc]]].
           exists cell. split; [ right; apply in_or_app; right; apply in_or_app; right; exact Hcell |].
           split.
           { rewrite Hrole. cbn [layout_role].
             assert (Hltb : k <? NN = false) by (apply Nat.ltb_ge; rewrite <- Hnlen; lia).
             rewrite Hltb.
             destruct ot as [t0|]; cbn in Holen; [| reflexivity ].
             assert (Heqb : k =? NN = false)
               by (apply Nat.eqb_neq; rewrite <- Hnlen; lia).
             rewrite Heqb. cbn [andb]. destruct (k <? NN); reflexivity. }
           split; [ intro He; discriminate He |].
           split; [ intros fl He; discriminate He |].
           apply no_reverse_clauses, Hnc.
    + apply child_layout_ok_app; [ exact Hnl | apply child_layout_ok_app; [ exact Hol | exact Hvl ] ].
Qed.

Lemma number_typespec_layout : forall par role b ts, child_layout_ok (fst (number_typespec par role b ts)).
Proof.
  intros par role b ts. unfold number_typespec.
  destruct ts as [bn t|bn t];
    (cbn [number_bindingname number_leaf];
     pose proof (number_typeexpr_view (Some b) RTypeUse (S (S b)) t) as [tcell [trest [Htf [Htr Htv]]]];
     pose proof (number_typeexpr_layout (Some b) RTypeUse (S (S b)) t) as Htl;
     destruct (number_typeexpr (Some b) RTypeUse (S (S b)) t) as [tc bfin]; cbn [fst] in Htf, Htl;
     cbn [fst app]; apply child_layout_ok_node;
     [ cbn [c_children c_view]; intros k cp Hcp;
       destruct k as [|[|k2]]; [| | destruct k2; discriminate Hcp ];
       [ injection Hcp as <-;
         eexists; split; [ right; left; reflexivity |];
         split; [ cbn [c_role]; reflexivity |];
         split; [ intro He; discriminate He |];
         split; [ intros fl He; discriminate He |];
         cbn [c_view]; apply no_reverse_clauses; exact I
       | injection Hcp as <-; exists tcell;
         split; [ right; right; rewrite Htf; left; reflexivity |];
         split; [ rewrite Htr; reflexivity |];
         split; [ intro He; discriminate He |];
         split; [ intros fl He; discriminate He |];
         rewrite Htv; apply no_reverse_clauses; exact I ]
     | apply child_layout_ok_node;
       [ cbn [c_children]; intros k cp Hcp; destruct k; discriminate Hcp
       | exact Htl ] ]).
Qed.

Lemma number_decl_layout : forall par role b d, child_layout_ok (fst (number_decl par role b d)).
Proof.
  intros par role b d. unfold number_decl.
  destruct d as [cs|vs|ts].
  - assert (Hroot : forall bb x, exists cell rest,
              fst (number_constspec (Some b) RPlain bb x) = (bb, cell) :: rest
              /\ (c_role cell = RPlain /\ (exists sh0, c_view cell = VConstSpec sh0))).
    { intros bb x. destruct (number_constspec_view (Some b) RPlain bb x) as [cell [rest [Hf [Hr Hv]]]].
      exists cell, rest. split; [ exact Hf |]. split; [ exact Hr | exists (constspec_shape x); exact Hv ]. }
    pose proof (number_list_roots (number_constspec (Some b) RPlain)
                  (fun cell => c_role cell = RPlain /\ (exists sh0, c_view cell = VConstSpec sh0))
                  (fun bb x => number_constspec_span (Some b) RPlain bb x) Hroot cs (S b)) as Hr.
    pose proof (number_list_layout (number_constspec (Some b) RPlain)
                  (fun bb x => number_constspec_layout (Some b) RPlain bb x) (S b) cs) as Hl.
    destruct (number_list (number_constspec (Some b) RPlain) (S b) cs) as [[kc bfin] roots].
    destruct Hr as [_ [_ [_ Hnth]]]. cbn [fst snd] in Hl.
    cbn [fst]. apply child_layout_ok_node;
      [ cbn [c_children c_view decl_flavor]; intros k cp Hcp;
        destruct (Hnth k cp Hcp) as [cell [Hcell [Hrole [sh0 Hv]]]];
        exists cell; split; [ right; exact Hcell |];
        split; [ rewrite Hrole; reflexivity |];
        split; [ intro He; discriminate He |];
        split; [ intros fl He; injection He as He; subst fl; rewrite Hv; exact I |];
        rewrite Hv; apply spec_reverse_clauses; exact I
      | exact Hl ].
  - assert (Hroot : forall bb x, exists cell rest,
              fst (number_varspec (Some b) RPlain bb x) = (bb, cell) :: rest
              /\ (c_role cell = RPlain /\ (exists sh0, c_view cell = VVarSpec sh0))).
    { intros bb x. destruct (number_varspec_view (Some b) RPlain bb x) as [cell [rest [Hf [Hr Hv]]]].
      exists cell, rest. split; [ exact Hf |]. split; [ exact Hr | exists (varspec_shape x); exact Hv ]. }
    pose proof (number_list_roots (number_varspec (Some b) RPlain)
                  (fun cell => c_role cell = RPlain /\ (exists sh0, c_view cell = VVarSpec sh0))
                  (fun bb x => number_varspec_span (Some b) RPlain bb x) Hroot vs (S b)) as Hr.
    pose proof (number_list_layout (number_varspec (Some b) RPlain)
                  (fun bb x => number_varspec_layout (Some b) RPlain bb x) (S b) vs) as Hl.
    destruct (number_list (number_varspec (Some b) RPlain) (S b) vs) as [[kc bfin] roots].
    destruct Hr as [_ [_ [_ Hnth]]]. cbn [fst snd] in Hl.
    cbn [fst]. apply child_layout_ok_node;
      [ cbn [c_children c_view decl_flavor]; intros k cp Hcp;
        destruct (Hnth k cp Hcp) as [cell [Hcell [Hrole [sh0 Hv]]]];
        exists cell; split; [ right; exact Hcell |];
        split; [ rewrite Hrole; reflexivity |];
        split; [ intro He; discriminate He |];
        split; [ intros fl He; injection He as He; subst fl; rewrite Hv; exact I |];
        rewrite Hv; apply spec_reverse_clauses; exact I
      | exact Hl ].
  - assert (Hroot : forall bb x, exists cell rest,
              fst (number_typespec (Some b) RPlain bb x) = (bb, cell) :: rest
              /\ (c_role cell = RPlain /\ (exists sh0, c_view cell = VTypeSpec sh0))).
    { intros bb x. destruct (number_typespec_view (Some b) RPlain bb x) as [cell [rest [Hf [Hr Hv]]]].
      exists cell, rest. split; [ exact Hf |]. split; [ exact Hr | exists (typespec_shape x); exact Hv ]. }
    pose proof (number_list_roots (number_typespec (Some b) RPlain)
                  (fun cell => c_role cell = RPlain /\ (exists sh0, c_view cell = VTypeSpec sh0))
                  (fun bb x => number_typespec_span (Some b) RPlain bb x) Hroot ts (S b)) as Hr.
    pose proof (number_list_layout (number_typespec (Some b) RPlain)
                  (fun bb x => number_typespec_layout (Some b) RPlain bb x) (S b) ts) as Hl.
    destruct (number_list (number_typespec (Some b) RPlain) (S b) ts) as [[kc bfin] roots].
    destruct Hr as [_ [_ [_ Hnth]]]. cbn [fst snd] in Hl.
    cbn [fst]. apply child_layout_ok_node;
      [ cbn [c_children c_view decl_flavor]; intros k cp Hcp;
        destruct (Hnth k cp Hcp) as [cell [Hcell [Hrole [sh0 Hv]]]];
        exists cell; split; [ right; exact Hcell |];
        split; [ rewrite Hrole; reflexivity |];
        split; [ intro He; discriminate He |];
        split; [ intros fl He; injection He as He; subst fl; rewrite Hv; exact I |];
        rewrite Hv; apply spec_reverse_clauses; exact I
      | exact Hl ].
Qed.

Lemma number_stmt_layout : forall par role b s, child_layout_ok (fst (number_stmt par role b s)).
Proof.
  intros par role b s. unfold number_stmt.
  destruct s as [e|d|names vals].
  - pose proof (number_expr_root e (Some b) RExprStatementExpr (S b)) as [erest [erc [Heroot [Herole [Heview _]]]]].
    pose proof (number_expr_layout e (Some b) RExprStatementExpr (S b)) as Hel.
    destruct (number_expr (Some b) RExprStatementExpr (S b) e) as [c b']. cbn [fst] in Heroot, Hel.
    cbn [fst]. apply child_layout_ok_node;
      [ cbn [c_children c_view]; intros k cp Hcp;
        destruct k as [|k']; [| destruct k'; discriminate Hcp ];
        injection Hcp as <-; exists erc;
        split; [ right; rewrite Heroot; left; reflexivity |];
        split; [ rewrite Herole; reflexivity |];
        split; [ intro He; discriminate He |];
        split; [ intros fl He; discriminate He |];
        rewrite Heview; apply no_reverse_clauses, expr_view_no_reverse
      | exact Hel ].
  - pose proof (number_decl_view (Some b) RPlain (S b) d) as [dcell [drest [Hdf [Hdr Hdv]]]].
    pose proof (number_decl_layout (Some b) RPlain (S b) d) as Hdl.
    destruct (number_decl (Some b) RPlain (S b) d) as [c b']. cbn [fst] in Hdf, Hdl.
    cbn [fst]. apply child_layout_ok_node;
      [ cbn [c_children c_view]; intros k cp Hcp;
        destruct k as [|k']; [| destruct k'; discriminate Hcp ];
        injection Hcp as <-; exists dcell;
        split; [ right; rewrite Hdf; left; reflexivity |];
        split; [ rewrite Hdr; reflexivity |];
        split; [ intro He; discriminate He |];
        split; [ intros fl He; discriminate He |];
        cbn [stmt_shape]; rewrite Hdv; apply decl_stmt_reverse_clauses
      | exact Hdl ].
  - assert (Hnroot : forall bb x, exists cell rest,
              fst (number_bindingname (Some b) RShortLhs bb x) = (bb, cell) :: rest
              /\ (c_role cell = RShortLhs /\ no_reverse (c_view cell))).
    { intros bb x. destruct (number_bindingname_view (Some b) RShortLhs bb x) as [cell [rest [Hf [Hr Hv]]]].
      exists cell, rest. split; [ exact Hf |].
      split; [ exact Hr | rewrite Hv; exact I ]. }
    pose proof (number_list_roots (number_bindingname (Some b) RShortLhs)
                  (fun cell => c_role cell = RShortLhs /\ no_reverse (c_view cell))
                  (fun bb x => number_bindingname_spans (Some b) RShortLhs bb x)
                  Hnroot
                  (Collections.ne_to_list names) (S b)) as Hnr.
    pose proof (number_list_layout (number_bindingname (Some b) RShortLhs)
                  (fun bb x => number_bindingname_layout (Some b) RShortLhs bb x)
                  (S b) (Collections.ne_to_list names)) as Hnl.
    destruct (number_list (number_bindingname (Some b) RShortLhs) (S b) (Collections.ne_to_list names))
      as [[nc b1] nroots].
    destruct Hnr as [Hnlen [_ [_ Hnnth]]]. cbn [fst snd] in Hnl.
    assert (Hvroot : forall bb x, exists cell rest,
              fst (number_expr (Some b) RPlain bb x) = (bb, cell) :: rest
              /\ (c_role cell = RPlain /\ no_reverse (c_view cell))).
    { intros bb x. destruct (number_expr_root x (Some b) RPlain bb) as [rest [rc [Hf [Hr [Hv _]]]]].
      exists rc, rest. split; [ exact Hf |].
      split; [ exact Hr | rewrite Hv; apply expr_view_no_reverse ]. }
    pose proof (number_list_roots (number_expr (Some b) RPlain)
                  (fun cell => c_role cell = RPlain /\ no_reverse (c_view cell))
                  (fun bb x => number_expr_spans x (Some b) RPlain bb)
                  Hvroot
                  (Collections.ne_to_list vals) b1) as Hvr.
    pose proof (number_list_layout (number_expr (Some b) RPlain)
                  (fun bb x => number_expr_layout x (Some b) RPlain bb)
                  b1 (Collections.ne_to_list vals)) as Hvl.
    destruct (number_list (number_expr (Some b) RPlain) b1 (Collections.ne_to_list vals)) as [[vc b2] vroots].
    destruct Hvr as [_ [_ [_ Hvnth]]]. cbn [fst snd] in Hvl.
    cbn [fst]. apply child_layout_ok_node.
    + cbn [c_children c_view]. unfold stmt_shape. intros k cp Hcp.
      set (NN := List.length (Collections.ne_to_list names)) in *.
      destruct (Nat.lt_ge_cases k (length nroots)) as [Hk|Hk].
      * rewrite nth_error_app1 in Hcp by exact Hk.
        destruct (Hnnth k cp Hcp) as [cell [Hcell [Hrole Hnc]]].
        exists cell. split; [ right; apply in_or_app; left; exact Hcell |].
        split.
        { rewrite Hrole. cbn [layout_role].
          assert (Hlt : k <? NN = true) by (apply Nat.ltb_lt; rewrite <- Hnlen; exact Hk).
          rewrite Hlt. reflexivity. }
        split; [ intro He; discriminate He |].
        split; [ intros fl He; discriminate He |].
        apply no_reverse_clauses, Hnc.
      * rewrite nth_error_app2 in Hcp by exact Hk.
        destruct (Hvnth (k - length nroots) cp Hcp) as [cell [Hcell [Hrole Hnc]]].
        exists cell. split; [ right; apply in_or_app; right; exact Hcell |].
        split.
        { rewrite Hrole. cbn [layout_role].
          assert (Hltb : k <? NN = false) by (apply Nat.ltb_ge; rewrite <- Hnlen; exact Hk).
          rewrite Hltb. reflexivity. }
        split; [ intro He; discriminate He |].
        split; [ intros fl He; discriminate He |].
        apply no_reverse_clauses, Hnc.
    + apply child_layout_ok_app; [ exact Hnl | exact Hvl ].
Qed.

Lemma number_block_layout : forall par role b blk, child_layout_ok (fst (number_block par role b blk)).
Proof.
  intros par role b [stmts]. unfold number_block.
  assert (Hroot : forall bb x, exists cell rest,
            fst (number_stmt (Some b) RPlain bb x) = (bb, cell) :: rest
            /\ (c_role cell = RPlain /\ (exists sh, c_view cell = VStmt sh))).
  { intros bb x. destruct (number_stmt_view (Some b) RPlain bb x) as [cell [rest [Hf [Hr Hv]]]].
    exists cell, rest. split; [ exact Hf |].
    split; [ exact Hr | exists (stmt_shape x); exact Hv ]. }
  pose proof (number_list_roots (number_stmt (Some b) RPlain)
                (fun cell => c_role cell = RPlain /\ (exists sh, c_view cell = VStmt sh))
                (fun bb x => number_stmt_span (Some b) RPlain bb x) Hroot stmts (S b)) as Hr.
  pose proof (number_list_layout (number_stmt (Some b) RPlain)
                (fun bb x => number_stmt_layout (Some b) RPlain bb x) (S b) stmts) as Hl.
  destruct (number_list (number_stmt (Some b) RPlain) (S b) stmts) as [[kc bfin] roots].
  destruct Hr as [_ [_ [_ Hnth]]]. cbn [fst snd] in Hl.
  cbn [fst]. apply child_layout_ok_node;
    [ cbn [c_children c_view]; intros k cp Hcp;
      destruct (Hnth k cp Hcp) as [cell [Hcell [Hrole [sh0 Hv]]]];
      exists cell; split; [ right; exact Hcell |];
      split; [ rewrite Hrole; reflexivity |];
      split; [ intro He; discriminate He |];
      split; [ intros fl He; discriminate He |];
      rewrite Hv; apply stmt_reverse_clauses
    | exact Hl ].
Qed.

Lemma number_toplevel_layout : forall par role b td, child_layout_ok (fst (number_toplevel par role b td)).
Proof.
  intros par role b td. unfold number_toplevel.
  destruct td as [d|blk].
  - pose proof (number_decl_view (Some b) RPlain (S b) d) as [dcell [drest [Hdf [Hdr Hdv]]]].
    pose proof (number_decl_layout (Some b) RPlain (S b) d) as Hdl.
    destruct (number_decl (Some b) RPlain (S b) d) as [c b']. cbn [fst] in Hdf, Hdl.
    cbn [fst]. apply child_layout_ok_node;
      [ cbn [c_children c_view]; intros k cp Hcp;
        destruct k as [|k']; [| destruct k'; discriminate Hcp ];
        injection Hcp as <-; exists dcell;
        split; [ right; rewrite Hdf; left; reflexivity |];
        split; [ rewrite Hdr; reflexivity |];
        split; [ intro He; discriminate He |];
        split; [ intros fl He; discriminate He |];
        cbn [top_shape]; rewrite Hdv; apply decl_top_reverse_clauses
      | exact Hdl ].
  - pose proof (number_block_view (Some b) RPlain (S b) blk) as [bcell [brest [Hbf [Hbr Hbv]]]].
    pose proof (number_block_layout (Some b) RPlain (S b) blk) as Hbl.
    destruct (number_block (Some b) RPlain (S b) blk) as [c b']. cbn [fst] in Hbf, Hbl.
    cbn [fst]. apply child_layout_ok_node;
      [ cbn [c_children c_view]; intros k cp Hcp;
        destruct k as [|k']; [| destruct k'; discriminate Hcp ];
        injection Hcp as <-; exists bcell;
        split; [ right; rewrite Hbf; left; reflexivity |];
        split; [ rewrite Hbr; reflexivity |];
        split; [ intros _; exact Hbv |];
        split; [ intros fl He; discriminate He |];
        rewrite Hbv; apply no_reverse_clauses; exact I
      | exact Hbl ].
Qed.

Lemma number_file_layout : forall f, child_layout_ok (number_file f).
Proof.
  intro f. unfold number_file.
  assert (Hroot : forall bb x, exists cell rest,
            fst (number_toplevel (Some 0) RPlain bb x) = (bb, cell) :: rest
            /\ (c_role cell = RPlain /\ no_reverse (c_view cell))).
  { intros bb x. destruct (number_toplevel_view (Some 0) RPlain bb x) as [cell [rest [Hf [Hr Hv]]]].
    exists cell, rest. split; [ exact Hf |].
    split; [ exact Hr | rewrite Hv; exact I ]. }
  pose proof (number_list_roots (number_toplevel (Some 0) RPlain)
                (fun cell => c_role cell = RPlain /\ no_reverse (c_view cell))
                (fun bb x => number_toplevel_span (Some 0) RPlain bb x) Hroot (Syntax.declarations f) 1) as Hr.
  pose proof (number_list_layout (number_toplevel (Some 0) RPlain)
                (fun bb x => number_toplevel_layout (Some 0) RPlain bb x) 1 (Syntax.declarations f)) as Hl.
  destruct (number_list (number_toplevel (Some 0) RPlain) 1 (Syntax.declarations f)) as [[dc bfin] droots].
  destruct Hr as [_ [_ [_ Hnth]]]. cbn [fst snd] in Hl.
  apply child_layout_ok_node;
    [ cbn [c_children c_view]; intros k cp Hcp;
      destruct (Hnth k cp Hcp) as [cell [Hcell [Hrole Hnc]]];
      exists cell; split; [ right; exact Hcell |];
      split; [ rewrite Hrole; reflexivity |];
      split; [ intro He; discriminate He |];
      split; [ intros fl He; discriminate He |];
      apply no_reverse_clauses, Hnc
    | exact Hl ].
Qed.

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

(* a listed child position is in range: coverage lifts it below the file's exact occurrence count *)
Lemma child_in_range {p} {idx : ProgramIndex p} (r : NodeRef idx) (q : nat) :
  In q (c_children (occ_at r)) -> q < occ_count (nr_file r).
Proof.
  intro Hq. destruct (occ_in_number_file r) as [f [Hin Hcount]].
  destruct (number_file_positions f) as [n Hpos].
  assert (Hlen : length (number_file f) = n).
  { apply (f_equal (@length nat)) in Hpos;
    first [ rewrite length_map in Hpos | rewrite map_length in Hpos ];
    first [ rewrite length_seq in Hpos | rewrite seq_length in Hpos ]; exact Hpos. }
  rewrite Hcount, Hlen. replace n with (0 + n) by lia.
  apply (child_lt (number_file f) n 0 (nr_pos r) (occ_at r) q);
    [ exact Hpos | apply number_file_cpo | exact Hin | exact Hq ].
Qed.

(* a parent edge points strictly earlier, so its ordinal is in range on the same file *)
Lemma parent_in_range {p} {idx : ProgramIndex p} (r : NodeRef idx) (pp : nat) :
  c_parent (occ_at r) = Some pp -> pp < occ_count (nr_file r).
Proof.
  intro Hpar. destruct (occ_in_number_file r) as [f [Hin Hcount]].
  destruct (number_file_pbounds f (nr_pos r) (occ_at r) Hin pp Hpar) as [_ Hlt].
  destruct (number_file_positions f) as [n Hpos].
  assert (Hposr : In (nr_pos r) (map fst (number_file f)))
    by (apply in_map_iff; exists (nr_pos r, occ_at r); split; [ reflexivity | exact Hin ]).
  rewrite Hpos in Hposr; apply in_seq in Hposr.
  assert (Hlen : length (number_file f) = n).
  { apply (f_equal (@length nat)) in Hpos;
    first [ rewrite length_map in Hpos | rewrite map_length in Hpos ];
    first [ rewrite length_seq in Hpos | rewrite seq_length in Hpos ]; exact Hpos. }
  rewrite Hcount, Hlen. lia.
Qed.

(* total refs: each in-range position becomes an exact NodeRef, never a dropped or optional member *)
Fixpoint refs_at_positions {p} {idx : ProgramIndex p} (fr : FileRef idx) (ps : list nat)
  : (forall pp, In pp ps -> pp < occ_count fr) -> list (NodeRef idx) :=
  match ps with
  | [] => fun _ => []
  | pp :: rest => fun H =>
      noderef_at_pos fr pp (H pp (or_introl eq_refl)) :: refs_at_positions fr rest (fun q Hq => H q (or_intror Hq))
  end.

(* the refs' ordinals are exactly the input positions, in order — no member dropped, none reordered *)
Lemma refs_at_positions_pos {p} {idx : ProgramIndex p} (fr : FileRef idx) (ps : list nat)
  (H : forall pp, In pp ps -> pp < occ_count fr) : map nr_pos (refs_at_positions fr ps H) = ps.
Proof. revert H; induction ps as [|pp rest IH]; intro H; cbn; [ reflexivity | rewrite noderef_at_pos_pos; f_equal; apply IH ]. Qed.

(* every ref built here lives on the given file *)
Lemma refs_at_positions_file {p} {idx : ProgramIndex p} (fr : FileRef idx) (ps : list nat)
  (H : forall pp, In pp ps -> pp < occ_count fr) (c : NodeRef idx) : In c (refs_at_positions fr ps H) -> nr_file c = fr.
Proof.
  revert H; induction ps as [|pp rest IH]; intros H Hc; cbn in Hc;
    [ destruct Hc | destruct Hc as [<-|Hin]; [ apply noderef_at_pos_file | apply (IH _ Hin) ] ].
Qed.

(* every ref on a file is a member of that file's one numbering, at its own ordinal *)
Lemma same_file_member {p} {idx : ProgramIndex p} (fr : FileRef idx) (f : Syntax.File) :
  cell_map fr = posmap_of (number_file f) ->
  forall x : NodeRef idx, nr_file x = fr -> In (nr_pos x, occ_at x) (number_file f).
Proof.
  intros Hcr x Hx. pose proof (occ_at_find x) as Hfx. rewrite Hx, Hcr in Hfx.
  destruct (posmap_find_in (number_file f) (nr_key x) (occ_at x) Hfx) as [pos [Hk Hinpos]].
  assert (pos = nr_pos x).
  { pose proof (nr_key_pos x) as Hkp.
    assert (Pos.of_succ_nat (nr_pos x) = Pos.of_succ_nat pos) as Hpp by (rewrite <- Hkp; exact Hk).
    apply (f_equal Pos.to_nat) in Hpp; rewrite !SuccNat2Pos.id_succ in Hpp; lia. }
  subst pos; exact Hinpos.
Qed.

(* the exact parent edge: a file root has no parent (genuine absence); otherwise the parent ref is total *)
Definition node_parent {p} {idx : ProgramIndex p} (r : NodeRef idx) : option (NodeRef idx) :=
  (match c_parent (occ_at r) as o return (forall pp, o = Some pp -> pp < occ_count (nr_file r)) -> option (NodeRef idx) with
   | Some pp => fun H => Some (noderef_at_pos (nr_file r) pp (H pp eq_refl))
   | None => fun _ => None
   end) (parent_in_range r).

(* the exact ordered direct children: every listed child is a total ref, none dropped or optional *)
Definition node_children {p} {idx : ProgramIndex p} (r : NodeRef idx) : list (NodeRef idx) :=
  refs_at_positions (nr_file r) (c_children (occ_at r)) (child_in_range r).

(* completeness + order + inverse: the children refs' ordinals are exactly this cell's child list *)
Lemma node_children_pos {p} {idx : ProgramIndex p} (r : NodeRef idx) :
  map nr_pos (node_children r) = c_children (occ_at r).
Proof. apply refs_at_positions_pos. Qed.

(* every direct child lives on its parent's file *)
Lemma node_children_file {p} {idx : ProgramIndex p} (r : NodeRef idx) (c : NodeRef idx) :
  In c (node_children r) -> nr_file c = nr_file r.
Proof. apply refs_at_positions_file. Qed.

(* a file root is exactly the parentless node: the parent edge is None iff the cell has no parent *)
Lemma node_parent_none {p} {idx : ProgramIndex p} (r : NodeRef idx) :
  node_parent r = None <-> c_parent (occ_at r) = None.
Proof.
  unfold node_parent; generalize (parent_in_range r); destruct (c_parent (occ_at r)) as [pp|]; intro H; cbn;
    split; intro H2; solve [ discriminate | reflexivity ].
Qed.

(* parent soundness: a present parent edge resolves to the exact parent ordinal on the same file *)
Lemma node_parent_some {p} {idx : ProgramIndex p} (r : NodeRef idx) (pp : nat) :
  c_parent (occ_at r) = Some pp ->
  exists pc, node_parent r = Some pc /\ nr_pos pc = pp /\ nr_file pc = nr_file r.
Proof.
  intro E. unfold node_parent; generalize (parent_in_range r); destruct (c_parent (occ_at r)) as [pp0|]; intro H;
    [ injection E as <-; cbn; eexists;
      split; [ reflexivity | split; [ apply noderef_at_pos_pos | apply noderef_at_pos_file ] ]
    | discriminate E ].
Qed.

(* parent/child inverse: a direct child's parent edge points back exactly to its parent node *)
Lemma node_children_inverse {p} {idx : ProgramIndex p} (r c : NodeRef idx) :
  In c (node_children r) -> node_parent c = Some r.
Proof.
  intro Hin.
  pose proof (node_children_file r c Hin) as Hf.
  assert (Hpos : In (nr_pos c) (c_children (occ_at r)))
    by (rewrite <- (node_children_pos r); apply in_map; exact Hin).
  destruct (cellmap_number_file (nr_file r)) as [f Hcr].
  pose proof (same_file_member (nr_file r) f Hcr) as Hmem.
  destruct (number_file_cpo f (nr_pos r) (occ_at r) (Hmem r eq_refl) (nr_pos c) Hpos) as [ccell [Hincell Hpar]].
  assert (Hcpar : c_parent (occ_at c) = Some (nr_pos r)).
  { assert (occ_at c = ccell)
      by (apply (occ_unique (number_file f) (nr_pos c) (occ_at c) ccell);
          [ apply occurrences_distinct | exact (Hmem c Hf) | exact Hincell ]).
    rewrite H; exact Hpar. }
  destruct (node_parent_some c (nr_pos r) Hcpar) as [pc [Hnp [Hpcpos Hpcfile]]].
  rewrite Hnp; f_equal; apply noderef_positional; [ rewrite Hpcfile; exact Hf | exact Hpcpos ].
Qed.

(* parent-edge inversion: a present parent resolves to the exact stored ordinal on the same file *)
Lemma node_parent_inv {p} {idx : ProgramIndex p} (r par : NodeRef idx) :
  node_parent r = Some par -> c_parent (occ_at r) = Some (nr_pos par) /\ nr_file par = nr_file r.
Proof.
  unfold node_parent. generalize (parent_in_range r).
  destruct (c_parent (occ_at r)) as [pp|]; intro H; cbn; intro He; [| discriminate He ].
  injection He as <-. split; [ rewrite noderef_at_pos_pos; reflexivity | apply noderef_at_pos_file ].
Qed.

(* the converse inverse: a node whose parent edge names par is itself among par's direct children *)
Lemma node_parent_children {p} {idx : ProgramIndex p} (r par : NodeRef idx) :
  node_parent r = Some par -> In r (node_children par).
Proof.
  intro Hnp. destruct (node_parent_inv r par Hnp) as [Hcp Hf].
  destruct (cellmap_number_file (nr_file r)) as [f Hcr].
  pose proof (same_file_member (nr_file r) f Hcr) as Hmem.
  pose proof (Hmem r eq_refl) as Hinr.
  assert (Hinp : In (nr_pos par, occ_at par) (number_file f)) by (apply Hmem; exact Hf).
  pose proof (number_file_complete f (nr_pos r) (occ_at r) (nr_pos par) (occ_at par) Hinr Hinp Hcp) as Hin.
  rewrite <- (node_children_pos par) in Hin.
  apply in_map_iff in Hin. destruct Hin as [c' [Hpos Hin']].
  assert (Hc : c' = r).
  { apply noderef_positional; [| exact Hpos ].
    rewrite (node_children_file par c' Hin'). exact Hf. }
  subst c'. exact Hin'.
Qed.

(* the numbering's head is the file root cell at position zero *)
Lemma number_file_root : forall f, exists ext ch, In (0, mkCell VFile RPlain None ext ch) (number_file f).
Proof.
  intro f. unfold number_file.
  destruct (number_list (number_toplevel (Some 0) RPlain) 1 (Syntax.declarations f)) as [[dc bfin] droots].
  eexists. eexists. left. reflexivity.
Qed.

(* only the file root is parentless: every other occurrence is some cell's exact child *)
Lemma parentless_view_file {p} {idx : ProgramIndex p} (r : NodeRef idx) :
  node_parent r = None -> node_view r = VFile.
Proof.
  intro Hn. apply node_parent_none in Hn.
  destruct (cellmap_number_file (nr_file r)) as [f Hcr].
  pose proof (same_file_member (nr_file r) f Hcr) as Hmem.
  pose proof (Hmem r eq_refl) as Hin.
  destruct (Nat.eq_dec (nr_pos r) 0) as [H0|Hpos].
  - destruct (number_file_root f) as [ext [ch Hroot]].
    assert (Hocc : occ_at r = mkCell VFile RPlain None ext ch)
      by (apply (occ_unique (number_file f) (nr_pos r));
          [ apply occurrences_distinct | exact Hin | rewrite H0; exact Hroot ]).
    unfold node_view. rewrite Hocc. reflexivity.
  - exfalso.
    pose proof (number_file_positions f) as [count Hposs].
    assert (Hinp : In (nr_pos r) (map fst (number_file f)))
      by (apply in_map_iff; exists (nr_pos r, occ_at r); split; [ reflexivity | exact Hin ]).
    rewrite Hposs in Hinp. apply in_seq in Hinp.
    assert (Hlen : List.length (number_file f) = count).
    { first [ rewrite <- (length_map fst (number_file f)) | rewrite <- (map_length fst (number_file f)) ].
      rewrite Hposs. first [ apply length_seq | apply seq_length ]. }
    destruct (number_file_cover f (nr_pos r) ltac:(lia)) as [q [qcell [Hinq Hch]]].
    destruct (number_file_cpo f q qcell Hinq (nr_pos r) Hch) as [ccell [Hinc Hpar]].
    assert (Hocc : ccell = occ_at r)
      by (apply (occ_unique (number_file f) (nr_pos r));
          [ apply occurrences_distinct | exact Hinc | exact Hin ]).
    rewrite Hocc in Hpar. rewrite Hn in Hpar. discriminate Hpar.
Qed.

(* a child's position never exceeds its parent's exact extent, and a node's extent covers its position *)
Lemma child_le_extent {p} {idx : ProgramIndex p} (r c : NodeRef idx) :
  node_parent c = Some r -> nr_pos c <= node_extent r.
Proof.
  intro Hp. destruct (node_parent_inv c r Hp) as [Hcp Hf].
  destruct (cellmap_number_file (nr_file c)) as [f Hcr].
  pose proof (same_file_member (nr_file c) f Hcr) as Hmem.
  pose proof (Hmem c eq_refl) as Hinc.
  assert (Hinr : In (nr_pos r, occ_at r) (number_file f)) by (apply Hmem; exact Hf).
  destruct (number_file_extent f (nr_pos r) (occ_at r) Hinr) as [_ Hch].
  exact (Hch (nr_pos c) (occ_at c) Hinc Hcp).
Qed.

Lemma node_extent_ge {p} {idx : ProgramIndex p} (r : NodeRef idx) : nr_pos r <= node_extent r.
Proof.
  destruct (cellmap_number_file (nr_file r)) as [f Hcr].
  pose proof (same_file_member (nr_file r) f Hcr) as Hmem.
  destruct (number_file_extent f (nr_pos r) (occ_at r) (Hmem r eq_refl)) as [[Hle _] _].
  exact Hle.
Qed.

(* the children refs' length matches the stored child list *)
Lemma node_children_length {p} {idx : ProgramIndex p} (r : NodeRef idx) :
  length (node_children r) = length (c_children (occ_at r)).
Proof.
  pose proof (node_children_pos r) as H. apply (f_equal (@length nat)) in H.
  rewrite length_map in H. exact H.
Qed.

(* an ordinal-indexed child ref sits at the exact stored child position *)
Lemma node_child_pos_at {p} {idx : ProgramIndex p} (r c : NodeRef idx) (k : nat) :
  nth_error (node_children r) k = Some c -> nth_error (c_children (occ_at r)) k = Some (nr_pos c).
Proof.
  intro H. rewrite <- (node_children_pos r). exact (map_nth_error nr_pos k (node_children r) H).
Qed.

(* the per-cell shape law lifted to any node: ascending children and shape-fixed counts *)
Lemma occ_shape_ok {p} {idx : ProgramIndex p} (r : NodeRef idx) : cell_shape_ok (occ_at r).
Proof.
  destruct (occ_in_number_file r) as [f [Hin _]].
  pose proof (number_file_shape f) as Hs. unfold shape_ok in Hs. rewrite Forall_forall in Hs.
  exact (Hs (nr_pos r, occ_at r) Hin).
Qed.

(* the exact child-count law: a shape-fixed count is the exact children length *)
Lemma node_children_count {p} {idx : ProgramIndex p} (r : NodeRef idx) (n : nat) :
  layout_count (node_view r) = Some n -> length (node_children r) = n.
Proof.
  intro Hc. destruct (occ_shape_ok r) as [_ Hcount].
  unfold node_view in Hc. rewrite Hc in Hcount. rewrite node_children_length. exact Hcount.
Qed.

(* source order is ordinal order: a lower child ordinal is an earlier source position *)
Lemma node_children_asc {p} {idx : ProgramIndex p} (r ci cj : NodeRef idx) (i j : nat) :
  i < j -> nth_error (node_children r) i = Some ci -> nth_error (node_children r) j = Some cj ->
  nr_pos ci < nr_pos cj.
Proof.
  intros Hij Hi Hj. destruct (occ_shape_ok r) as [Hasc _].
  exact (asc_nth (c_children (occ_at r)) i j (nr_pos ci) (nr_pos cj) Hasc Hij
           (node_child_pos_at r ci i Hi) (node_child_pos_at r cj j Hj)).
Qed.

(* each direct child sits at exactly one ordinal: the canonical positional identity is unique *)
Lemma node_child_ord_unique {p} {idx : ProgramIndex p} (r c : NodeRef idx) (i j : nat) :
  nth_error (node_children r) i = Some c -> nth_error (node_children r) j = Some c -> i = j.
Proof.
  intros Hi Hj. destruct (Nat.lt_trichotomy i j) as [Hlt|[Heq|Hgt]]; [| exact Heq |].
  - exfalso. pose proof (node_children_asc r c c i j Hlt Hi Hj). lia.
  - exfalso. pose proof (node_children_asc r c c j i Hgt Hj Hi). lia.
Qed.

(* the exact layout-role law: the child at ordinal k carries exactly the role the parent's view fixes *)
Lemma node_child_role {p} {idx : ProgramIndex p} (r c : NodeRef idx) (k : nat) :
  nth_error (node_children r) k = Some c -> node_role c = layout_role (node_view r) k.
Proof.
  intro H.
  assert (Hf : nr_file c = nr_file r) by (apply node_children_file; exact (nth_error_In _ _ H)).
  pose proof (node_child_pos_at r c k H) as Hat.
  destruct (cellmap_number_file (nr_file r)) as [f Hcr].
  pose proof (same_file_member (nr_file r) f Hcr) as Hmem.
  destruct (number_file_layout f (nr_pos r) (occ_at r) (Hmem r eq_refl) k (nr_pos c) Hat)
    as [cc [Hincc [Hrole _]]].
  assert (Hocc : occ_at c = cc)
    by (apply (occ_unique (number_file f) (nr_pos c) (occ_at c) cc);
        [ apply occurrences_distinct | exact (Hmem c Hf) | exact Hincc ]).
  unfold node_role, node_view. rewrite Hocc. exact Hrole.
Qed.

(* the fixed-main body law: the child of a main top-level occurrence is exactly a block *)
Lemma node_child_main_block {p} {idx : ProgramIndex p} (r c : NodeRef idx) (k : nat) :
  node_view r = VTop TSMain -> nth_error (node_children r) k = Some c -> node_view c = VBlock.
Proof.
  intros Hm H.
  assert (Hf : nr_file c = nr_file r) by (apply node_children_file; exact (nth_error_In _ _ H)).
  pose proof (node_child_pos_at r c k H) as Hat.
  destruct (cellmap_number_file (nr_file r)) as [f Hcr].
  pose proof (same_file_member (nr_file r) f Hcr) as Hmem.
  destruct (number_file_layout f (nr_pos r) (occ_at r) (Hmem r eq_refl) k (nr_pos c) Hat)
    as [cc [Hincc [_ [Hblock _]]]].
  assert (Hocc : occ_at c = cc)
    by (apply (occ_unique (number_file f) (nr_pos c) (occ_at c) cc);
        [ apply occurrences_distinct | exact (Hmem c Hf) | exact Hincc ]).
  unfold node_view in Hm |- *. rewrite Hocc. exact (Hblock Hm).
Qed.

(* a declaration's children are exactly its flavor's specs, and const specs arise only under declarations *)
Lemma node_child_decl_spec {p} {idx : ProgramIndex p} (r c : NodeRef idx) (fl : SpecFlavor) (k : nat) :
  node_view r = VDecl fl -> nth_error (node_children r) k = Some c -> spec_view_of_flavor fl (node_view c).
Proof.
  intros Hd H.
  assert (Hf : nr_file c = nr_file r) by (apply node_children_file; exact (nth_error_In _ _ H)).
  pose proof (node_child_pos_at r c k H) as Hat.
  destruct (cellmap_number_file (nr_file r)) as [f Hcr].
  pose proof (same_file_member (nr_file r) f Hcr) as Hmem.
  destruct (number_file_layout f (nr_pos r) (occ_at r) (Hmem r eq_refl) k (nr_pos c) Hat)
    as [cc [Hincc [_ [_ [Hdecl _]]]]].
  assert (Hocc : occ_at c = cc)
    by (apply (occ_unique (number_file f) (nr_pos c) (occ_at c) cc);
        [ apply occurrences_distinct | exact (Hmem c Hf) | exact Hincc ]).
  unfold node_view in Hd |- *. rewrite Hocc. exact (Hdecl fl Hd).
Qed.

(* the shared reverse-clause extraction: the child's exact cell and the parent's reverse clauses *)
Lemma node_child_reverse {p} {idx : ProgramIndex p} (r c : NodeRef idx) (k : nat) :
  nth_error (node_children r) k = Some c -> reverse_clauses (node_view r) (node_view c).
Proof.
  intro H.
  assert (Hf : nr_file c = nr_file r) by (apply node_children_file; exact (nth_error_In _ _ H)).
  pose proof (node_child_pos_at r c k H) as Hat.
  destruct (cellmap_number_file (nr_file r)) as [f Hcr].
  pose proof (same_file_member (nr_file r) f Hcr) as Hmem.
  destruct (number_file_layout f (nr_pos r) (occ_at r) (Hmem r eq_refl) k (nr_pos c) Hat)
    as [cc [Hincc [_ [_ [_ Hrev]]]]].
  assert (Hocc : occ_at c = cc)
    by (apply (occ_unique (number_file f) (nr_pos c) (occ_at c) cc);
        [ apply occurrences_distinct | exact (Hmem c Hf) | exact Hincc ]).
  unfold node_view. rewrite Hocc. exact Hrev.
Qed.

Lemma node_child_const_parent {p} {idx : ProgramIndex p} (r c : NodeRef idx) (k : nat) (sh : ConstShape) :
  nth_error (node_children r) k = Some c -> node_view c = VConstSpec sh ->
  exists fl, node_view r = VDecl fl.
Proof.
  intros H Hc. destruct (node_child_reverse r c k H) as [Hspec _].
  exists ConstSpecF. apply Hspec. rewrite Hc. exact I.
Qed.

(* a spec's parent is its exact flavor's declaration *)
Lemma node_child_spec_decl {p} {idx : ProgramIndex p} (r c : NodeRef idx) (k : nat) (fl : SpecFlavor) :
  nth_error (node_children r) k = Some c -> spec_view_of_flavor fl (node_view c) ->
  node_view r = VDecl fl.
Proof.
  intros H Hv. destruct (node_child_reverse r c k H) as [Hspec _]. exact (Hspec fl Hv).
Qed.

(* a statement's parent is its block: statements arise only as block children *)
Lemma node_child_stmt_block {p} {idx : ProgramIndex p} (r c : NodeRef idx) (k : nat) (sh : StmtShape) :
  nth_error (node_children r) k = Some c -> node_view c = VStmt sh -> node_view r = VBlock.
Proof.
  intros H Hv. destruct (node_child_reverse r c k H) as [_ [Hstmt _]]. exact (Hstmt sh Hv).
Qed.

(* a declaration's parent is a declaration statement or a top-level declaration *)
Lemma node_child_decl_parent {p} {idx : ProgramIndex p} (r c : NodeRef idx) (k : nat) (fl : SpecFlavor) :
  nth_error (node_children r) k = Some c -> node_view c = VDecl fl ->
  node_view r = VStmt SSDecl \/ node_view r = VTop TSTopDecl.
Proof.
  intros H Hv. destruct (node_child_reverse r c k H) as [_ [_ Hdecl]]. exact (Hdecl fl Hv).
Qed.

(* a spec-name-roled child sits under its exact flavor's spec: the layout role pins the parent view class *)
Lemma node_child_specname_spec {p} {idx : ProgramIndex p} (r c : NodeRef idx) (k : nat) (fl : SpecFlavor) :
  nth_error (node_children r) k = Some c -> node_role c = RSpecName fl ->
  spec_view_of_flavor fl (node_view r).
Proof.
  intros H Hr. pose proof (node_child_role r c k H) as Hrole. rewrite Hr in Hrole.
  destruct (node_view r) as [n|l|u| |t|bn|csh|vsh|tsh|dfl|ssh| |ts|]; cbn [layout_role] in Hrole;
    try discriminate Hrole.
  - destruct k; discriminate Hrole.
  - destruct csh as [ht nn nv|nn]; cbn [layout_role] in Hrole.
    + destruct (k <? nn); [ injection Hrole as ->; exact I |].
      destruct (andb ht (k =? nn)); discriminate Hrole.
    + injection Hrole as ->; exact I.
  - destruct vsh as [nn|ht nn nv]; cbn [layout_role] in Hrole.
    + destruct (k <? nn); [ injection Hrole as ->; exact I | discriminate Hrole ].
    + destruct (k <? nn); [ injection Hrole as ->; exact I |].
      destruct (andb ht (k =? nn)); discriminate Hrole.
  - destruct k; [ injection Hrole as ->; exact I | discriminate Hrole ].
  - destruct ssh as [| |nn nv]; cbn [layout_role] in Hrole; try discriminate Hrole.
    destruct (k <? nn); discriminate Hrole.
Qed.

(* total file enumeration: every retained occurrence position becomes an exact NodeRef, none omitted *)
Definition file_nodes {p} {idx : ProgramIndex p} (fr : FileRef idx) : list (NodeRef idx) :=
  refs_at_positions fr (seq 0 (occ_count fr)) (fun pp Hpp => proj2 (proj1 (in_seq (occ_count fr) 0 pp) Hpp)).

(* every enumerated node lives on the given file *)
Lemma file_nodes_file {p} {idx : ProgramIndex p} (fr : FileRef idx) (r : NodeRef idx) :
  In r (file_nodes fr) -> nr_file r = fr.
Proof. apply refs_at_positions_file. Qed.

(* the enumeration covers exactly the file's ordinal positions in ascending order, none dropped *)
Lemma file_nodes_pos {p} {idx : ProgramIndex p} (fr : FileRef idx) :
  map nr_pos (file_nodes fr) = seq 0 (occ_count fr).
Proof. apply refs_at_positions_pos. Qed.

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


(* exact refined parents: each edge family is requested only from a parent proven to be its exact kind *)
Record AppRef {p} (idx : ProgramIndex p) : Type := mkAppRef {
  app_node : NodeRef idx ;
  app_ok   : node_view app_node = VApplication
}.
Arguments mkAppRef {p idx} _ _.
Arguments app_node {p idx} _.
Arguments app_ok {p idx} _.

Record UnaryRef {p} (idx : ProgramIndex p) : Type := mkUnaryRef {
  un_node : NodeRef idx ;
  un_op   : Syntax.UnaryOp ;
  un_ok   : node_view un_node = VUnary un_op
}.
Arguments mkUnaryRef {p idx} _ _ _.
Arguments un_node {p idx} _.
Arguments un_op {p idx} _.
Arguments un_ok {p idx} _.

Record ExprStmtRef {p} (idx : ProgramIndex p) : Type := mkExprStmtRef {
  exs_node : NodeRef idx ;
  exs_ok   : node_view exs_node = VStmt SSExpr
}.
Arguments mkExprStmtRef {p idx} _ _.
Arguments exs_node {p idx} _.
Arguments exs_ok {p idx} _.

Record ShortStmtRef {p} (idx : ProgramIndex p) : Type := mkShortStmtRef {
  sh_node   : NodeRef idx ;
  sh_names  : nat ;
  sh_values : nat ;
  sh_ok     : node_view sh_node = VStmt (SSShort sh_names sh_values)
}.
Arguments mkShortStmtRef {p idx} _ _ _ _.
Arguments sh_node {p idx} _.
Arguments sh_names {p idx} _.
Arguments sh_values {p idx} _.
Arguments sh_ok {p idx} _.

(* one flavor-indexed spec parent: the exact shape is retained, so every field formula reads it *)
Definition SpecShape (fl : SpecFlavor) : Type :=
  match fl with ConstSpecF => ConstShape | VarSpecF => VarShape | TypeSpecF => TypeSpecShape end.
Definition spec_view_of (fl : SpecFlavor) : SpecShape fl -> NodeView :=
  match fl with ConstSpecF => VConstSpec | VarSpecF => VVarSpec | TypeSpecF => VTypeSpec end.
Record SpecRef {p} (idx : ProgramIndex p) (fl : SpecFlavor) : Type := mkSpecRef {
  sp_node  : NodeRef idx ;
  sp_shape : SpecShape fl ;
  sp_ok    : node_view sp_node = spec_view_of fl sp_shape
}.
Arguments mkSpecRef {p idx fl} _ _ _.
Arguments sp_node {p idx fl} _.
Arguments sp_shape {p idx fl} _.
Arguments sp_ok {p idx fl} _.

(* the scalar layout each spec shape fixes: name count, declared-type presence, value count *)
Definition shape_names (fl : SpecFlavor) : SpecShape fl -> nat :=
  match fl with
  | ConstSpecF => fun sh => match sh with CSExplicit _ nn _ => nn | CSInherited nn => nn end
  | VarSpecF   => fun sh => match sh with VSTypeOnly nn => nn | VSValues _ nn _ => nn end
  | TypeSpecF  => fun _ => 1
  end.
Definition shape_has_type (fl : SpecFlavor) : SpecShape fl -> bool :=
  match fl with
  | ConstSpecF => fun sh => match sh with CSExplicit ht _ _ => ht | CSInherited _ => false end
  | VarSpecF   => fun sh => match sh with VSTypeOnly _ => true | VSValues ht _ _ => ht end
  | TypeSpecF  => fun _ => true
  end.
Definition shape_values (fl : SpecFlavor) : SpecShape fl -> nat :=
  match fl with
  | ConstSpecF => fun sh => match sh with CSExplicit _ _ nv => nv | CSInherited _ => 0 end
  | VarSpecF   => fun sh => match sh with VSValues _ _ nv => nv | VSTypeOnly _ => 0 end
  | TypeSpecF  => fun _ => 0
  end.
Definition type_ordinal (fl : SpecFlavor) (sh : SpecShape fl) : nat := shape_names fl sh.
Definition value_ordinal (fl : SpecFlavor) (sh : SpecShape fl) (j : nat) : nat :=
  shape_names fl sh + (if shape_has_type fl sh then 1 else 0) + j.

(* the shape-fixed count IS the layout count of the spec's view: the two authorities agree by computation *)
Lemma spec_layout_count : forall fl (sh : SpecShape fl),
  layout_count (spec_view_of fl sh)
  = Some (shape_names fl sh + (if shape_has_type fl sh then 1 else 0) + shape_values fl sh).
Proof. destruct fl; destruct sh; cbn; try reflexivity; f_equal; lia. Qed.

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

(* the target's own canonical edge, recovered exactly; the scan cannot miss a real child *)
Lemma child_eq_of {p} {idx : ProgramIndex p} {par : NodeRef idx} {o : nat} (r : NodeRef idx)
  (e : ChildAt par o) : nr_pos (ca_child e) = nr_pos r -> nr_file par = nr_file r -> ca_child e = r.
Proof.
  intros Hp Hf. apply noderef_positional; [| exact Hp ].
  rewrite (node_children_file par _ (ca_in e)). exact Hf.
Qed.

Fixpoint self_scan {p} {idx : ProgramIndex p} (r par : NodeRef idx) (Hf : nr_file par = nr_file r)
  (l : list { o : nat & ChildAt par o }) {struct l} : option (SelfEdge r) :=
  match l with
  | [] => None
  | existT _ o e :: rest =>
      match Nat.eq_dec (nr_pos (ca_child e)) (nr_pos r) with
      | left Hp => Some (mkSelfEdge par o e (child_eq_of r e Hp Hf))
      | right _ => self_scan r par Hf rest
      end
  end.

Lemma self_scan_finds {p} {idx : ProgramIndex p} (r par : NodeRef idx) (Hf : nr_file par = nr_file r) :
  forall l, (exists o (e : ChildAt par o), In (existT _ o e) l /\ ca_child e = r) ->
  self_scan r par Hf l <> None.
Proof.
  induction l as [|[o e] rest IH]; intros [o0 [e0 [Hin Heq]]]; [ destruct Hin |].
  cbn. destruct (Nat.eq_dec (nr_pos (ca_child e)) (nr_pos r)) as [|Hne]; [ discriminate |].
  destruct Hin as [Hhead|Hin].
  - exfalso. apply Hne. injection Hhead as Ho He. subst o0.
    apply Eqdep_dec.inj_pair2_eq_dec in He; [| exact Nat.eq_dec ]. subst e0.
    rewrite Heq. reflexivity.
  - apply IH. exists o0, e0. split; [ exact Hin | exact Heq ].
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

Definition self_edge_of {p} {idx : ProgramIndex p} (r par : NodeRef idx)
  (H : node_parent r = Some par) : SelfEdge r :=
  (match self_scan r par (proj2 (node_parent_inv r par H)) (all_children par)
         as o return self_scan r par (proj2 (node_parent_inv r par H)) (all_children par) = o -> SelfEdge r with
   | Some se => fun _ => se
   | None => fun E =>
       False_rect _ (self_scan_finds r par (proj2 (node_parent_inv r par H)) (all_children par)
                       (all_children_has par r (node_parent_children r par H)) E)
   end) eq_refl.

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
