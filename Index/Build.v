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
