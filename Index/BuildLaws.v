(* Index.BuildLaws — the laws of the one canonical numbering/build: spans, roots, coverage, layout, shape. *)
From Stdlib Require Import List Bool Arith PeanoNat Lia Eqdep_dec PArith FSets.FMapFacts.
From Fido Require Import Collections Syntax Index.Model Index.Build.
Import ListNotations.

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

(* the numbering's head is the file root cell at position zero *)
Lemma number_file_root : forall f, exists ext ch, In (0, mkCell VFile RPlain None ext ch) (number_file f).
Proof.
  intro f. unfold number_file.
  destruct (number_list (number_toplevel (Some 0) RPlain) 1 (Syntax.declarations f)) as [[dc bfin] droots].
  eexists. eexists. left. reflexivity.
Qed.


Definition child_kind_ok (occs : list (nat * Cell)) : Prop :=
  forall pos cell, In (pos, cell) occs ->
    forall k cp, nth_error (c_children cell) k = Some cp ->
      exists cc, In (cp, cc) occs /\ kind_of_view (c_view cc) = layout_kind (c_view cell) k.

Lemma child_kind_ok_app : forall c1 c2, child_kind_ok c1 -> child_kind_ok c2 -> child_kind_ok (c1 ++ c2).
Proof.
  intros c1 c2 H1 H2 pos cell Hin k cp Hcp. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  - destruct (H1 pos cell Hin k cp Hcp) as [cc [Hc Hp]]. exists cc.
    split; [ apply in_or_app; left; exact Hc | exact Hp ].
  - destruct (H2 pos cell Hin k cp Hcp) as [cc [Hc Hp]]. exists cc.
    split; [ apply in_or_app; right; exact Hc | exact Hp ].
Qed.

Lemma child_kind_ok_node : forall self cell kids,
  (forall k cp, nth_error (c_children cell) k = Some cp ->
     exists cc, In (cp, cc) ((self, cell) :: kids) /\ kind_of_view (c_view cc) = layout_kind (c_view cell) k) ->
  child_kind_ok kids -> child_kind_ok ((self, cell) :: kids).
Proof.
  intros self cell kids Hself Hkids pos c Hin k cp Hcp. destruct Hin as [Heq|Hin].
  - inversion Heq; subst. exact (Hself k cp Hcp).
  - destruct (Hkids pos c Hin k cp Hcp) as [cc [Hc Hp]]. exists cc. split; [ right; exact Hc | exact Hp ].
Qed.

Lemma number_leaf_kind : forall v par role b, child_kind_ok (fst (number_leaf v par role b)).
Proof.
  intros v par role b pos cell Hin k cp Hcp. cbn [number_leaf fst] in Hin. destruct Hin as [Heq|[]].
  inversion Heq; subst. cbn [c_children] in Hcp. destruct k; discriminate Hcp.
Qed.

Lemma expr_view_kind : forall e, kind_of_view (expr_view e) = ExprKind.
Proof. intro e; destruct e; reflexivity. Qed.

Lemma number_list_kind {A} (g : nat -> A -> list (nat * Cell) * nat) :
  (forall b x, child_kind_ok (fst (g b x))) ->
  forall b xs, child_kind_ok (fst (fst (number_list g b xs))).
Proof.
  intros Hg b xs; revert b; induction xs as [|x rest IH]; intro b.
  - intros pos c Hin; destruct Hin.
  - cbn [number_list]. pose proof (Hg b x) as Hgx. destruct (g b x) as [xc b'].
    specialize (IH b'). destruct (number_list g b' rest) as [[rc bfin] roots].
    cbn [fst snd] in Hgx, IH |- *. apply child_kind_ok_app; [ exact Hgx | exact IH ].
Qed.

Lemma number_expr_kind : forall e par role b, child_kind_ok (fst (number_expr par role b e)).
Proof.
  intro e; induction e using Syntax.Expr_ind'; intros par role b; cbn [number_expr].
  - apply number_leaf_kind.
  - apply number_leaf_kind.
  - specialize (IHe (Some b) RUnaryOperand (S b)).
    pose proof (number_expr_root e (Some b) RUnaryOperand (S b)) as [urest [urc [Huroot [_ [Huview _]]]]].
    destruct (number_expr (Some b) RUnaryOperand (S b) e) as [kc nxt].
    cbn [fst] in IHe, Huroot |- *.
    apply child_kind_ok_node.
    + cbn [c_children c_view]. intros k cp Hcp. destruct k as [|k']; [| destruct k'; discriminate Hcp ].
      injection Hcp as <-. exists urc.
      split; [ right; rewrite Huroot; left; reflexivity |].
      cbn [layout_kind]. rewrite Huview. apply expr_view_kind.
    + exact IHe.
  - specialize (IHe (Some b) RApplicationHead (S b)).
    pose proof (number_expr_root e (Some b) RApplicationHead (S b)) as [hrest [hrc [Hhroot [_ [Hhview _]]]]].
    destruct (number_expr (Some b) RApplicationHead (S b) e) as [hc b1].
    cbn [fst] in IHe, Hhroot.
    assert (Hda : forall es, Forall (fun a => forall par role bb,
                     child_kind_ok (fst (number_expr par role bb a))) es ->
      forall i0 bi, (let '(ac, _, roots) := (fix do_args (i bi : nat) (es : list Syntax.Expr) {struct es}
              : list (nat * Cell) * nat * list nat :=
              match es with
              | [] => ([], bi, [])
              | a :: rest =>
                  let '(ac, bi') := number_expr (Some b) (RApplicationArg i) bi a in
                  let '(rc, bf, roots) := do_args (S i) bi' rest in
                  (ac ++ rc, bf, bi :: roots)
              end) i0 bi es in
        child_kind_ok ac /\
        (forall k r0, nth_error roots k = Some r0 ->
           exists cc, In (r0, cc) ac /\ kind_of_view (c_view cc) = ExprKind))).
    { intros es Hall; induction Hall as [| a rest Ha Hrest IHrest]; intros i0 bi.
      - split; [ intros pos c Hin; destruct Hin | intros k r0 Hk; destruct k; discriminate Hk ].
      - pose proof (number_expr_root a (Some b) (RApplicationArg i0) bi) as [arest [arc [Haroot [_ [Haview _]]]]].
        specialize (Ha (Some b) (RApplicationArg i0) bi).
        destruct (number_expr (Some b) (RApplicationArg i0) bi a) as [ac1 bi'].
        cbn [fst] in Ha, Haroot.
        specialize (IHrest (S i0) bi').
        destruct ((fix do_args (i bi : nat) (es : list Syntax.Expr) {struct es} := _) (S i0) bi' rest)
          as [[rc bf] roots].
        destruct IHrest as [Hrcok Hroots]. cbn [fst snd] in Hrcok, Hroots |- *.
        split; [ apply child_kind_ok_app; [ exact Ha | exact Hrcok ] |].
        intros k r0 Hk. destruct k as [|k'].
        + injection Hk as <-. exists arc.
          split; [ apply in_or_app; left; rewrite Haroot; left; reflexivity |].
          rewrite Haview. apply expr_view_kind.
        + cbn in Hk. destruct (Hroots k' r0 Hk) as [cc [Hcc Hcck]]. exists cc.
          split; [ apply in_or_app; right; exact Hcc | exact Hcck ]. }
    specialize (Hda args H 0 b1).
    destruct ((fix do_args (i bi : nat) (es : list Syntax.Expr) {struct es} := _) 0 b1 args)
      as [[ac bfin] aroots].
    destruct Hda as [Hacok Haroots]. cbn [fst snd] in Hacok, Haroots |- *.
    apply child_kind_ok_node.
    + cbn [c_children c_view]. intros k cp Hcp. destruct k as [|i].
      * injection Hcp as <-. exists hrc.
        split; [ right; apply in_or_app; left; rewrite Hhroot; left; reflexivity |].
        cbn [layout_kind]. rewrite Hhview. apply expr_view_kind.
      * cbn in Hcp. destruct (Haroots i cp Hcp) as [cc [Hcc Hcck]]. exists cc.
        split; [ right; apply in_or_app; right; exact Hcc |].
        cbn [layout_kind]. exact Hcck.
    + apply child_kind_ok_app; [ exact IHe | exact Hacok ].
Qed.

Lemma number_typeexpr_kind : forall par role b t, child_kind_ok (fst (number_typeexpr par role b t)).
Proof. intros; apply number_leaf_kind. Qed.
Lemma number_bindingname_kind : forall par role b bn, child_kind_ok (fst (number_bindingname par role b bn)).
Proof. intros; apply number_leaf_kind. Qed.
Lemma number_opttype_kind : forall self b ot, child_kind_ok (fst (fst (number_opttype (Some self) b ot))).
Proof.
  intros self b [t|]; cbn [number_opttype].
  - pose proof (number_typeexpr_kind (Some self) RTypeUse b t) as Hc.
    destruct (number_typeexpr (Some self) RTypeUse b t) as [c b']. cbn [fst snd] in Hc |- *. exact Hc.
  - intros pos c Hin; destruct Hin.
Qed.

Lemma number_constspec_kind : forall par role b cs, child_kind_ok (fst (number_constspec par role b cs)).
Proof.
  intros par role b cs. unfold number_constspec.
  assert (Hnroot : forall bb x, exists cell rest,
            fst (number_bindingname (Some b) (RSpecName ConstSpecF) bb x) = (bb, cell) :: rest
            /\ kind_of_view (c_view cell) = BindingNameKind).
  { intros bb x. destruct (number_bindingname_view (Some b) (RSpecName ConstSpecF) bb x)
      as [cell [rest [Hf [_ Hv]]]].
    exists cell, rest. split; [ exact Hf | rewrite Hv; reflexivity ]. }
  pose proof (number_list_roots (number_bindingname (Some b) (RSpecName ConstSpecF))
                (fun cell => kind_of_view (c_view cell) = BindingNameKind)
                (fun bb x => number_bindingname_spans (Some b) (RSpecName ConstSpecF) bb x)
                Hnroot (Collections.ne_to_list (Syntax.const_names cs)) (S b)) as Hnr.
  pose proof (number_list_kind (number_bindingname (Some b) (RSpecName ConstSpecF))
                (fun bb x => number_bindingname_kind (Some b) (RSpecName ConstSpecF) bb x)
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
    pose proof (number_opttype_kind b b1 ot) as Hol.
    pose proof (number_opttype_class ot (Some b) b1) as Hocls.
    destruct (number_opttype (Some b) b1 ot) as [[oc b2] oroots].
    destruct Hor as [Holen [_ [_ [_ Honth]]]]. cbn [fst snd] in Hol, Hocls.
    assert (Hvroot : forall bb x, exists cell rest,
              fst (number_expr (Some b) RPlain bb x) = (bb, cell) :: rest
              /\ kind_of_view (c_view cell) = ExprKind).
    { intros bb x. destruct (number_expr_root x (Some b) RPlain bb) as [rest [rc [Hf [_ [Hv _]]]]].
      exists rc, rest. split; [ exact Hf | rewrite Hv; apply expr_view_kind ]. }
    pose proof (number_list_roots (number_expr (Some b) RPlain)
                  (fun cell => kind_of_view (c_view cell) = ExprKind)
                  (fun bb x => number_expr_spans x (Some b) RPlain bb)
                  Hvroot (Collections.ne_to_list vals) b2) as Hvr.
    pose proof (number_list_kind (number_expr (Some b) RPlain)
                  (fun bb x => number_expr_kind x (Some b) RPlain bb)
                  b2 (Collections.ne_to_list vals)) as Hvl.
    destruct (number_list (number_expr (Some b) RPlain) b2 (Collections.ne_to_list vals)) as [[vc b3] vroots].
    destruct Hvr as [Hvlen [_ [_ Hvnth]]]. cbn [fst snd] in Hvl.
    cbn [fst]. apply child_kind_ok_node.
    + cbn [c_children c_view]. rewrite Hsh. intros k cp Hcp.
      set (NN := List.length (Collections.ne_to_list (Syntax.const_names cs))) in *.
      destruct (Nat.lt_ge_cases k (length nroots)) as [Hk|Hk].
      * rewrite nth_error_app1 in Hcp by exact Hk.
        destruct (Hnnth k cp Hcp) as [cell [Hcell Hkind]].
        exists cell. split; [ right; apply in_or_app; left; exact Hcell |].
        rewrite Hkind. cbn [layout_kind].
        assert (Hlt : k <? NN = true) by (apply Nat.ltb_lt; rewrite <- Hnlen; exact Hk).
        rewrite Hlt. reflexivity.
      * rewrite nth_error_app2 in Hcp by exact Hk.
        destruct (Nat.lt_ge_cases (k - length nroots) (length oroots)) as [Hk2|Hk2].
        -- rewrite nth_error_app1 in Hcp by exact Hk2.
           destruct (Honth (k - length nroots) cp Hcp) as [cell [Hcell [Hrole _]]].
           exists cell. split; [ right; apply in_or_app; right; apply in_or_app; left; exact Hcell |].
           assert (Hkind : kind_of_view (c_view cell) = TypeExprKind).
           { pose proof Hocls as H. unfold class_ok in H. rewrite Forall_forall in H.
             specialize (H (cp, cell) Hcell).
             cbn in H. unfold rv_ok in H. rewrite Hrole in H. cbn in H. exact H. }
           rewrite Hkind. cbn [layout_kind].
           destruct ot as [t0|]; cbn in Holen; [| lia ].
           assert (Hke : k = NN) by (rewrite Holen in Hk2; rewrite Hnlen in Hk; lia).
           assert (Hltb : k <? NN = false) by (apply Nat.ltb_ge; lia).
           assert (Heqb : k =? NN = true) by (apply Nat.eqb_eq; exact Hke).
           rewrite Hltb, Heqb. reflexivity.
        -- rewrite nth_error_app2 in Hcp by exact Hk2.
           destruct (Hvnth (k - length nroots - length oroots) cp Hcp) as [cell [Hcell Hkind]].
           exists cell. split; [ right; apply in_or_app; right; apply in_or_app; right; exact Hcell |].
           rewrite Hkind. cbn [layout_kind].
           assert (Hltb : k <? NN = false) by (apply Nat.ltb_ge; rewrite <- Hnlen; lia).
           rewrite Hltb.
           destruct ot as [t0|]; cbn in Holen; [| reflexivity ].
           assert (Heqb : k =? NN = false) by (apply Nat.eqb_neq; rewrite <- Hnlen; lia).
           rewrite Heqb. cbn [andb]. reflexivity.
    + apply child_kind_ok_app; [ exact Hnl | apply child_kind_ok_app; [ exact Hol | exact Hvl ] ].
  - cbn [fst]. apply child_kind_ok_node.
    + cbn [c_children c_view].
      assert (Hsh : constspec_shape cs
                    = CSInherited (List.length (Collections.ne_to_list (Syntax.const_names cs))))
        by (unfold constspec_shape; rewrite E; reflexivity).
      rewrite Hsh. intros k cp Hcp. rewrite app_nil_r in Hcp.
      destruct (Hnnth k cp Hcp) as [cell [Hcell Hkind]].
      exists cell. split; [ right; rewrite app_nil_r; exact Hcell |].
      rewrite Hkind; reflexivity.
    + rewrite app_nil_r. exact Hnl.
Qed.

Lemma number_varspec_kind : forall par role b vs, child_kind_ok (fst (number_varspec par role b vs)).
Proof.
  intros par role b vs. unfold number_varspec.
  assert (Hnroot : forall bb x, exists cell rest,
            fst (number_bindingname (Some b) (RSpecName VarSpecF) bb x) = (bb, cell) :: rest
            /\ kind_of_view (c_view cell) = BindingNameKind).
  { intros bb x. destruct (number_bindingname_view (Some b) (RSpecName VarSpecF) bb x)
      as [cell [rest [Hf [_ Hv]]]].
    exists cell, rest. split; [ exact Hf | rewrite Hv; reflexivity ]. }
  pose proof (number_list_roots (number_bindingname (Some b) (RSpecName VarSpecF))
                (fun cell => kind_of_view (c_view cell) = BindingNameKind)
                (fun bb x => number_bindingname_spans (Some b) (RSpecName VarSpecF) bb x)
                Hnroot (Collections.ne_to_list (Syntax.var_names vs)) (S b)) as Hnr.
  pose proof (number_list_kind (number_bindingname (Some b) (RSpecName VarSpecF))
                (fun bb x => number_bindingname_kind (Some b) (RSpecName VarSpecF) bb x)
                (S b) (Collections.ne_to_list (Syntax.var_names vs))) as Hnl.
  destruct (number_list (number_bindingname (Some b) (RSpecName VarSpecF)) (S b)
             (Collections.ne_to_list (Syntax.var_names vs))) as [[nc b1] nroots].
  destruct Hnr as [Hnlen [_ [_ Hnnth]]]. cbn [fst snd] in Hnl.
  destruct (Syntax.var_init vs) as [t | ot vals] eqn:E.
  - assert (Hsh : varspec_shape vs
                  = VSTypeOnly (List.length (Collections.ne_to_list (Syntax.var_names vs))))
      by (unfold varspec_shape; rewrite E; reflexivity).
    pose proof (number_typeexpr_view (Some b) RTypeUse b1 t) as [tcell [trest [Htf [_ Htv]]]].
    pose proof (number_typeexpr_kind (Some b) RTypeUse b1 t) as Htl.
    destruct (number_typeexpr (Some b) RTypeUse b1 t) as [tc b2]. cbn [fst] in Htf, Htl.
    cbn [fst]. apply child_kind_ok_node.
    + cbn [c_children c_view]. rewrite Hsh. intros k cp Hcp.
      set (NN := List.length (Collections.ne_to_list (Syntax.var_names vs))) in *.
      destruct (Nat.lt_ge_cases k (length nroots)) as [Hk|Hk].
      * rewrite nth_error_app1 in Hcp by exact Hk.
        destruct (Hnnth k cp Hcp) as [cell [Hcell Hkind]].
        exists cell. split; [ right; apply in_or_app; left; exact Hcell |].
        rewrite Hkind. cbn [layout_kind].
        assert (Hlt : k <? NN = true) by (apply Nat.ltb_lt; rewrite <- Hnlen; exact Hk).
        rewrite Hlt. reflexivity.
      * rewrite nth_error_app2 in Hcp by exact Hk.
        destruct (k - length nroots) as [|k2] eqn:Hk2; [| destruct k2; discriminate Hcp ].
        injection Hcp as <-. exists tcell.
        split; [ right; apply in_or_app; right; rewrite Htf; left; reflexivity |].
        rewrite Htv. cbn [layout_kind].
        assert (Hltb : k <? NN = false) by (apply Nat.ltb_ge; rewrite <- Hnlen; exact Hk).
        rewrite Hltb. reflexivity.
    + apply child_kind_ok_app; [ exact Hnl | exact Htl ].
  - assert (Hsh : varspec_shape vs
                  = VSValues (match ot with Some _ => true | None => false end)
                             (List.length (Collections.ne_to_list (Syntax.var_names vs)))
                             (List.length (Collections.ne_to_list vals)))
      by (unfold varspec_shape; rewrite E; reflexivity).
    pose proof (number_opttype_roots b b1 ot) as Hor.
    pose proof (number_opttype_kind b b1 ot) as Hol.
    pose proof (number_opttype_class ot (Some b) b1) as Hocls.
    destruct (number_opttype (Some b) b1 ot) as [[oc b2] oroots].
    destruct Hor as [Holen [_ [_ [_ Honth]]]]. cbn [fst snd] in Hol, Hocls.
    assert (Hvroot : forall bb x, exists cell rest,
              fst (number_expr (Some b) RPlain bb x) = (bb, cell) :: rest
              /\ kind_of_view (c_view cell) = ExprKind).
    { intros bb x. destruct (number_expr_root x (Some b) RPlain bb) as [rest [rc [Hf [_ [Hv _]]]]].
      exists rc, rest. split; [ exact Hf | rewrite Hv; apply expr_view_kind ]. }
    pose proof (number_list_roots (number_expr (Some b) RPlain)
                  (fun cell => kind_of_view (c_view cell) = ExprKind)
                  (fun bb x => number_expr_spans x (Some b) RPlain bb)
                  Hvroot (Collections.ne_to_list vals) b2) as Hvr.
    pose proof (number_list_kind (number_expr (Some b) RPlain)
                  (fun bb x => number_expr_kind x (Some b) RPlain bb)
                  b2 (Collections.ne_to_list vals)) as Hvl.
    destruct (number_list (number_expr (Some b) RPlain) b2 (Collections.ne_to_list vals)) as [[vc b3] vroots].
    destruct Hvr as [Hvlen [_ [_ Hvnth]]]. cbn [fst snd] in Hvl.
    cbn [fst]. apply child_kind_ok_node.
    + cbn [c_children c_view]. rewrite Hsh. intros k cp Hcp.
      set (NN := List.length (Collections.ne_to_list (Syntax.var_names vs))) in *.
      destruct (Nat.lt_ge_cases k (length nroots)) as [Hk|Hk].
      * rewrite nth_error_app1 in Hcp by exact Hk.
        destruct (Hnnth k cp Hcp) as [cell [Hcell Hkind]].
        exists cell. split; [ right; apply in_or_app; left; exact Hcell |].
        rewrite Hkind. cbn [layout_kind].
        assert (Hlt : k <? NN = true) by (apply Nat.ltb_lt; rewrite <- Hnlen; exact Hk).
        rewrite Hlt. reflexivity.
      * rewrite nth_error_app2 in Hcp by exact Hk.
        destruct (Nat.lt_ge_cases (k - length nroots) (length oroots)) as [Hk2|Hk2].
        -- rewrite nth_error_app1 in Hcp by exact Hk2.
           destruct (Honth (k - length nroots) cp Hcp) as [cell [Hcell [Hrole _]]].
           exists cell. split; [ right; apply in_or_app; right; apply in_or_app; left; exact Hcell |].
           assert (Hkind : kind_of_view (c_view cell) = TypeExprKind).
           { pose proof Hocls as H. unfold class_ok in H. rewrite Forall_forall in H.
             specialize (H (cp, cell) Hcell).
             cbn in H. unfold rv_ok in H. rewrite Hrole in H. cbn in H. exact H. }
           rewrite Hkind. cbn [layout_kind].
           destruct ot as [t0|]; cbn in Holen; [| lia ].
           assert (Hke : k = NN) by (rewrite Holen in Hk2; rewrite Hnlen in Hk; lia).
           assert (Hltb : k <? NN = false) by (apply Nat.ltb_ge; lia).
           assert (Heqb : k =? NN = true) by (apply Nat.eqb_eq; exact Hke).
           rewrite Hltb, Heqb. reflexivity.
        -- rewrite nth_error_app2 in Hcp by exact Hk2.
           destruct (Hvnth (k - length nroots - length oroots) cp Hcp) as [cell [Hcell Hkind]].
           exists cell. split; [ right; apply in_or_app; right; apply in_or_app; right; exact Hcell |].
           rewrite Hkind. cbn [layout_kind].
           assert (Hltb : k <? NN = false) by (apply Nat.ltb_ge; rewrite <- Hnlen; lia).
           rewrite Hltb.
           destruct ot as [t0|]; cbn in Holen; [| reflexivity ].
           assert (Heqb : k =? NN = false) by (apply Nat.eqb_neq; rewrite <- Hnlen; lia).
           rewrite Heqb. cbn [andb]. reflexivity.
    + apply child_kind_ok_app; [ exact Hnl | apply child_kind_ok_app; [ exact Hol | exact Hvl ] ].
Qed.

Lemma number_typespec_kind : forall par role b ts, child_kind_ok (fst (number_typespec par role b ts)).
Proof.
  intros par role b ts. unfold number_typespec.
  destruct ts as [bn t|bn t];
    (cbn [number_bindingname number_leaf];
     pose proof (number_typeexpr_view (Some b) RTypeUse (S (S b)) t) as [tcell [trest [Htf [_ Htv]]]];
     pose proof (number_typeexpr_kind (Some b) RTypeUse (S (S b)) t) as Htl;
     destruct (number_typeexpr (Some b) RTypeUse (S (S b)) t) as [tc bfin]; cbn [fst] in Htf, Htl;
     cbn [fst app]; apply child_kind_ok_node;
     [ cbn [c_children c_view]; intros k cp Hcp;
       destruct k as [|[|k2]]; [| | destruct k2; discriminate Hcp ];
       [ injection Hcp as <-;
         eexists; split; [ right; left; reflexivity |];
         cbn [c_view]; reflexivity
       | injection Hcp as <-; exists tcell;
         split; [ right; right; rewrite Htf; left; reflexivity |];
         rewrite Htv; reflexivity ]
     | apply child_kind_ok_node;
       [ cbn [c_children]; intros k cp Hcp; destruct k; discriminate Hcp
       | exact Htl ] ]).
Qed.

Lemma number_decl_kind : forall par role b d, child_kind_ok (fst (number_decl par role b d)).
Proof.
  intros par role b d. unfold number_decl.
  destruct d as [cs|vs|ts].
  - assert (Hroot : forall bb x, exists cell rest,
              fst (number_constspec (Some b) RPlain bb x) = (bb, cell) :: rest
              /\ kind_of_view (c_view cell) = SpecKind ConstSpecF).
    { intros bb x. destruct (number_constspec_view (Some b) RPlain bb x) as [cell [rest [Hf [_ Hv]]]].
      exists cell, rest. split; [ exact Hf | rewrite Hv; reflexivity ]. }
    pose proof (number_list_roots (number_constspec (Some b) RPlain)
                  (fun cell => kind_of_view (c_view cell) = SpecKind ConstSpecF)
                  (fun bb x => number_constspec_span (Some b) RPlain bb x) Hroot cs (S b)) as Hr.
    pose proof (number_list_kind (number_constspec (Some b) RPlain)
                  (fun bb x => number_constspec_kind (Some b) RPlain bb x) (S b) cs) as Hl.
    destruct (number_list (number_constspec (Some b) RPlain) (S b) cs) as [[kc bfin] roots].
    destruct Hr as [_ [_ [_ Hnth]]]. cbn [fst snd] in Hl.
    cbn [fst]. apply child_kind_ok_node;
      [ cbn [c_children c_view decl_flavor]; intros k cp Hcp;
        destruct (Hnth k cp Hcp) as [cell [Hcell Hkind]];
        exists cell; split; [ right; exact Hcell |]; rewrite Hkind; reflexivity
      | exact Hl ].
  - assert (Hroot : forall bb x, exists cell rest,
              fst (number_varspec (Some b) RPlain bb x) = (bb, cell) :: rest
              /\ kind_of_view (c_view cell) = SpecKind VarSpecF).
    { intros bb x. destruct (number_varspec_view (Some b) RPlain bb x) as [cell [rest [Hf [_ Hv]]]].
      exists cell, rest. split; [ exact Hf | rewrite Hv; reflexivity ]. }
    pose proof (number_list_roots (number_varspec (Some b) RPlain)
                  (fun cell => kind_of_view (c_view cell) = SpecKind VarSpecF)
                  (fun bb x => number_varspec_span (Some b) RPlain bb x) Hroot vs (S b)) as Hr.
    pose proof (number_list_kind (number_varspec (Some b) RPlain)
                  (fun bb x => number_varspec_kind (Some b) RPlain bb x) (S b) vs) as Hl.
    destruct (number_list (number_varspec (Some b) RPlain) (S b) vs) as [[kc bfin] roots].
    destruct Hr as [_ [_ [_ Hnth]]]. cbn [fst snd] in Hl.
    cbn [fst]. apply child_kind_ok_node;
      [ cbn [c_children c_view decl_flavor]; intros k cp Hcp;
        destruct (Hnth k cp Hcp) as [cell [Hcell Hkind]];
        exists cell; split; [ right; exact Hcell |]; rewrite Hkind; reflexivity
      | exact Hl ].
  - assert (Hroot : forall bb x, exists cell rest,
              fst (number_typespec (Some b) RPlain bb x) = (bb, cell) :: rest
              /\ kind_of_view (c_view cell) = SpecKind TypeSpecF).
    { intros bb x. destruct (number_typespec_view (Some b) RPlain bb x) as [cell [rest [Hf [_ Hv]]]].
      exists cell, rest. split; [ exact Hf | rewrite Hv; reflexivity ]. }
    pose proof (number_list_roots (number_typespec (Some b) RPlain)
                  (fun cell => kind_of_view (c_view cell) = SpecKind TypeSpecF)
                  (fun bb x => number_typespec_span (Some b) RPlain bb x) Hroot ts (S b)) as Hr.
    pose proof (number_list_kind (number_typespec (Some b) RPlain)
                  (fun bb x => number_typespec_kind (Some b) RPlain bb x) (S b) ts) as Hl.
    destruct (number_list (number_typespec (Some b) RPlain) (S b) ts) as [[kc bfin] roots].
    destruct Hr as [_ [_ [_ Hnth]]]. cbn [fst snd] in Hl.
    cbn [fst]. apply child_kind_ok_node;
      [ cbn [c_children c_view decl_flavor]; intros k cp Hcp;
        destruct (Hnth k cp Hcp) as [cell [Hcell Hkind]];
        exists cell; split; [ right; exact Hcell |]; rewrite Hkind; reflexivity
      | exact Hl ].
Qed.

Lemma number_stmt_kind : forall par role b s, child_kind_ok (fst (number_stmt par role b s)).
Proof.
  intros par role b s. unfold number_stmt.
  destruct s as [e|d|names vals].
  - pose proof (number_expr_root e (Some b) RExprStatementExpr (S b)) as [erest [erc [Heroot [_ [Heview _]]]]].
    pose proof (number_expr_kind e (Some b) RExprStatementExpr (S b)) as Hel.
    destruct (number_expr (Some b) RExprStatementExpr (S b) e) as [c b']. cbn [fst] in Heroot, Hel.
    cbn [fst]. apply child_kind_ok_node;
      [ cbn [c_children c_view]; intros k cp Hcp;
        destruct k as [|k']; [| destruct k'; discriminate Hcp ];
        injection Hcp as <-; exists erc;
        split; [ right; rewrite Heroot; left; reflexivity |];
        rewrite Heview; apply expr_view_kind
      | exact Hel ].
  - pose proof (number_decl_view (Some b) RPlain (S b) d) as [dcell [drest [Hdf [_ Hdv]]]].
    pose proof (number_decl_kind (Some b) RPlain (S b) d) as Hdl.
    destruct (number_decl (Some b) RPlain (S b) d) as [c b']. cbn [fst] in Hdf, Hdl.
    cbn [fst]. apply child_kind_ok_node;
      [ cbn [c_children c_view]; intros k cp Hcp;
        destruct k as [|k']; [| destruct k'; discriminate Hcp ];
        injection Hcp as <-; exists dcell;
        split; [ right; rewrite Hdf; left; reflexivity |];
        cbn [stmt_shape]; rewrite Hdv; reflexivity
      | exact Hdl ].
  - assert (Hnroot : forall bb x, exists cell rest,
              fst (number_bindingname (Some b) RShortLhs bb x) = (bb, cell) :: rest
              /\ kind_of_view (c_view cell) = BindingNameKind).
    { intros bb x. destruct (number_bindingname_view (Some b) RShortLhs bb x) as [cell [rest [Hf [_ Hv]]]].
      exists cell, rest. split; [ exact Hf | rewrite Hv; reflexivity ]. }
    pose proof (number_list_roots (number_bindingname (Some b) RShortLhs)
                  (fun cell => kind_of_view (c_view cell) = BindingNameKind)
                  (fun bb x => number_bindingname_spans (Some b) RShortLhs bb x)
                  Hnroot (Collections.ne_to_list names) (S b)) as Hnr.
    pose proof (number_list_kind (number_bindingname (Some b) RShortLhs)
                  (fun bb x => number_bindingname_kind (Some b) RShortLhs bb x)
                  (S b) (Collections.ne_to_list names)) as Hnl.
    destruct (number_list (number_bindingname (Some b) RShortLhs) (S b) (Collections.ne_to_list names))
      as [[nc b1] nroots].
    destruct Hnr as [Hnlen [_ [_ Hnnth]]]. cbn [fst snd] in Hnl.
    assert (Hvroot : forall bb x, exists cell rest,
              fst (number_expr (Some b) RPlain bb x) = (bb, cell) :: rest
              /\ kind_of_view (c_view cell) = ExprKind).
    { intros bb x. destruct (number_expr_root x (Some b) RPlain bb) as [rest [rc [Hf [_ [Hv _]]]]].
      exists rc, rest. split; [ exact Hf | rewrite Hv; apply expr_view_kind ]. }
    pose proof (number_list_roots (number_expr (Some b) RPlain)
                  (fun cell => kind_of_view (c_view cell) = ExprKind)
                  (fun bb x => number_expr_spans x (Some b) RPlain bb)
                  Hvroot (Collections.ne_to_list vals) b1) as Hvr.
    pose proof (number_list_kind (number_expr (Some b) RPlain)
                  (fun bb x => number_expr_kind x (Some b) RPlain bb)
                  b1 (Collections.ne_to_list vals)) as Hvl.
    destruct (number_list (number_expr (Some b) RPlain) b1 (Collections.ne_to_list vals)) as [[vc b2] vroots].
    destruct Hvr as [_ [_ [_ Hvnth]]]. cbn [fst snd] in Hvl.
    cbn [fst]. apply child_kind_ok_node.
    + cbn [c_children c_view]. unfold stmt_shape. intros k cp Hcp.
      set (NN := List.length (Collections.ne_to_list names)) in *.
      destruct (Nat.lt_ge_cases k (length nroots)) as [Hk|Hk].
      * rewrite nth_error_app1 in Hcp by exact Hk.
        destruct (Hnnth k cp Hcp) as [cell [Hcell Hkind]].
        exists cell. split; [ right; apply in_or_app; left; exact Hcell |].
        rewrite Hkind. cbn [layout_kind].
        assert (Hlt : k <? NN = true) by (apply Nat.ltb_lt; rewrite <- Hnlen; exact Hk).
        rewrite Hlt. reflexivity.
      * rewrite nth_error_app2 in Hcp by exact Hk.
        destruct (Hvnth (k - length nroots) cp Hcp) as [cell [Hcell Hkind]].
        exists cell. split; [ right; apply in_or_app; right; exact Hcell |].
        rewrite Hkind. cbn [layout_kind].
        assert (Hltb : k <? NN = false) by (apply Nat.ltb_ge; rewrite <- Hnlen; exact Hk).
        rewrite Hltb. reflexivity.
    + apply child_kind_ok_app; [ exact Hnl | exact Hvl ].
Qed.

Lemma number_block_kind : forall par role b blk, child_kind_ok (fst (number_block par role b blk)).
Proof.
  intros par role b [stmts]. unfold number_block.
  assert (Hroot : forall bb x, exists cell rest,
            fst (number_stmt (Some b) RPlain bb x) = (bb, cell) :: rest
            /\ kind_of_view (c_view cell) = StmtKind).
  { intros bb x. destruct (number_stmt_view (Some b) RPlain bb x) as [cell [rest [Hf [_ Hv]]]].
    exists cell, rest. split; [ exact Hf | rewrite Hv; reflexivity ]. }
  pose proof (number_list_roots (number_stmt (Some b) RPlain)
                (fun cell => kind_of_view (c_view cell) = StmtKind)
                (fun bb x => number_stmt_span (Some b) RPlain bb x) Hroot stmts (S b)) as Hr.
  pose proof (number_list_kind (number_stmt (Some b) RPlain)
                (fun bb x => number_stmt_kind (Some b) RPlain bb x) (S b) stmts) as Hl.
  destruct (number_list (number_stmt (Some b) RPlain) (S b) stmts) as [[kc bfin] roots].
  destruct Hr as [_ [_ [_ Hnth]]]. cbn [fst snd] in Hl.
  cbn [fst]. apply child_kind_ok_node;
    [ cbn [c_children c_view]; intros k cp Hcp;
      destruct (Hnth k cp Hcp) as [cell [Hcell Hkind]];
      exists cell; split; [ right; exact Hcell |]; rewrite Hkind; reflexivity
    | exact Hl ].
Qed.

Lemma number_toplevel_kind : forall par role b td, child_kind_ok (fst (number_toplevel par role b td)).
Proof.
  intros par role b td. unfold number_toplevel.
  destruct td as [d|blk].
  - pose proof (number_decl_view (Some b) RPlain (S b) d) as [dcell [drest [Hdf [_ Hdv]]]].
    pose proof (number_decl_kind (Some b) RPlain (S b) d) as Hdl.
    destruct (number_decl (Some b) RPlain (S b) d) as [c b']. cbn [fst] in Hdf, Hdl.
    cbn [fst]. apply child_kind_ok_node;
      [ cbn [c_children c_view]; intros k cp Hcp;
        destruct k as [|k']; [| destruct k'; discriminate Hcp ];
        injection Hcp as <-; exists dcell;
        split; [ right; rewrite Hdf; left; reflexivity |];
        cbn [top_shape]; rewrite Hdv; reflexivity
      | exact Hdl ].
  - pose proof (number_block_view (Some b) RPlain (S b) blk) as [bcell [brest [Hbf [_ Hbv]]]].
    pose proof (number_block_kind (Some b) RPlain (S b) blk) as Hbl.
    destruct (number_block (Some b) RPlain (S b) blk) as [c b']. cbn [fst] in Hbf, Hbl.
    cbn [fst]. apply child_kind_ok_node;
      [ cbn [c_children c_view]; intros k cp Hcp;
        destruct k as [|k']; [| destruct k'; discriminate Hcp ];
        injection Hcp as <-; exists bcell;
        split; [ right; rewrite Hbf; left; reflexivity |];
        cbn [top_shape]; rewrite Hbv; reflexivity
      | exact Hbl ].
Qed.

Lemma number_file_kind : forall f, child_kind_ok (number_file f).
Proof.
  intro f. unfold number_file.
  assert (Hroot : forall bb x, exists cell rest,
            fst (number_toplevel (Some 0) RPlain bb x) = (bb, cell) :: rest
            /\ kind_of_view (c_view cell) = TopKind).
  { intros bb x. destruct (number_toplevel_view (Some 0) RPlain bb x) as [cell [rest [Hf [_ Hv]]]].
    exists cell, rest. split; [ exact Hf | rewrite Hv; reflexivity ]. }
  pose proof (number_list_roots (number_toplevel (Some 0) RPlain)
                (fun cell => kind_of_view (c_view cell) = TopKind)
                (fun bb x => number_toplevel_span (Some 0) RPlain bb x) Hroot (Syntax.declarations f) 1) as Hr.
  pose proof (number_list_kind (number_toplevel (Some 0) RPlain)
                (fun bb x => number_toplevel_kind (Some 0) RPlain bb x) 1 (Syntax.declarations f)) as Hl.
  destruct (number_list (number_toplevel (Some 0) RPlain) 1 (Syntax.declarations f)) as [[dc bfin] droots].
  destruct Hr as [_ [_ [_ Hnth]]]. cbn [fst snd] in Hl.
  apply child_kind_ok_node;
    [ cbn [c_children c_view]; intros k cp Hcp;
      destruct (Hnth k cp Hcp) as [cell [Hcell Hkind]];
      exists cell; split; [ right; exact Hcell |]; rewrite Hkind; reflexivity
    | exact Hl ].
Qed.
