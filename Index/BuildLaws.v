(* Index.BuildLaws — the laws of the one canonical numbering/build: spans, roots, coverage, layout, shape. *)
From Stdlib Require Import List Bool Arith PeanoNat Lia Eqdep_dec PArith FSets.FMapFacts.
From Fido Require Import Collections Syntax Index.Model Index.Build.
Import ListNotations.

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
