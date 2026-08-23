(* Index.Core — the canonical indexed occurrence authority: ProgramIndex, FileRef/NodeRef, generic parent/child. *)
From Stdlib Require Import List Bool Arith PeanoNat Lia Eqdep_dec PArith FSets.FMapFacts.
From Fido Require Import FilePath Collections Syntax Index.Model Index.Build Index.BuildLaws.
Import ListNotations.

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

