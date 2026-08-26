(* Index — the canonical indexed occurrence authority: ProgramIndex, FileRef/NodeRef, generic parent/child. *)
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

(* strict structural progress: a parent edge points strictly earlier — the parent's position precedes the child's *)
Lemma node_parent_pos_lt {p} {idx : ProgramIndex p} (r par : NodeRef idx) :
  node_parent r = Some par -> nr_pos par < nr_pos r.
Proof.
  intro Hpar.
  destruct (c_parent (occ_at r)) as [pp|] eqn:Hcp;
    [ | apply node_parent_none in Hcp; rewrite Hcp in Hpar; discriminate ].
  destruct (node_parent_some r pp Hcp) as [pc [Hpc [Hpos _]]].
  rewrite Hpar in Hpc. injection Hpc as Heq. subst pc.
  destruct (occ_in_number_file r) as [f [Hin _]].
  destruct (number_file_pbounds f (nr_pos r) (occ_at r) Hin pp Hcp) as [_ Hlt].
  rewrite Hpos. exact Hlt.
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


(* FileRef construction, equality, and canonical file enumeration — the exact file-level Core authority *)
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

(* every node's position is in range on its own file *)
Lemma nr_pos_lt {p} {idx : ProgramIndex p} (r : NodeRef idx) :
  nr_pos r < occ_count (nr_file r).
Proof.
  destruct (occ_in_number_file r) as [f [Hin Hcount]].
  destruct (BuildLaws.number_file_positions f) as [n Hpos].
  assert (Hinp : In (nr_pos r) (map fst (Build.number_file f)))
    by (apply in_map_iff; exists (nr_pos r, occ_at r); split; [ reflexivity | exact Hin ]).
  rewrite Hpos in Hinp. apply in_seq in Hinp.
  assert (Hlen : length (Build.number_file f) = n).
  { apply (f_equal (@length nat)) in Hpos.
    rewrite length_map, length_seq in Hpos. exact Hpos. }
  lia.
Qed.

(* the file enumeration is duplicate-free: one file per retained path key *)
Lemma files_emit_paths_nodup {p} {idx : ProgramIndex p} :
  forall l : list (FilePath.T * Build.FileInfo),
  NoDup (map fst l) ->
  NoDup (map fr_path
           (flat_map (fun kv => match mk_fileref idx (fst kv) with
                                | Some fr => [fr] | None => [] end) l)).
Proof.
  induction l as [|kv rest IH]; intro Hk; [ constructor |].
  cbn [map] in Hk. apply NoDup_cons_iff in Hk. destruct Hk as [Hnotin Hk'].
  specialize (IH Hk'). cbn [flat_map].
  destruct (mk_fileref idx (fst kv)) as [fr|] eqn:Hmk; [| cbn [app]; exact IH ].
  cbn [app map]. constructor; [| exact IH ].
  intro Hin. apply Hnotin.
  rewrite (mk_fileref_path idx (fst kv) fr Hmk) in Hin.
  clear -Hin. induction rest as [|kv' rest' IH']; [ destruct Hin |].
  cbn [flat_map] in Hin. cbn [map].
  destruct (mk_fileref idx (fst kv')) as [fr'|] eqn:Hmk'.
  - cbn [app map] in Hin. destruct Hin as [He|Hin];
      [ left; rewrite <- (mk_fileref_path idx (fst kv') fr' Hmk'); exact He
      | right; exact (IH' Hin) ].
  - cbn [app] in Hin. right. exact (IH' Hin).
Qed.

Lemma all_files_paths_nodup {p} {idx : ProgramIndex p} :
  NoDup (map fr_path (all_files idx)).
Proof.
  exact (files_emit_paths_nodup (Collections.FileMap.elements (prog_map idx))
           (Collections.file_map_elements_keys_nodup (prog_map idx))).
Qed.

Lemma all_files_nodup {p} {idx : ProgramIndex p} : NoDup (all_files idx).
Proof. exact (NoDup_map_inv _ _ all_files_paths_nodup). Qed.
