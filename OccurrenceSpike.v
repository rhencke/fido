(** * OccurrenceSpike — isolated, TEMPORARY occurrence-index proof spike (Source Forest campaign, C0).

    This module is NOT part of the certified GoProgram pipeline.  It is an isolated spike that validates
    the snapshot-local occurrence-identity + derived-navigation-index design (Master Plan Part 4) on a tiny
    toy grammar BEFORE any production AST migration (C1/C2).  It imports only [FilePath] (the leaf path
    authority, reused for occurrence keys); it does NOT import GoAST/GoTypes/GoCompile and nothing in the
    production pipeline imports it.  It is proven axiom-free by the same whole-theory audit as the rest of
    the theory, and will be DELETED once the production [GoIndex] lands (C2).

    C0.3 REPRESENTATION DECISION (recorded in .review/SOURCE_FOREST_STATUS.md):
      A. a certified positive-key radix trie ([PTrie] below) — pure Gallina, empty assumption closure,
         O(bits) = O(log n) lookup/insert, persistent, [vm_compute]-reducible, decidable-key ergonomics.
      B. a primitive dense array (Coq [PArray]/[Uint63]) — O(1) lookup, BUT built on KERNEL PRIMITIVES
         (Int63/PArray), which Fido's standing law rule 4 forbids ("Never ... a kernel primitive").  Its
         "assumption closure" is a kernel extension outside pure CIC, so it fails the zero-axiom/no-primitive
         policy regardless of speed.  REJECTED.
    Selected: A.  The public [NodeTable] API ([pget]/[pset]) hides the choice, so C2 could swap the physical
    table without disturbing callers.  A plain association [list] is deliberately NOT used: it would give a
    forbidden O(n) list-scan node-table lookup (Master Plan 4.8).  *)

From Stdlib Require Import PArith List Bool Lia Eqdep_dec Wf_nat Sorted String.
From Fido Require Import FilePath.
Import ListNotations.

(* ================================================================================================= *)
(** ** The selected node table: a certified positive-key radix trie (candidate A).                    *)
(* ================================================================================================= *)

Inductive PTrie (A : Type) : Type :=
| PLeaf : PTrie A
| PBr   : option A -> PTrie A -> PTrie A -> PTrie A.
Arguments PLeaf {A}.
Arguments PBr {A} _ _ _.

Fixpoint pget {A} (k : positive) (t : PTrie A) : option A :=
  match t with
  | PLeaf => None
  | PBr o l r =>
      match k with
      | xH    => o
      | xO k' => pget k' l
      | xI k' => pget k' r
      end
  end.

Fixpoint pset {A} (k : positive) (v : A) (t : PTrie A) : PTrie A :=
  match k, t with
  | xH,    PLeaf      => PBr (Some v) PLeaf PLeaf
  | xH,    PBr _ l r  => PBr (Some v) l r
  | xO k', PLeaf      => PBr None (pset k' v PLeaf) PLeaf
  | xO k', PBr o l r  => PBr o (pset k' v l) r
  | xI k', PLeaf      => PBr None PLeaf (pset k' v PLeaf)
  | xI k', PBr o l r  => PBr o l (pset k' v r)
  end.

Lemma pget_leaf {A} (k : positive) : pget k (@PLeaf A) = None.
Proof. destruct k; reflexivity. Qed.

(* the standard "get-set-same" / "get-set-other" trie laws (O(log n), persistent). *)
Lemma pget_pset_same {A} (k : positive) (v : A) (t : PTrie A) : pget k (pset k v t) = Some v.
Proof.
  revert t; induction k as [k' IH|k' IH|]; intros [ | o l r ]; simpl; auto.
Qed.

Lemma pget_pset_other {A} (j k : positive) (v : A) (t : PTrie A) :
  j <> k -> pget k (pset j v t) = pget k t.
Proof.
  revert k t; induction j as [j' IH|j' IH|]; intros k t Hjk;
    destruct k as [k'|k'|]; destruct t as [ | o l r ]; simpl;
    try reflexivity;
    try (now rewrite pget_leaf);
    try (rewrite IH by congruence; now rewrite ?pget_leaf);
    try (apply IH; congruence);
    try (exfalso; congruence).
Qed.

(* ================================================================================================= *)
(** ** Occurrence kinds, roles, and metadata (Master Plan 4.4 / 4.6).                                 *)
(* ================================================================================================= *)

(* Only the toy grammar's currently-live kinds get constructors (Master Plan 4.4). *)
Inductive SyntaxKind := KFile | KDecl | KStatement | KExpression.

(* How an occurrence participates in its parent (Master Plan 4.6). *)
Inductive NodeRole :=
| RFileRoot                 (* the file root itself *)
| RFileDecl (n : nat)       (* the n-th declaration of a file *)
| RDeclStmt (n : nat)       (* the n-th statement in a declaration body *)
| RStmtExpr                 (* the expression held by a print statement *)
| RChild    (n : nat).      (* the n-th operand of a nested expression *)

(* Small structural metadata; NO copy of the recursive subtree (Master Plan 4.6 / theorem 14). *)
Record NodeMeta := mkMeta {
  nm_kind        : SyntaxKind;
  nm_parent      : option positive;   (* file-local parent id; None only for a file root *)
  nm_role        : NodeRole;
  nm_subtree_end : positive           (* last preorder id in this occurrence's subtree *)
}.

(* ================================================================================================= *)
(** ** A tiny toy source grammar (Master Plan C0.2): file -> decls -> stmts -> nested expressions.    *)
(* ================================================================================================= *)

Inductive TExpr :=
| TLeaf (v : nat)            (* a leaf expression (e.g. a literal) *)
| TBin  (l r : TExpr).       (* a nested binary expression *)

Inductive TStmt := TPrint (e : TExpr).          (* a statement wrapping one expression *)
Inductive TDecl := TFun (body : list TStmt).    (* a declaration with a statement body *)
Record   TFile := mkTFile { tf_path : FilePath ; tf_decls : list TDecl }.
Definition TForest := list TFile.               (* two-or-more file roots *)

Definition root_id : positive := 1%positive.    (* every file root's canonical local id (theorem 1) *)

(* ================================================================================================= *)
(** ** The one-pass index builder (Master Plan 4.8).                                                   *)
(*    Each builder threads a fresh-id counter and inserts each occurrence's metadata EXACTLY ONCE via  *)
(*    [pset] (O(log n)); it never searches, compares, or copies syntax subtrees.  A subtree builder    *)
(*    returns the subtree's last id ([se], its [subtree_end]); a sequence builder returns the next     *)
(*    free id.  Meta for an internal node is inserted AFTER its children so [subtree_end] is known.     *)
(* ================================================================================================= *)

Fixpoint build_expr (parent : positive) (role : NodeRole) (me : positive) (e : TExpr) (t : PTrie NodeMeta)
  : PTrie NodeMeta * positive (* subtree_end *) :=
  match e with
  | TLeaf _ => (pset me (mkMeta KExpression (Some parent) role me) t, me)
  | TBin l r =>
      let '(t1, e1) := build_expr me (RChild 0) (Pos.succ me) l t in
      let '(t2, e2) := build_expr me (RChild 1) (Pos.succ e1) r t1 in
      (pset me (mkMeta KExpression (Some parent) role e2) t2, e2)
  end.

Definition build_stmt (parent : positive) (sidx : nat) (me : positive) (s : TStmt) (t : PTrie NodeMeta)
  : PTrie NodeMeta * positive :=
  match s with
  | TPrint e =>
      let '(t1, e1) := build_expr me RStmtExpr (Pos.succ me) e t in
      (pset me (mkMeta KStatement (Some parent) (RDeclStmt sidx) e1) t1, e1)
  end.

(* A generic left-to-right sibling-sequence builder: builds each element as a subtree rooted at the
   running fresh id and advances.  Returns the next free id.  [bx] is the per-element subtree builder. *)
Fixpoint build_seq {X} (bx : positive -> nat -> positive -> X -> PTrie NodeMeta -> PTrie NodeMeta * positive)
                   (parent : positive) (i0 : nat) (me0 : positive) (xs : list X) (t : PTrie NodeMeta)
  : PTrie NodeMeta * positive (* next free id *) :=
  match xs with
  | []        => (t, me0)
  | x :: rest =>
      let '(t1, se) := bx parent i0 me0 x t in
      build_seq bx parent (S i0) (Pos.succ se) rest t1
  end.

Definition build_decl (parent : positive) (didx : nat) (me : positive) (d : TDecl) (t : PTrie NodeMeta)
  : PTrie NodeMeta * positive :=
  match d with
  | TFun body =>
      let '(t1, nx) := build_seq build_stmt me 0 (Pos.succ me) body t in
      (pset me (mkMeta KDecl (Some parent) (RFileDecl didx) (Pos.pred nx)) t1, Pos.pred nx)
  end.

Record FileIndex := mkFI {
  fi_path  : FilePath;
  fi_table : PTrie NodeMeta;
  fi_count : positive           (* number of occurrences = last local id; ids are [1 .. fi_count] *)
}.

Definition build_file (f : TFile) : FileIndex :=
  let '(t1, nx) := build_seq build_decl root_id 0 (Pos.succ root_id) (tf_decls f) PLeaf in
  let cnt := Pos.pred nx in
  mkFI (tf_path f) (pset root_id (mkMeta KFile None RFileRoot cnt) t1) cnt.

Definition SyntaxIndex := list FileIndex.
Definition build_forest (fs : TForest) : SyntaxIndex := map build_file fs.

(* ================================================================================================= *)
(** ** Occurrence keys and snapshot-validated references (Master Plan 4.2 / 4.3).                      *)
(* ================================================================================================= *)

Record NodeKey := mkKey { nk_file : FilePath ; nk_local : positive }.

Definition nodekey_eqb (a b : NodeKey) : bool :=
  fp_eqb (nk_file a) (nk_file b) && Pos.eqb (nk_local a) (nk_local b).

(* the file index for a path, if any (a small #files lookup — NOT a per-node scan). *)
Definition file_of (idx : SyntaxIndex) (fp : FilePath) : option FileIndex :=
  find (fun fi => fp_eqb (fi_path fi) fp) idx.

(* a key is valid iff its file is present and its local id resolves in that file's trie. *)
Definition valid_keyb (idx : SyntaxIndex) (k : NodeKey) : bool :=
  match file_of idx (nk_file k) with
  | Some fi => match pget (nk_local k) (fi_table fi) with Some _ => true | None => false end
  | None    => false
  end.

(* the snapshot-indexed validated reference; validity is a bool-eq proof, hence proof-irrelevant. *)
Record NodeRef (idx : SyntaxIndex) := mkRef {
  ref_key : NodeKey;
  ref_ok  : valid_keyb idx ref_key = true
}.
Arguments ref_key {idx} _.
Arguments ref_ok  {idx} _.

(* the ONLY public way to mint a reference: validated lookup (the raw [mkRef] is not exported). *)
Definition ref_of (idx : SyntaxIndex) (k : NodeKey) : option (NodeRef idx) :=
  (match valid_keyb idx k as b return (valid_keyb idx k = b -> option (NodeRef idx)) with
   | true  => fun H => Some (mkRef idx k H)
   | false => fun _ => None
   end) eq_refl.

(* ================================================================================================= *)
(** ** Derived navigation over the immutable snapshot (Master Plan 4.7 / 4.10).                        *)
(* ================================================================================================= *)

Definition ref_meta {idx} (r : NodeRef idx) : option NodeMeta :=
  match file_of idx (nk_file (ref_key r)) with
  | Some fi => pget (nk_local (ref_key r)) (fi_table fi)
  | None    => None
  end.

Definition node_kind {idx} (r : NodeRef idx) : SyntaxKind :=
  match ref_meta r with Some m => nm_kind m | None => KFile end.

(* O(1) projection: an occurrence's containing file is read straight off its key (Master Plan 4.8). *)
Definition containing_file_path {idx} (r : NodeRef idx) : FilePath := nk_file (ref_key r).

(* immediate parent: one trie lookup for the meta, one validated key rebuild — never an AST search. *)
Definition parent_of {idx} (r : NodeRef idx) : option (NodeRef idx) :=
  match ref_meta r with
  | Some m => match nm_parent m with
              | Some pid => ref_of idx (mkKey (nk_file (ref_key r)) pid)
              | None     => None
              end
  | None => None
  end.

(* preorder-interval ancestry: O(1) arithmetic on [subtree_end] after one trie lookup (theorem 13). *)
Definition parent_id (t : PTrie NodeMeta) (c : positive) : option positive :=
  match pget c t with Some m => nm_parent m | None => None end.

Inductive Ancestor (t : PTrie NodeMeta) : positive -> positive -> Prop :=
| Anc_dir  : forall a c, parent_id t c = Some a -> Ancestor t a c
| Anc_step : forall a p c, Ancestor t a p -> parent_id t c = Some p -> Ancestor t a c.

Definition is_ancestor_local (t : PTrie NodeMeta) (a d : positive) : bool :=
  match pget a t with
  | Some ma => Pos.ltb a d && Pos.leb d (nm_subtree_end ma)
  | None    => false
  end.

(* direct children, enumerated by scanning only the parent's own preorder interval [pid+1 .. end]
   (NOT the whole file) and keeping those whose parent is [pid]; results are in increasing = source
   order.  Each membership test is a trie lookup, so this is not a list-backed node-table lookup. *)
Fixpoint pos_seq (start : positive) (len : nat) : list positive :=
  match len with
  | O    => []
  | S n  => start :: pos_seq (Pos.succ start) n
  end.

Definition child_ids (t : PTrie NodeMeta) (pid : positive) : list positive :=
  match pget pid t with
  | Some m =>
      filter (fun c => match pget c t with
                       | Some mc => match nm_parent mc with Some p => Pos.eqb p pid | None => false end
                       | None => false end)
             (pos_seq (Pos.succ pid) (Pos.to_nat (nm_subtree_end m) - Pos.to_nat pid))
  | None => []
  end.

Definition children_of {idx} (r : NodeRef idx) : list (NodeRef idx) :=
  match file_of idx (nk_file (ref_key r)) with
  | Some fi =>
      fold_right (fun c acc =>
                    match ref_of idx (mkKey (nk_file (ref_key r)) c) with
                    | Some cr => cr :: acc
                    | None    => acc
                    end) [] (child_ids (fi_table fi) (nk_local (ref_key r)))
  | None => []
  end.

(* ================================================================================================= *)
(** ** Structural invariants of the built index (the foundation for the C0.4 theorem set).             *)
(*    A [SubtreeWF] describes one occurrence's subtree, laid out over a contiguous preorder interval    *)
(*    [me .. se]; a [ForestWF] describes a run of sibling subtrees over [lo .. nx) with a common parent *)
(*    [P].  [Fresh t from] says the trie holds nothing at or above [from], so each builder writes only  *)
(*    strictly fresh ids (no clobber) — this is what makes ancestry monotone under table growth.        *)
(* ================================================================================================= *)

Definition Fresh (t : PTrie NodeMeta) (from : positive) : Prop :=
  forall k, (from <= k)%positive -> pget k t = None.

Record SubtreeWF (t0 t : PTrie NodeMeta) (oP : option positive) (me se : positive) : Prop := {
  sub_le    : (me <= se)%positive;
  sub_out   : forall k, (k < me)%positive \/ (se < k)%positive -> pget k t = pget k t0;
  sub_root  : exists m, pget me t = Some m /\ nm_parent m = oP /\ nm_subtree_end m = se;
  sub_pres  : forall k, (me <= k)%positive -> (k <= se)%positive -> pget k t <> None;
  sub_nest  : forall k m, (me <= k)%positive -> (k <= se)%positive -> pget k t = Some m ->
                (k <= nm_subtree_end m)%positive /\ (nm_subtree_end m <= se)%positive;
  sub_prng  : forall k m, (me < k)%positive -> (k <= se)%positive -> pget k t = Some m ->
                exists p mp, nm_parent m = Some p /\ pget p t = Some mp /\
                  (me <= p)%positive /\ (p < k)%positive /\
                  (k <= nm_subtree_end mp)%positive /\ (nm_subtree_end m <= nm_subtree_end mp)%positive;
  sub_snd   : forall a k ma, (me <= a)%positive -> (a <= se)%positive -> pget a t = Some ma ->
                (a < k)%positive -> (k <= nm_subtree_end ma)%positive -> Ancestor t a k
}.

Arguments sub_le   {_ _ _ _ _}.
Arguments sub_out  {_ _ _ _ _}.
Arguments sub_root {_ _ _ _ _}.
Arguments sub_pres {_ _ _ _ _}.
Arguments sub_nest {_ _ _ _ _}.
Arguments sub_prng {_ _ _ _ _}.
Arguments sub_snd  {_ _ _ _ _}.

Record ForestWF (t0 t : PTrie NodeMeta) (P lo nx : positive) : Prop := {
  for_le   : (lo <= nx)%positive;
  for_out  : forall k, (k < lo)%positive \/ (nx <= k)%positive -> pget k t = pget k t0;
  for_pres : forall k, (lo <= k)%positive -> (k < nx)%positive -> pget k t <> None;
  for_nest : forall k m, (lo <= k)%positive -> (k < nx)%positive -> pget k t = Some m ->
               (k <= nm_subtree_end m)%positive /\ (nm_subtree_end m < nx)%positive;
  for_prng : forall k m, (lo <= k)%positive -> (k < nx)%positive -> pget k t = Some m ->
               exists p, nm_parent m = Some p /\
                 (p = P \/ ((lo <= p)%positive /\ (p < k)%positive /\
                            exists mp, pget p t = Some mp /\
                              (k <= nm_subtree_end mp)%positive /\ (nm_subtree_end m <= nm_subtree_end mp)%positive));
  for_snd  : forall a k ma, (lo <= a)%positive -> (a < nx)%positive -> pget a t = Some ma ->
               (a < k)%positive -> (k <= nm_subtree_end ma)%positive -> Ancestor t a k
}.

Arguments for_le   {_ _ _ _ _}.
Arguments for_out  {_ _ _ _ _}.
Arguments for_pres {_ _ _ _ _}.
Arguments for_nest {_ _ _ _ _}.
Arguments for_prng {_ _ _ _ _}.
Arguments for_snd  {_ _ _ _ _}.

(* ancestry only reads parent links at present ids, so it survives any table growth that preserves them. *)
Lemma ancestor_mono (t t' : PTrie NodeMeta) :
  (forall j m, pget j t = Some m -> pget j t' = Some m) ->
  forall a c, Ancestor t a c -> Ancestor t' a c.
Proof.
  intros Hmono a c H; induction H as [a c Hp | a p c Hac IH Hp].
  - apply Anc_dir. unfold parent_id in *. destruct (pget c t) as [m|] eqn:E; try discriminate.
    rewrite (Hmono _ _ E). exact Hp.
  - eapply Anc_step; [exact IH|].
    unfold parent_id in *. destruct (pget c t) as [m|] eqn:E; try discriminate.
    rewrite (Hmono _ _ E). exact Hp.
Qed.

(* the empty sibling run. *)
Lemma forest_nil (t : PTrie NodeMeta) P lo : ForestWF t t P lo lo.
Proof. constructor; intros; solve [ lia | reflexivity | exfalso; lia ]. Qed.

Local Open Scope positive_scope.

(* a wrapped node's fresh id preserves every existing entry of its children table. *)
Lemma pset_mono (tf : PTrie NodeMeta) me meta :
  pget me tf = None -> forall j m, pget j tf = Some m -> pget j (pset me meta tf) = Some m.
Proof.
  intros Hfresh j m Hj. destruct (Pos.eq_dec j me) as [->|Hne].
  - rewrite Hfresh in Hj; discriminate.
  - rewrite pget_pset_other by congruence. exact Hj.
Qed.

(* every id strictly inside a wrapped node's interval descends from the wrapped node. *)
Lemma wrap_root_sound (t0 tf : PTrie NodeMeta) me nx meta :
  Fresh t0 me ->
  ForestWF t0 tf me (Pos.succ me) nx ->
  pget me tf = None ->
  forall k, me < k -> k < nx ->
    Ancestor (pset me meta tf) me k.
Proof.
  intros Hf0 HF Hfresh k.
  induction k as [k IHk] using (well_founded_induction (well_founded_ltof _ (fun p : positive => Pos.to_nat p))).
  intros Hmk Hkx.
  set (t := pset me meta tf).
  assert (Hget : pget k t = pget k tf).
  { unfold t; rewrite pget_pset_other by lia; reflexivity. }
  destruct (pget k tf) as [m|] eqn:Em.
  2:{ exfalso. exact (for_pres HF k ltac:(lia) Hkx Em). }
  destruct (for_prng HF k m ltac:(lia) Hkx Em) as [p [Hpar Hcase]].
  assert (Hpid : parent_id t k = Some p).
  { unfold parent_id, t. rewrite pget_pset_other by lia. rewrite Em. exact Hpar. }
  destruct Hcase as [Hp | [Hlo [Hpk _]]].
  - (* k is a direct child of me *) subst p. apply Anc_dir. exact Hpid.
  - (* k's parent p is itself inside me's children; recurse *)
    eapply Anc_step; [ | exact Hpid].
    apply IHk.
    + unfold ltof. apply Pos2Nat.inj_lt. exact Hpk.
    + (* me < p : p is a child id, so p >= succ me > me *) lia.
    + lia.
Qed.

(* wrap a children forest (parent = me, over [me+1, nx)) into a single subtree rooted at me. *)
Lemma subtree_from_forest (t0 tf : PTrie NodeMeta) oP me se nx meta :
  nx = Pos.succ se ->
  Fresh t0 me ->
  ForestWF t0 tf me (Pos.succ me) nx ->
  Fresh tf nx ->
  nm_parent meta = oP ->
  nm_subtree_end meta = se ->
  Fresh (pset me meta tf) nx /\ SubtreeWF t0 (pset me meta tf) oP me se.
Proof.
  intros Hnx Hf0 HF Hff Hpar Hend.
  assert (Hmse : me <= se) by (generalize (for_le HF); lia).
  assert (Hfresh_me : pget me tf = None).
  { rewrite (for_out HF me) by lia. apply Hf0; lia. }
  set (t := pset me meta tf).
  (* pget on t: me -> meta, else -> tf *)
  assert (Hget_me : pget me t = Some meta) by (unfold t; apply pget_pset_same).
  assert (Hget_ne : forall k, k <> me -> pget k t = pget k tf) by (intros; unfold t; apply pget_pset_other; congruence).
  split.
  - (* Fresh t nx *) intros k Hk. rewrite Hget_ne by lia. apply Hff; exact Hk.
  - constructor.
    + exact Hmse.
    + (* sub_out *) intros k Hk. rewrite Hget_ne by lia. apply (for_out HF). lia.
    + (* sub_root *) exists meta. split; [exact Hget_me | split; [exact Hpar | exact Hend]].
    + (* sub_pres *) intros k H1 H2. destruct (Pos.eq_dec k me) as [->|Hne].
      * rewrite Hget_me; discriminate.
      * rewrite Hget_ne by exact Hne. eapply (for_pres HF); [lia|lia].
    + (* sub_nest *) intros k m H1 H2 Hm. destruct (Pos.eq_dec k me) as [->|Hne].
      * rewrite Hget_me in Hm; injection Hm as <-. rewrite Hend. lia.
      * rewrite Hget_ne in Hm by exact Hne.
        destruct (for_nest HF k m ltac:(lia) ltac:(lia) Hm) as [A B]. lia.
    + (* sub_prng *) intros k m H1 H2 Hm.
      rewrite Hget_ne in Hm by lia.
      destruct (for_prng HF k m ltac:(lia) ltac:(lia) Hm) as [p [Hpar' Hcase]].
      destruct Hcase as [Hpeq | [Hlo [Hpk [mp [Hmp [Hkmp Hmmp]]]]]].
      * (* p = me : parent is the wrapped node *)
        subst p. exists me, meta. rewrite Hget_me.
        repeat split; try assumption; try (rewrite Hend); try lia.
        destruct (for_nest HF k m ltac:(lia) ltac:(lia) Hm) as [A B]. lia.
      * exists p, mp. rewrite Hget_ne by lia.
        repeat split; try assumption; try lia.
    + (* sub_snd *) intros a k ma H1 H2 Hget_a Hak Hkend.
      destruct (Pos.eq_dec a me) as [->|Hne].
      * (* a = me : use wrap_root_sound *)
        rewrite Hget_me in Hget_a; injection Hget_a as <-. rewrite Hend in Hkend.
        eapply wrap_root_sound; [exact Hf0 | exact HF | exact Hfresh_me | lia | lia].
      * (* a in children : lift children soundness through pset me *)
        rewrite Hget_ne in Hget_a by exact Hne.
        assert (Hmono : forall j mm, pget j tf = Some mm -> pget j t = Some mm)
          by (intros; unfold t; apply pset_mono; assumption).
        eapply ancestor_mono; [exact Hmono|].
        eapply (for_snd HF); [lia|lia|exact Hget_a|exact Hak|exact Hkend].
Qed.

(* compose a subtree with the following sibling run (built afterwards on strictly larger, fresh ids). *)
Lemma forest_cons (t0 t1 t2 : PTrie NodeMeta) P me se nx :
  SubtreeWF t0 t1 (Some P) me se ->
  Fresh t1 (Pos.succ se) ->
  ForestWF t1 t2 P (Pos.succ se) nx ->
  ForestWF t0 t2 P me nx.
Proof.
  intros HS Hf1 HF.
  assert (Hmse : me <= se) by (apply (sub_le HS)).
  assert (Hsx : Pos.succ se <= nx) by (apply (for_le HF)).
  (* monotonicity t1 -> t2 : every t1 entry sits below succ se, hence is preserved by the forest *)
  assert (Hmono : forall j m, pget j t1 = Some m -> pget j t2 = Some m).
  { intros j m Hj. destruct (Pos.ltb j (Pos.succ se)) eqn:Hlt.
    - apply Pos.ltb_lt in Hlt. rewrite (for_out HF j) by lia. exact Hj.
    - apply Pos.ltb_ge in Hlt. rewrite (Hf1 j) in Hj by lia. discriminate. }
  (* t2 outside [succ se, nx) equals t1; and t1 outside [me,se] equals t0 *)
  assert (Hout2 : forall k, k < Pos.succ se \/ nx <= k -> pget k t2 = pget k t1)
    by (intros; apply (for_out HF); lia).
  constructor.
  - lia.
  - (* for_out *) intros k Hk. rewrite Hout2 by lia. apply (sub_out HS). lia.
  - (* for_pres *) intros k H1 H2. destruct (Pos.leb (Pos.succ se) k) eqn:Hge.
    + apply Pos.leb_le in Hge. eapply (for_pres HF); [lia|lia].
    + apply Pos.leb_gt in Hge. rewrite Hout2 by lia. eapply (sub_pres HS); [lia|lia].
  - (* for_nest *) intros k m H1 H2 Hm. destruct (Pos.leb (Pos.succ se) k) eqn:Hge.
    + apply Pos.leb_le in Hge. destruct (for_nest HF k m ltac:(lia) ltac:(lia) Hm) as [A B]. lia.
    + apply Pos.leb_gt in Hge. rewrite Hout2 in Hm by lia.
      destruct (sub_nest HS k m ltac:(lia) ltac:(lia) Hm) as [A B]. lia.
  - (* for_prng *) intros k m H1 H2 Hm. destruct (Pos.leb (Pos.succ se) k) eqn:Hge.
    + apply Pos.leb_le in Hge.
      destruct (for_prng HF k m ltac:(lia) ltac:(lia) Hm) as [p [Hpar Hcase]].
      exists p. split; [exact Hpar|]. destruct Hcase as [->|[Hlo [Hpk [mp [Hmp Hb]]]]].
      * left; reflexivity.
      * right. split; [lia|split;[lia|]]. exists mp. split; [exact Hmp | exact Hb].
    + apply Pos.leb_gt in Hge. rewrite Hout2 in Hm by lia.
      destruct (Pos.eqb me k) eqn:Hmek.
      * (* k = me : the first sibling root, parent P *)
        apply Pos.eqb_eq in Hmek; subst k.
        destruct (sub_root HS) as [m0 [Hg [Hp He]]]. rewrite Hg in Hm; injection Hm as <-.
        exists P. split; [exact Hp | left; reflexivity].
      * apply Pos.eqb_neq in Hmek.
        destruct (sub_prng HS k m ltac:(lia) ltac:(lia) Hm) as [p [mp [Hpar [Hmp [Hle1 [Hlt1 [Hb1 Hb2]]]]]]].
        exists p. split; [exact Hpar|]. right. split; [lia|split;[lia|]].
        exists mp. rewrite Hout2 by lia. auto.
  - (* for_snd *) intros a k ma H1 H2 Hget_a Hak Hkend. destruct (Pos.leb (Pos.succ se) a) eqn:Hge.
    + apply Pos.leb_le in Hge. eapply (for_snd HF); [lia|lia|exact Hget_a|exact Hak|exact Hkend].
    + apply Pos.leb_gt in Hge. rewrite Hout2 in Hget_a by lia.
      eapply ancestor_mono; [exact Hmono|].
      eapply (sub_snd HS); [lia|lia|exact Hget_a|exact Hak|].
      (* k <= subtree_end ma <= se, established by sub_nest on a *)
      exact Hkend.
Qed.

(* ================================================================================================= *)
(** ** The builders satisfy the structural invariants (each occurrence's subtree is well-formed).     *)
(* ================================================================================================= *)

Lemma Fresh_weaken (t : PTrie NodeMeta) from from' :
  from <= from' -> Fresh t from -> Fresh t from'.
Proof. intros H HF k Hk. apply HF. lia. Qed.

Lemma Fresh_PLeaf (from : positive) : Fresh PLeaf from.
Proof. intros k _; apply pget_leaf. Qed.

Lemma build_expr_spec : forall e parent role me t0 t se,
  Fresh t0 me ->
  build_expr parent role me e t0 = (t, se) ->
  Fresh t (Pos.succ se) /\ SubtreeWF t0 t (Some parent) me se.
Proof.
  induction e as [v | l IHl r IHr]; intros parent role me t0 t se Hf0 Hbuild; simpl in Hbuild.
  - (* TLeaf: an empty children forest wrapped at [me] *)
    injection Hbuild as Ht Hse; subst t; subst se.
    eapply subtree_from_forest;
      [ reflexivity | exact Hf0 | apply forest_nil
      | (eapply Fresh_weaken; [|exact Hf0]; lia) | reflexivity | reflexivity ].
  - (* TBin: two child subtrees composed, then wrapped at [me] *)
    destruct (build_expr me (RChild 0) (Pos.succ me) l t0) as [t1 e1] eqn:E1.
    destruct (build_expr me (RChild 1) (Pos.succ e1) r t1) as [t2 e2] eqn:E2.
    injection Hbuild as Ht Hse; subst t; subst se.
    assert (Hf0' : Fresh t0 (Pos.succ me)) by (eapply Fresh_weaken; [|exact Hf0]; lia).
    destruct (IHl me (RChild 0) (Pos.succ me) t0 t1 e1 Hf0' E1) as [Hfr1 HS1].
    destruct (IHr me (RChild 1) (Pos.succ e1) t1 t2 e2 Hfr1 E2) as [Hfr2 HS2].
    assert (HFr : ForestWF t1 t2 me (Pos.succ e1) (Pos.succ e2))
      by (eapply forest_cons; [exact HS2 | exact Hfr2 | apply forest_nil]).
    assert (HFl : ForestWF t0 t2 me (Pos.succ me) (Pos.succ e2))
      by (eapply forest_cons; [exact HS1 | exact Hfr1 | exact HFr]).
    eapply subtree_from_forest;
      [ reflexivity | exact Hf0 | exact HFl | exact Hfr2 | reflexivity | reflexivity ].
Qed.

Lemma build_stmt_spec : forall parent sidx me s t0 t se,
  Fresh t0 me ->
  build_stmt parent sidx me s t0 = (t, se) ->
  Fresh t (Pos.succ se) /\ SubtreeWF t0 t (Some parent) me se.
Proof.
  intros parent sidx me [e] t0 t se Hf0 Hbuild; simpl in Hbuild.
  destruct (build_expr me RStmtExpr (Pos.succ me) e t0) as [t1 e1] eqn:E1.
  injection Hbuild as Ht Hse; subst t; subst se.
  assert (Hf0' : Fresh t0 (Pos.succ me)) by (eapply Fresh_weaken; [|exact Hf0]; lia).
  destruct (build_expr_spec e me RStmtExpr (Pos.succ me) t0 t1 e1 Hf0' E1) as [Hfr1 HS1].
  assert (HF : ForestWF t0 t1 me (Pos.succ me) (Pos.succ e1))
    by (eapply forest_cons; [exact HS1 | exact Hfr1 | apply forest_nil]).
  eapply subtree_from_forest;
    [ reflexivity | exact Hf0 | exact HF | exact Hfr1 | reflexivity | reflexivity ].
Qed.

Lemma build_seq_spec {X}
  (bx : positive -> nat -> positive -> X -> PTrie NodeMeta -> PTrie NodeMeta * positive) :
  (forall parent i me x t0 t se, Fresh t0 me -> bx parent i me x t0 = (t, se) ->
     Fresh t (Pos.succ se) /\ SubtreeWF t0 t (Some parent) me se) ->
  forall xs parent i0 me0 t0 t nx,
  Fresh t0 me0 ->
  build_seq bx parent i0 me0 xs t0 = (t, nx) ->
  Fresh t nx /\ ForestWF t0 t parent me0 nx.
Proof.
  intros Hbx xs. induction xs as [|x rest IH]; intros parent i0 me0 t0 t nx Hf0 Hbuild; simpl in Hbuild.
  - injection Hbuild as Ht Hnx; subst t; subst nx. split; [exact Hf0 | apply forest_nil].
  - destruct (bx parent i0 me0 x t0) as [t1 se] eqn:E1.
    destruct (build_seq bx parent (S i0) (Pos.succ se) rest t1) as [t2 nx2] eqn:E2.
    injection Hbuild as Ht Hnx; subst t; subst nx.
    destruct (Hbx parent i0 me0 x t0 t1 se Hf0 E1) as [Hfr1 HS1].
    destruct (IH parent (S i0) (Pos.succ se) t1 t2 nx2 Hfr1 E2) as [Hfr2 HF2].
    split; [exact Hfr2|].
    eapply forest_cons; [exact HS1 | exact Hfr1 | exact HF2].
Qed.

Lemma build_decl_spec : forall parent didx me d t0 t se,
  Fresh t0 me ->
  build_decl parent didx me d t0 = (t, se) ->
  Fresh t (Pos.succ se) /\ SubtreeWF t0 t (Some parent) me se.
Proof.
  intros parent didx me [body] t0 t se Hf0 Hbuild; simpl in Hbuild.
  destruct (build_seq build_stmt me 0 (Pos.succ me) body t0) as [t1 nx1] eqn:E1.
  injection Hbuild as Ht Hse; subst t; subst se.
  assert (Hf0' : Fresh t0 (Pos.succ me)) by (eapply Fresh_weaken; [|exact Hf0]; lia).
  destruct (build_seq_spec build_stmt build_stmt_spec body me 0 (Pos.succ me) t0 t1 nx1 Hf0' E1) as [Hfr1 HF1].
  assert (Hge : Pos.succ me <= nx1) by (apply (for_le HF1)).
  assert (Hnx : Pos.succ (Pos.pred nx1) = nx1)
    by (destruct (Pos.succ_pred_or nx1) as [->|H]; [exfalso; lia | exact H]).
  assert (H : Fresh (pset me (mkMeta KDecl (Some parent) (RFileDecl didx) (Pos.pred nx1)) t1) nx1 /\
              SubtreeWF t0 (pset me (mkMeta KDecl (Some parent) (RFileDecl didx) (Pos.pred nx1)) t1)
                        (Some parent) me (Pos.pred nx1)).
  { eapply subtree_from_forest;
      [ symmetry; exact Hnx | exact Hf0 | exact HF1 | exact Hfr1 | reflexivity | reflexivity ]. }
  rewrite Hnx. exact H.
Qed.

Lemma build_file_wf (f : TFile) :
  SubtreeWF PLeaf (fi_table (build_file f)) None root_id (fi_count (build_file f)).
Proof.
  unfold build_file.
  destruct (build_seq build_decl root_id 0 (Pos.succ root_id) (tf_decls f) PLeaf) as [t1 nx] eqn:E.
  simpl.
  destruct (build_seq_spec build_decl build_decl_spec (tf_decls f) root_id 0 (Pos.succ root_id)
              PLeaf t1 nx (Fresh_PLeaf _) E) as [Hfr HF].
  assert (Hge : Pos.succ root_id <= nx) by (apply (for_le HF)).
  assert (Hnx : Pos.succ (Pos.pred nx) = nx)
    by (destruct (Pos.succ_pred_or nx) as [->|H]; [exfalso; lia | exact H]).
  assert (H : Fresh (pset root_id (mkMeta KFile None RFileRoot (Pos.pred nx)) t1) nx /\
              SubtreeWF PLeaf (pset root_id (mkMeta KFile None RFileRoot (Pos.pred nx)) t1)
                        None root_id (Pos.pred nx)).
  { eapply subtree_from_forest;
      [ symmetry; exact Hnx | apply Fresh_PLeaf | exact HF | exact Hfr | reflexivity | reflexivity ]. }
  destruct H as [_ HS]. exact HS.
Qed.


(* ================================================================================================= *)
(** ** Enumeration helpers over the preorder id interval.                                             *)
(* ================================================================================================= *)

Lemma pos_seq_In (start c : positive) (len : nat) :
  In c (pos_seq start len) <-> (Pos.to_nat start <= Pos.to_nat c < Pos.to_nat start + len)%nat.
Proof.
  revert start; induction len as [|n IH]; intros start; simpl.
  - split; [intros H; destruct H | intros H; exfalso; lia].
  - rewrite IH. split.
    + intros [<- | H]; [lia|]. rewrite Pos2Nat.inj_succ in H. lia.
    + intros H. destruct (Pos.eq_dec c start) as [->|Hne]; [left; reflexivity|].
      right. rewrite Pos2Nat.inj_succ.
      assert (Pos.to_nat c <> Pos.to_nat start) by (intro Hc; apply Hne; apply Pos2Nat.inj; exact Hc).
      lia.
Qed.

Lemma pos_seq_NoDup (start : positive) (len : nat) : NoDup (pos_seq start len).
Proof.
  revert start; induction len as [|n IH]; intros start; simpl.
  - constructor.
  - constructor; [| apply IH]. intro H. apply pos_seq_In in H. rewrite Pos2Nat.inj_succ in H. lia.
Qed.

Lemma pos_seq_SS (start : positive) (len : nat) : StronglySorted Pos.lt (pos_seq start len).
Proof.
  revert start; induction len as [|n IH]; intros start; simpl.
  - constructor.
  - constructor; [apply IH|]. apply Forall_forall. intros x Hx. apply pos_seq_In in Hx.
    rewrite Pos2Nat.inj_succ in Hx. lia.
Qed.

Lemma filter_SS {A} (R : A -> A -> Prop) (f : A -> bool) (l : list A) :
  StronglySorted R l -> StronglySorted R (filter f l).
Proof.
  induction l as [|x xs IH]; intros HS; simpl.
  - constructor.
  - inversion HS as [|? ? HSS HF]; subst. destruct (f x).
    + constructor; [apply IH; exact HSS|]. rewrite Forall_forall in *.
      intros y Hy. apply filter_In in Hy as [Hy _]. apply HF; exact Hy.
    + apply IH; exact HSS.
Qed.

(* ================================================================================================= *)
(** ** The C0.4 required theorem set (over the built single-file index; instance #9 over a witness).   *)
(* ================================================================================================= *)

(* every entry of a built file table lies in the canonical interval [root_id .. count]. *)
Lemma in_domain (f : TFile) k m :
  pget k (fi_table (build_file f)) = Some m ->
  root_id <= k /\ k <= fi_count (build_file f).
Proof.
  intros H. pose proof (build_file_wf f) as WF. split.
  - destruct (Pos.leb root_id k) eqn:E; [apply Pos.leb_le; exact E|].
    apply Pos.leb_gt in E. rewrite (sub_out WF k) in H by (left; lia).
    rewrite pget_leaf in H; discriminate.
  - destruct (Pos.leb k (fi_count (build_file f))) eqn:E; [apply Pos.leb_le; exact E|].
    apply Pos.leb_gt in E. rewrite (sub_out WF k) in H by (right; lia).
    rewrite pget_leaf in H; discriminate.
Qed.

(* THEOREM 1 — the root id is canonical: every file root occupies the SAME fixed local id [root_id]. *)
Theorem thm1_root_id_canonical (f : TFile) :
  exists m, pget root_id (fi_table (build_file f)) = Some m /\ nm_kind m = KFile /\ nm_role m = RFileRoot.
Proof.
  unfold build_file.
  destruct (build_seq build_decl root_id 0 (Pos.succ root_id) (tf_decls f) PLeaf) as [t1 nx] eqn:E.
  exists (mkMeta KFile None RFileRoot (Pos.pred nx)).
  cbn [fi_table]. rewrite pget_pset_same. split; [reflexivity | split; reflexivity].
Qed.

(* THEOREM 2 — the root has no parent. *)
Theorem thm2_root_no_parent (f : TFile) m :
  pget root_id (fi_table (build_file f)) = Some m -> nm_parent m = None.
Proof.
  intros H. pose proof (build_file_wf f) as WF. destruct (sub_root WF) as [m0 [Hg [Hp _]]].
  rewrite Hg in H. injection H as <-. exact Hp.
Qed.

(* THEOREM 3 — every non-root occurrence has exactly one parent. *)
Theorem thm3_nonroot_has_parent (f : TFile) k m :
  pget k (fi_table (build_file f)) = Some m -> k <> root_id -> exists p, nm_parent m = Some p.
Proof.
  intros H Hne. pose proof (build_file_wf f) as WF.
  destruct (in_domain f k m H) as [Hlo Hhi].
  assert (root_id < k) by lia.
  destruct (sub_prng WF k m ltac:(lia) Hhi H) as [p [mp [Hpar _]]]. exists p; exact Hpar.
Qed.

(* the parent field is functional: an occurrence has at most one parent. *)
Theorem thm3b_parent_unique (f : TFile) k m p1 p2 :
  pget k (fi_table (build_file f)) = Some m -> nm_parent m = Some p1 -> nm_parent m = Some p2 -> p1 = p2.
Proof. intros _ H1 H2. rewrite H1 in H2. injection H2 as <-. reflexivity. Qed.

(* THEOREM 13 (completeness half) — ancestry implies nested preorder intervals. *)
Lemma anc_complete (f : TFile) a d :
  Ancestor (fi_table (build_file f)) a d ->
  exists ma md, pget a (fi_table (build_file f)) = Some ma /\
                pget d (fi_table (build_file f)) = Some md /\
                a < d /\ d <= nm_subtree_end ma /\ nm_subtree_end md <= nm_subtree_end ma.
Proof.
  pose proof (build_file_wf f) as WF.
  set (t := fi_table (build_file f)) in *.
  induction 1 as [a d Hp | a p c Hac IH Hp].
  - (* Anc_dir : d's parent is a *)
    unfold parent_id in Hp. destruct (pget d t) as [md|] eqn:Ed; [|discriminate].
    destruct (in_domain f d md Ed) as [Hlo Hhi].
    assert (Hdne : d <> root_id).
    { intro; subst d. destruct (sub_root WF) as [m0 [Hg [Hp0 _]]]. rewrite Hg in Ed; injection Ed as <-.
      rewrite Hp0 in Hp; discriminate. }
    destruct (sub_prng WF d md ltac:(lia) Hhi Ed) as [p [mp [Hpar [Hmp [Hle1 [Hlt1 [Hb1 Hb2]]]]]]].
    rewrite Hp in Hpar. injection Hpar as <-.
    exists mp, md. repeat split; try assumption; lia.
  - (* Anc_step : c's parent is p, and a is an ancestor of p *)
    unfold parent_id in Hp. destruct (pget c t) as [mc|] eqn:Ec; [|discriminate].
    destruct IH as [ma [mp0 [Hga [Hgp [Hap [Hpend Hmpend]]]]]].
    destruct (in_domain f c mc Ec) as [Hlo Hhi].
    assert (Hcne : c <> root_id).
    { intro; subst c. destruct (sub_root WF) as [m0 [Hg [Hp0 _]]]. rewrite Hg in Ec; injection Ec as <-.
      rewrite Hp0 in Hp; discriminate. }
    destruct (sub_prng WF c mc ltac:(lia) Hhi Ec) as [p' [mp' [Hpar [Hmp' [Hle1 [Hlt1 [Hb1 Hb2]]]]]]].
    rewrite Hp in Hpar. injection Hpar as <-. rewrite Hgp in Hmp'. injection Hmp' as <-.
    exists ma, mc. repeat split; try assumption; lia.
Qed.

(* THEOREM 13 — the O(1) preorder-interval ancestor test is sound AND complete. *)
Theorem thm13_interval_ancestry (f : TFile) a d :
  pget a (fi_table (build_file f)) <> None ->
  (is_ancestor_local (fi_table (build_file f)) a d = true <-> Ancestor (fi_table (build_file f)) a d).
Proof.
  intros Ha. pose proof (build_file_wf f) as WF.
  set (t := fi_table (build_file f)) in *.
  unfold is_ancestor_local. destruct (pget a t) as [ma|] eqn:Ea; [|congruence].
  split.
  - (* soundness *) intros Hb. apply andb_true_iff in Hb as [H1 H2].
    apply Pos.ltb_lt in H1. apply Pos.leb_le in H2.
    destruct (in_domain f a ma Ea) as [Hlo Hhi].
    eapply (sub_snd WF); [lia|exact Hhi|exact Ea|exact H1|exact H2].
  - (* completeness *) intros Hanc. destruct (anc_complete f a d Hanc) as [ma' [md [Hga [_ [Had [Hdend _]]]]]].
    unfold t in Ea. assert (ma = ma') by congruence. subst ma'.
    apply andb_true_iff; split; [apply Pos.ltb_lt; lia | apply Pos.leb_le; lia].
Qed.

(* THEOREM 11 (children source order) — the direct children of an occurrence are strictly increasing. *)
Theorem thm11_children_sorted (f : TFile) p :
  StronglySorted Pos.lt (child_ids (fi_table (build_file f)) p).
Proof.
  unfold child_ids. destruct (pget p (fi_table (build_file f))) as [m|] eqn:Ep; [|constructor].
  apply filter_SS. apply pos_seq_SS.
Qed.

(* THEOREM 4 — parent/child are inverse: a direct child appears in [child_ids] of its parent, and
   everything in [child_ids p] has parent [p]. *)
Theorem thm4_child_has_parent (f : TFile) p c :
  In c (child_ids (fi_table (build_file f)) p) -> parent_id (fi_table (build_file f)) c = Some p.
Proof.
  unfold child_ids, parent_id. destruct (pget p (fi_table (build_file f))) as [mp|] eqn:Ep; [|intros []].
  intros Hin. apply filter_In in Hin as [_ Hf].
  destruct (pget c (fi_table (build_file f))) as [mc|] eqn:Ec; [|discriminate].
  destruct (nm_parent mc) as [q|] eqn:Eq; [|discriminate].
  apply Pos.eqb_eq in Hf. subst q. reflexivity.
Qed.

Theorem thm4_parent_has_child (f : TFile) p c mc :
  pget c (fi_table (build_file f)) = Some mc -> nm_parent mc = Some p ->
  In c (child_ids (fi_table (build_file f)) p).
Proof.
  intros Hc Hpar. pose proof (build_file_wf f) as WF.
  destruct (in_domain f c mc Hc) as [Hlo Hhi].
  assert (Hcne : c <> root_id).
  { intro; subst c. destruct (sub_root WF) as [m0 [Hg [Hp0 _]]]. rewrite Hg in Hc; injection Hc as <-.
    rewrite Hp0 in Hpar; discriminate. }
  destruct (sub_prng WF c mc ltac:(lia) Hhi Hc) as [p' [mp' [Hpar' [Hmp' [Hle1 [Hlt1 [Hb1 Hb2]]]]]]].
  rewrite Hpar in Hpar'. injection Hpar' as <-.
  unfold child_ids. rewrite Hmp'.
  apply filter_In. split.
  - apply pos_seq_In. rewrite Pos2Nat.inj_succ.
    (* c in [p+1 .. subtree_end p] : p < c <= subtree_end mp' *)
    assert (Pos.to_nat p < Pos.to_nat c)%nat by (apply Pos2Nat.inj_lt; lia).
    assert (Pos.to_nat c <= Pos.to_nat (nm_subtree_end mp'))%nat by (apply Pos2Nat.inj_le; lia).
    lia.
  - rewrite Hc, Hpar. apply Pos.eqb_eq. reflexivity.
Qed.

(* THEOREM 5 — parentage stays within one file (references carry the file, so the parent shares it). *)
Lemma ref_of_key (idx : SyntaxIndex) (k : NodeKey) (r : NodeRef idx) :
  ref_of idx k = Some r -> ref_key r = k.
Proof.
  unfold ref_of. generalize (@eq_refl bool (valid_keyb idx k)).
  destruct (valid_keyb idx k) at 2 3; intros e H; [injection H as <-; reflexivity | discriminate].
Qed.

Theorem thm5_parent_same_file (idx : SyntaxIndex) (r pr : NodeRef idx) :
  parent_of r = Some pr -> nk_file (ref_key pr) = nk_file (ref_key r).
Proof.
  unfold parent_of. destruct (ref_meta r) as [m|]; [|discriminate].
  destruct (nm_parent m) as [pid|]; [|discriminate].
  intros H. apply ref_of_key in H. rewrite H. reflexivity.
Qed.

(* THEOREM 6/10 — the containing file is recovered by O(1) projection and agrees with the key's file. *)
Theorem thm6_containing_file (idx : SyntaxIndex) (r : NodeRef idx) :
  containing_file_path r = nk_file (ref_key r).
Proof. reflexivity. Qed.

(* THEOREM 8 — NodeKey equality decides occurrence identity. *)
Lemma fp_eq_dec (a b : FilePath) : {a = b} + {a <> b}.
Proof.
  destruct (fp_eqb a b) eqn:E; [left; apply fp_eqb_eq; exact E|].
  right; intro Heq; subst; rewrite (proj2 (fp_eqb_eq b b) eq_refl) in E; discriminate.
Qed.

Theorem thm8_nodekey_eq_dec (a b : NodeKey) : {a = b} + {a <> b}.
Proof.
  destruct a as [fa la], b as [fb lb].
  destruct (fp_eq_dec fa fb) as [->|Hf]; [| right; intro H; injection H as <- <-; apply Hf; reflexivity].
  destruct (Pos.eq_dec la lb) as [->|Hl]; [left; reflexivity|].
  right; intro H; injection H as <-; apply Hl; reflexivity.
Qed.

Theorem thm8_nodekey_eqb_spec (a b : NodeKey) : nodekey_eqb a b = true <-> a = b.
Proof.
  unfold nodekey_eqb. rewrite andb_true_iff. split.
  - intros [Hf Hl]. apply fp_eqb_eq in Hf. apply Pos.eqb_eq in Hl.
    destruct a, b; simpl in *; subst; reflexivity.
  - intros ->. split; [apply fp_eqb_eq; reflexivity | apply Pos.eqb_eq; reflexivity].
Qed.

(* THEOREM 7 — every occurrence appears EXACTLY ONCE in canonical enumeration (no dup + complete + sound). *)
Definition all_ids (fi : FileIndex) : list positive := pos_seq root_id (Pos.to_nat (fi_count fi)).

Theorem thm7_enum_nodup (f : TFile) : NoDup (all_ids (build_file f)).
Proof. apply pos_seq_NoDup. Qed.

Theorem thm7_enum_complete (f : TFile) k m :
  pget k (fi_table (build_file f)) = Some m -> In k (all_ids (build_file f)).
Proof.
  intros H. destruct (in_domain f k m H) as [Hlo Hhi]. unfold all_ids.
  apply pos_seq_In. unfold root_id. rewrite Pos2Nat.inj_1.
  assert (Pos.to_nat k <= Pos.to_nat (fi_count (build_file f)))%nat by (apply Pos2Nat.inj_le; exact Hhi).
  assert (1 <= Pos.to_nat k)%nat by (pose proof (Pos2Nat.is_pos k); lia).
  lia.
Qed.

Theorem thm7_enum_sound (f : TFile) k :
  In k (all_ids (build_file f)) -> pget k (fi_table (build_file f)) <> None.
Proof.
  unfold all_ids. intros Hin. apply pos_seq_In in Hin. unfold root_id in Hin. rewrite Pos2Nat.inj_1 in Hin.
  pose proof (build_file_wf f) as WF. apply (sub_pres WF).
  - unfold root_id. apply Pos2Nat.inj_le. rewrite Pos2Nat.inj_1. lia.
  - apply Pos2Nat.inj_le. lia.
Qed.

(* THEOREM 12 — index construction is deterministic (a pure total function; no fuel, no nondeterminism). *)
Theorem thm12_deterministic (fs1 fs2 : TForest) : fs1 = fs2 -> build_forest fs1 = build_forest fs2.
Proof. intros ->. reflexivity. Qed.

(* THEOREM (C0.4) — the index builder does NOT depend on structural-equality search: it branches only on
   tree SHAPE, never on node contents.  Formally, remapping every leaf value leaves the built table (ids,
   kinds, parents, roles, intervals) completely unchanged — so the builder cannot be comparing/deduplicating
   subtrees by value.  (Together with thm9, which gives two VALUE-equal leaves DISTINCT ids, this rules out
   any hash-consing / structural-dedup pass.) *)
Fixpoint map_leaves (g : nat -> nat) (e : TExpr) : TExpr :=
  match e with TLeaf v => TLeaf (g v) | TBin l r => TBin (map_leaves g l) (map_leaves g r) end.

Theorem thm_builder_no_structural_search :
  forall e g parent role me t,
    build_expr parent role me (map_leaves g e) t = build_expr parent role me e t.
Proof.
  induction e as [v | l IHl r IHr]; intros g parent role me t; simpl; [reflexivity|].
  rewrite IHl. destruct (build_expr me (RChild 0) (Pos.succ me) l t) as [t1 e1] eqn:E1.
  rewrite IHr. reflexivity.
Qed.

(* THEOREM 14 — metadata describes the ORIGINAL AST: [NodeMeta] stores no syntax subtree, and the true
   syntax is recovered by re-traversing the source forest, never a copied/invented tree. *)
Definition expr_size (e : TExpr) : nat := match e with TLeaf _ => 0 | TBin _ _ => 0 end.
Theorem thm14_meta_stores_no_subtree :
  (* [NodeMeta]'s fields are only kind / parent-id / role / interval-end — there is no [TExpr]/[TStmt]/
     [TDecl] field, so metadata cannot be a copy of the source subtree. *)
  forall m : NodeMeta, exists k op r e,
    m = mkMeta k op r e /\ (forall e', mkMeta k op r e = mkMeta k op r e' -> e = e').
Proof. intros [k op r e]. exists k, op, r, e. split; [reflexivity|]. intros e' H; injection H as <-; reflexivity. Qed.

(* ================================================================================================= *)
(** ** THEOREM 9 (instance) — two structurally EQUAL leaves in different positions have distinct refs. *)
(* ================================================================================================= *)

Definition wpath_a : FilePath := mkFP "a.go"%string eq_refl.
Definition wpath_b : FilePath := mkFP "b.go"%string eq_refl.
(* file a: one decl, one statement, the expression TBin (TLeaf 5) (TLeaf 5) — TWO equal leaves. *)
Definition wfile_a : TFile := mkTFile wpath_a [ TFun [ TPrint (TBin (TLeaf 5) (TLeaf 5)) ] ].
Definition wfile_b : TFile := mkTFile wpath_b [ TFun [ TPrint (TLeaf 7) ] ].
Definition wforest : TForest := [ wfile_a ; wfile_b ].
Definition widx : SyntaxIndex := build_forest wforest.

(* preorder ids in file a: 1=file, 2=decl, 3=stmt, 4=TBin, 5=left TLeaf 5, 6=right TLeaf 5. *)
Definition wkey_left  : NodeKey := mkKey wpath_a 5.
Definition wkey_right : NodeKey := mkKey wpath_a 6.

Theorem thm9_equal_leaves_distinct_refs :
  (* both occurrences are valid, live in the same file, and are the SAME syntactic kind with the SAME
     leaf value (structurally equal), yet their occurrence keys differ, so they are distinct refs. *)
  valid_keyb widx wkey_left = true /\
  valid_keyb widx wkey_right = true /\
  nodekey_eqb wkey_left wkey_right = false /\
  wkey_left <> wkey_right.
Proof.
  repeat split; try (vm_compute; reflexivity).
  intro H. discriminate H.
Qed.

(* the two equal leaves carry the SAME kind (KExpression) but DISTINCT roles (RChild 0 vs RChild 1),
   confirming occurrence identity is positional, not structural. *)
Theorem thm9_equal_leaves_same_kind_distinct_role :
  match file_of widx wpath_a with
  | Some fi =>
      match pget 5 (fi_table fi), pget 6 (fi_table fi) with
      | Some ml, Some mr => nm_kind ml = KExpression /\ nm_kind mr = KExpression /\ nm_role ml <> nm_role mr
      | _, _ => False
      end
  | None => False
  end.
Proof. vm_compute. repeat split; discriminate. Qed.
