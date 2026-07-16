(** * OccurrenceSpike — isolated, TEMPORARY occurrence-index proof spike (Source Forest campaign, C0).

    This module is NOT part of the certified GoProgram pipeline.  It is an isolated spike that validates
    the snapshot-local occurrence-identity + derived-navigation-index design (Master Plan Part 4) on a tiny
    toy grammar BEFORE any production AST migration (C1/C2).  It imports only [FilePath] (the leaf path
    authority, reused for occurrence keys); it does NOT import GoAST/GoTypes/GoCompile and nothing in the
    production pipeline imports it.  It is proven axiom-free by the same whole-theory audit as the rest of
    the theory, and will be DELETED once the production [GoIndex] lands (C2).

    C0.3 REPRESENTATION DECISION (recorded in .review/SOURCE_FOREST_STATUS.md):
      A. a certified positive-key radix trie (the [NodeTable] module below) — pure Gallina, empty assumption
         closure, O(bits) = O(log n) lookup/insert, persistent, decidable-key ergonomics.
      B. a primitive dense array (Coq [PArray]/[Uint63]) — O(1) lookup, BUT built on KERNEL PRIMITIVES
         (Int63/PArray), which Fido's standing law rule 4 forbids ("Never ... a kernel primitive").  Its
         "assumption closure" is a kernel extension outside pure CIC, so it fails the zero-axiom/no-primitive
         policy regardless of speed.  REJECTED.
    Selected: A.  The public [NodeTable] interface ([table]/[empty]/[get]/[set] + the three laws) HIDES the
    trie representation, so C2 can swap the physical table without disturbing any caller.  A plain association
    [list] is deliberately NOT used: it would give a forbidden O(n) list-scan node-table lookup (Master
    Plan 4.8).  *)

From Stdlib Require Import PArith List Bool Lia Eqdep_dec Wf_nat Sorted String Recdef Arith.
From Fido Require Import FilePath.
Import ListNotations.

(* ================================================================================================= *)
(** ** The selected node table: an ABSTRACT interface, implemented internally by a certified            *)
(*    positive-key radix trie (candidate A).  Callers see ONLY [NodeTable.table]/[empty]/[get]/[set]     *)
(*    and the three laws; the trie representation and its constructors are sealed inside the module, so   *)
(*    C2 may swap the physical table without disturbing any caller (Master Plan 4.9).                     *)
(* ================================================================================================= *)

Module Type NODE_TABLE.
  Parameter table : Type -> Type.
  Parameter empty : forall {A}, table A.
  Parameter get   : forall {A}, positive -> table A -> option A.
  Parameter set   : forall {A}, positive -> A -> table A -> table A.
  Parameter get_empty     : forall {A} (k : positive), get k (@empty A) = None.
  Parameter get_set_same  : forall {A} (k : positive) (v : A) (t : table A), get k (set k v t) = Some v.
  Parameter get_set_other : forall {A} (j k : positive) (v : A) (t : table A),
    j <> k -> get k (set j v t) = get k t.
End NODE_TABLE.

Module NodeTable : NODE_TABLE.
  (* internal representation — a persistent positive-key radix trie; O(log n) get/set. *)
  Inductive tr (A : Type) : Type := Lf : tr A | Nd : option A -> tr A -> tr A -> tr A.
  Arguments Lf {A}.
  Arguments Nd {A} _ _ _.
  Fixpoint rd {A} (k : positive) (t : tr A) : option A :=
    match t with
    | Lf => None
    | Nd o l r => match k with xH => o | xO k' => rd k' l | xI k' => rd k' r end
    end.
  Fixpoint wr {A} (k : positive) (v : A) (t : tr A) : tr A :=
    match k, t with
    | xH,    Lf        => Nd (Some v) Lf Lf
    | xH,    Nd _ l r  => Nd (Some v) l r
    | xO k', Lf        => Nd None (wr k' v Lf) Lf
    | xO k', Nd o l r  => Nd o (wr k' v l) r
    | xI k', Lf        => Nd None Lf (wr k' v Lf)
    | xI k', Nd o l r  => Nd o l (wr k' v r)
    end.
  Lemma rd_leaf {A} (k : positive) : rd k (@Lf A) = None. Proof. destruct k; reflexivity. Qed.
  Definition table := tr.
  Definition empty {A} : table A := @Lf A.
  Definition get {A} := @rd A.
  Definition set {A} := @wr A.
  Lemma get_empty {A} (k : positive) : get k (@empty A) = None. Proof. apply rd_leaf. Qed.
  Lemma get_set_same {A} (k : positive) (v : A) (t : table A) : get k (set k v t) = Some v.
  Proof. unfold get, set. revert t; induction k as [k' IH|k' IH|]; intros [ | o l r ]; simpl; auto. Qed.
  Lemma get_set_other {A} (j k : positive) (v : A) (t : table A) :
    j <> k -> get k (set j v t) = get k t.
  Proof.
    unfold get, set. revert k t; induction j as [j' IH|j' IH|]; intros k t Hjk;
      destruct k as [k'|k'|]; destruct t as [ | o l r ]; simpl;
      try reflexivity;
      try (now rewrite rd_leaf);
      try (rewrite IH by congruence; now rewrite ?rd_leaf);
      try (apply IH; congruence);
      try (exfalso; congruence).
  Qed.
End NodeTable.

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
(* An immutable toy SOURCE SNAPSHOT: a file sequence whose paths are unique by construction, so one path
   names at most one file root and a raw [NodeKey] cannot ambiguously name two roots (C0A §3). *)
Record TForest := mkTForest {
  forest_files        : list TFile;
  forest_paths_unique : NoDup (map tf_path forest_files)
}.

Definition root_id : positive := 1%positive.    (* every file root's canonical local id (theorem 1) *)

(* ================================================================================================= *)
(** ** The one-pass index builder (Master Plan 4.8).                                                   *)
(*    Each builder threads a fresh-id counter and inserts each occurrence's metadata EXACTLY ONCE via  *)
(*    [NodeTable.set] (O(log n)); it never searches, compares, or copies syntax subtrees.  A subtree    *)
(*    builder returns the subtree's last id ([se], its [subtree_end]); a sequence builder returns the   *)
(*    free id.  Meta for an internal node is inserted AFTER its children so [subtree_end] is known.     *)
(* ================================================================================================= *)

Fixpoint build_expr (parent : positive) (role : NodeRole) (me : positive) (e : TExpr) (t : NodeTable.table NodeMeta)
  : NodeTable.table NodeMeta * positive (* subtree_end *) :=
  match e with
  | TLeaf _ => (NodeTable.set me (mkMeta KExpression (Some parent) role me) t, me)
  | TBin l r =>
      let '(t1, e1) := build_expr me (RChild 0) (Pos.succ me) l t in
      let '(t2, e2) := build_expr me (RChild 1) (Pos.succ e1) r t1 in
      (NodeTable.set me (mkMeta KExpression (Some parent) role e2) t2, e2)
  end.

Definition build_stmt (parent : positive) (sidx : nat) (me : positive) (s : TStmt) (t : NodeTable.table NodeMeta)
  : NodeTable.table NodeMeta * positive :=
  match s with
  | TPrint e =>
      let '(t1, e1) := build_expr me RStmtExpr (Pos.succ me) e t in
      (NodeTable.set me (mkMeta KStatement (Some parent) (RDeclStmt sidx) e1) t1, e1)
  end.

(* A generic left-to-right sibling-sequence builder: builds each element as a subtree rooted at the
   running fresh id and advances.  Returns the next free id.  [bx] is the per-element subtree builder. *)
Fixpoint build_seq {X} (bx : positive -> nat -> positive -> X -> NodeTable.table NodeMeta -> NodeTable.table NodeMeta * positive)
                   (parent : positive) (i0 : nat) (me0 : positive) (xs : list X) (t : NodeTable.table NodeMeta)
  : NodeTable.table NodeMeta * positive (* next free id *) :=
  match xs with
  | []        => (t, me0)
  | x :: rest =>
      let '(t1, se) := bx parent i0 me0 x t in
      build_seq bx parent (S i0) (Pos.succ se) rest t1
  end.

Definition build_decl (parent : positive) (didx : nat) (me : positive) (d : TDecl) (t : NodeTable.table NodeMeta)
  : NodeTable.table NodeMeta * positive :=
  match d with
  | TFun body =>
      let '(t1, nx) := build_seq build_stmt me 0 (Pos.succ me) body t in
      (NodeTable.set me (mkMeta KDecl (Some parent) (RFileDecl didx) (Pos.pred nx)) t1, Pos.pred nx)
  end.

Record FileIndex := mkFI {
  fi_path  : FilePath;
  fi_table : NodeTable.table NodeMeta;
  fi_count : positive           (* number of occurrences = last local id; ids are [1 .. fi_count] *)
}.

Definition build_file (f : TFile) : FileIndex :=
  let '(t1, nx) := build_seq build_decl root_id 0 (Pos.succ root_id) (tf_decls f) NodeTable.empty in
  let cnt := Pos.pred nx in
  mkFI (tf_path f) (NodeTable.set root_id (mkMeta KFile None RFileRoot cnt) t1) cnt.

(* ================================================================================================= *)
(** ** C0A source snapshot: path-unique file lookup, hidden per-file slots, and a slot-keyed outer table. *)
(* ================================================================================================= *)

(* total extraction from a provably-present option — the key to a total validated-reference API. *)
Definition option_get {A} (o : option A) : o <> None -> A :=
  match o with Some a => fun _ => a | None => fun H => False_rect A (H eq_refl) end.
Lemma option_get_eq {A} (o : option A) (H : o <> None) (a : A) : o = Some a -> option_get o H = a.
Proof. intros Heq. subst o. reflexivity. Qed.

(* the file occupying a 1-based slot in the snapshot; slots are the hidden structural handle. *)
Definition forest_file_at (fs : TForest) (slot : positive) : option TFile :=
  nth_error (forest_files fs) (Nat.pred (Pos.to_nat slot)).

(* path -> (slot, file), scanning the file list ONCE (this is the raw-key minting boundary, §7). *)
Fixpoint find_slot (files : list TFile) (fp : FilePath) (slot : positive) : option (positive * TFile) :=
  match files with
  | [] => None
  | f :: rest => if fp_eqb (tf_path f) fp then Some (slot, f) else find_slot rest fp (Pos.succ slot)
  end.
Definition forest_find (fs : TForest) (fp : FilePath) : option (positive * TFile) :=
  find_slot (forest_files fs) fp 1.

(* the outer index: an abstract [NodeTable] keyed by the hidden slot, each entry the built per-file index.
   Navigation from a NodeRef reaches its file's index by ONE slot lookup here — no file-list scan. *)
Fixpoint build_outer (files : list TFile) (slot : positive) (t : NodeTable.table FileIndex)
  : NodeTable.table FileIndex :=
  match files with
  | [] => t
  | f :: rest => build_outer rest (Pos.succ slot) (NodeTable.set slot (build_file f) t)
  end.
Definition outer_of (fs : TForest) : NodeTable.table FileIndex :=
  build_outer (forest_files fs) 1 NodeTable.empty.

(* the outer builder only writes slots >= start, so it preserves any lookup strictly below start. *)
Lemma build_outer_below : forall files start slot t,
  (slot < start)%positive -> NodeTable.get slot (build_outer files start t) = NodeTable.get slot t.
Proof.
  induction files as [|f rest IH]; intros start slot t Hlt; simpl; [reflexivity|].
  rewrite IH by lia. apply NodeTable.get_set_other. lia.
Qed.

(* outer correspondence: slot [start + i] holds the build of the i-th file, else the base table. *)
Lemma build_outer_get : forall files start slot t,
  (start <= slot)%positive ->
  match nth_error files (Pos.to_nat slot - Pos.to_nat start)%nat with
  | Some f => NodeTable.get slot (build_outer files start t) = Some (build_file f)
  | None   => NodeTable.get slot (build_outer files start t) = NodeTable.get slot t
  end.
Proof.
  induction files as [|f rest IH]; intros start slot t Hle; simpl.
  - destruct (Pos.to_nat slot - Pos.to_nat start)%nat; reflexivity.
  - destruct (Pos.eq_dec slot start) as [Heq|Hne].
    + subst slot.
      replace (Pos.to_nat start - Pos.to_nat start)%nat with 0%nat by lia. simpl.
      rewrite build_outer_below by lia. apply NodeTable.get_set_same.
    + assert (Hlt : (start < slot)%positive) by lia.
      assert (Hstep : (Pos.to_nat slot - Pos.to_nat start = S (Pos.to_nat slot - Pos.to_nat (Pos.succ start)))%nat)
        by (rewrite Pos2Nat.inj_succ; lia).
      rewrite Hstep. simpl.
      specialize (IH (Pos.succ start) slot (NodeTable.set start (build_file f) t) ltac:(lia)).
      destruct (nth_error rest (Pos.to_nat slot - Pos.to_nat (Pos.succ start))%nat) eqn:Hnth.
      * exact IH.
      * rewrite IH. apply NodeTable.get_set_other. lia.
Qed.

(* the fact ref_meta needs: a real slot holds exactly the build of the file at that slot. *)
Lemma outer_get_at : forall fs slot f,
  forest_file_at fs slot = Some f -> NodeTable.get slot (outer_of fs) = Some (build_file f).
Proof.
  intros fs slot f Hat. unfold outer_of, forest_file_at in *.
  assert (Hle : (1 <= slot)%positive) by lia.
  pose proof (build_outer_get (forest_files fs) 1 slot NodeTable.empty Hle) as HG.
  replace (Pos.to_nat slot - Pos.to_nat 1)%nat with (Nat.pred (Pos.to_nat slot)) in HG
    by (change (Pos.to_nat 1) with 1%nat; lia).
  rewrite Hat in HG. exact HG.
Qed.

(* ================================================================================================= *)
(** ** Occurrence keys and snapshot-validated references (Master Plan 4.2 / 4.3).                      *)
(* ================================================================================================= *)

Record NodeKey := mkKey { nk_file : FilePath ; nk_local : positive }.

Definition nodekey_eqb (a b : NodeKey) : bool :=
  fp_eqb (nk_file a) (nk_file b) && Pos.eqb (nk_local a) (nk_local b).

(* (The source-indexed reference layer + total navigation is built LATE — after the per-file builder
   correctness proofs it depends on — in the sealed [Snap] module near the end of this file.) *)

(* preorder-interval ancestry: O(1) arithmetic on [subtree_end] after one trie lookup (theorem 13). *)
Definition parent_id (t : NodeTable.table NodeMeta) (c : positive) : option positive :=
  match NodeTable.get c t with Some m => nm_parent m | None => None end.

Inductive Ancestor (t : NodeTable.table NodeMeta) : positive -> positive -> Prop :=
| Anc_dir  : forall a c, parent_id t c = Some a -> Ancestor t a c
| Anc_step : forall a p c, Ancestor t a p -> parent_id t c = Some p -> Ancestor t a c.

Definition is_ancestor_local (t : NodeTable.table NodeMeta) (a d : positive) : bool :=
  match NodeTable.get a t with
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

(* direct children by INTERVAL JUMP (Master Plan 4.8/4.10): the cursor walks DIRECTLY from the first child
   to the parent's interval end, looking up ONLY the id at the cursor and, after each node, jumping the cursor
   PAST its whole subtree to [subtree_end+1] — it never constructs or traverses the skipped descendant ids.
   So both the lookup count AND the number of recursive steps are O(#direct children), not O(#descendants).
   Totality is by the decreasing measure [limit+1 - cursor] (no fuel); the jump takes [max (cursor+1) …] so
   the measure strictly decreases even on a malformed table, and equals [subtree_end+1] on a built one. *)
Function child_enum (t : NodeTable.table NodeMeta) (pid limit cursor : positive)
    {measure (fun c => (S (Pos.to_nat limit) - Pos.to_nat c)%nat) cursor} : list positive :=
  if Pos.leb cursor limit then
    match NodeTable.get cursor t with
    | Some mc =>
        let next := Pos.max (Pos.succ cursor) (Pos.succ (nm_subtree_end mc)) in
        match nm_parent mc with
        | Some p => if Pos.eqb p pid then cursor :: child_enum t pid limit next else child_enum t pid limit next
        | None   => child_enum t pid limit next
        end
    | None => []
    end
  else [].
Proof.
  all: intros;
    repeat match goal with H : Pos.leb _ _ = true |- _ =>
             apply Pos.leb_le in H; apply Pos2Nat.inj_le in H end;
    match goal with |- context [Pos.max (Pos.succ ?a) (Pos.succ ?b)] =>
      pose proof (Pos.le_max_l (Pos.succ a) (Pos.succ b)) as Hm end;
    apply Pos2Nat.inj_le in Hm; rewrite Pos2Nat.inj_succ in Hm; lia.
Defined.

Definition child_ids (t : NodeTable.table NodeMeta) (pid : positive) : list positive :=
  match NodeTable.get pid t with
  | Some m => child_enum t pid (nm_subtree_end m) (Pos.succ pid)
  | None => []
  end.

(* ================================================================================================= *)
(** ** Structural invariants of the built index (the foundation for the C0.4 theorem set).             *)
(*    A [SubtreeWF] describes one occurrence's subtree, laid out over a contiguous preorder interval    *)
(*    [me .. se]; a [ForestWF] describes a run of sibling subtrees over [lo .. nx) with a common parent *)
(*    [P].  [Fresh t from] says the trie holds nothing at or above [from], so each builder writes only  *)
(*    strictly fresh ids (no clobber) — this is what makes ancestry monotone under table growth.        *)
(* ================================================================================================= *)

Definition Fresh (t : NodeTable.table NodeMeta) (from : positive) : Prop :=
  forall k, (from <= k)%positive -> NodeTable.get k t = None.

Record SubtreeWF (t0 t : NodeTable.table NodeMeta) (oP : option positive) (me se : positive) : Prop := {
  sub_le    : (me <= se)%positive;
  sub_out   : forall k, (k < me)%positive \/ (se < k)%positive -> NodeTable.get k t = NodeTable.get k t0;
  sub_root  : exists m, NodeTable.get me t = Some m /\ nm_parent m = oP /\ nm_subtree_end m = se;
  sub_pres  : forall k, (me <= k)%positive -> (k <= se)%positive -> NodeTable.get k t <> None;
  sub_nest  : forall k m, (me <= k)%positive -> (k <= se)%positive -> NodeTable.get k t = Some m ->
                (k <= nm_subtree_end m)%positive /\ (nm_subtree_end m <= se)%positive;
  sub_prng  : forall k m, (me < k)%positive -> (k <= se)%positive -> NodeTable.get k t = Some m ->
                exists p mp, nm_parent m = Some p /\ NodeTable.get p t = Some mp /\
                  (me <= p)%positive /\ (p < k)%positive /\
                  (k <= nm_subtree_end mp)%positive /\ (nm_subtree_end m <= nm_subtree_end mp)%positive;
  sub_snd   : forall a k ma, (me <= a)%positive -> (a <= se)%positive -> NodeTable.get a t = Some ma ->
                (a < k)%positive -> (k <= nm_subtree_end ma)%positive -> Ancestor t a k
}.

Arguments sub_le   {_ _ _ _ _}.
Arguments sub_out  {_ _ _ _ _}.
Arguments sub_root {_ _ _ _ _}.
Arguments sub_pres {_ _ _ _ _}.
Arguments sub_nest {_ _ _ _ _}.
Arguments sub_prng {_ _ _ _ _}.
Arguments sub_snd  {_ _ _ _ _}.

Record ForestWF (t0 t : NodeTable.table NodeMeta) (P lo nx : positive) : Prop := {
  for_le   : (lo <= nx)%positive;
  for_out  : forall k, (k < lo)%positive \/ (nx <= k)%positive -> NodeTable.get k t = NodeTable.get k t0;
  for_pres : forall k, (lo <= k)%positive -> (k < nx)%positive -> NodeTable.get k t <> None;
  for_nest : forall k m, (lo <= k)%positive -> (k < nx)%positive -> NodeTable.get k t = Some m ->
               (k <= nm_subtree_end m)%positive /\ (nm_subtree_end m < nx)%positive;
  for_prng : forall k m, (lo <= k)%positive -> (k < nx)%positive -> NodeTable.get k t = Some m ->
               exists p, nm_parent m = Some p /\
                 (p = P \/ ((lo <= p)%positive /\ (p < k)%positive /\
                            exists mp, NodeTable.get p t = Some mp /\
                              (k <= nm_subtree_end mp)%positive /\ (nm_subtree_end m <= nm_subtree_end mp)%positive));
  for_snd  : forall a k ma, (lo <= a)%positive -> (a < nx)%positive -> NodeTable.get a t = Some ma ->
               (a < k)%positive -> (k <= nm_subtree_end ma)%positive -> Ancestor t a k
}.

Arguments for_le   {_ _ _ _ _}.
Arguments for_out  {_ _ _ _ _}.
Arguments for_pres {_ _ _ _ _}.
Arguments for_nest {_ _ _ _ _}.
Arguments for_prng {_ _ _ _ _}.
Arguments for_snd  {_ _ _ _ _}.

(* ancestry only reads parent links at present ids, so it survives any table growth that preserves them. *)
Lemma ancestor_mono (t t' : NodeTable.table NodeMeta) :
  (forall j m, NodeTable.get j t = Some m -> NodeTable.get j t' = Some m) ->
  forall a c, Ancestor t a c -> Ancestor t' a c.
Proof.
  intros Hmono a c H; induction H as [a c Hp | a p c Hac IH Hp].
  - apply Anc_dir. unfold parent_id in *. destruct (NodeTable.get c t) as [m|] eqn:E; try discriminate.
    rewrite (Hmono _ _ E). exact Hp.
  - eapply Anc_step; [exact IH|].
    unfold parent_id in *. destruct (NodeTable.get c t) as [m|] eqn:E; try discriminate.
    rewrite (Hmono _ _ E). exact Hp.
Qed.

(* the empty sibling run. *)
Lemma forest_nil (t : NodeTable.table NodeMeta) P lo : ForestWF t t P lo lo.
Proof. constructor; intros; solve [ lia | reflexivity | exfalso; lia ]. Qed.

Local Open Scope positive_scope.

(* a wrapped node's fresh id preserves every existing entry of its children table. *)
Lemma set_mono (tf : NodeTable.table NodeMeta) me meta :
  NodeTable.get me tf = None -> forall j m, NodeTable.get j tf = Some m -> NodeTable.get j (NodeTable.set me meta tf) = Some m.
Proof.
  intros Hfresh j m Hj. destruct (Pos.eq_dec j me) as [->|Hne].
  - rewrite Hfresh in Hj; discriminate.
  - rewrite NodeTable.get_set_other by congruence. exact Hj.
Qed.

(* every id strictly inside a wrapped node's interval descends from the wrapped node. *)
Lemma wrap_root_sound (t0 tf : NodeTable.table NodeMeta) me nx meta :
  Fresh t0 me ->
  ForestWF t0 tf me (Pos.succ me) nx ->
  NodeTable.get me tf = None ->
  forall k, me < k -> k < nx ->
    Ancestor (NodeTable.set me meta tf) me k.
Proof.
  intros Hf0 HF Hfresh k.
  induction k as [k IHk] using (well_founded_induction (well_founded_ltof _ (fun p : positive => Pos.to_nat p))).
  intros Hmk Hkx.
  set (t := NodeTable.set me meta tf).
  assert (Hget : NodeTable.get k t = NodeTable.get k tf).
  { unfold t; rewrite NodeTable.get_set_other by lia; reflexivity. }
  destruct (NodeTable.get k tf) as [m|] eqn:Em.
  2:{ exfalso. exact (for_pres HF k ltac:(lia) Hkx Em). }
  destruct (for_prng HF k m ltac:(lia) Hkx Em) as [p [Hpar Hcase]].
  assert (Hpid : parent_id t k = Some p).
  { unfold parent_id, t. rewrite NodeTable.get_set_other by lia. rewrite Em. exact Hpar. }
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
Lemma subtree_from_forest (t0 tf : NodeTable.table NodeMeta) oP me se nx meta :
  nx = Pos.succ se ->
  Fresh t0 me ->
  ForestWF t0 tf me (Pos.succ me) nx ->
  Fresh tf nx ->
  nm_parent meta = oP ->
  nm_subtree_end meta = se ->
  Fresh (NodeTable.set me meta tf) nx /\ SubtreeWF t0 (NodeTable.set me meta tf) oP me se.
Proof.
  intros Hnx Hf0 HF Hff Hpar Hend.
  assert (Hmse : me <= se) by (generalize (for_le HF); lia).
  assert (Hfresh_me : NodeTable.get me tf = None).
  { rewrite (for_out HF me) by lia. apply Hf0; lia. }
  set (t := NodeTable.set me meta tf).
  (* NodeTable.get on t: me -> meta, else -> tf *)
  assert (Hget_me : NodeTable.get me t = Some meta) by (unfold t; apply NodeTable.get_set_same).
  assert (Hget_ne : forall k, k <> me -> NodeTable.get k t = NodeTable.get k tf) by (intros; unfold t; apply NodeTable.get_set_other; congruence).
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
      * (* a in children : lift children soundness through NodeTable.set me *)
        rewrite Hget_ne in Hget_a by exact Hne.
        assert (Hmono : forall j mm, NodeTable.get j tf = Some mm -> NodeTable.get j t = Some mm)
          by (intros; unfold t; apply set_mono; assumption).
        eapply ancestor_mono; [exact Hmono|].
        eapply (for_snd HF); [lia|lia|exact Hget_a|exact Hak|exact Hkend].
Qed.

(* compose a subtree with the following sibling run (built afterwards on strictly larger, fresh ids). *)
Lemma forest_cons (t0 t1 t2 : NodeTable.table NodeMeta) P me se nx :
  SubtreeWF t0 t1 (Some P) me se ->
  Fresh t1 (Pos.succ se) ->
  ForestWF t1 t2 P (Pos.succ se) nx ->
  ForestWF t0 t2 P me nx.
Proof.
  intros HS Hf1 HF.
  assert (Hmse : me <= se) by (apply (sub_le HS)).
  assert (Hsx : Pos.succ se <= nx) by (apply (for_le HF)).
  (* monotonicity t1 -> t2 : every t1 entry sits below succ se, hence is preserved by the forest *)
  assert (Hmono : forall j m, NodeTable.get j t1 = Some m -> NodeTable.get j t2 = Some m).
  { intros j m Hj. destruct (Pos.ltb j (Pos.succ se)) eqn:Hlt.
    - apply Pos.ltb_lt in Hlt. rewrite (for_out HF j) by lia. exact Hj.
    - apply Pos.ltb_ge in Hlt. rewrite (Hf1 j) in Hj by lia. discriminate. }
  (* t2 outside [succ se, nx) equals t1; and t1 outside [me,se] equals t0 *)
  assert (Hout2 : forall k, k < Pos.succ se \/ nx <= k -> NodeTable.get k t2 = NodeTable.get k t1)
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

Lemma Fresh_weaken (t : NodeTable.table NodeMeta) from from' :
  from <= from' -> Fresh t from -> Fresh t from'.
Proof. intros H HF k Hk. apply HF. lia. Qed.

Lemma Fresh_empty (from : positive) : Fresh NodeTable.empty from.
Proof. intros k _; apply NodeTable.get_empty. Qed.

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
  (bx : positive -> nat -> positive -> X -> NodeTable.table NodeMeta -> NodeTable.table NodeMeta * positive) :
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
  assert (H : Fresh (NodeTable.set me (mkMeta KDecl (Some parent) (RFileDecl didx) (Pos.pred nx1)) t1) nx1 /\
              SubtreeWF t0 (NodeTable.set me (mkMeta KDecl (Some parent) (RFileDecl didx) (Pos.pred nx1)) t1)
                        (Some parent) me (Pos.pred nx1)).
  { eapply subtree_from_forest;
      [ symmetry; exact Hnx | exact Hf0 | exact HF1 | exact Hfr1 | reflexivity | reflexivity ]. }
  rewrite Hnx. exact H.
Qed.

Lemma build_file_wf (f : TFile) :
  SubtreeWF NodeTable.empty (fi_table (build_file f)) None root_id (fi_count (build_file f)).
Proof.
  unfold build_file.
  destruct (build_seq build_decl root_id 0 (Pos.succ root_id) (tf_decls f) NodeTable.empty) as [t1 nx] eqn:E.
  simpl.
  destruct (build_seq_spec build_decl build_decl_spec (tf_decls f) root_id 0 (Pos.succ root_id)
              NodeTable.empty t1 nx (Fresh_empty _) E) as [Hfr HF].
  assert (Hge : Pos.succ root_id <= nx) by (apply (for_le HF)).
  assert (Hnx : Pos.succ (Pos.pred nx) = nx)
    by (destruct (Pos.succ_pred_or nx) as [->|H]; [exfalso; lia | exact H]).
  assert (H : Fresh (NodeTable.set root_id (mkMeta KFile None RFileRoot (Pos.pred nx)) t1) nx /\
              SubtreeWF NodeTable.empty (NodeTable.set root_id (mkMeta KFile None RFileRoot (Pos.pred nx)) t1)
                        None root_id (Pos.pred nx)).
  { eapply subtree_from_forest;
      [ symmetry; exact Hnx | apply Fresh_empty | exact HF | exact Hfr | reflexivity | reflexivity ]. }
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

(* ================================================================================================= *)
(** ** The C0.4 required theorem set (over the built single-file index; instance #9 over a witness).   *)
(* ================================================================================================= *)

(* every entry of a built file table lies in the canonical interval [root_id .. count]. *)
Lemma in_domain (f : TFile) k m :
  NodeTable.get k (fi_table (build_file f)) = Some m ->
  root_id <= k /\ k <= fi_count (build_file f).
Proof.
  intros H. pose proof (build_file_wf f) as WF. split.
  - destruct (Pos.leb root_id k) eqn:E; [apply Pos.leb_le; exact E|].
    apply Pos.leb_gt in E. rewrite (sub_out WF k) in H by (left; lia).
    rewrite NodeTable.get_empty in H; discriminate.
  - destruct (Pos.leb k (fi_count (build_file f))) eqn:E; [apply Pos.leb_le; exact E|].
    apply Pos.leb_gt in E. rewrite (sub_out WF k) in H by (right; lia).
    rewrite NodeTable.get_empty in H; discriminate.
Qed.

(* THEOREM 1 — the root id is canonical: every file root occupies the SAME fixed local id [root_id]. *)
Theorem thm1_root_id_canonical (f : TFile) :
  exists m, NodeTable.get root_id (fi_table (build_file f)) = Some m /\ nm_kind m = KFile /\ nm_role m = RFileRoot.
Proof.
  unfold build_file.
  destruct (build_seq build_decl root_id 0 (Pos.succ root_id) (tf_decls f) NodeTable.empty) as [t1 nx] eqn:E.
  exists (mkMeta KFile None RFileRoot (Pos.pred nx)).
  cbn [fi_table]. rewrite NodeTable.get_set_same. split; [reflexivity | split; reflexivity].
Qed.

(* THEOREM 2 — the root has no parent. *)
Theorem thm2_root_no_parent (f : TFile) m :
  NodeTable.get root_id (fi_table (build_file f)) = Some m -> nm_parent m = None.
Proof.
  intros H. pose proof (build_file_wf f) as WF. destruct (sub_root WF) as [m0 [Hg [Hp _]]].
  rewrite Hg in H. injection H as <-. exact Hp.
Qed.

(* THEOREM 3 — every non-root occurrence has exactly one parent. *)
Theorem thm3_nonroot_has_parent (f : TFile) k m :
  NodeTable.get k (fi_table (build_file f)) = Some m -> k <> root_id -> exists p, nm_parent m = Some p.
Proof.
  intros H Hne. pose proof (build_file_wf f) as WF.
  destruct (in_domain f k m H) as [Hlo Hhi].
  assert (root_id < k) by lia.
  destruct (sub_prng WF k m ltac:(lia) Hhi H) as [p [mp [Hpar _]]]. exists p; exact Hpar.
Qed.

(* the parent field is functional: an occurrence has at most one parent. *)
Theorem thm3b_parent_unique (f : TFile) k m p1 p2 :
  NodeTable.get k (fi_table (build_file f)) = Some m -> nm_parent m = Some p1 -> nm_parent m = Some p2 -> p1 = p2.
Proof. intros _ H1 H2. rewrite H1 in H2. injection H2 as <-. reflexivity. Qed.

(* THEOREM 13 (completeness half) — ancestry implies nested preorder intervals. *)
Lemma anc_complete (f : TFile) a d :
  Ancestor (fi_table (build_file f)) a d ->
  exists ma md, NodeTable.get a (fi_table (build_file f)) = Some ma /\
                NodeTable.get d (fi_table (build_file f)) = Some md /\
                a < d /\ d <= nm_subtree_end ma /\ nm_subtree_end md <= nm_subtree_end ma.
Proof.
  pose proof (build_file_wf f) as WF.
  set (t := fi_table (build_file f)) in *.
  induction 1 as [a d Hp | a p c Hac IH Hp].
  - (* Anc_dir : d's parent is a *)
    unfold parent_id in Hp. destruct (NodeTable.get d t) as [md|] eqn:Ed; [|discriminate].
    destruct (in_domain f d md Ed) as [Hlo Hhi].
    assert (Hdne : d <> root_id).
    { intro; subst d. destruct (sub_root WF) as [m0 [Hg [Hp0 _]]]. rewrite Hg in Ed; injection Ed as <-.
      rewrite Hp0 in Hp; discriminate. }
    destruct (sub_prng WF d md ltac:(lia) Hhi Ed) as [p [mp [Hpar [Hmp [Hle1 [Hlt1 [Hb1 Hb2]]]]]]].
    rewrite Hp in Hpar. injection Hpar as <-.
    exists mp, md. repeat split; try assumption; lia.
  - (* Anc_step : c's parent is p, and a is an ancestor of p *)
    unfold parent_id in Hp. destruct (NodeTable.get c t) as [mc|] eqn:Ec; [|discriminate].
    destruct IH as [ma [mp0 [Hga [Hgp [Hap [Hpend Hmpend]]]]]].
    destruct (in_domain f c mc Ec) as [Hlo Hhi].
    assert (Hcne : c <> root_id).
    { intro; subst c. destruct (sub_root WF) as [m0 [Hg [Hp0 _]]]. rewrite Hg in Ec; injection Ec as <-.
      rewrite Hp0 in Hp; discriminate. }
    destruct (sub_prng WF c mc ltac:(lia) Hhi Ec) as [p' [mp' [Hpar [Hmp' [Hle1 [Hlt1 [Hb1 Hb2]]]]]]].
    rewrite Hp in Hpar. injection Hpar as <-. rewrite Hgp in Hmp'. injection Hmp' as <-.
    exists ma, mc. repeat split; try assumption; lia.
Qed.

(* ================================================================================================= *)
(** ** Interval-jump child enumeration is correct (the tiling of a node's interval by its children).   *)
(* ================================================================================================= *)

Definition parentb (t : NodeTable.table NodeMeta) (c pid : positive) : bool :=
  match NodeTable.get c t with
  | Some mc => match nm_parent mc with Some p => Pos.eqb p pid | None => false end
  | None => false
  end.

(* a descendant's immediate parent never precedes its ancestor. *)
Lemma anc_parent_ge (f : TFile) a d p :
  Ancestor (fi_table (build_file f)) a d ->
  parent_id (fi_table (build_file f)) d = Some p -> (a <= p)%positive.
Proof.
  intros Hanc Hp. inversion Hanc; subst.
  - rewrite H in Hp. injection Hp as <-. lia.
  - rewrite H0 in Hp. injection Hp as <-.
    destruct (anc_complete f a _ H) as [ma [md [_ [_ [Hlt _]]]]]. lia.
Qed.

(* every id strictly inside a node's preorder interval has that node as an ancestor, so its parent is at
   least that node — the interval interior contains no id whose parent lies before the node. *)
Lemma desc_parent_ge (f : TFile) a ma d p :
  NodeTable.get a (fi_table (build_file f)) = Some ma ->
  (a < d)%positive -> (d <= nm_subtree_end ma)%positive ->
  parent_id (fi_table (build_file f)) d = Some p -> (a <= p)%positive.
Proof.
  intros Ha Hlt Hle Hp. pose proof (build_file_wf f) as WF.
  destruct (in_domain f a ma Ha) as [Hlo Hhi].
  eapply anc_parent_ge; [ eapply (sub_snd WF a d ma); [lia|lia|exact Ha|exact Hlt|exact Hle] | exact Hp ].
Qed.

(* a pid-child is a proper descendant of pid: pid < c and c is present. *)
Lemma child_gt (f : TFile) pid c mc :
  NodeTable.get c (fi_table (build_file f)) = Some mc -> nm_parent mc = Some pid ->
  (pid < c)%positive.
Proof.
  intros Hc Hpar. pose proof (build_file_wf f) as WF.
  destruct (in_domain f c mc Hc) as [Hlo Hhi].
  assert (Hcne : c <> root_id).
  { intro; subst c. destruct (sub_root WF) as [m0 [Hg [Hp0 _]]]. rewrite Hg in Hc; injection Hc as <-.
    rewrite Hp0 in Hpar; discriminate. }
  destruct (sub_prng WF c mc ltac:(lia) Hhi Hc) as [p' [mp' [Hpar' [_ [_ [Hltp' _]]]]]].
  rewrite Hpar in Hpar'. injection Hpar' as <-. exact Hltp'.
Qed.

(* the FIRST descendant of a node is its child: parent(node+1) = node. *)
Lemma first_child (f : TFile) pid mp :
  NodeTable.get pid (fi_table (build_file f)) = Some mp ->
  (pid < nm_subtree_end mp)%positive ->
  parent_id (fi_table (build_file f)) (Pos.succ pid) = Some pid.
Proof.
  intros Hpid Hlt. pose proof (build_file_wf f) as WF.
  destruct (in_domain f pid mp Hpid) as [Hlo Hhi].
  destruct (sub_nest WF pid mp Hlo Hhi Hpid) as [_ Hmpcnt].
  assert (Hpres : NodeTable.get (Pos.succ pid) (fi_table (build_file f)) <> None)
    by (eapply (sub_pres WF (Pos.succ pid)); lia).
  destruct (NodeTable.get (Pos.succ pid) (fi_table (build_file f))) as [m1|] eqn:E1; [|contradiction].
  destruct (sub_prng WF (Pos.succ pid) m1 ltac:(lia) ltac:(lia) E1) as [p [mp2 [Hpar [_ [_ [Hltp _]]]]]].
  assert (Hpge : (pid <= p)%positive)
    by (eapply (desc_parent_ge f pid mp (Pos.succ pid) p Hpid); [lia|lia|unfold parent_id; rewrite E1; exact Hpar]).
  unfold parent_id. rewrite E1. rewrite Hpar. f_equal. lia.
Qed.

(* the id just past a child's subtree, if still inside the parent's interval, is the NEXT child. *)
Lemma next_child (f : TFile) pid mp c mc :
  NodeTable.get pid (fi_table (build_file f)) = Some mp ->
  NodeTable.get c (fi_table (build_file f)) = Some mc -> nm_parent mc = Some pid ->
  (nm_subtree_end mc < nm_subtree_end mp)%positive ->
  parent_id (fi_table (build_file f)) (Pos.succ (nm_subtree_end mc)) = Some pid.
Proof.
  intros Hpid Hc Hpar HEc. pose proof (build_file_wf f) as WF.
  pose proof (child_gt f pid c mc Hc Hpar) as Hpc.
  destruct (in_domain f pid mp Hpid) as [Hlo_pid Hhi_pid].
  destruct (in_domain f c mc Hc) as [Hlo_c Hhi_c].
  destruct (sub_nest WF c mc ltac:(lia) Hhi_c Hc) as [Hc_le _].
  destruct (sub_nest WF pid mp Hlo_pid Hhi_pid Hpid) as [_ Hmpcnt].
  set (d := Pos.succ (nm_subtree_end mc)).
  assert (Hd1 : (pid < d)%positive) by (unfold d; lia).
  assert (Hd2 : (d <= nm_subtree_end mp)%positive) by (unfold d; lia).
  assert (Hpres : NodeTable.get d (fi_table (build_file f)) <> None) by (eapply (sub_pres WF d); lia).
  destruct (NodeTable.get d (fi_table (build_file f))) as [md|] eqn:Ed; [|contradiction].
  destruct (sub_prng WF d md ltac:(lia) ltac:(lia) Ed) as [p [mpp [Hparp [Hgetp [_ [Hltp [Hb1 _]]]]]]].
  (* Hb1 : d <= subtree_end mpp — d is within its own parent p's subtree *)
  assert (Hpge : (pid <= p)%positive)
    by (eapply (desc_parent_ge f pid mp d p Hpid); [lia|lia|unfold parent_id; rewrite Ed; exact Hparp]).
  destruct (in_domain f p mpp Hgetp) as [Hlop Hhip].
  (* p in [pid, subtree_end mc]; show p = pid by excluding p in cur's subtree and p in (pid, c) *)
  assert (Hp_eq : p = pid).
  { destruct (Pos.eq_dec p pid) as [->|Hne]; [reflexivity|]. exfalso.
    assert (Hpgt : (pid < p)%positive) by lia.
    destruct (Pos.leb c p) eqn:Hcp.
    - (* c <= p <= subtree_end mc : p in cur's subtree, so subtree_end p <= subtree_end mc < d <= subtree_end p *)
      apply Pos.leb_le in Hcp.
      assert (Hpsub : (nm_subtree_end mpp <= nm_subtree_end mc)%positive).
      { destruct (Pos.eq_dec p c) as [->|Hpc2].
        - rewrite Hgetp in Hc. injection Hc as <-. lia.
        - destruct (anc_complete f c p (sub_snd WF c p mc ltac:(lia) Hhi_c Hc ltac:(lia) ltac:(lia)))
            as [mc' [mpp' [Hgc [Hgp [_ [_ Hend]]]]]].
          rewrite Hc in Hgc; injection Hgc as <-. rewrite Hgetp in Hgp; injection Hgp as <-. lia. }
      unfold d in Hb1. lia.
    - (* p < c : c is a descendant of p, so parent(c)=pid >= p, contradicting p > pid *)
      apply Pos.leb_gt in Hcp.
      assert (Hcanc : Ancestor (fi_table (build_file f)) p c).
      { eapply (sub_snd WF p c mpp); [lia|exact Hhip|exact Hgetp|lia|]. unfold d in Hb1. lia. }
      assert (p <= pid)%positive by (eapply anc_parent_ge; [exact Hcanc | unfold parent_id; rewrite Hc; exact Hpar]).
      lia. }
  unfold parent_id. rewrite Ed. rewrite Hparp. rewrite Hp_eq. reflexivity.
Qed.

(* the interior of a child's subtree contains no further child of the same parent. *)
Lemma interior_not_child (f : TFile) pid cur mcur k :
  NodeTable.get cur (fi_table (build_file f)) = Some mcur -> nm_parent mcur = Some pid ->
  (cur < k)%positive -> (k <= nm_subtree_end mcur)%positive ->
  parentb (fi_table (build_file f)) k pid = false.
Proof.
  intros Hcur Hpar Hlt Hle. pose proof (child_gt f pid cur mcur Hcur Hpar) as Hpc.
  unfold parentb. destruct (NodeTable.get k (fi_table (build_file f))) as [mk|] eqn:Ek; [|reflexivity].
  destruct (nm_parent mk) as [q|] eqn:Eq; [|reflexivity].
  assert (cur <= q)%positive
    by (eapply (desc_parent_ge f cur mcur k q Hcur); [lia|lia|unfold parent_id; rewrite Ek; exact Eq]).
  destruct (Pos.eqb q pid) eqn:Eqp; [apply Pos.eqb_eq in Eqp; lia | reflexivity].
Qed.

(* --- child_enum correctness --- *)

(* every present id in the built table has [id <= subtree_end]. *)
Lemma built_nested (f : TFile) x mx :
  NodeTable.get x (fi_table (build_file f)) = Some mx -> (x <= nm_subtree_end mx)%positive.
Proof.
  intros Hx. pose proof (build_file_wf f) as WF. destruct (in_domain f x mx Hx) as [Hlo Hhi].
  destruct (sub_nest WF x mx Hlo Hhi Hx) as [A _]. exact A.
Qed.

(* soundness: every enumerated id truly has parent [pid]. *)
Lemma child_enum_sound : forall t pid limit cursor c,
  In c (child_enum t pid limit cursor) -> parent_id t c = Some pid.
Proof.
  intros t pid limit cursor c.
  functional induction (child_enum t pid limit cursor); intros Hin;
    try (exfalso; exact Hin); try (exact (IHl Hin)).
  apply in_inv in Hin. destruct Hin as [Heq|Hin]; [|exact (IHl Hin)].
  subst c. unfold parent_id. rewrite e0. cbn. rewrite e1. apply Pos.eqb_eq in e2. rewrite e2. reflexivity.
Qed.

(* every enumerated id is >= the cursor (the jump only moves forward). *)
Lemma child_enum_ge : forall t pid limit cursor c,
  In c (child_enum t pid limit cursor) -> (cursor <= c)%positive.
Proof.
  intros t pid limit cursor c.
  functional induction (child_enum t pid limit cursor); intros Hin; try (exfalso; exact Hin);
    pose proof (Pos.le_max_l (Pos.succ cursor) (Pos.succ (nm_subtree_end mc))) as Hm.
  - apply in_inv in Hin. destruct Hin as [Heq|Hin]; [subst c; lia|]. apply IHl in Hin. lia.
  - apply IHl in Hin. lia.
  - apply IHl in Hin. lia.
Qed.

(* the enumerated children are strictly increasing (source order). *)
Lemma child_enum_SS : forall t pid limit cursor,
  StronglySorted Pos.lt (child_enum t pid limit cursor).
Proof.
  intros t pid limit cursor.
  functional induction (child_enum t pid limit cursor); try (solve [constructor]); try exact IHl.
  constructor; [exact IHl|].
  apply Forall_forall. intros y Hy. apply child_enum_ge in Hy.
  pose proof (Pos.le_max_l (Pos.succ cursor) (Pos.succ (nm_subtree_end mc))). lia.
Qed.

(* completeness: the jump reaches every child; strong induction on the interval size above the cursor. *)
Lemma child_enum_reaches : forall N f pid mp cur mcur c mc,
  NodeTable.get pid (fi_table (build_file f)) = Some mp ->
  NodeTable.get cur (fi_table (build_file f)) = Some mcur -> nm_parent mcur = Some pid ->
  NodeTable.get c  (fi_table (build_file f)) = Some mc  -> nm_parent mc  = Some pid ->
  (cur <= c)%positive -> (c <= nm_subtree_end mp)%positive ->
  N = (S (Pos.to_nat (nm_subtree_end mp)) - Pos.to_nat cur)%nat ->
  In c (child_enum (fi_table (build_file f)) pid (nm_subtree_end mp) cur).
Proof.
  induction N as [N IH] using (well_founded_induction lt_wf).
  intros f pid mp cur mcur c mc Hpid Hcur Hpar Hc Hpc Hle Hcend HN.
  rewrite child_enum_equation.
  destruct (Pos.leb cur (nm_subtree_end mp)) eqn:Hleb; [|apply Pos.leb_gt in Hleb; exfalso; lia].
  rewrite Hcur. cbn iota beta zeta. rewrite Hpar. cbn iota beta zeta. rewrite Pos.eqb_refl.
  destruct (Pos.eq_dec c cur) as [->|Hcne]; [left; reflexivity|].
  right.
  assert (Hcurlt : (cur < c)%positive) by lia.
  (* c is not in cur's subtree: subtree_end mcur < c *)
  assert (HEcur : (nm_subtree_end mcur < c)%positive).
  { destruct (Pos.leb c (nm_subtree_end mcur)) eqn:Hb; [|apply Pos.leb_gt in Hb; lia].
    apply Pos.leb_le in Hb. exfalso.
    pose proof (interior_not_child f pid cur mcur c Hcur Hpar Hcurlt Hb) as Hnc.
    assert (parentb (fi_table (build_file f)) c pid = true)
      by (unfold parentb; rewrite Hc; cbn; rewrite Hpc; cbn; apply Pos.eqb_refl).
    congruence. }
  (* on the built table the jump target is succ(subtree_end mcur) *)
  assert (Hcur_le_Ecur : (cur <= nm_subtree_end mcur)%positive) by (apply built_nested in Hcur; exact Hcur).
  rewrite (Pos.max_r (Pos.succ cur) (Pos.succ (nm_subtree_end mcur))) by lia.
  assert (HEcE : (nm_subtree_end mcur < nm_subtree_end mp)%positive) by lia.
  pose proof (next_child f pid mp cur mcur Hpid Hcur Hpar HEcE) as Hnext. unfold parent_id in Hnext.
  destruct (NodeTable.get (Pos.succ (nm_subtree_end mcur)) (fi_table (build_file f))) as [mnc|] eqn:Enc;
    [|discriminate].
  eapply (IH (S (Pos.to_nat (nm_subtree_end mp)) - Pos.to_nat (Pos.succ (nm_subtree_end mcur)))%nat);
    [ rewrite HN, Pos2Nat.inj_succ;
      assert (Pos.to_nat cur <= Pos.to_nat (nm_subtree_end mcur))%nat by (apply Pos2Nat.inj_le; exact Hcur_le_Ecur);
      lia
    | exact Hpid | exact Enc | exact Hnext | exact Hc | exact Hpc | lia | exact Hcend | reflexivity ].
Qed.

(* THEOREM 13 — the O(1) preorder-interval ancestor test is sound AND complete. *)
Theorem thm13_interval_ancestry (f : TFile) a d :
  NodeTable.get a (fi_table (build_file f)) <> None ->
  (is_ancestor_local (fi_table (build_file f)) a d = true <-> Ancestor (fi_table (build_file f)) a d).
Proof.
  intros Ha. pose proof (build_file_wf f) as WF.
  set (t := fi_table (build_file f)) in *.
  unfold is_ancestor_local. destruct (NodeTable.get a t) as [ma|] eqn:Ea; [|congruence].
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
  unfold child_ids. destruct (NodeTable.get p (fi_table (build_file f))) as [m|] eqn:Ep; [|constructor].
  apply child_enum_SS.
Qed.

(* THEOREM 4 — parent/child are inverse: a direct child appears in the interval-jump [child_ids] of its
   parent, and everything the jump enumerates has that parent. *)
Theorem thm4_child_has_parent (f : TFile) p c :
  In c (child_ids (fi_table (build_file f)) p) -> parent_id (fi_table (build_file f)) c = Some p.
Proof.
  unfold child_ids. destruct (NodeTable.get p (fi_table (build_file f))) as [mp|] eqn:Ep; [|intros []].
  apply child_enum_sound.
Qed.

Theorem thm4_parent_has_child (f : TFile) p c mc :
  NodeTable.get c (fi_table (build_file f)) = Some mc -> nm_parent mc = Some p ->
  In c (child_ids (fi_table (build_file f)) p).
Proof.
  intros Hc Hpar. pose proof (build_file_wf f) as WF.
  pose proof (child_gt f p c mc Hc Hpar) as Hpc.
  (* p is present (it is c's parent) *)
  destruct (in_domain f c mc Hc) as [Hlo Hhi].
  assert (Hcne : c <> root_id)
    by (intro; subst c; destruct (sub_root WF) as [m0 [Hg [Hp0 _]]]; rewrite Hg in Hc; injection Hc as <-;
        rewrite Hp0 in Hpar; discriminate).
  destruct (sub_prng WF c mc ltac:(lia) Hhi Hc) as [p' [mp' [Hpar' [Hgp [_ [_ [Hcbound _]]]]]]].
  rewrite Hpar in Hpar'. injection Hpar' as <-.
  (* the first child p+1 exists (p < c <= subtree_end mp'), so the jump starts on a real child *)
  assert (HpE : (p < nm_subtree_end mp')%positive) by lia.
  pose proof (first_child f p mp' Hgp HpE) as Hfc. unfold parent_id in Hfc.
  destruct (NodeTable.get (Pos.succ p) (fi_table (build_file f))) as [m1|] eqn:E1; [|discriminate].
  unfold child_ids. rewrite Hgp.
  eapply (child_enum_reaches _ f p mp' (Pos.succ p) m1 c mc);
    [ exact Hgp | exact E1 | exact Hfc | exact Hc | exact Hpar | lia | exact Hcbound | reflexivity ].
Qed.

(* THEOREM 5 — parentage stays within one file (references carry the file, so the parent shares it). *)
Lemma fi_path_build (f : TFile) : fi_path (build_file f) = tf_path f.
Proof.
  unfold build_file.
  destruct (build_seq build_decl root_id 0 (Pos.succ root_id) (tf_decls f) NodeTable.empty) as [t1 nx].
  reflexivity.
Qed.

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
  NodeTable.get k (fi_table (build_file f)) = Some m -> In k (all_ids (build_file f)).
Proof.
  intros H. destruct (in_domain f k m H) as [Hlo Hhi]. unfold all_ids.
  apply pos_seq_In. unfold root_id. rewrite Pos2Nat.inj_1.
  assert (Pos.to_nat k <= Pos.to_nat (fi_count (build_file f)))%nat by (apply Pos2Nat.inj_le; exact Hhi).
  assert (1 <= Pos.to_nat k)%nat by (pose proof (Pos2Nat.is_pos k); lia).
  lia.
Qed.

Theorem thm7_enum_sound (f : TFile) k :
  In k (all_ids (build_file f)) -> NodeTable.get k (fi_table (build_file f)) <> None.
Proof.
  unfold all_ids. intros Hin. apply pos_seq_In in Hin. unfold root_id in Hin. rewrite Pos2Nat.inj_1 in Hin.
  pose proof (build_file_wf f) as WF. apply (sub_pres WF).
  - unfold root_id. apply Pos2Nat.inj_le. rewrite Pos2Nat.inj_1. lia.
  - apply Pos2Nat.inj_le. lia.
Qed.

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
(* --- source-occurrence recovery: a TABLE-FREE preorder numbering + the occurrence it addresses, proved
       to coincide with the builder's own id assignment (build_*_end / build_file_count).  This is what
       formally connects a local id back to the exact source occurrence the builder indexed there. --- *)

Fixpoint end_expr (me : positive) (e : TExpr) : positive :=
  match e with
  | TLeaf _  => me
  | TBin l r => end_expr (Pos.succ (end_expr (Pos.succ me) l)) r
  end.
Definition end_stmt (me : positive) (s : TStmt) : positive :=
  match s with TPrint e => end_expr (Pos.succ me) e end.
Fixpoint next_stmts (me : positive) (ss : list TStmt) : positive :=
  match ss with [] => me | s :: rest => next_stmts (Pos.succ (end_stmt me s)) rest end.
Definition end_decl (me : positive) (d : TDecl) : positive :=
  match d with TFun body => Pos.pred (next_stmts (Pos.succ me) body) end.
Fixpoint next_decls (me : positive) (ds : list TDecl) : positive :=
  match ds with [] => me | d :: rest => next_decls (Pos.succ (end_decl me d)) rest end.
Definition count_file (f : TFile) : positive := Pos.pred (next_decls (Pos.succ root_id) (tf_decls f)).

Lemma build_expr_end : forall e parent role me t,
  snd (build_expr parent role me e t) = end_expr me e.
Proof.
  induction e as [v|l IHl r IHr]; intros parent role me t; [reflexivity|].
  simpl. specialize (IHl me (RChild 0) (Pos.succ me) t).
  destruct (build_expr me (RChild 0) (Pos.succ me) l t) as [t1 e1]. simpl in IHl.
  specialize (IHr me (RChild 1) (Pos.succ e1) t1).
  destruct (build_expr me (RChild 1) (Pos.succ e1) r t1) as [t2 e2]. simpl in IHr.
  simpl. rewrite IHr, IHl. reflexivity.
Qed.

Lemma build_stmt_end : forall s parent i me t,
  snd (build_stmt parent i me s t) = end_stmt me s.
Proof.
  intros [e] parent i me t. simpl.
  rewrite <- (build_expr_end e me RStmtExpr (Pos.succ me) t).
  destruct (build_expr me RStmtExpr (Pos.succ me) e t) as [t1 e1]. reflexivity.
Qed.

Lemma build_seq_stmt_next : forall ss parent i me t,
  snd (build_seq build_stmt parent i me ss t) = next_stmts me ss.
Proof.
  induction ss as [|s rest IH]; intros parent i me t; [reflexivity|].
  simpl. rewrite <- (build_stmt_end s parent i me t).
  destruct (build_stmt parent i me s t) as [t1 se]. simpl. apply IH.
Qed.

Lemma build_decl_end : forall d parent i me t,
  snd (build_decl parent i me d t) = end_decl me d.
Proof.
  intros [body] parent i me t. simpl.
  rewrite <- (build_seq_stmt_next body me 0 (Pos.succ me) t).
  destruct (build_seq build_stmt me 0 (Pos.succ me) body t) as [t1 nx]. reflexivity.
Qed.

Lemma build_seq_decl_next : forall ds parent i me t,
  snd (build_seq build_decl parent i me ds t) = next_decls me ds.
Proof.
  induction ds as [|d rest IH]; intros parent i me t; [reflexivity|].
  simpl. rewrite <- (build_decl_end d parent i me t).
  destruct (build_decl parent i me d t) as [t1 de]. simpl. apply IH.
Qed.

Lemma build_file_count : forall f, fi_count (build_file f) = count_file f.
Proof.
  intros f. unfold build_file, count_file.
  rewrite <- (build_seq_decl_next (tf_decls f) root_id 0 (Pos.succ root_id) NodeTable.empty).
  destruct (build_seq build_decl root_id 0 (Pos.succ root_id) (tf_decls f) NodeTable.empty) as [t1 nx].
  reflexivity.
Qed.

(* the source occurrence addressed by a preorder id (None if the id is a non-expression node or absent). *)
Fixpoint occ_expr (me : positive) (e : TExpr) (target : positive) : option TExpr :=
  if Pos.eqb target me then Some e
  else match e with
       | TLeaf _  => None
       | TBin l r =>
           if Pos.leb target (end_expr (Pos.succ me) l)
           then occ_expr (Pos.succ me) l target
           else occ_expr (Pos.succ (end_expr (Pos.succ me) l)) r target
       end.
Definition occ_stmt (me : positive) (s : TStmt) (target : positive) : option TExpr :=
  match s with TPrint e => occ_expr (Pos.succ me) e target end.
Fixpoint occ_stmts (me : positive) (ss : list TStmt) (target : positive) : option TExpr :=
  match ss with
  | [] => None
  | s :: rest =>
      if Pos.leb target (end_stmt me s) then occ_stmt me s target
      else occ_stmts (Pos.succ (end_stmt me s)) rest target
  end.
Definition occ_decl (me : positive) (d : TDecl) (target : positive) : option TExpr :=
  match d with TFun body => occ_stmts (Pos.succ me) body target end.
Fixpoint occ_decls (me : positive) (ds : list TDecl) (target : positive) : option TExpr :=
  match ds with
  | [] => None
  | d :: rest =>
      if Pos.leb target (end_decl me d) then occ_decl me d target
      else occ_decls (Pos.succ (end_decl me d)) rest target
  end.
Definition occ_file (f : TFile) (target : positive) : option TExpr :=
  occ_decls (Pos.succ root_id) (tf_decls f) target.


(* ================================================================================================= *)
(** ** C0A: source-snapshot-local references and TOTAL navigation.                                     *)
(*    A reference belongs to the EXACT immutable source snapshot [fs] (it is indexed by [fs]), never to *)
(*    free-standing index data.  Same-shaped but different-payload snapshots therefore have             *)
(*    NON-INTERCHANGEABLE reference types.  Structurally guaranteed queries are TOTAL; only [parent_of]  *)
(*    is optional (a file root has no parent).                                                          *)
(* ================================================================================================= *)

(* a local id is a real occurrence of file [f] iff it resolves in [f]'s built per-file table. *)
Definition valid_localb (f : TFile) (local : positive) : bool :=
  match NodeTable.get local (fi_table (build_file f)) with Some _ => true | None => false end.

(* The public interface of the reference layer.  It exposes the abstract snapshot-indexed types, the
   validated MINTING boundaries, the projections, the TOTAL navigation API, and the theorem/regression
   surfaces — but NOT the raw record constructors ([mkFileRef]/[mkNodeRef]/[mkSyntaxIndex]) nor the hidden
   file slot.  Sealing the module against this signature makes "the only way to mint a reference is a
   validated function" TRUE rather than aspirational (C0A §6/§11). *)
Module Type SNAP_SIG.
  Parameter FileRef    : TForest -> Type.
  Parameter NodeRef    : TForest -> Type.
  Parameter SyntaxIndex : TForest -> Type.
  Parameter index_forest : forall fs, SyntaxIndex fs.
  Parameter file_of_path : forall fs, FilePath -> option (FileRef fs).
  Parameter ref_of_key   : forall fs, SyntaxIndex fs -> NodeKey -> option (NodeRef fs).
  Parameter file_ref_file : forall {fs}, FileRef fs -> TFile.
  Parameter file_ref_path : forall {fs}, FileRef fs -> FilePath.
  Parameter node_ref_file  : forall {fs}, NodeRef fs -> FileRef fs.
  Parameter node_ref_local : forall {fs}, NodeRef fs -> positive.
  Parameter node_ref_valid : forall {fs} (r : NodeRef fs),
    valid_localb (file_ref_file (node_ref_file r)) (node_ref_local r) = true.
  Parameter node_ref_key   : forall {fs}, NodeRef fs -> NodeKey.
  Parameter ref_meta         : forall {fs}, SyntaxIndex fs -> NodeRef fs -> NodeMeta.
  Parameter node_kind        : forall {fs}, SyntaxIndex fs -> NodeRef fs -> SyntaxKind.
  Parameter node_role        : forall {fs}, SyntaxIndex fs -> NodeRef fs -> NodeRole.
  Parameter node_subtree_end : forall {fs}, SyntaxIndex fs -> NodeRef fs -> positive.
  Parameter containing_file  : forall {fs}, NodeRef fs -> FileRef fs.
  Parameter parent_of        : forall {fs}, SyntaxIndex fs -> NodeRef fs -> option (NodeRef fs).
  Parameter children_of      : forall {fs}, SyntaxIndex fs -> NodeRef fs -> list (NodeRef fs).
  Parameter node_at          : forall {fs}, NodeRef fs -> option TExpr.
  (* identity + total-API correctness *)
  Parameter node_ref_ext : forall fs (r1 r2 : NodeRef fs),
    node_ref_file r1 = node_ref_file r2 -> node_ref_local r1 = node_ref_local r2 -> r1 = r2.
  Parameter thm_node_kind : forall fs (idx : SyntaxIndex fs) (r : NodeRef fs),
    node_kind idx r = nm_kind (ref_meta idx r).
  Parameter thm_ref_meta_built : forall fs (idx : SyntaxIndex fs) (r : NodeRef fs),
    NodeTable.get (node_ref_local r) (fi_table (build_file (file_ref_file (node_ref_file r)))) = Some (ref_meta idx r).
  Parameter thm_containing_file : forall fs (r : NodeRef fs),
    containing_file r = node_ref_file r /\ file_ref_path (containing_file r) = nk_file (node_ref_key r).
  Parameter thm_parent_root : forall fs (idx : SyntaxIndex fs) (r : NodeRef fs),
    node_ref_local r = root_id -> parent_of idx r = None.
  Parameter thm_parent_nonroot : forall fs (idx : SyntaxIndex fs) (r : NodeRef fs),
    node_ref_local r <> root_id -> exists pr, parent_of idx r = Some pr.
  (* §9 source-snapshot regression witnesses + theorems *)
  Parameter fs_a : TForest.  Parameter fs_b : TForest.
  Parameter rleaf_a5 : NodeRef fs_a.  Parameter rleaf_a6 : NodeRef fs_a.  Parameter rleaf_b5 : NodeRef fs_b.
  Parameter reg_node_at_a : node_at rleaf_a5 = Some (TLeaf 5).
  Parameter reg_node_at_b : node_at rleaf_b5 = Some (TLeaf 6).
  Parameter reg_equal_leaves_distinct : rleaf_a5 <> rleaf_a6.
End SNAP_SIG.

Module Snap : SNAP_SIG.

(* a file-root handle for ONE file occurrence of [fs]: a hidden structural slot + the exact file + proof. *)
Record FileRef_T (fs : TForest) := mkFileRef {
  file_ref_slot : positive;          (* hidden optimization handle; NOT source identity, NOT rendered *)
  file_ref_file : TFile;
  file_ref_at   : forest_file_at fs file_ref_slot = Some file_ref_file
}.
Arguments file_ref_slot {fs} _.
Arguments file_ref_file {fs} _.
Arguments file_ref_at   {fs} _.
Definition FileRef := FileRef_T.
Definition file_ref_path {fs} (fr : FileRef fs) : FilePath := tf_path (file_ref_file fr).

(* a reference to ONE occurrence in ONE exact file of ONE exact source snapshot [fs]. *)
Record NodeRef_T (fs : TForest) := mkNodeRef {
  node_ref_file  : FileRef fs;
  node_ref_local : positive;
  node_ref_valid : valid_localb (file_ref_file node_ref_file) node_ref_local = true
}.
Arguments node_ref_file  {fs} _.
Arguments node_ref_local {fs} _.
Arguments node_ref_valid {fs} _.
Definition NodeRef := NodeRef_T.

(* the public raw key: file PATH (the identity) + local id — the hidden slot is NOT part of it. *)
Definition node_ref_key {fs} (r : NodeRef fs) : NodeKey :=
  mkKey (file_ref_path (node_ref_file r)) (node_ref_local r).

(* the derived certified index for a snapshot: a slot-keyed outer table + the correspondence to [fs]. *)
Record SyntaxIndex_T (fs : TForest) := mkSyntaxIndex {
  si_outer : NodeTable.table FileIndex;
  si_ok    : forall slot f, forest_file_at fs slot = Some f -> NodeTable.get slot si_outer = Some (build_file f)
}.
Arguments si_outer {fs} _.
Arguments si_ok    {fs} _.
Definition SyntaxIndex := SyntaxIndex_T.
Definition index_forest (fs : TForest) : SyntaxIndex fs :=
  mkSyntaxIndex fs (outer_of fs) (outer_get_at fs).

(* ONE outer slot lookup gives the NodeRef's file index — no file-list scan.  Present by correspondence. *)
Definition ref_fi_opt {fs} (idx : SyntaxIndex fs) (r : NodeRef fs) : option FileIndex :=
  NodeTable.get (file_ref_slot (node_ref_file r)) (si_outer idx).
Lemma ref_fi_some {fs} (idx : SyntaxIndex fs) (r : NodeRef fs) :
  ref_fi_opt idx r = Some (build_file (file_ref_file (node_ref_file r))).
Proof. unfold ref_fi_opt. apply (si_ok idx). apply (file_ref_at (node_ref_file r)). Qed.
Lemma ref_fi_some' {fs} (idx : SyntaxIndex fs) (r : NodeRef fs) : ref_fi_opt idx r <> None.
Proof. rewrite ref_fi_some. discriminate. Qed.
Definition ref_fi {fs} (idx : SyntaxIndex fs) (r : NodeRef fs) : FileIndex :=
  option_get (ref_fi_opt idx r) (ref_fi_some' idx r).
Lemma ref_fi_eq {fs} (idx : SyntaxIndex fs) (r : NodeRef fs) :
  ref_fi idx r = build_file (file_ref_file (node_ref_file r)).
Proof. unfold ref_fi. apply option_get_eq, ref_fi_some. Qed.

(* the metadata option: one per-file local lookup in the file index reached via the slot. *)
Definition ref_meta_opt {fs} (idx : SyntaxIndex fs) (r : NodeRef fs) : option NodeMeta :=
  NodeTable.get (node_ref_local r) (fi_table (ref_fi idx r)).
Lemma ref_meta_some {fs} (idx : SyntaxIndex fs) (r : NodeRef fs) : ref_meta_opt idx r <> None.
Proof.
  unfold ref_meta_opt. rewrite ref_fi_eq.
  pose proof (node_ref_valid r) as Hv. unfold valid_localb in Hv.
  destruct (NodeTable.get (node_ref_local r) (fi_table (build_file (file_ref_file (node_ref_file r)))));
    [discriminate | discriminate Hv].
Qed.

(* TOTAL metadata query — no option, no fallback. *)
Definition ref_meta {fs} (idx : SyntaxIndex fs) (r : NodeRef fs) : NodeMeta :=
  option_get (ref_meta_opt idx r) (ref_meta_some idx r).

(* the metadata is exactly the per-file built meta for the occurrence — ties navigation to the builder. *)
Lemma ref_meta_spec {fs} (idx : SyntaxIndex fs) (r : NodeRef fs) m :
  NodeTable.get (node_ref_local r) (fi_table (build_file (file_ref_file (node_ref_file r)))) = Some m ->
  ref_meta idx r = m.
Proof. intros H. unfold ref_meta. apply option_get_eq. unfold ref_meta_opt. rewrite ref_fi_eq. exact H. Qed.

Definition node_kind        {fs} (idx : SyntaxIndex fs) (r : NodeRef fs) : SyntaxKind := nm_kind (ref_meta idx r).
Definition node_role        {fs} (idx : SyntaxIndex fs) (r : NodeRef fs) : NodeRole   := nm_role (ref_meta idx r).
Definition node_subtree_end {fs} (idx : SyntaxIndex fs) (r : NodeRef fs) : positive   := nm_subtree_end (ref_meta idx r).

(* TOTAL containing-file — the carried FileRef, an O(1) projection. *)
Definition containing_file {fs} (r : NodeRef fs) : FileRef fs := node_ref_file r.

(* the meta at a valid ref's local id IS [ref_meta] — connects the total query to the per-file table. *)
Lemma ref_meta_get {fs} (idx : SyntaxIndex fs) (r : NodeRef fs) :
  NodeTable.get (node_ref_local r) (fi_table (build_file (file_ref_file (node_ref_file r)))) = Some (ref_meta idx r).
Proof.
  pose proof (node_ref_valid r) as Hv. unfold valid_localb in Hv.
  destruct (NodeTable.get (node_ref_local r) (fi_table (build_file (file_ref_file (node_ref_file r))))) as [m|] eqn:E;
    [| discriminate Hv].
  rewrite (ref_meta_spec idx r m E). reflexivity.
Qed.

(* the parent of a valid occurrence is itself a valid occurrence of the same file (so parent_of is total-when-Some). *)
Lemma parent_valid {fs} (idx : SyntaxIndex fs) (r : NodeRef fs) pid :
  nm_parent (ref_meta idx r) = Some pid -> valid_localb (file_ref_file (node_ref_file r)) pid = true.
Proof.
  intros Hpar.
  pose proof (build_file_wf (file_ref_file (node_ref_file r))) as WF.
  pose proof (ref_meta_get idx r) as Hget.
  destruct (in_domain (file_ref_file (node_ref_file r)) (node_ref_local r) (ref_meta idx r) Hget) as [Hlo Hhi].
  assert (Hne : node_ref_local r <> root_id).
  { intro Hr. rewrite Hr in Hget. destruct (sub_root WF) as [m0 [Hg [Hp0 _]]].
    rewrite Hg in Hget. injection Hget as Heq. rewrite <- Heq in Hpar. rewrite Hp0 in Hpar. discriminate Hpar. }
  destruct (sub_prng WF (node_ref_local r) (ref_meta idx r) ltac:(lia) Hhi Hget) as [p [mp [Hpar' [Hgp _]]]].
  rewrite Hpar in Hpar'. injection Hpar' as <-.
  unfold valid_localb. rewrite Hgp. reflexivity.
Qed.

(* TOTAL-when-Some parent: constructed directly from the parent-validity proof; [None] only at a root. *)
Definition parent_of {fs} (idx : SyntaxIndex fs) (r : NodeRef fs) : option (NodeRef fs) :=
  (match nm_parent (ref_meta idx r) as o return (nm_parent (ref_meta idx r) = o -> option (NodeRef fs)) with
   | Some pid => fun H => Some (mkNodeRef fs (node_ref_file r) pid (parent_valid idx r pid H))
   | None     => fun _ => None
   end) eq_refl.

(* every enumerated child id is a real occurrence of the file — so no child reference is ever dropped. *)
Lemma child_valid (f : TFile) local c :
  In c (child_ids (fi_table (build_file f)) local) -> valid_localb f c = true.
Proof.
  intros Hin. unfold child_ids in Hin.
  destruct (NodeTable.get local (fi_table (build_file f))) as [m|] eqn:El; [|destruct Hin].
  apply child_enum_sound in Hin. unfold parent_id in Hin.
  unfold valid_localb. destruct (NodeTable.get c (fi_table (build_file f))); [reflexivity | discriminate Hin].
Qed.

(* build a validated reference for EVERY id in a list of proven-valid ids (no filtering, no drops). *)
Fixpoint refine_children {fs} (fr : FileRef fs) (ids : list positive)
  : (forall c, In c ids -> valid_localb (file_ref_file fr) c = true) -> list (NodeRef fs) :=
  match ids with
  | []        => fun _    => []
  | c :: rest => fun Hall =>
      mkNodeRef fs fr c (Hall c (or_introl eq_refl)) :: refine_children fr rest (fun c' H => Hall c' (or_intror H))
  end.

Lemma children_valid {fs} (idx : SyntaxIndex fs) (r : NodeRef fs) c :
  In c (child_ids (fi_table (ref_fi idx r)) (node_ref_local r)) ->
  valid_localb (file_ref_file (node_ref_file r)) c = true.
Proof. rewrite ref_fi_eq. apply child_valid. Qed.

(* TOTAL direct children — one outer slot lookup, then the file's interval-jump enumeration; no drops. *)
Definition children_of {fs} (idx : SyntaxIndex fs) (r : NodeRef fs) : list (NodeRef fs) :=
  refine_children (node_ref_file r)
    (child_ids (fi_table (ref_fi idx r)) (node_ref_local r)) (children_valid idx r).

(* --- the raw-key minting boundary (§7): a path lookup that scans the file list ONCE. --- *)
Lemma find_slot_at : forall files fp start slot f,
  find_slot files fp start = Some (slot, f) ->
  nth_error files (Nat.pred (Pos.to_nat slot) - Nat.pred (Pos.to_nat start))%nat = Some f
  /\ tf_path f = fp /\ (start <= slot)%positive.
Proof.
  induction files as [|g rest IH]; intros fp start slot f H; simpl in H; [discriminate|].
  destruct (fp_eqb (tf_path g) fp) eqn:Eq.
  - injection H as <- <-. apply fp_eqb_eq in Eq. rewrite Nat.sub_diag. simpl.
    split; [reflexivity | split; [exact Eq | lia]].
  - apply IH in H as [Hnth [Hpath Hle]].
    split; [| split; [exact Hpath | lia]].
    rewrite Pos2Nat.inj_succ in Hnth.
    replace (Nat.pred (Pos.to_nat slot) - Nat.pred (Pos.to_nat start))%nat
       with (S (Nat.pred (Pos.to_nat slot) - Nat.pred (S (Pos.to_nat start))))%nat by lia.
    simpl. exact Hnth.
Qed.

Lemma forest_find_at (fs : TForest) (fp : FilePath) (slot : positive) (f : TFile) :
  forest_find fs fp = Some (slot, f) -> forest_file_at fs slot = Some f.
Proof.
  unfold forest_find, forest_file_at. intros H. apply find_slot_at in H as [Hnth [_ _]].
  change (Nat.pred (Pos.to_nat 1)) with 0%nat in Hnth. rewrite Nat.sub_0_r in Hnth. exact Hnth.
Qed.

Definition file_of_path (fs : TForest) (fp : FilePath) : option (FileRef fs) :=
  (match forest_find fs fp as o return (forest_find fs fp = o -> option (FileRef fs)) with
   | Some (slot, f) => fun H => Some (mkFileRef fs slot f (forest_find_at fs fp slot f H))
   | None           => fun _ => None
   end) eq_refl.

(* validate a local id THROUGH the snapshot's PRECOMPUTED outer table (no per-file rebuild): one outer-slot
   lookup + one per-file lookup.  Provably agrees with [valid_localb] by the index correspondence [si_ok]. *)
Definition valid_in_index {fs} (idx : SyntaxIndex fs) (fr : FileRef fs) (local : positive) : bool :=
  match NodeTable.get (file_ref_slot fr) (si_outer idx) with
  | Some fi => match NodeTable.get local (fi_table fi) with Some _ => true | None => false end
  | None    => false
  end.
Lemma valid_in_index_eq {fs} (idx : SyntaxIndex fs) (fr : FileRef fs) (local : positive) :
  valid_in_index idx fr local = valid_localb (file_ref_file fr) local.
Proof.
  unfold valid_in_index, valid_localb.
  rewrite (si_ok idx (file_ref_slot fr) (file_ref_file fr) (file_ref_at fr)). reflexivity.
Qed.
Lemma valid_in_index_true {fs} (idx : SyntaxIndex fs) (fr : FileRef fs) (local : positive) :
  valid_in_index idx fr local = true -> valid_localb (file_ref_file fr) local = true.
Proof. rewrite valid_in_index_eq. exact (fun H => H). Qed.

(* mint a validated reference from a raw key THROUGH the snapshot's index (§7 raw-lookup boundary): one
   file-list scan (path -> slot) + one outer-slot lookup + one per-file lookup — NO per-file rebuild.
   Cost O(files + log files + log nodes-per-file).  The hot path from an existing [NodeRef] never uses this. *)
Definition ref_of_key (fs : TForest) (idx : SyntaxIndex fs) (k : NodeKey) : option (NodeRef fs) :=
  match file_of_path fs (nk_file k) with
  | Some fr =>
      (match valid_in_index idx fr (nk_local k) as b
             return (valid_in_index idx fr (nk_local k) = b -> option (NodeRef fs)) with
       | true  => fun H => Some (mkNodeRef fs fr (nk_local k) (valid_in_index_true idx fr (nk_local k) H))
       | false => fun _ => None
       end) eq_refl
  | None => None
  end.

(* source recovery: the exact source occurrence a reference addresses (proof/diagnostic view, table-free). *)
Definition node_at {fs} (r : NodeRef fs) : option TExpr :=
  occ_file (file_ref_file (node_ref_file r)) (node_ref_local r).

(* ================================================================================================= *)
(** ** C0A §9 regression — same paths + tree shape, DIFFERENT payloads => non-interchangeable refs.     *)
(* ================================================================================================= *)

Definition rpath : FilePath := mkFP "a.go"%string eq_refl.
(* one file: one decl / one stmt / TBin (TLeaf v) (TLeaf v) — TWO structurally equal leaves of value v. *)
Definition rfile (v : nat) : TFile := mkTFile rpath [ TFun [ TPrint (TBin (TLeaf v) (TLeaf v)) ] ].
Lemma rnodup (v : nat) : NoDup (map tf_path [ rfile v ]).
Proof. simpl. constructor; [ intros H; exact H | constructor ]. Qed.
(* two snapshots: identical paths and identical tree shape, but leaves 5 vs 6. *)
Definition fs_a : TForest := mkTForest [ rfile 5 ] (rnodup 5).
Definition fs_b : TForest := mkTForest [ rfile 6 ] (rnodup 6).

Lemma rfile_at (v : nat) : forest_file_at (mkTForest [ rfile v ] (rnodup v)) 1 = Some (rfile v).
Proof. reflexivity. Qed.
Definition fref_a : FileRef fs_a := mkFileRef fs_a 1 (rfile 5) (rfile_at 5).
Definition fref_b : FileRef fs_b := mkFileRef fs_b 1 (rfile 6) (rfile_at 6).

(* every id in [1..6] is a real occurrence of the single file (root=1, decl=2, stmt=3, TBin=4, leaves=5,6). *)
Lemma rvalid (v : nat) (n : positive) : (root_id <= n)%positive -> (n <= 6)%positive -> valid_localb (rfile v) n = true.
Proof.
  intros H1 H2. unfold valid_localb.
  pose proof (build_file_wf (rfile v)) as WF.
  assert (Hc : fi_count (build_file (rfile v)) = 6) by (rewrite build_file_count; reflexivity).
  destruct (NodeTable.get n (fi_table (build_file (rfile v)))) eqn:E; [reflexivity|].
  exfalso. apply (sub_pres WF n); [ exact H1 | rewrite Hc; exact H2 | exact E ].
Qed.

(* the two equal leaves of fs_a as validated references, id 5 (left) and id 6 (right). *)
Definition rleaf_a5 : NodeRef fs_a :=
  mkNodeRef fs_a fref_a 5 (rvalid 5 5 ltac:(unfold root_id; lia) ltac:(lia)).
Definition rleaf_a6 : NodeRef fs_a :=
  mkNodeRef fs_a fref_a 6 (rvalid 5 6 ltac:(unfold root_id; lia) ltac:(lia)).
Definition rleaf_b5 : NodeRef fs_b :=
  mkNodeRef fs_b fref_b 5 (rvalid 6 5 ltac:(unfold root_id; lia) ltac:(lia)).

(* §9.2 — a reference of fs_a is NOT usable as a reference of fs_b: type-level snapshot separation. *)
Fail Definition reg_cross_snapshot : NodeRef fs_b := rleaf_a5.

(* §9.3 / §9.4 — the SAME id recovers the exact per-snapshot source payload: TLeaf 5 in fs_a, TLeaf 6 in fs_b. *)
Theorem reg_node_at_a : node_at rleaf_a5 = Some (TLeaf 5).
Proof. vm_compute. reflexivity. Qed.
Theorem reg_node_at_b : node_at rleaf_b5 = Some (TLeaf 6).
Proof. vm_compute. reflexivity. Qed.

(* §9.5 — the two structurally EQUAL leaves inside fs_a are STILL distinct references (distinct keys). *)
Theorem reg_equal_leaves_distinct : rleaf_a5 <> rleaf_a6.
Proof.
  intro H. apply (f_equal node_ref_key) in H. unfold node_ref_key in H. cbn in H.
  injection H as H. discriminate H.
Qed.

(* ================================================================================================= *)
(** ** C0A ref-level theorem family (§10): total-API correctness + snapshot-local reference identity.  *)
(* ================================================================================================= *)

(* decidable equality for the toy syntax + files (for UIP over reference proof fields). *)
Definition texpr_eq_dec (a b : TExpr) : {a = b} + {a <> b}.
Proof. decide equality; apply Nat.eq_dec. Defined.
Definition tstmt_eq_dec (a b : TStmt) : {a = b} + {a <> b}.
Proof. decide equality; apply texpr_eq_dec. Defined.
Definition tdecl_eq_dec (a b : TDecl) : {a = b} + {a <> b}.
Proof. decide equality; apply (list_eq_dec tstmt_eq_dec). Defined.
Definition tfile_eq_dec (a b : TFile) : {a = b} + {a <> b}.
Proof. decide equality; [ apply (list_eq_dec tdecl_eq_dec) | apply fp_eq_dec ]. Defined.
Definition option_tfile_eq_dec (a b : option TFile) : {a = b} + {a <> b}.
Proof. decide equality; apply tfile_eq_dec. Defined.

(* reference extensionality: a NodeRef is fixed by its file handle and local id (validity is proof-irrelevant). *)
Lemma node_ref_ext (fs : TForest) (r1 r2 : NodeRef fs) :
  node_ref_file r1 = node_ref_file r2 -> node_ref_local r1 = node_ref_local r2 -> r1 = r2.
Proof.
  destruct r1 as [f1 l1 v1], r2 as [f2 l2 v2]; simpl; intros -> ->.
  f_equal. apply (UIP_dec Bool.bool_dec).
Qed.

(* a FileRef is fixed by its hidden slot (the [forest_file_at] witness is proof-irrelevant). *)
Lemma file_ref_ext (fs : TForest) (fr1 fr2 : FileRef fs) :
  file_ref_slot fr1 = file_ref_slot fr2 -> fr1 = fr2.
Proof.
  destruct fr1 as [s1 f1 p1], fr2 as [s2 f2 p2]; simpl; intros Hs. subst s2.
  assert (f1 = f2) by (pose proof p1 as q; rewrite p2 in q; injection q as <-; reflexivity).
  subst f2. f_equal. apply (UIP_dec option_tfile_eq_dec).
Qed.

(* --- total-API correctness (§10) --- *)

Theorem thm_node_kind (fs : TForest) (idx : SyntaxIndex fs) (r : NodeRef fs) :
  node_kind idx r = nm_kind (ref_meta idx r).
Proof. reflexivity. Qed.

Theorem thm_ref_meta_built (fs : TForest) (idx : SyntaxIndex fs) (r : NodeRef fs) :
  NodeTable.get (node_ref_local r) (fi_table (build_file (file_ref_file (node_ref_file r)))) = Some (ref_meta idx r).
Proof. apply ref_meta_get. Qed.

Theorem thm_containing_file (fs : TForest) (r : NodeRef fs) :
  containing_file r = node_ref_file r /\ file_ref_path (containing_file r) = nk_file (node_ref_key r).
Proof. split; reflexivity. Qed.

(* parent_of behaviour: [None] exactly when the metadata parent is absent (a root). *)
Lemma parent_of_none (fs : TForest) (idx : SyntaxIndex fs) (r : NodeRef fs) :
  nm_parent (ref_meta idx r) = None -> parent_of idx r = None.
Proof.
  intros Hn. unfold parent_of. generalize (@eq_refl (option positive) (nm_parent (ref_meta idx r))).
  destruct (nm_parent (ref_meta idx r)) at 2 3; intros e; [ congruence | reflexivity ].
Qed.

Lemma parent_of_some (fs : TForest) (idx : SyntaxIndex fs) (r : NodeRef fs) pid :
  nm_parent (ref_meta idx r) = Some pid ->
  exists pr, parent_of idx r = Some pr
             /\ node_ref_file pr = node_ref_file r /\ node_ref_local pr = pid.
Proof.
  intros Hs. unfold parent_of. generalize (@eq_refl (option positive) (nm_parent (ref_meta idx r))).
  destruct (nm_parent (ref_meta idx r)) at 2 3; intros e.
  - eexists. split; [reflexivity | split; [reflexivity | cbn; congruence]].
  - congruence.
Qed.

(* the ROOT occurrence has no parent; every NON-root occurrence has a Some parent reference. *)
Theorem thm_parent_root (fs : TForest) (idx : SyntaxIndex fs) (r : NodeRef fs) :
  node_ref_local r = root_id -> parent_of idx r = None.
Proof.
  intros Hr. apply parent_of_none.
  pose proof (build_file_wf (file_ref_file (node_ref_file r))) as WF.
  destruct (sub_root WF) as [m0 [Hg [Hp0 _]]]. pose proof (ref_meta_get idx r) as Hget.
  rewrite Hr, Hg in Hget. injection Hget as Heq. rewrite <- Heq. exact Hp0.
Qed.

Theorem thm_parent_nonroot (fs : TForest) (idx : SyntaxIndex fs) (r : NodeRef fs) :
  node_ref_local r <> root_id -> exists pr, parent_of idx r = Some pr.
Proof.
  intros Hne.
  pose proof (build_file_wf (file_ref_file (node_ref_file r))) as WF.
  pose proof (ref_meta_get idx r) as Hget.
  destruct (in_domain (file_ref_file (node_ref_file r)) (node_ref_local r) (ref_meta idx r) Hget) as [Hlo Hhi].
  destruct (sub_prng WF (node_ref_local r) (ref_meta idx r) ltac:(lia) Hhi Hget) as [p [mp [Hpar _]]].
  destruct (parent_of_some fs idx r p Hpar) as [pr [Hpr _]]. exists pr. exact Hpr.
Qed.

End Snap.
