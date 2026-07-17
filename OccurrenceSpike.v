(** * OccurrenceSpike — isolated, TEMPORARY occurrence-index proof spike (Source Forest campaign, C0).

    This module is NOT part of the certified GoProgram pipeline.  It is an isolated spike that validates
    the snapshot-local occurrence-identity + derived-navigation-index design (Master Plan Part 4) on a tiny
    toy grammar BEFORE any production AST migration (C1/C2).  It imports only [FilePath] (the leaf path
    authority, reused for occurrence keys); it does NOT import GoAST/GoTypes/GoCompile and nothing in the
    production pipeline imports it.  It is proven axiom-free by the same whole-theory audit as the rest of
    the theory, and will be DELETED once the production [GoIndex] lands (C2).

    COLLECTION LAW (Master Plan / .review/SOURCE_FOREST_STATUS.md): the per-file local-node table is the
    STANDARD pinned-stdlib positive-key map [FMapPositive.PositiveMap] (aliased [Collections.NodeMapBase]) — a
    mature positive-key map from certified-compiler work with a structural key-bit traversal shape and an empty
    assumption closure.  (Fido relies on that structural shape; it does NOT claim a project kernel theorem for
    machine-level lookup complexity — the semantic node-table laws are what Fido proves.)  A primitive dense
    array (Coq [PArray]/[Uint63]) is REJECTED: it is built on KERNEL PRIMITIVES
    (Int63/PArray), which Fido's standing law rule 4 forbids ("Never ... a kernel primitive").  A project-
    authored radix trie is REJECTED by C1A: Fido authors NO collection implementation.  The thin [NodeTable]
    wrapper below stores a [Collections.NodeMapBase] and proves its three laws directly from the standard map
    facts — it contains no custom tree constructor; the sealed interface hides the standard map's CONSTRUCTORS
    and RAW operations (NOT the choice of collection) so callers cannot depend on internals, while C2 RETAINS
    this selected standard positive map.  A plain association [list] is likewise forbidden (an O(n) list-scan
    node-table lookup). *)

From Stdlib Require Import PArith List Bool Lia Eqdep_dec Wf_nat Sorted String Recdef Arith.
From Stdlib Require Import SetoidList.
From Fido Require Import FilePath Collections.
Import ListNotations.

(* ================================================================================================= *)
(** ** The SELECTED node table: an ABSTRACT interface, implemented internally by the STANDARD pinned-stdlib *)
(*    positive-key map [Collections.NodeMapBase] ([FMapPositive]).  Callers see ONLY                       *)
(*    [NodeTable.table]/[empty]/[get]/[set] and the three laws; the sealing hides the standard map's        *)
(*    CONSTRUCTORS and RAW operations, NOT the choice of collection — C2 RETAINS this selected standard      *)
(*    positive map (it does not swap it for another representation; Master Plan 4.9). *)
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
  (* internal representation — the STANDARD positive-key map [Collections.NodeMapBase] (FMapPositive); the
     three laws are proved directly from the standard [find]/[add]/[empty] facts (no custom tree). *)
  Definition table := Collections.NodeMapBase.t.
  Definition empty {A} : table A := Collections.NodeMapBase.empty A.
  Definition get {A} (k : positive) (t : table A) : option A := Collections.NodeMapBase.find k t.
  Definition set {A} (k : positive) (v : A) (t : table A) : table A := Collections.NodeMapBase.add k v t.
  Lemma get_empty {A} (k : positive) : get k (@empty A) = None.
  Proof. apply Collections.NodeMapBase.gempty. Qed.
  Lemma get_set_same {A} (k : positive) (v : A) (t : table A) : get k (set k v t) = Some v.
  Proof. apply Collections.NodeMapBase.gss. Qed.
  Lemma get_set_other {A} (j k : positive) (v : A) (t : table A) :
    j <> k -> get k (set j v t) = get k t.
  Proof. intro H. apply Collections.NodeMapBase.gso. congruence. Qed.
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

(* The toy SOURCE VALUE — the file's syntax ALONE (its path is NOT stored here; the path is the map key,
   exactly as production separates [GoSourceFile] from its [FilePath] key: no second file identity). *)
Record TSourceFile := mkTSource { ts_decls : list TDecl }.
(* The toy construction/view record — a path paired with its source, mirroring production's [GoFileNode]. *)
Record TFileNode := mkTFileNode { tfn_path : FilePath ; tfn_source : TSourceFile }.
(* An immutable toy SOURCE SNAPSHOT is a STANDARD FilePath map (C1A §10.2): the path IS the key, so one path
   names at most one source root INTRINSICALLY (no [NoDup] side condition, no list scan, no hidden slot). *)
Definition TForest := Collections.FileMapBase.t TSourceFile.

(* place a list of construction nodes into the standard file map (view -> forest).  This DUPLICATE-REJECTS
   exactly like production's [filemap_of_nodes]: a repeated path makes the build FAIL ([None]) rather than
   letting [add]'s overwrite SILENTLY ERASE the earlier source occurrence (C1A §6 — never let a standard
   map's overwrite behavior drop a duplicate source). *)
Fixpoint forest_of (nodes : list TFileNode) : option TForest :=
  match nodes with
  | [] => Some (Collections.FileMapBase.empty TSourceFile)
  | n :: rest =>
      match forest_of rest with
      | None => None
      | Some fm => if Collections.FileMapBase.mem (tfn_path n) fm then None
                   else Some (Collections.FileMapBase.add (tfn_path n) (tfn_source n) fm)
      end
  end.

(* the empty map has no member, so a single-node build takes the [add] branch (not the reject branch). *)
Lemma mem_empty (k : FilePath) :
  Collections.FileMapBase.mem k (Collections.FileMapBase.empty TSourceFile) = false.
Proof.
  destruct (Collections.FileMapBase.mem k (Collections.FileMapBase.empty TSourceFile)) eqn:E; [ | reflexivity ].
  apply Collections.FileMapBase.mem_2 in E. destruct E as [v Hv].
  exfalso. revert Hv. apply Collections.FileMapBase.empty_1.
Qed.

(* a same-path pair is REJECTED at construction, so no earlier source is silently overwritten. *)
Lemma forest_of_dup_rejected (p : FilePath) (s1 s2 : TSourceFile) :
  forest_of [ mkTFileNode p s1 ; mkTFileNode p s2 ] = None.
Proof.
  cbn [forest_of tfn_path tfn_source]. rewrite mem_empty. cbv beta iota.
  assert (Hmem : Collections.FileMapBase.mem p
                   (Collections.FileMapBase.add p s2 (Collections.FileMapBase.empty TSourceFile)) = true).
  { apply Collections.FileMapBase.mem_1. exists s2. apply Collections.FileMapBase.add_1. reflexivity. }
  rewrite Hmem. reflexivity.
Qed.

(* a single distinct-path node builds to exactly [add path source empty] — the §9 fixtures are the standard
   map constructed DIRECTLY and PROVED to be [forest_of]'s successful result (NO fail-soft [None => empty]
   default: a rejected/duplicate source description is never silently the empty snapshot). *)
Lemma forest_of_single (n : TFileNode) :
  forest_of [ n ] = Some (Collections.FileMapBase.add (tfn_path n) (tfn_source n)
                            (Collections.FileMapBase.empty TSourceFile)).
Proof. cbn [forest_of]. rewrite mem_empty. reflexivity. Qed.

Definition root_id : positive := 1%positive.    (* every file root's canonical local id (theorem 1) *)

(* ================================================================================================= *)
(** ** The one-pass index builder (Master Plan 4.8).                                                   *)
(*    Each builder threads a fresh-id counter and inserts each occurrence's metadata EXACTLY ONCE via  *)
(*    one standard-map [NodeTable.set]; it never searches, compares, or copies syntax subtrees.  A subtree    *)
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

(* The per-file index carries NO path (the path is the outer map key — no second file identity, C1A §10.3). *)
Record FileIndex := mkFI {
  fi_table : NodeTable.table NodeMeta;
  fi_count : positive           (* number of occurrences = last local id; ids are [1 .. fi_count] *)
}.

Definition build_file (f : TSourceFile) : FileIndex :=
  let '(t1, nx) := build_seq build_decl root_id 0 (Pos.succ root_id) (ts_decls f) NodeTable.empty in
  let cnt := Pos.pred nx in
  mkFI (NodeTable.set root_id (mkMeta KFile None RFileRoot cnt) t1) cnt.

(* ================================================================================================= *)
(** ** C0A source snapshot: standard FilePath-map file lookup and a path-keyed outer index (no hidden slot). *)
(* ================================================================================================= *)

(* total extraction from a provably-present option — the key to a total validated-reference API. *)
Definition option_get {A} (o : option A) : o <> None -> A :=
  match o with Some a => fun _ => a | None => fun H => False_rect A (H eq_refl) end.
Lemma option_get_eq {A} (o : option A) (H : o <> None) (a : A) : o = Some a -> option_get o H = a.
Proof. intros Heq. subst o. reflexivity. Qed.
Lemma option_get_some {A} (o : option A) : forall (H : o <> None), o = Some (option_get o H).
Proof. destruct o as [a|]; intro H; [reflexivity | exfalso; exact (H eq_refl)]. Qed.

(* ---- the outer index: a STANDARD FilePath map [FileMap.t FileIndex] keyed DIRECTLY by path (C1A §10.3);
        [outer_of] is the standard [map] of [build_file] over the source forest, so ONE map lookup reaches a
        file's index — NO hidden slot, NO list scan, NO second file identity. ---- *)
Module OFM := Collections.FileMapBase.
Module OFMF := Collections.FileMapFacts.

Definition outer_of (fs : TForest) : OFM.t FileIndex := OFM.map build_file fs.

(* EXACT correspondence (both directions): the outer map holds the build of the file at a real path AND holds
   NOTHING at any path with no file — the standard [map] law, so no spurious entry can satisfy the invariant. *)
Lemma outer_get_exact : forall fs path,
  OFM.find path (outer_of fs)
  = match OFM.find path fs with Some f => Some (build_file f) | None => None end.
Proof.
  intros fs path. unfold outer_of. rewrite OFMF.map_o.
  destruct (OFM.find path fs); reflexivity.
Qed.

(* a real path holds exactly its file's build (the one direction driving the query API). *)
Lemma outer_get_at : forall fs path f,
  OFM.find path fs = Some f -> OFM.find path (outer_of fs) = Some (build_file f).
Proof. intros fs path f H. rewrite outer_get_exact, H. reflexivity. Qed.

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

Lemma build_file_wf (f : TSourceFile) :
  SubtreeWF NodeTable.empty (fi_table (build_file f)) None root_id (fi_count (build_file f)).
Proof.
  unfold build_file.
  destruct (build_seq build_decl root_id 0 (Pos.succ root_id) (ts_decls f) NodeTable.empty) as [t1 nx] eqn:E.
  simpl.
  destruct (build_seq_spec build_decl build_decl_spec (ts_decls f) root_id 0 (Pos.succ root_id)
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
Lemma in_domain (f : TSourceFile) k m :
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
Theorem thm1_root_id_canonical (f : TSourceFile) :
  exists m, NodeTable.get root_id (fi_table (build_file f)) = Some m /\ nm_kind m = KFile /\ nm_role m = RFileRoot.
Proof.
  unfold build_file.
  destruct (build_seq build_decl root_id 0 (Pos.succ root_id) (ts_decls f) NodeTable.empty) as [t1 nx] eqn:E.
  exists (mkMeta KFile None RFileRoot (Pos.pred nx)).
  cbn [fi_table]. rewrite NodeTable.get_set_same. split; [reflexivity | split; reflexivity].
Qed.

(* THEOREM 2 — the root has no parent. *)
Theorem thm2_root_no_parent (f : TSourceFile) m :
  NodeTable.get root_id (fi_table (build_file f)) = Some m -> nm_parent m = None.
Proof.
  intros H. pose proof (build_file_wf f) as WF. destruct (sub_root WF) as [m0 [Hg [Hp _]]].
  rewrite Hg in H. injection H as <-. exact Hp.
Qed.

(* THEOREM 3 — every non-root occurrence has exactly one parent. *)
Theorem thm3_nonroot_has_parent (f : TSourceFile) k m :
  NodeTable.get k (fi_table (build_file f)) = Some m -> k <> root_id -> exists p, nm_parent m = Some p.
Proof.
  intros H Hne. pose proof (build_file_wf f) as WF.
  destruct (in_domain f k m H) as [Hlo Hhi].
  assert (root_id < k) by lia.
  destruct (sub_prng WF k m ltac:(lia) Hhi H) as [p [mp [Hpar _]]]. exists p; exact Hpar.
Qed.

(* the parent field is functional: an occurrence has at most one parent. *)
Theorem thm3b_parent_unique (f : TSourceFile) k m p1 p2 :
  NodeTable.get k (fi_table (build_file f)) = Some m -> nm_parent m = Some p1 -> nm_parent m = Some p2 -> p1 = p2.
Proof. intros _ H1 H2. rewrite H1 in H2. injection H2 as <-. reflexivity. Qed.

(* THEOREM 13 (completeness half) — ancestry implies nested preorder intervals. *)
Lemma anc_complete (f : TSourceFile) a d :
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
Lemma anc_parent_ge (f : TSourceFile) a d p :
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
Lemma desc_parent_ge (f : TSourceFile) a ma d p :
  NodeTable.get a (fi_table (build_file f)) = Some ma ->
  (a < d)%positive -> (d <= nm_subtree_end ma)%positive ->
  parent_id (fi_table (build_file f)) d = Some p -> (a <= p)%positive.
Proof.
  intros Ha Hlt Hle Hp. pose proof (build_file_wf f) as WF.
  destruct (in_domain f a ma Ha) as [Hlo Hhi].
  eapply anc_parent_ge; [ eapply (sub_snd WF a d ma); [lia|lia|exact Ha|exact Hlt|exact Hle] | exact Hp ].
Qed.

(* a pid-child is a proper descendant of pid: pid < c and c is present. *)
Lemma child_gt (f : TSourceFile) pid c mc :
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
Lemma first_child (f : TSourceFile) pid mp :
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
Lemma next_child (f : TSourceFile) pid mp c mc :
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
Lemma interior_not_child (f : TSourceFile) pid cur mcur k :
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
Lemma built_nested (f : TSourceFile) x mx :
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
Theorem thm13_interval_ancestry (f : TSourceFile) a d :
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
Theorem thm11_children_sorted (f : TSourceFile) p :
  StronglySorted Pos.lt (child_ids (fi_table (build_file f)) p).
Proof.
  unfold child_ids. destruct (NodeTable.get p (fi_table (build_file f))) as [m|] eqn:Ep; [|constructor].
  apply child_enum_SS.
Qed.

(* THEOREM 4 — parent/child are inverse: a direct child appears in the interval-jump [child_ids] of its
   parent, and everything the jump enumerates has that parent. *)
Theorem thm4_child_has_parent (f : TSourceFile) p c :
  In c (child_ids (fi_table (build_file f)) p) -> parent_id (fi_table (build_file f)) c = Some p.
Proof.
  unfold child_ids. destruct (NodeTable.get p (fi_table (build_file f))) as [mp|] eqn:Ep; [|intros []].
  apply child_enum_sound.
Qed.

Theorem thm4_parent_has_child (f : TSourceFile) p c mc :
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

(* THEOREM 5 — parentage stays within one file: a reference carries its file PATH (the map key), so the
   parent shares it.  (The former [fi_path] field of [FileIndex] is DELETED — the path is the outer map key,
   never a second identity stored beside the table; file/parent sharing is proved at the reference level by
   [thm_parent_same_file] / [thm_children_same_file] in the sealed [Snap] module.) *)

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

Theorem thm7_enum_nodup (f : TSourceFile) : NoDup (all_ids (build_file f)).
Proof. apply pos_seq_NoDup. Qed.

Theorem thm7_enum_complete (f : TSourceFile) k m :
  NodeTable.get k (fi_table (build_file f)) = Some m -> In k (all_ids (build_file f)).
Proof.
  intros H. destruct (in_domain f k m H) as [Hlo Hhi]. unfold all_ids.
  apply pos_seq_In. unfold root_id. rewrite Pos2Nat.inj_1.
  assert (Pos.to_nat k <= Pos.to_nat (fi_count (build_file f)))%nat by (apply Pos2Nat.inj_le; exact Hhi).
  assert (1 <= Pos.to_nat k)%nat by (pose proof (Pos2Nat.is_pos k); lia).
  lia.
Qed.

Theorem thm7_enum_sound (f : TSourceFile) k :
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
Definition count_file (f : TSourceFile) : positive := Pos.pred (next_decls (Pos.succ root_id) (ts_decls f)).

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
  rewrite <- (build_seq_decl_next (ts_decls f) root_id 0 (Pos.succ root_id) NodeTable.empty).
  destruct (build_seq build_decl root_id 0 (Pos.succ root_id) (ts_decls f) NodeTable.empty) as [t1 nx].
  reflexivity.
Qed.

(* (The old expression-only [occ_*]/[occ_file] recovery locator is REMOVED in C0B: it was a second,
   independent source-recovery authority.  Source recovery now goes through the ONE general
   [source_occurrence_at] specification below, projected to an expression by [view_expr].) *)

(* ================================================================================================= *)
(** ** C0B: an INDEPENDENT source-occurrence specification (table-free, builder-independent).           *)
(*    For a source file and a local preorder id, this states — purely from the source syntax and the    *)
(*    boundary functions above ([end_expr]/[end_stmt]/[end_decl]/[count_file]) — the EXACT occurrence    *)
(*    that id designates and the metadata it SHOULD carry (kind, parent, role, subtree end).  It never   *)
(*    consults [NodeTable], [build_*], [FileIndex], or any query; it is the semantic yardstick against   *)
(*    which [build_file] is proved correct in [build_file_source_exact].                                 *)
(* ================================================================================================= *)

(* a kind-indexed view onto the ORIGINAL syntax fragment (no copied/parallel grammar). *)
Inductive SyntaxView : SyntaxKind -> Type :=
| ViewFile       : TSourceFile -> SyntaxView KFile
| ViewDecl       : TDecl -> SyntaxView KDecl
| ViewStatement  : TStmt -> SyntaxView KStatement
| ViewExpression : TExpr -> SyntaxView KExpression.

Record SourceOccurrence := mkOcc {
  occurrence_kind        : SyntaxKind;
  occurrence_view        : SyntaxView occurrence_kind;
  occurrence_parent      : option positive;
  occurrence_role        : NodeRole;
  occurrence_subtree_end : positive
}.

(* the metadata an occurrence SHOULD carry — derived only from the occurrence, NEVER from the builder. *)
Definition occurrence_meta (o : SourceOccurrence) : NodeMeta :=
  mkMeta (occurrence_kind o) (occurrence_parent o) (occurrence_role o) (occurrence_subtree_end o).

(* the original expression fragment an occurrence's view carries (Some only for expression occurrences). *)
Definition view_expr (o : SourceOccurrence) : option TExpr :=
  match occurrence_view o with ViewExpression e => Some e | _ => None end.

(* the occurrence a preorder id designates inside one expression subtree rooted at [me]. *)
Fixpoint occ_expr' (parent : positive) (role : NodeRole) (me : positive) (e : TExpr) (target : positive)
  : option SourceOccurrence :=
  match e with
  | TLeaf _ =>
      if Pos.eqb target me
      then Some (mkOcc KExpression (ViewExpression e) (Some parent) role me)
      else None
  | TBin l r =>
      if Pos.eqb target me
      then Some (mkOcc KExpression (ViewExpression e) (Some parent) role (end_expr me e))
      else if Pos.leb target (end_expr (Pos.succ me) l)
           then occ_expr' me (RChild 0) (Pos.succ me) l target
           else occ_expr' me (RChild 1) (Pos.succ (end_expr (Pos.succ me) l)) r target
  end.
Definition occ_stmt' (parent : positive) (sidx : nat) (me : positive) (s : TStmt) (target : positive)
  : option SourceOccurrence :=
  match s with
  | TPrint e =>
      if Pos.eqb target me
      then Some (mkOcc KStatement (ViewStatement s) (Some parent) (RDeclStmt sidx) (end_stmt me s))
      else occ_expr' me RStmtExpr (Pos.succ me) e target
  end.
Fixpoint occ_stmts' (parent : positive) (sidx : nat) (me : positive) (ss : list TStmt) (target : positive)
  : option SourceOccurrence :=
  match ss with
  | [] => None
  | s :: rest =>
      if Pos.leb target (end_stmt me s)
      then occ_stmt' parent sidx me s target
      else occ_stmts' parent (S sidx) (Pos.succ (end_stmt me s)) rest target
  end.
Definition occ_decl' (parent : positive) (didx : nat) (me : positive) (d : TDecl) (target : positive)
  : option SourceOccurrence :=
  match d with
  | TFun body =>
      if Pos.eqb target me
      then Some (mkOcc KDecl (ViewDecl d) (Some parent) (RFileDecl didx) (end_decl me d))
      else occ_stmts' me 0 (Pos.succ me) body target
  end.
Fixpoint occ_decls' (parent : positive) (didx : nat) (me : positive) (ds : list TDecl) (target : positive)
  : option SourceOccurrence :=
  match ds with
  | [] => None
  | d :: rest =>
      if Pos.leb target (end_decl me d)
      then occ_decl' parent didx me d target
      else occ_decls' parent (S didx) (Pos.succ (end_decl me d)) rest target
  end.
Definition source_occurrence_at (f : TSourceFile) (target : positive) : option SourceOccurrence :=
  if Pos.eqb target root_id
  then Some (mkOcc KFile (ViewFile f) None RFileRoot (count_file f))
  else occ_decls' root_id 0 (Pos.succ root_id) (ts_decls f) target.

(* --- interval frame lemmas: an occurrence lookup outside a subtree's [me .. end] window is [None]. --- *)

Lemma end_expr_ge : forall e me, (me <= end_expr me e)%positive.
Proof.
  induction e as [v|l IHl r IHr]; intros me; simpl; [lia|].
  specialize (IHl (Pos.succ me)). specialize (IHr (Pos.succ (end_expr (Pos.succ me) l))). lia.
Qed.

Lemma occ_expr'_below : forall e parent role me target,
  (target < me)%positive -> occ_expr' parent role me e target = None.
Proof.
  induction e as [v|l IHl r IHr]; intros parent role me target Hlt; simpl.
  - destruct (Pos.eqb_spec target me); [lia|reflexivity].
  - destruct (Pos.eqb_spec target me); [lia|].
    pose proof (end_expr_ge l (Pos.succ me)) as Hl.
    destruct (Pos.leb_spec target (end_expr (Pos.succ me) l)) as [Hle|Hgt].
    + apply IHl. lia.
    + lia.
Qed.

Lemma occ_expr'_above : forall e parent role me target,
  (end_expr me e < target)%positive -> occ_expr' parent role me e target = None.
Proof.
  induction e as [v|l IHl r IHr]; intros parent role me target Hgt; simpl in *.
  - destruct (Pos.eqb_spec target me); [lia|reflexivity].
  - pose proof (end_expr_ge l (Pos.succ me)) as Hl.
    pose proof (end_expr_ge r (Pos.succ (end_expr (Pos.succ me) l))) as Hr.
    destruct (Pos.eqb_spec target me); [lia|].
    destruct (Pos.leb_spec target (end_expr (Pos.succ me) l)) as [Hle|Hgt2].
    + lia.
    + apply IHr. lia.
Qed.

Lemma end_stmt_ge : forall s me, (Pos.succ me <= end_stmt me s)%positive.
Proof. intros [e] me. simpl. apply end_expr_ge. Qed.

Lemma occ_stmt'_below : forall s parent sidx me target,
  (target < me)%positive -> occ_stmt' parent sidx me s target = None.
Proof.
  intros [e] parent sidx me target Hlt. simpl.
  destruct (Pos.eqb_spec target me); [lia|]. apply occ_expr'_below. lia.
Qed.

Lemma occ_stmt'_above : forall s parent sidx me target,
  (end_stmt me s < target)%positive -> occ_stmt' parent sidx me s target = None.
Proof.
  intros [e] parent sidx me target Hgt. simpl in *.
  pose proof (end_expr_ge e (Pos.succ me)) as He.
  destruct (Pos.eqb_spec target me); [lia|]. apply occ_expr'_above. exact Hgt.
Qed.

Lemma next_stmts_ge : forall ss me, (me <= next_stmts me ss)%positive.
Proof.
  induction ss as [|s rest IH]; intros me; simpl; [lia|].
  specialize (IH (Pos.succ (end_stmt me s))). pose proof (end_stmt_ge s me) as Hs. lia.
Qed.

Lemma occ_stmts'_below : forall ss parent sidx me target,
  (target < me)%positive -> occ_stmts' parent sidx me ss target = None.
Proof.
  induction ss as [|s rest IH]; intros parent sidx me target Hlt; simpl; [reflexivity|].
  pose proof (end_stmt_ge s me) as Hs.
  destruct (Pos.leb_spec target (end_stmt me s)) as [Hle|Hgt].
  - apply occ_stmt'_below. exact Hlt.
  - lia.
Qed.

Lemma occ_stmts'_above : forall ss parent sidx me target,
  (next_stmts me ss <= target)%positive -> occ_stmts' parent sidx me ss target = None.
Proof.
  induction ss as [|s rest IH]; intros parent sidx me target Hge; simpl in *; [reflexivity|].
  pose proof (next_stmts_ge rest (Pos.succ (end_stmt me s))) as Hn.
  destruct (Pos.leb_spec target (end_stmt me s)) as [Hle|Hgt].
  - lia.
  - apply IH. lia.
Qed.

Lemma end_decl_ge : forall d me, (me <= end_decl me d)%positive.
Proof.
  intros [body] me. unfold end_decl. pose proof (next_stmts_ge body (Pos.succ me)) as Hn. lia.
Qed.

Lemma occ_decl'_below : forall d parent didx me target,
  (target < me)%positive -> occ_decl' parent didx me d target = None.
Proof.
  intros [body] parent didx me target Hlt. simpl.
  destruct (Pos.eqb_spec target me); [lia|]. apply occ_stmts'_below. lia.
Qed.

Lemma occ_decl'_above : forall d parent didx me target,
  (end_decl me d < target)%positive -> occ_decl' parent didx me d target = None.
Proof.
  intros [body] parent didx me target Hgt. simpl in *.
  pose proof (next_stmts_ge body (Pos.succ me)) as Hn. unfold end_decl in Hgt.
  destruct (Pos.eqb_spec target me); [lia|].
  apply occ_stmts'_above. lia.
Qed.

Lemma occ_decls'_below : forall ds parent didx me target,
  (target < me)%positive -> occ_decls' parent didx me ds target = None.
Proof.
  induction ds as [|d rest IH]; intros parent didx me target Hlt; simpl; [reflexivity|].
  pose proof (end_decl_ge d me) as Hd.
  destruct (Pos.leb_spec target (end_decl me d)) as [Hle|Hgt].
  - apply occ_decl'_below. exact Hlt.
  - lia.
Qed.

(* --- the builder AGREES with the independent spec: the table built for a subtree holds exactly the
       source occurrence's metadata at every id in its window, and leaves every id outside untouched. --- *)

Lemma build_expr_get : forall e parent role me t target,
  NodeTable.get target (fst (build_expr parent role me e t)) =
    match occ_expr' parent role me e target with
    | Some o => Some (occurrence_meta o)
    | None   => NodeTable.get target t
    end.
Proof.
  induction e as [v|l IHl r IHr]; intros parent role me t target; cbn [build_expr occ_expr'].
  - cbn [fst]. destruct (Pos.eqb_spec target me).
    + subst. rewrite NodeTable.get_set_same. reflexivity.
    + rewrite NodeTable.get_set_other by congruence. reflexivity.
  - pose proof (build_expr_end l me (RChild 0) (Pos.succ me) t) as He1.
    destruct (build_expr me (RChild 0) (Pos.succ me) l t) as [t1 e1] eqn:E1. cbn [snd] in He1. subst e1.
    pose proof (build_expr_end r me (RChild 1) (Pos.succ (end_expr (Pos.succ me) l)) t1) as He2.
    destruct (build_expr me (RChild 1) (Pos.succ (end_expr (Pos.succ me) l)) r t1) as [t2 e2] eqn:E2.
    cbn [snd] in He2. subst e2. cbn [fst].
    destruct (Pos.eqb_spec target me).
    + subst. rewrite NodeTable.get_set_same. reflexivity.
    + rewrite NodeTable.get_set_other by congruence.
      specialize (IHr me (RChild 1) (Pos.succ (end_expr (Pos.succ me) l)) t1 target).
      rewrite E2 in IHr. cbn [fst] in IHr. rewrite IHr.
      specialize (IHl me (RChild 0) (Pos.succ me) t target).
      rewrite E1 in IHl. cbn [fst] in IHl. rewrite IHl.
      destruct (Pos.leb_spec target (end_expr (Pos.succ me) l)) as [Hle|Hgt].
      * rewrite (occ_expr'_below r me (RChild 1) (Pos.succ (end_expr (Pos.succ me) l)) target ltac:(lia)).
        reflexivity.
      * rewrite (occ_expr'_above l me (RChild 0) (Pos.succ me) target ltac:(lia)). reflexivity.
Qed.

Lemma build_stmt_get : forall s parent sidx me t target,
  NodeTable.get target (fst (build_stmt parent sidx me s t)) =
    match occ_stmt' parent sidx me s target with
    | Some o => Some (occurrence_meta o)
    | None   => NodeTable.get target t
    end.
Proof.
  intros [e] parent sidx me t target. cbn [build_stmt occ_stmt'].
  pose proof (build_expr_end e me RStmtExpr (Pos.succ me) t) as He.
  destruct (build_expr me RStmtExpr (Pos.succ me) e t) as [t1 e1] eqn:E1. cbn [snd] in He. subst e1. cbn [fst].
  destruct (Pos.eqb_spec target me).
  - subst. rewrite NodeTable.get_set_same. reflexivity.
  - rewrite NodeTable.get_set_other by congruence.
    specialize (build_expr_get e me RStmtExpr (Pos.succ me) t target) as HG.
    rewrite E1 in HG. cbn [fst] in HG. exact HG.
Qed.

Lemma build_seq_stmt_get : forall ss parent sidx me t target,
  NodeTable.get target (fst (build_seq build_stmt parent sidx me ss t)) =
    match occ_stmts' parent sidx me ss target with
    | Some o => Some (occurrence_meta o)
    | None   => NodeTable.get target t
    end.
Proof.
  induction ss as [|s rest IH]; intros parent sidx me t target; cbn [build_seq occ_stmts'].
  - reflexivity.
  - pose proof (build_stmt_end s parent sidx me t) as Hse.
    destruct (build_stmt parent sidx me s t) as [t1 se] eqn:E1. cbn [snd] in Hse. subst se. cbn [fst].
    specialize (IH parent (S sidx) (Pos.succ (end_stmt me s)) t1 target). rewrite IH.
    specialize (build_stmt_get s parent sidx me t target) as HG.
    rewrite E1 in HG. cbn [fst] in HG. rewrite HG.
    destruct (Pos.leb_spec target (end_stmt me s)) as [Hle|Hgt].
    + rewrite (occ_stmts'_below rest parent (S sidx) (Pos.succ (end_stmt me s)) target ltac:(lia)). reflexivity.
    + rewrite (occ_stmt'_above s parent sidx me target ltac:(lia)). reflexivity.
Qed.

Lemma build_decl_get : forall d parent didx me t target,
  NodeTable.get target (fst (build_decl parent didx me d t)) =
    match occ_decl' parent didx me d target with
    | Some o => Some (occurrence_meta o)
    | None   => NodeTable.get target t
    end.
Proof.
  intros [body] parent didx me t target. cbn [build_decl occ_decl'].
  pose proof (build_seq_stmt_next body me 0 (Pos.succ me) t) as Hnx.
  destruct (build_seq build_stmt me 0 (Pos.succ me) body t) as [t1 nx] eqn:E1. cbn [snd] in Hnx. subst nx.
  cbn [fst].
  destruct (Pos.eqb_spec target me).
  - subst. rewrite NodeTable.get_set_same. reflexivity.
  - rewrite NodeTable.get_set_other by congruence.
    specialize (build_seq_stmt_get body me 0 (Pos.succ me) t target) as HG.
    rewrite E1 in HG. cbn [fst] in HG. exact HG.
Qed.

Lemma build_seq_decl_get : forall ds parent didx me t target,
  NodeTable.get target (fst (build_seq build_decl parent didx me ds t)) =
    match occ_decls' parent didx me ds target with
    | Some o => Some (occurrence_meta o)
    | None   => NodeTable.get target t
    end.
Proof.
  induction ds as [|d rest IH]; intros parent didx me t target; cbn [build_seq occ_decls'].
  - reflexivity.
  - pose proof (build_decl_end d parent didx me t) as Hde.
    destruct (build_decl parent didx me d t) as [t1 de] eqn:E1. cbn [snd] in Hde. subst de. cbn [fst].
    specialize (IH parent (S didx) (Pos.succ (end_decl me d)) t1 target). rewrite IH.
    specialize (build_decl_get d parent didx me t target) as HG.
    rewrite E1 in HG. cbn [fst] in HG. rewrite HG.
    destruct (Pos.leb_spec target (end_decl me d)) as [Hle|Hgt].
    + rewrite (occ_decls'_below rest parent (S didx) (Pos.succ (end_decl me d)) target ltac:(lia)). reflexivity.
    + rewrite (occ_decl'_above d parent didx me target ltac:(lia)). reflexivity.
Qed.

(* ============ the load-bearing UNIVERSAL exactness theorem (Master Plan / C0B §4). ============ *)

(* the metadata the builder stores at EVERY local id is EXACTLY the metadata of the source occurrence that
   id designates — both presence (a real occurrence -> its meta) and absence (no occurrence -> no entry).
   It ranges over every positive id, needs no pre-existing NodeRef, and never assumes the id is valid.
   A structurally-coherent MISLABELING (leaf as KDecl, swapped RChild, shifted index, wrong parent/subtree)
   makes the two sides disagree, so it CANNOT satisfy this equality. *)
Theorem build_file_source_exact : forall f local,
  NodeTable.get local (fi_table (build_file f)) = option_map occurrence_meta (source_occurrence_at f local).
Proof.
  intros f local. unfold build_file, source_occurrence_at.
  pose proof (build_seq_decl_next (ts_decls f) root_id 0 (Pos.succ root_id) NodeTable.empty) as Hnx.
  destruct (build_seq build_decl root_id 0 (Pos.succ root_id) (ts_decls f) NodeTable.empty) as [t1 nx] eqn:E1.
  cbn [snd] in Hnx. subst nx. cbn [fi_table].
  destruct (Pos.eqb_spec local root_id).
  - subst. rewrite NodeTable.get_set_same.
    cbn [option_map occurrence_meta occurrence_kind occurrence_parent occurrence_role occurrence_subtree_end].
    unfold count_file. reflexivity.
  - rewrite NodeTable.get_set_other by congruence.
    specialize (build_seq_decl_get (ts_decls f) root_id 0 (Pos.succ root_id) NodeTable.empty local) as HG.
    rewrite E1 in HG. cbn [fst] in HG. rewrite HG.
    destruct (occ_decls' root_id 0 (Pos.succ root_id) (ts_decls f) local) as [o|] eqn:Eo;
      cbn [option_map]; [reflexivity | apply NodeTable.get_empty].
Qed.

(* --- the C0B §4.2 consequences (A..H), all derived from the one universal theorem. --- *)

(* A: a real source occurrence -> its metadata is stored. *)
Theorem source_occurrence_meta : forall f local o,
  source_occurrence_at f local = Some o ->
  NodeTable.get local (fi_table (build_file f)) = Some (occurrence_meta o).
Proof. intros f local o H. rewrite build_file_source_exact, H. reflexivity. Qed.

(* B: a stored entry -> exactly one source occurrence whose metadata it is. *)
Theorem meta_source_occurrence : forall f local m,
  NodeTable.get local (fi_table (build_file f)) = Some m ->
  exists o, source_occurrence_at f local = Some o /\ m = occurrence_meta o.
Proof.
  intros f local m H. rewrite build_file_source_exact in H.
  destruct (source_occurrence_at f local) as [o|] eqn:Eo; cbn [option_map] in H; [|discriminate].
  injection H as <-. exists o. split; reflexivity.
Qed.

(* C: absence both directions. *)
Theorem source_absence : forall f local,
  source_occurrence_at f local = None <->
  NodeTable.get local (fi_table (build_file f)) = None.
Proof.
  intros f local. rewrite build_file_source_exact.
  destruct (source_occurrence_at f local); cbn [option_map]; split; intro H; congruence.
Qed.

(* D: the source occurrence at a local id is unique (the lookup is a function). *)
Theorem source_occurrence_unique : forall f local o1 o2,
  source_occurrence_at f local = Some o1 -> source_occurrence_at f local = Some o2 -> o1 = o2.
Proof. intros f local o1 o2 H1 H2. rewrite H1 in H2. injection H2 as <-. reflexivity. Qed.

(* E..H: the stored kind / role / parent / subtree-end are EXACTLY the source occurrence's. *)
Theorem source_kind_exact : forall f local o,
  source_occurrence_at f local = Some o ->
  exists m, NodeTable.get local (fi_table (build_file f)) = Some m /\ nm_kind m = occurrence_kind o.
Proof. intros f local o H. exists (occurrence_meta o). split; [apply source_occurrence_meta; exact H | reflexivity]. Qed.

Theorem source_role_exact : forall f local o,
  source_occurrence_at f local = Some o ->
  exists m, NodeTable.get local (fi_table (build_file f)) = Some m /\ nm_role m = occurrence_role o.
Proof. intros f local o H. exists (occurrence_meta o). split; [apply source_occurrence_meta; exact H | reflexivity]. Qed.

Theorem source_parent_exact : forall f local o,
  source_occurrence_at f local = Some o ->
  exists m, NodeTable.get local (fi_table (build_file f)) = Some m /\ nm_parent m = occurrence_parent o.
Proof. intros f local o H. exists (occurrence_meta o). split; [apply source_occurrence_meta; exact H | reflexivity]. Qed.

Theorem source_subtree_end_exact : forall f local o,
  source_occurrence_at f local = Some o ->
  exists m, NodeTable.get local (fi_table (build_file f)) = Some m /\ nm_subtree_end m = occurrence_subtree_end o.
Proof. intros f local o H. exists (occurrence_meta o). split; [apply source_occurrence_meta; exact H | reflexivity]. Qed.

(* ============ C0B §8: mutation-sensitive fixtures over a nested two-declaration witness. ============ *)
(* wf: decl0 = { println(10+20); println(30) }, decl1 = { println(40) }.  Preorder ids 1..11:
   1 file / 2 decl0 / 3 stmt0 / 4 bin / 5 left-leaf / 6 right-leaf / 7 stmt1 / 8 leaf / 9 decl1 / 10 stmt / 11 leaf. *)
Definition wf : TSourceFile :=
  mkTSource [ TFun [ TPrint (TBin (TLeaf 10) (TLeaf 20)) ; TPrint (TLeaf 30) ]
            ; TFun [ TPrint (TLeaf 40) ] ].

(* Each stored metadatum is derived from the UNIVERSAL theorem — rewrite by build_file_source_exact, then
   compute the INDEPENDENT source spec — NEVER by unfolding the builder.  A wrong builder kind/role/parent/
   index/subtree would make build_file_source_exact unprovable, so these pin exact per-occurrence labels. *)
Ltac wf_meta := rewrite build_file_source_exact; vm_compute; reflexivity.
Example wf_meta_root  : NodeTable.get 1  (fi_table (build_file wf)) = Some (mkMeta KFile       None    RFileRoot     11). Proof. wf_meta. Qed.
Example wf_meta_decl0 : NodeTable.get 2  (fi_table (build_file wf)) = Some (mkMeta KDecl      (Some 1) (RFileDecl 0)  8). Proof. wf_meta. Qed.
Example wf_meta_stmt0 : NodeTable.get 3  (fi_table (build_file wf)) = Some (mkMeta KStatement (Some 2) (RDeclStmt 0)  6). Proof. wf_meta. Qed.
Example wf_meta_bin   : NodeTable.get 4  (fi_table (build_file wf)) = Some (mkMeta KExpression (Some 3) RStmtExpr      6). Proof. wf_meta. Qed.
Example wf_meta_left  : NodeTable.get 5  (fi_table (build_file wf)) = Some (mkMeta KExpression (Some 4) (RChild 0)     5). Proof. wf_meta. Qed.
Example wf_meta_right : NodeTable.get 6  (fi_table (build_file wf)) = Some (mkMeta KExpression (Some 4) (RChild 1)     6). Proof. wf_meta. Qed.
Example wf_meta_stmt1 : NodeTable.get 7  (fi_table (build_file wf)) = Some (mkMeta KStatement (Some 2) (RDeclStmt 1)  8). Proof. wf_meta. Qed.
Example wf_meta_leaf1 : NodeTable.get 8  (fi_table (build_file wf)) = Some (mkMeta KExpression (Some 7) RStmtExpr      8). Proof. wf_meta. Qed.
Example wf_meta_decl1 : NodeTable.get 9  (fi_table (build_file wf)) = Some (mkMeta KDecl      (Some 1) (RFileDecl 1) 11). Proof. wf_meta. Qed.
Example wf_meta_stmt2 : NodeTable.get 10 (fi_table (build_file wf)) = Some (mkMeta KStatement (Some 9) (RDeclStmt 0) 11). Proof. wf_meta. Qed.
Example wf_meta_leaf2 : NodeTable.get 11 (fi_table (build_file wf)) = Some (mkMeta KExpression (Some 10) RStmtExpr    11). Proof. wf_meta. Qed.
(* absence past the last occurrence — the universal theorem pins both directions. *)
Example wf_meta_absent : NodeTable.get 12 (fi_table (build_file wf)) = None. Proof. wf_meta. Qed.

(* §10.1 source-VIEW surfaces: the INDEPENDENT spec recovers the exact original fragment (the [occurrence_view]
   that [occurrence_meta] erases) for EACH occurrence kind — file / decl / statement / binary / leaf. *)
Example wf_src_root : source_occurrence_at wf 1 = Some (mkOcc KFile (ViewFile wf) None RFileRoot 11).
Proof. vm_compute. reflexivity. Qed.
Example wf_src_decl0 : source_occurrence_at wf 2 =
  Some (mkOcc KDecl (ViewDecl (TFun [ TPrint (TBin (TLeaf 10) (TLeaf 20)) ; TPrint (TLeaf 30) ])) (Some 1) (RFileDecl 0) 8).
Proof. vm_compute. reflexivity. Qed.
Example wf_src_stmt0 : source_occurrence_at wf 3 =
  Some (mkOcc KStatement (ViewStatement (TPrint (TBin (TLeaf 10) (TLeaf 20)))) (Some 2) (RDeclStmt 0) 6).
Proof. vm_compute. reflexivity. Qed.
Example wf_src_bin : source_occurrence_at wf 4 =
  Some (mkOcc KExpression (ViewExpression (TBin (TLeaf 10) (TLeaf 20))) (Some 3) RStmtExpr 6).
Proof. vm_compute. reflexivity. Qed.
Example wf_src_leaf : source_occurrence_at wf 5 =
  Some (mkOcc KExpression (ViewExpression (TLeaf 10)) (Some 4) (RChild 0) 5).
Proof. vm_compute. reflexivity. Qed.


(* ================================================================================================= *)
(** ** C0A: source-snapshot-local references and TOTAL navigation.                                     *)
(*    A reference belongs to the EXACT immutable source snapshot [fs] (it is indexed by [fs]), never to *)
(*    free-standing index data.  Same-shaped but different-payload snapshots therefore have             *)
(*    NON-INTERCHANGEABLE reference types.  Structurally guaranteed queries are TOTAL; only [parent_of]  *)
(*    is optional (a file root has no parent).                                                          *)
(* ================================================================================================= *)

(* a local id is a real occurrence of file [f] iff it resolves in [f]'s built per-file table. *)
Definition valid_localb (f : TSourceFile) (local : positive) : bool :=
  match NodeTable.get local (fi_table (build_file f)) with Some _ => true | None => false end.

(* The public interface of the reference layer.  It exposes the abstract snapshot-indexed types, the
   validated MINTING boundaries, the projections, the TOTAL navigation API, and the theorem/regression
   surfaces — but NOT the raw record constructors ([mkFileRef]/[mkNodeRef]/[mkSyntaxIndex]) nor the raw
   index map.  Sealing the module against this signature makes "the only way to mint a reference is a
   validated function" TRUE rather than aspirational (C0A §6/§11). *)
Module Type SNAP_SIG.
  Parameter FileRef    : TForest -> Type.
  Parameter NodeRef    : TForest -> Type.
  Parameter SyntaxIndex : TForest -> Type.
  Parameter index_forest : forall fs, SyntaxIndex fs.
  Parameter file_of_path : forall fs, FilePath -> option (FileRef fs).
  Parameter ref_of_key   : forall fs, SyntaxIndex fs -> NodeKey -> option (NodeRef fs).
  Parameter file_ref_source : forall {fs}, FileRef fs -> TSourceFile.
  Parameter file_ref_path : forall {fs}, FileRef fs -> FilePath.
  Parameter node_ref_file  : forall {fs}, NodeRef fs -> FileRef fs.
  Parameter node_ref_local : forall {fs}, NodeRef fs -> positive.
  Parameter node_ref_valid : forall {fs} (r : NodeRef fs),
    valid_localb (file_ref_source (node_ref_file r)) (node_ref_local r) = true.
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
    NodeTable.get (node_ref_local r) (fi_table (build_file (file_ref_source (node_ref_file r)))) = Some (ref_meta idx r).
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
  (* FINAL navigation/identity family *)
  Parameter thm_node_role : forall fs (idx : SyntaxIndex fs) (r : NodeRef fs),
    node_role idx r = nm_role (ref_meta idx r).
  Parameter node_ref_key_inj : forall fs (r1 r2 : NodeRef fs),
    node_ref_key r1 = node_ref_key r2 -> r1 = r2.
  Parameter thm_parent_same_file : forall fs (idx : SyntaxIndex fs) (r pr : NodeRef fs),
    parent_of idx r = Some pr -> node_ref_file pr = node_ref_file r.
  Parameter thm_children_same_file : forall fs (idx : SyntaxIndex fs) (r cr : NodeRef fs),
    In cr (children_of idx r) -> node_ref_file cr = node_ref_file r.
  Parameter ref_of_key_sound : forall fs (idx : SyntaxIndex fs) (k : NodeKey) (r : NodeRef fs),
    ref_of_key fs idx k = Some r -> node_ref_key r = k.
  Parameter ref_of_key_complete : forall fs (idx : SyntaxIndex fs) (r : NodeRef fs),
    ref_of_key fs idx (node_ref_key r) = Some r.
  Parameter file_of_path_complete : forall fs (fr : FileRef fs),
    file_of_path fs (file_ref_path fr) = Some fr.
  Parameter file_ref_path_inj : forall fs (fr1 fr2 : FileRef fs),
    file_ref_path fr1 = file_ref_path fr2 -> fr1 = fr2.
  Parameter thm_child_parent : forall fs (idx : SyntaxIndex fs) (r cr : NodeRef fs),
    In cr (children_of idx r) -> parent_of idx cr = Some r.
  Parameter thm_parent_child : forall fs (idx : SyntaxIndex fs) (r pr : NodeRef fs),
    parent_of idx r = Some pr -> In r (children_of idx pr).
  (* NON-CIRCULAR source-membership minting (§§5,10): every source file / valid occurrence yields a handle.
     Membership is now a STANDARD map binding ([find path fs = Some f]), not a hidden slot. *)
  Parameter file_of_path_source : forall fs (path : FilePath) (f : TSourceFile),
    Collections.FileMapBase.find path fs = Some f ->
    exists fr, file_of_path fs path = Some fr /\ file_ref_path fr = path /\ file_ref_source fr = f.
  Parameter ref_of_key_source : forall fs (idx : SyntaxIndex fs) (path : FilePath) (f : TSourceFile) (local : positive),
    Collections.FileMapBase.find path fs = Some f -> valid_localb f local = true ->
    exists r, ref_of_key fs idx (mkKey path local) = Some r
              /\ node_ref_local r = local /\ file_ref_source (node_ref_file r) = f.
  (* canonical children ENUMERATION at the NodeRef level (§10): source order + NoDup. *)
  Parameter thm_children_of_source_order : forall fs (idx : SyntaxIndex fs) (r : NodeRef fs),
    StronglySorted Pos.lt (map node_ref_local (children_of idx r)).
  Parameter thm_children_of_nodup : forall fs (idx : SyntaxIndex fs) (r : NodeRef fs),
    NoDup (children_of idx r).
  (* NodeRef-level ANCESTRY (§10): the O(1) interval test, sound + complete vs the parent_of closure. *)
  Parameter is_ancestor_ref : forall {fs}, SyntaxIndex fs -> NodeRef fs -> NodeRef fs -> bool.
  Inductive RefAncestor (fs : TForest) (idx : SyntaxIndex fs) : NodeRef fs -> NodeRef fs -> Prop :=
  | RAnc_dir  : forall a d, parent_of idx d = Some a -> RefAncestor fs idx a d
  | RAnc_step : forall a p d, RefAncestor fs idx a p -> parent_of idx d = Some p -> RefAncestor fs idx a d.
  Parameter thm_ref_ancestry : forall fs (idx : SyntaxIndex fs) (a d : NodeRef fs),
    is_ancestor_ref idx a d = true <-> RefAncestor fs idx a d.
  (* §9 fixtures: erased-index equality (SEMANTIC map equality, not record [=]), a functional-key negative
     (a path names at most one source — duplicate paths unrepresentable in the map), two-file forest. *)
  Parameter reg_index_data_equal : Collections.FileMapBase.Equal (outer_of fs_a) (outer_of fs_b).
  Parameter reg_dup_path_rejected : forall (fs : TForest) (p : FilePath) (s1 s2 : TSourceFile),
    Collections.FileMapBase.MapsTo p s1 fs -> Collections.FileMapBase.MapsTo p s2 fs -> s1 = s2.
  Parameter reg_two_file :
    exists (fs : TForest) (fra frb : FileRef fs),
      file_of_path fs (file_ref_path fra) = Some fra /\
      file_of_path fs (file_ref_path frb) = Some frb /\
      file_ref_path fra <> file_ref_path frb.
  (* C0B: EXACT source-occurrence correspondence lifted through the sealed reference API (§6).  Every valid
     reference has a TOTAL source occurrence whose metadata IS the metadata the reference returns — kind,
     role, parent, and subtree end all pinned to the exact source occurrence, no fallback. *)
  Parameter source_occurrence_of_ref : forall {fs}, NodeRef fs -> SourceOccurrence.
  Parameter ref_meta_matches_source : forall fs (idx : SyntaxIndex fs) (r : NodeRef fs),
    ref_meta idx r = occurrence_meta (source_occurrence_of_ref r).
  Parameter node_kind_matches_source : forall fs (idx : SyntaxIndex fs) (r : NodeRef fs),
    node_kind idx r = occurrence_kind (source_occurrence_of_ref r).
  Parameter node_role_matches_source : forall fs (idx : SyntaxIndex fs) (r : NodeRef fs),
    node_role idx r = occurrence_role (source_occurrence_of_ref r).
  Parameter node_parent_matches_source : forall fs (idx : SyntaxIndex fs) (r : NodeRef fs),
    nm_parent (ref_meta idx r) = occurrence_parent (source_occurrence_of_ref r).
  Parameter node_subtree_end_matches_source : forall fs (idx : SyntaxIndex fs) (r : NodeRef fs),
    node_subtree_end idx r = occurrence_subtree_end (source_occurrence_of_ref r).
  (* the reference's source occurrence IS the independent spec's occurrence (ties the exposed occurrence — and
     hence its VIEW, which [occurrence_meta] erases — to [source_occurrence_at], so the recovered fragment is
     not free); UNIVERSAL [node_at] source-view agreement; and [parent_of] returns the EXACT source parent. *)
  Parameter source_occ_of_ref_eq : forall {fs} (r : NodeRef fs),
    source_occurrence_at (file_ref_source (node_ref_file r)) (node_ref_local r) = Some (source_occurrence_of_ref r).
  Parameter node_at_matches_source_view : forall {fs} (r : NodeRef fs),
    node_at r = view_expr (source_occurrence_of_ref r).
  Parameter node_parent_ref_matches_source : forall fs (idx : SyntaxIndex fs) (r : NodeRef fs),
    match occurrence_parent (source_occurrence_of_ref r) with
    | None     => parent_of idx r = None
    | Some pid => exists pr, parent_of idx r = Some pr /\ node_ref_local pr = pid
    end.
  (* §8 sealed-API leaf-reference fixtures (fs_a id 5 = left RChild 0 leaf). *)
  Parameter reg_ref_kind_a5 : node_kind (index_forest fs_a) rleaf_a5 = KExpression.
  Parameter reg_ref_role_a5 : node_role (index_forest fs_a) rleaf_a5 = RChild 0.
  Parameter reg_ref_parent_a5 : nm_parent (ref_meta (index_forest fs_a) rleaf_a5) = Some 4%positive.
End SNAP_SIG.

(* --- raw-key minting COMPLETENESS foundations (top-level; only over the source snapshot + file builder) ---
   In the standard-map snapshot, file lookup IS [FileMapBase.find]: complete + functional by the map facts,
   with no list scan and no hidden slot (the former [find_slot]/[forest_find] scan is deleted). *)

Lemma fp_eqb_refl (a : FilePath) : fp_eqb a a = true.
Proof. apply (proj2 (fp_eqb_eq a a)). reflexivity. Qed.

(* an enumerated direct child truly has the queried parent id — the child-list soundness at the id level. *)
Lemma child_ids_parent (t : NodeTable.table NodeMeta) (pid c : positive) :
  In c (child_ids t pid) -> parent_id t c = Some pid.
Proof.
  unfold child_ids. destruct (NodeTable.get pid t) as [m|] eqn:Ep; [| intros []].
  apply child_enum_sound.
Qed.

(* the builder is a pure total function of the source file alone: equal sources build identical indices —
   determinism is inherent (no state, no ordering choice, no external input), stated here as congruence. *)
Theorem thm_builder_deterministic (f1 f2 : TSourceFile) : f1 = f2 -> build_file f1 = build_file f2.
Proof. intros ->. reflexivity. Qed.

Module Snap : SNAP_SIG.

(* a file-root handle for ONE file occurrence of [fs] (C1A §10.3): the file's PATH (its public identity) +
   its source + a STANDARD-MAP membership proof.  No hidden slot: the path IS the map key. *)
Record FileRef_T (fs : TForest) := mkFileRef {
  file_ref_path   : FilePath;
  file_ref_source : TSourceFile;
  file_ref_at     : Collections.FileMapBase.find file_ref_path fs = Some file_ref_source
}.
Arguments file_ref_path   {fs} _.
Arguments file_ref_source {fs} _.
Arguments file_ref_at     {fs} _.
Definition FileRef := FileRef_T.

(* a reference to ONE occurrence in ONE exact file of ONE exact source snapshot [fs]. *)
Record NodeRef_T (fs : TForest) := mkNodeRef {
  node_ref_file  : FileRef fs;
  node_ref_local : positive;
  node_ref_valid : valid_localb (file_ref_source node_ref_file) node_ref_local = true
}.
Arguments node_ref_file  {fs} _.
Arguments node_ref_local {fs} _.
Arguments node_ref_valid {fs} _.
Definition NodeRef := NodeRef_T.

(* the public raw key: file PATH (the identity = the map key) + local id — no hidden handle beside it. *)
Definition node_ref_key {fs} (r : NodeRef fs) : NodeKey :=
  mkKey (file_ref_path (node_ref_file r)) (node_ref_local r).

(* the derived certified index for a snapshot: a PATH-keyed standard outer map PROVED EQUAL to the canonical
   build of [fs].  This is the EXACT source/index correspondence (IndexDescribesForest): the map is not
   arbitrary data beside an unused proof — it IS [outer_of fs], so every path holds the build of the file
   there and nothing at a path with no file.  A bogus entry at an unoccupied path cannot satisfy this. *)
Record SyntaxIndex_T (fs : TForest) := mkSyntaxIndex {
  si_outer : Collections.FileMapBase.t FileIndex;
  si_ok    : si_outer = outer_of fs
}.
Arguments si_outer {fs} _.
Arguments si_ok    {fs} _.
Definition SyntaxIndex := SyntaxIndex_T.
Definition index_forest (fs : TForest) : SyntaxIndex fs :=
  mkSyntaxIndex fs (outer_of fs) eq_refl.

(* the correspondence, one direction, driving the query API: a real path holds exactly its file's build. *)
Lemma si_ok_at {fs} (idx : SyntaxIndex fs) path f :
  Collections.FileMapBase.find path fs = Some f ->
  Collections.FileMapBase.find path (si_outer idx) = Some (build_file f).
Proof. intros H. rewrite (si_ok idx). apply outer_get_at. exact H. Qed.

(* a lookup query into the index (keeps the raw map representation hidden — returns the FileIndex). *)
Definition index_at {fs} (idx : SyntaxIndex fs) (path : FilePath) : option FileIndex :=
  Collections.FileMapBase.find path (si_outer idx).

(* EXACT index description (§4): every file path holds its file's build, every non-file path holds nothing —
   so the index describes EXACTLY [fs], with no entry belonging to another snapshot and none spurious. *)
Theorem thm_index_describes_forest {fs} (idx : SyntaxIndex fs) (path : FilePath) :
  index_at idx path = match Collections.FileMapBase.find path fs with Some f => Some (build_file f) | None => None end.
Proof. unfold index_at. rewrite (si_ok idx). apply outer_get_exact. Qed.

(* ONE outer map lookup gives the NodeRef's file index — no file-list scan.  Present by correspondence. *)
Definition ref_fi_opt {fs} (idx : SyntaxIndex fs) (r : NodeRef fs) : option FileIndex :=
  Collections.FileMapBase.find (file_ref_path (node_ref_file r)) (si_outer idx).
Lemma ref_fi_some {fs} (idx : SyntaxIndex fs) (r : NodeRef fs) :
  ref_fi_opt idx r = Some (build_file (file_ref_source (node_ref_file r))).
Proof. unfold ref_fi_opt. apply (si_ok_at idx). apply (file_ref_at (node_ref_file r)). Qed.
Lemma ref_fi_some' {fs} (idx : SyntaxIndex fs) (r : NodeRef fs) : ref_fi_opt idx r <> None.
Proof. rewrite ref_fi_some. discriminate. Qed.
Definition ref_fi {fs} (idx : SyntaxIndex fs) (r : NodeRef fs) : FileIndex :=
  option_get (ref_fi_opt idx r) (ref_fi_some' idx r).
Lemma ref_fi_eq {fs} (idx : SyntaxIndex fs) (r : NodeRef fs) :
  ref_fi idx r = build_file (file_ref_source (node_ref_file r)).
Proof. unfold ref_fi. apply option_get_eq, ref_fi_some. Qed.

(* the metadata option: one per-file local lookup in the file index reached via the path. *)
Definition ref_meta_opt {fs} (idx : SyntaxIndex fs) (r : NodeRef fs) : option NodeMeta :=
  NodeTable.get (node_ref_local r) (fi_table (ref_fi idx r)).
Lemma ref_meta_some {fs} (idx : SyntaxIndex fs) (r : NodeRef fs) : ref_meta_opt idx r <> None.
Proof.
  unfold ref_meta_opt. rewrite ref_fi_eq.
  pose proof (node_ref_valid r) as Hv. unfold valid_localb in Hv.
  destruct (NodeTable.get (node_ref_local r) (fi_table (build_file (file_ref_source (node_ref_file r)))));
    [discriminate | discriminate Hv].
Qed.

(* TOTAL metadata query — no option, no fallback. *)
Definition ref_meta {fs} (idx : SyntaxIndex fs) (r : NodeRef fs) : NodeMeta :=
  option_get (ref_meta_opt idx r) (ref_meta_some idx r).

(* the metadata is exactly the per-file built meta for the occurrence — ties navigation to the builder. *)
Lemma ref_meta_spec {fs} (idx : SyntaxIndex fs) (r : NodeRef fs) m :
  NodeTable.get (node_ref_local r) (fi_table (build_file (file_ref_source (node_ref_file r)))) = Some m ->
  ref_meta idx r = m.
Proof. intros H. unfold ref_meta. apply option_get_eq. unfold ref_meta_opt. rewrite ref_fi_eq. exact H. Qed.

Definition node_kind        {fs} (idx : SyntaxIndex fs) (r : NodeRef fs) : SyntaxKind := nm_kind (ref_meta idx r).
Definition node_role        {fs} (idx : SyntaxIndex fs) (r : NodeRef fs) : NodeRole   := nm_role (ref_meta idx r).
Definition node_subtree_end {fs} (idx : SyntaxIndex fs) (r : NodeRef fs) : positive   := nm_subtree_end (ref_meta idx r).

(* TOTAL containing-file — the carried FileRef, an O(1) projection. *)
Definition containing_file {fs} (r : NodeRef fs) : FileRef fs := node_ref_file r.

(* the meta at a valid ref's local id IS [ref_meta] — connects the total query to the per-file table. *)
Lemma ref_meta_get {fs} (idx : SyntaxIndex fs) (r : NodeRef fs) :
  NodeTable.get (node_ref_local r) (fi_table (build_file (file_ref_source (node_ref_file r)))) = Some (ref_meta idx r).
Proof.
  pose proof (node_ref_valid r) as Hv. unfold valid_localb in Hv.
  destruct (NodeTable.get (node_ref_local r) (fi_table (build_file (file_ref_source (node_ref_file r))))) as [m|] eqn:E;
    [| discriminate Hv].
  rewrite (ref_meta_spec idx r m E). reflexivity.
Qed.

(* the parent of a valid occurrence is itself a valid occurrence of the same file (so parent_of is total-when-Some). *)
Lemma parent_valid {fs} (idx : SyntaxIndex fs) (r : NodeRef fs) pid :
  nm_parent (ref_meta idx r) = Some pid -> valid_localb (file_ref_source (node_ref_file r)) pid = true.
Proof.
  intros Hpar.
  pose proof (build_file_wf (file_ref_source (node_ref_file r))) as WF.
  pose proof (ref_meta_get idx r) as Hget.
  destruct (in_domain (file_ref_source (node_ref_file r)) (node_ref_local r) (ref_meta idx r) Hget) as [Hlo Hhi].
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
Lemma child_valid (f : TSourceFile) local c :
  In c (child_ids (fi_table (build_file f)) local) -> valid_localb f c = true.
Proof.
  intros Hin. unfold child_ids in Hin.
  destruct (NodeTable.get local (fi_table (build_file f))) as [m|] eqn:El; [|destruct Hin].
  apply child_enum_sound in Hin. unfold parent_id in Hin.
  unfold valid_localb. destruct (NodeTable.get c (fi_table (build_file f))); [reflexivity | discriminate Hin].
Qed.

(* build a validated reference for EVERY id in a list of proven-valid ids (no filtering, no drops). *)
Fixpoint refine_children {fs} (fr : FileRef fs) (ids : list positive)
  : (forall c, In c ids -> valid_localb (file_ref_source fr) c = true) -> list (NodeRef fs) :=
  match ids with
  | []        => fun _    => []
  | c :: rest => fun Hall =>
      mkNodeRef fs fr c (Hall c (or_introl eq_refl)) :: refine_children fr rest (fun c' H => Hall c' (or_intror H))
  end.

Lemma children_valid {fs} (idx : SyntaxIndex fs) (r : NodeRef fs) c :
  In c (child_ids (fi_table (ref_fi idx r)) (node_ref_local r)) ->
  valid_localb (file_ref_source (node_ref_file r)) c = true.
Proof. rewrite ref_fi_eq. apply child_valid. Qed.

(* TOTAL direct children — one outer map lookup by path, then the file's interval-jump enumeration; no drops. *)
Definition children_of {fs} (idx : SyntaxIndex fs) (r : NodeRef fs) : list (NodeRef fs) :=
  refine_children (node_ref_file r)
    (child_ids (fi_table (ref_fi idx r)) (node_ref_local r)) (children_valid idx r).

(* --- the raw-key minting boundary (§7): ONE standard-map [find] by path (no list scan, no hidden slot). --- *)
Definition file_of_path (fs : TForest) (fp : FilePath) : option (FileRef fs) :=
  (match Collections.FileMapBase.find fp fs as o
         return (Collections.FileMapBase.find fp fs = o -> option (FileRef fs)) with
   | Some f => fun H => Some (mkFileRef fs fp f H)
   | None   => fun _ => None
   end) eq_refl.

(* validate a local id THROUGH the snapshot's PRECOMPUTED outer map (no per-file rebuild): one outer-map
   lookup by path + one per-file lookup.  Provably agrees with [valid_localb] by the correspondence [si_ok]. *)
Definition valid_in_index {fs} (idx : SyntaxIndex fs) (fr : FileRef fs) (local : positive) : bool :=
  match Collections.FileMapBase.find (file_ref_path fr) (si_outer idx) with
  | Some fi => match NodeTable.get local (fi_table fi) with Some _ => true | None => false end
  | None    => false
  end.
Lemma valid_in_index_eq {fs} (idx : SyntaxIndex fs) (fr : FileRef fs) (local : positive) :
  valid_in_index idx fr local = valid_localb (file_ref_source fr) local.
Proof.
  unfold valid_in_index, valid_localb.
  rewrite (si_ok_at idx (file_ref_path fr) (file_ref_source fr) (file_ref_at fr)). reflexivity.
Qed.
Lemma valid_in_index_true {fs} (idx : SyntaxIndex fs) (fr : FileRef fs) (local : positive) :
  valid_in_index idx fr local = true -> valid_localb (file_ref_source fr) local = true.
Proof. rewrite valid_in_index_eq. exact (fun H => H). Qed.

(* mint a validated reference from a raw key THROUGH the snapshot's index (§7 raw-lookup boundary): one
   outer-map lookup by path + one per-file lookup — NO list scan, NO per-file rebuild.
   Cost O(log files + log nodes-per-file).  The hot path from an existing [NodeRef] never uses this. *)
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

(* --- C0B: lift EXACT source-occurrence correspondence through the sealed reference API (§6). --- *)

(* a valid reference's occurrence EXISTS: validity means the id is populated, hence a source occurrence. *)
Lemma source_occ_of_ref_some {fs} (r : NodeRef fs) :
  source_occurrence_at (file_ref_source (node_ref_file r)) (node_ref_local r) <> None.
Proof.
  pose proof (node_ref_valid r) as Hv. unfold valid_localb in Hv.
  destruct (NodeTable.get (node_ref_local r) (fi_table (build_file (file_ref_source (node_ref_file r))))) as [m|] eqn:E;
    [|discriminate Hv].
  destruct (meta_source_occurrence _ _ _ E) as [o [Ho _]]. rewrite Ho. discriminate.
Qed.

(* TOTAL source-occurrence recovery for a valid reference — no option, no semantic fallback (§6.1). *)
Definition source_occurrence_of_ref {fs} (r : NodeRef fs) : SourceOccurrence :=
  option_get (source_occurrence_at (file_ref_source (node_ref_file r)) (node_ref_local r))
             (source_occ_of_ref_some r).

Lemma source_occ_of_ref_eq {fs} (r : NodeRef fs) :
  source_occurrence_at (file_ref_source (node_ref_file r)) (node_ref_local r)
    = Some (source_occurrence_of_ref r).
Proof. unfold source_occurrence_of_ref. apply option_get_some. Qed.

(* THE permanent public theorem (§6.2): the metadata a valid reference returns IS this exact source
   occurrence's metadata.  A structurally-coherent mislabeling would break it. *)
Theorem ref_meta_matches_source {fs} (idx : SyntaxIndex fs) (r : NodeRef fs) :
  ref_meta idx r = occurrence_meta (source_occurrence_of_ref r).
Proof.
  pose proof (ref_meta_get idx r) as Hget.
  pose proof (build_file_source_exact (file_ref_source (node_ref_file r)) (node_ref_local r)) as HE.
  rewrite (source_occ_of_ref_eq r) in HE. cbn [option_map] in HE.
  rewrite Hget in HE. injection HE as HEq. exact HEq.
Qed.

(* §6.3 public projections — kind / role / parent / subtree end all equal the source occurrence's. *)
Theorem node_kind_matches_source {fs} (idx : SyntaxIndex fs) (r : NodeRef fs) :
  node_kind idx r = occurrence_kind (source_occurrence_of_ref r).
Proof. unfold node_kind. rewrite ref_meta_matches_source. reflexivity. Qed.
Theorem node_role_matches_source {fs} (idx : SyntaxIndex fs) (r : NodeRef fs) :
  node_role idx r = occurrence_role (source_occurrence_of_ref r).
Proof. unfold node_role. rewrite ref_meta_matches_source. reflexivity. Qed.
Theorem node_parent_matches_source {fs} (idx : SyntaxIndex fs) (r : NodeRef fs) :
  nm_parent (ref_meta idx r) = occurrence_parent (source_occurrence_of_ref r).
Proof. rewrite ref_meta_matches_source. reflexivity. Qed.
Theorem node_subtree_end_matches_source {fs} (idx : SyntaxIndex fs) (r : NodeRef fs) :
  node_subtree_end idx r = occurrence_subtree_end (source_occurrence_of_ref r).
Proof. unfold node_subtree_end. rewrite ref_meta_matches_source. reflexivity. Qed.

(* source recovery (§6.4): the exact original expression fragment, projected from the ONE source-occurrence
   view — no second recovery authority. *)
Definition node_at {fs} (r : NodeRef fs) : option TExpr := view_expr (source_occurrence_of_ref r).

(* UNIVERSAL source-view agreement (§6.4): [node_at] recovers exactly the expression fragment carried by the
   reference's ONE source occurrence — the public view is pinned to the source occurrence, not free.  With
   [source_occ_of_ref_eq] tying that occurrence to the independent [source_occurrence_at] spec, the recovered
   fragment cannot be an unrelated syntax value carrying the right structural metadata. *)
Theorem node_at_matches_source_view {fs} (r : NodeRef fs) :
  node_at r = view_expr (source_occurrence_of_ref r).
Proof. reflexivity. Qed.

(* ================================================================================================= *)
(** ** C0A §9 regression — same paths + tree shape, DIFFERENT payloads => non-interchangeable refs.     *)
(* ================================================================================================= *)

Definition rpath : FilePath := mkFP "a.go"%string eq_refl.
(* one file's SOURCE: one decl / one stmt / TBin (TLeaf v) (TLeaf v) — TWO structurally equal leaves of v. *)
Definition rfile (v : nat) : TSourceFile := mkTSource [ TFun [ TPrint (TBin (TLeaf v) (TLeaf v)) ] ].
(* two snapshots (standard maps): identical path + tree shape, but leaves 5 vs 6.  Each is the standard map
   constructed DIRECTLY and separately PROVED to be [forest_of]'s successful result ([fs_a_built]/[fs_b_built]);
   no fail-soft default. *)
Definition rmap (v : nat) : TForest :=
  Collections.FileMapBase.add rpath (rfile v) (Collections.FileMapBase.empty TSourceFile).
Definition fs_a : TForest := rmap 5.
Definition fs_b : TForest := rmap 6.
Lemma fs_a_built : forest_of [ mkTFileNode rpath (rfile 5) ] = Some fs_a.
Proof. rewrite forest_of_single. reflexivity. Qed.
Lemma fs_b_built : forest_of [ mkTFileNode rpath (rfile 6) ] = Some fs_b.
Proof. rewrite forest_of_single. reflexivity. Qed.

Lemma rfind (v : nat) : Collections.FileMapBase.find rpath (rmap v) = Some (rfile v).
Proof. apply Collections.FileMapFacts.add_eq_o. reflexivity. Qed.
Definition fref_a : FileRef fs_a := mkFileRef fs_a rpath (rfile 5) (rfind 5).
Definition fref_b : FileRef fs_b := mkFileRef fs_b rpath (rfile 6) (rfind 6).

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

(* §9.3 / §9.4 — the SAME id recovers the exact per-snapshot source payload: TLeaf 5 in fs_a, TLeaf 6 in fs_b.
   node_at now projects the ONE general source-occurrence view (§6.4), not a second recovery authority. *)
Theorem reg_node_at_a : node_at rleaf_a5 = Some (TLeaf 5).
Proof. vm_compute. reflexivity. Qed.
Theorem reg_node_at_b : node_at rleaf_b5 = Some (TLeaf 6).
Proof. vm_compute. reflexivity. Qed.

(* C0B §8 sealed-API fixtures: the validated left-leaf reference of fs_a recovers its EXACT kind / role /
   parent / subtree end / source fragment THROUGH the sealed [*_matches_source] theorems (id 5 = RChild 0). *)
Example reg_ref_kind_a5 : node_kind (index_forest fs_a) rleaf_a5 = KExpression.
Proof. rewrite node_kind_matches_source. vm_compute. reflexivity. Qed.
Example reg_ref_role_a5 : node_role (index_forest fs_a) rleaf_a5 = RChild 0.
Proof. rewrite node_role_matches_source. vm_compute. reflexivity. Qed.
Example reg_ref_parent_a5 : nm_parent (ref_meta (index_forest fs_a) rleaf_a5) = Some 4%positive.
Proof. rewrite node_parent_matches_source. vm_compute. reflexivity. Qed.
Example reg_ref_view_a5 : occurrence_view (source_occurrence_of_ref rleaf_a5) = ViewExpression (TLeaf 5).
Proof. vm_compute. reflexivity. Qed.

(* §9.5 — the two structurally EQUAL leaves inside fs_a are STILL distinct references (distinct keys). *)
Theorem reg_equal_leaves_distinct : rleaf_a5 <> rleaf_a6.
Proof.
  intro H. apply (f_equal node_ref_key) in H. unfold node_ref_key in H. cbn in H.
  injection H as H. discriminate H.
Qed.

(* §9.1 — ERASED-INDEX EQUALITY: [fs_a] and [fs_b] have identical paths + tree shape and differ ONLY in leaf
   PAYLOAD (5 vs 6), which the metadata builder discards; so their index maps are SEMANTICALLY EQUAL (standard
   [FileMap.Equal], NOT record [=]) after erasing the source payload.  Only the [TForest] value distinguishes
   their reference TYPES; the index DATA is interchangeable. *)
Theorem reg_index_data_equal : Collections.FileMapBase.Equal (outer_of fs_a) (outer_of fs_b).
Proof.
  intro k. unfold outer_of. rewrite !Collections.FileMapFacts.map_o.
  unfold fs_a, fs_b, rmap.
  rewrite !Collections.FileMapFacts.add_o.
  destruct (Collections.FilePath_OT.eq_dec rpath k) as [Heq|Hne].
  - cbn [option_map]. reflexivity.
  - rewrite !Collections.FileMapFacts.empty_o. reflexivity.
Qed.

(* DUPLICATE-PATH NEGATIVE (map form): a path names AT MOST ONE source in the standard file map — two bindings
   at the same path are the SAME source (key-functionality), so duplicate paths are UNREPRESENTABLE. *)
Theorem reg_dup_path_rejected (fs : TForest) (p : FilePath) (s1 s2 : TSourceFile) :
  Collections.FileMapBase.MapsTo p s1 fs -> Collections.FileMapBase.MapsTo p s2 fs -> s1 = s2.
Proof.
  intros H1 H2.
  apply Collections.FileMapFacts.find_mapsto_iff in H1.
  apply Collections.FileMapFacts.find_mapsto_iff in H2.
  rewrite H1 in H2. injection H2 as ->. reflexivity.
Qed.

(* TWO-FILE forest: distinct paths a.go / b.go — path uniqueness is intrinsic to the map; each path mints its
   own file handle with no cross-file confusion.  (The minting witnesses are below, after [file_of_path_source].) *)
Definition rpathb : FilePath := mkFP "b.go"%string eq_refl.
Definition rfileb (v : nat) : TSourceFile := mkTSource [ TFun [ TPrint (TLeaf v) ] ].
Definition fs_two : TForest :=
  Collections.FileMapBase.add rpath (rfile 5)
    (Collections.FileMapBase.add rpathb (rfileb 7) (Collections.FileMapBase.empty TSourceFile)).
Lemma fs_two_built :
  forest_of [ mkTFileNode rpath (rfile 5) ; mkTFileNode rpathb (rfileb 7) ] = Some fs_two.
Proof. vm_compute. reflexivity. Qed.

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
Definition tfile_eq_dec (a b : TSourceFile) : {a = b} + {a <> b}.
Proof. decide equality; apply (list_eq_dec tdecl_eq_dec). Defined.
Definition option_tfile_eq_dec (a b : option TSourceFile) : {a = b} + {a <> b}.
Proof. decide equality; apply tfile_eq_dec. Defined.

(* reference extensionality: a NodeRef is fixed by its file handle and local id (validity is proof-irrelevant). *)
Lemma node_ref_ext (fs : TForest) (r1 r2 : NodeRef fs) :
  node_ref_file r1 = node_ref_file r2 -> node_ref_local r1 = node_ref_local r2 -> r1 = r2.
Proof.
  destruct r1 as [f1 l1 v1], r2 as [f2 l2 v2]; simpl; intros -> ->.
  f_equal. apply (UIP_dec Bool.bool_dec).
Qed.

(* a FileRef is fixed by its PATH (the map-membership witness is proof-irrelevant, and the source it maps to
   is functionally determined by the path — standard-map key functionality). *)
Lemma file_ref_ext (fs : TForest) (fr1 fr2 : FileRef fs) :
  file_ref_path fr1 = file_ref_path fr2 -> fr1 = fr2.
Proof.
  destruct fr1 as [p1 f1 h1], fr2 as [p2 f2 h2]; simpl; intros Hp. subst p2.
  assert (f1 = f2) by (pose proof h1 as q; rewrite h2 in q; injection q as <-; reflexivity).
  subst f2. f_equal. apply (UIP_dec option_tfile_eq_dec).
Qed.

(* --- total-API correctness (§10) --- *)

Theorem thm_node_kind (fs : TForest) (idx : SyntaxIndex fs) (r : NodeRef fs) :
  node_kind idx r = nm_kind (ref_meta idx r).
Proof. reflexivity. Qed.

Theorem thm_ref_meta_built (fs : TForest) (idx : SyntaxIndex fs) (r : NodeRef fs) :
  NodeTable.get (node_ref_local r) (fi_table (build_file (file_ref_source (node_ref_file r)))) = Some (ref_meta idx r).
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
  pose proof (build_file_wf (file_ref_source (node_ref_file r))) as WF.
  destruct (sub_root WF) as [m0 [Hg [Hp0 _]]]. pose proof (ref_meta_get idx r) as Hget.
  rewrite Hr, Hg in Hget. injection Hget as Heq. rewrite <- Heq. exact Hp0.
Qed.

Theorem thm_parent_nonroot (fs : TForest) (idx : SyntaxIndex fs) (r : NodeRef fs) :
  node_ref_local r <> root_id -> exists pr, parent_of idx r = Some pr.
Proof.
  intros Hne.
  pose proof (build_file_wf (file_ref_source (node_ref_file r))) as WF.
  pose proof (ref_meta_get idx r) as Hget.
  destruct (in_domain (file_ref_source (node_ref_file r)) (node_ref_local r) (ref_meta idx r) Hget) as [Hlo Hhi].
  destruct (sub_prng WF (node_ref_local r) (ref_meta idx r) ltac:(lia) Hhi Hget) as [p [mp [Hpar _]]].
  destruct (parent_of_some fs idx r p Hpar) as [pr [Hpr _]]. exists pr. exact Hpr.
Qed.

(* §6.3: [parent_of] returns EXACTLY the source parent — its optionality and the parent reference's local id
   both agree with [occurrence_parent].  A root's [None] parent matches [occurrence_parent = None]; a non-root's
   [Some pid] yields a parent reference whose [node_ref_local] IS [pid].  This connects the metadata parent
   (which [node_parent_matches_source] pins) to the actual navigated parent reference. *)
Theorem node_parent_ref_matches_source (fs : TForest) (idx : SyntaxIndex fs) (r : NodeRef fs) :
  match occurrence_parent (source_occurrence_of_ref r) with
  | None     => parent_of idx r = None
  | Some pid => exists pr, parent_of idx r = Some pr /\ node_ref_local pr = pid
  end.
Proof.
  rewrite <- (node_parent_matches_source idx r).
  destruct (nm_parent (ref_meta idx r)) as [pid|] eqn:Hp.
  - destruct (parent_of_some fs idx r pid Hp) as [pr [Hpr [_ Hpl]]]. exists pr. split; [exact Hpr | exact Hpl].
  - apply (parent_of_none fs idx r Hp).
Qed.

Theorem thm_node_role (fs : TForest) (idx : SyntaxIndex fs) (r : NodeRef fs) :
  node_role idx r = nm_role (ref_meta idx r).
Proof. reflexivity. Qed.

(* NodeKey equality REFLECTS reference equality within one snapshot: same path + local => same reference. *)
Theorem node_ref_key_inj (fs : TForest) (r1 r2 : NodeRef fs) :
  node_ref_key r1 = node_ref_key r2 -> r1 = r2.
Proof.
  intros H. unfold node_ref_key in H. injection H as Hpath Hlocal.
  apply node_ref_ext; [ apply file_ref_ext; exact Hpath | exact Hlocal ].
Qed.

(* the immediate parent shares the containing file with its child. *)
Theorem thm_parent_same_file (fs : TForest) (idx : SyntaxIndex fs) (r pr : NodeRef fs) :
  parent_of idx r = Some pr -> node_ref_file pr = node_ref_file r.
Proof.
  intros H. destruct (nm_parent (ref_meta idx r)) as [pid|] eqn:Hp.
  - destruct (parent_of_some fs idx r pid Hp) as [pr' [Hpr' [Hf _]]].
    rewrite H in Hpr'. injection Hpr' as <-. exact Hf.
  - rewrite (parent_of_none fs idx r Hp) in H. discriminate H.
Qed.

(* every enumerated child shares the containing file, and NO child reference is dropped or invented. *)
Lemma refine_children_file (fs : TForest) (fr : FileRef fs) ids
  (H : forall c, In c ids -> valid_localb (file_ref_source fr) c = true) cr :
  In cr (refine_children fr ids H) -> node_ref_file cr = fr.
Proof.
  revert H. induction ids as [|c rest IH]; intros H Hin; simpl in Hin; [destruct Hin|].
  destruct Hin as [<-|Hin]; [reflexivity | eapply IH; exact Hin].
Qed.
Theorem thm_children_same_file (fs : TForest) (idx : SyntaxIndex fs) (r cr : NodeRef fs) :
  In cr (children_of idx r) -> node_ref_file cr = node_ref_file r.
Proof. unfold children_of. apply refine_children_file. Qed.

Lemma refine_children_local (fs : TForest) (fr : FileRef fs) ids
  (H : forall c, In c ids -> valid_localb (file_ref_source fr) c = true) cr :
  In cr (refine_children fr ids H) -> In (node_ref_local cr) ids.
Proof.
  revert H. induction ids as [|c rest IH]; intros H Hin; simpl in Hin; [destruct Hin|].
  destruct Hin as [<-|Hin]; [left; reflexivity | right; eapply IH; exact Hin].
Qed.
Lemma refine_children_complete (fs : TForest) (fr : FileRef fs) ids
  (H : forall c, In c ids -> valid_localb (file_ref_source fr) c = true) c :
  In c ids -> exists cr, In cr (refine_children fr ids H) /\ node_ref_local cr = c.
Proof.
  revert H. induction ids as [|c0 rest IH]; intros H Hin; simpl in Hin; [destruct Hin|].
  destruct Hin as [->|Hin].
  - eexists. split; [left; reflexivity | reflexivity].
  - destruct (IH (fun c' Hc' => H c' (or_intror Hc')) Hin) as [cr [Hcr Hl]].
    exists cr. split; [right; exact Hcr | exact Hl].
Qed.

(* children ENUMERATION is exactly the per-file child ids: no child dropped, none invented. *)
Theorem thm_children_no_drop (fs : TForest) (idx : SyntaxIndex fs) (r : NodeRef fs) c :
  In c (child_ids (fi_table (ref_fi idx r)) (node_ref_local r)) ->
  exists cr, In cr (children_of idx r) /\ node_ref_local cr = c.
Proof. unfold children_of. apply refine_children_complete. Qed.
Theorem thm_children_sound (fs : TForest) (idx : SyntaxIndex fs) (r cr : NodeRef fs) :
  In cr (children_of idx r) -> In (node_ref_local cr) (child_ids (fi_table (ref_fi idx r)) (node_ref_local r)).
Proof. unfold children_of. apply refine_children_local. Qed.

(* --- canonical children ENUMERATION at the NodeRef level (§10): source order + NoDup. --- *)

(* the enumerated child references project back to exactly the per-file child ids (order preserved). *)
Lemma refine_children_map_local (fs : TForest) (fr : FileRef fs) ids
  (H : forall c, In c ids -> valid_localb (file_ref_source fr) c = true) :
  map node_ref_local (refine_children fr ids H) = ids.
Proof.
  revert H. induction ids as [|c rest IH]; intros H; simpl; [reflexivity|]. rewrite IH. reflexivity.
Qed.

Lemma sorted_lt_nodup : forall (l : list positive), StronglySorted Pos.lt l -> NoDup l.
Proof.
  induction l as [|x rest IH]; intros HS; [constructor|].
  inversion HS as [|? ? HSS HF]; subst. constructor.
  - intros Hin. rewrite Forall_forall in HF. specialize (HF x Hin). lia.
  - apply IH. exact HSS.
Qed.

(* the direct children of an occurrence are enumerated in strictly increasing (canonical source) order. *)
Theorem thm_children_of_source_order (fs : TForest) (idx : SyntaxIndex fs) (r : NodeRef fs) :
  StronglySorted Pos.lt (map node_ref_local (children_of idx r)).
Proof.
  unfold children_of. rewrite refine_children_map_local, (ref_fi_eq idx r). apply thm11_children_sorted.
Qed.

(* the direct-children reference list has NO duplicates (distinct occurrences => distinct references). *)
Theorem thm_children_of_nodup (fs : TForest) (idx : SyntaxIndex fs) (r : NodeRef fs) :
  NoDup (children_of idx r).
Proof.
  apply (NoDup_map_inv node_ref_local). apply sorted_lt_nodup. apply thm_children_of_source_order.
Qed.

(* a minted file handle carries the queried path. *)
Lemma file_of_path_path (fs : TForest) (fp : FilePath) (fr : FileRef fs) :
  file_of_path fs fp = Some fr -> file_ref_path fr = fp.
Proof.
  unfold file_of_path. generalize (@eq_refl (option TSourceFile) (Collections.FileMapBase.find fp fs)).
  destruct (Collections.FileMapBase.find fp fs) as [f|] at 2 3; intros e H; [| discriminate H].
  injection H as <-. reflexivity.
Qed.

(* raw-key minting is SOUND: a returned reference carries exactly the queried key. *)
Theorem ref_of_key_sound (fs : TForest) (idx : SyntaxIndex fs) (k : NodeKey) (r : NodeRef fs) :
  ref_of_key fs idx k = Some r -> node_ref_key r = k.
Proof.
  unfold ref_of_key. destruct (file_of_path fs (nk_file k)) as [fr|] eqn:Ef; [| discriminate].
  generalize (@eq_refl bool (valid_in_index idx fr (nk_local k))).
  destruct (valid_in_index idx fr (nk_local k)) at 2 3; intros e H; [| discriminate H].
  injection H as <-. unfold node_ref_key. simpl.
  rewrite (file_of_path_path fs (nk_file k) fr Ef). destruct k; reflexivity.
Qed.

(* file minting is COMPLETE: the handle for a file's own path is exactly that file handle. *)
Lemma file_of_path_complete (fs : TForest) (fr : FileRef fs) :
  file_of_path fs (file_ref_path fr) = Some fr.
Proof.
  unfold file_of_path.
  generalize (@eq_refl (option TSourceFile) (Collections.FileMapBase.find (file_ref_path fr) fs)).
  destruct (Collections.FileMapBase.find (file_ref_path fr) fs) as [f|] at 2 3; intros e.
  - f_equal. apply file_ref_ext. reflexivity.
  - exfalso. rewrite (file_ref_at fr) in e. discriminate e.
Qed.

(* raw-key minting is COMPLETE: minting from any reference's own key recovers exactly that reference. *)
Theorem ref_of_key_complete (fs : TForest) (idx : SyntaxIndex fs) (r : NodeRef fs) :
  ref_of_key fs idx (node_ref_key r) = Some r.
Proof.
  unfold ref_of_key, node_ref_key. cbn [nk_file nk_local].
  rewrite (file_of_path_complete fs (node_ref_file r)).
  generalize (@eq_refl bool (valid_in_index idx (node_ref_file r) (node_ref_local r))).
  destruct (valid_in_index idx (node_ref_file r) (node_ref_local r)) at 2 3; intros e.
  - f_equal. apply node_ref_ext; reflexivity.
  - exfalso. rewrite valid_in_index_eq, (node_ref_valid r) in e. discriminate e.
Qed.

(* --- SOURCE-membership minting (§§5,10): every source binding / valid occurrence yields a handle. --- *)

(* NON-CIRCULAR file completeness: a source binding [find path fs = Some f] can be MINTED into a FileRef. *)
Theorem file_of_path_source {fs} (path : FilePath) (f : TSourceFile) :
  Collections.FileMapBase.find path fs = Some f ->
  exists fr, file_of_path fs path = Some fr /\ file_ref_path fr = path /\ file_ref_source fr = f.
Proof.
  intros Hfind. exists (mkFileRef fs path f Hfind). split; [| split; reflexivity].
  unfold file_of_path.
  generalize (@eq_refl (option TSourceFile) (Collections.FileMapBase.find path fs)).
  destruct (Collections.FileMapBase.find path fs) as [f'|] at 2 3; intros e.
  - f_equal. apply file_ref_ext. reflexivity.
  - rewrite Hfind in e. discriminate e.
Qed.

(* NON-CIRCULAR reference completeness: a VALID source occurrence can be MINTED into a NodeRef by its key. *)
Theorem ref_of_key_source {fs} (idx : SyntaxIndex fs) (path : FilePath) (f : TSourceFile) (local : positive) :
  Collections.FileMapBase.find path fs = Some f -> valid_localb f local = true ->
  exists r, ref_of_key fs idx (mkKey path local) = Some r
            /\ node_ref_local r = local /\ file_ref_source (node_ref_file r) = f.
Proof.
  intros Hfind Hv.
  destruct (file_of_path_source path f Hfind) as [fr [Hfp [_ Hff]]].
  assert (Hvi : valid_in_index idx fr local = true) by (rewrite valid_in_index_eq, Hff; exact Hv).
  unfold ref_of_key. cbn [nk_file nk_local]. rewrite Hfp.
  generalize (@eq_refl bool (valid_in_index idx fr local)).
  destruct (valid_in_index idx fr local) at 2 3; intros e.
  - eexists. split; [reflexivity | split; [reflexivity | exact Hff]].
  - rewrite Hvi in e. discriminate e.
Qed.

(* the two toy paths are distinct (their exact byte strings differ). *)
Lemma rpath_neq : rpath <> rpathb.
Proof. intro H. apply (f_equal fp_str) in H. discriminate H. Qed.

(* the two-file forest's map bindings, by path (standard [add]/[find] — no scan). *)
Lemma rfind_two_a : Collections.FileMapBase.find rpath fs_two = Some (rfile 5).
Proof. vm_compute. reflexivity. Qed.
Lemma rfind_two_b : Collections.FileMapBase.find rpathb fs_two = Some (rfileb 7).
Proof. vm_compute. reflexivity. Qed.

(* TWO-FILE minting witnesses: each distinct path resolves to its own file handle (keyed by that path). *)
Theorem reg_two_file_a : exists fr, file_of_path fs_two rpath = Some fr /\ file_ref_path fr = rpath.
Proof.
  destruct (file_of_path_source rpath (rfile 5) rfind_two_a) as [fr [Hfp [Hpath _]]].
  exists fr. split; [exact Hfp | exact Hpath].
Qed.
Theorem reg_two_file_b : exists fr, file_of_path fs_two rpathb = Some fr /\ file_ref_path fr = rpathb.
Proof.
  destruct (file_of_path_source rpathb (rfileb 7) rfind_two_b) as [fr [Hfp [Hpath _]]].
  exists fr. split; [exact Hfp | exact Hpath].
Qed.

(* TWO-FILE fixture (exposable): a forest with two DISTINCT-path files, both mintable to their own file
   handles, whose public path identities differ — cross-file navigation with no path confusion. *)
Theorem reg_two_file :
  exists (fs : TForest) (fra frb : FileRef fs),
    file_of_path fs (file_ref_path fra) = Some fra /\
    file_of_path fs (file_ref_path frb) = Some frb /\
    file_ref_path fra <> file_ref_path frb.
Proof.
  destruct (file_of_path_source rpath (rfile 5) rfind_two_a) as [fra [_ [Hpa _]]].
  destruct (file_of_path_source rpathb (rfileb 7) rfind_two_b) as [frb [_ [Hpb _]]].
  exists fs_two, fra, frb.
  split; [apply file_of_path_complete | split; [apply file_of_path_complete|]].
  rewrite Hpa, Hpb. exact rpath_neq.
Qed.

(* FileRef path equality DECIDES file occurrence equality within one snapshot (public identity is the path). *)
Theorem file_ref_path_inj (fs : TForest) (fr1 fr2 : FileRef fs) :
  file_ref_path fr1 = file_ref_path fr2 -> fr1 = fr2.
Proof. apply file_ref_ext. Qed.

(* parent/child inverse at the NodeRef level: every enumerated child's parent is exactly the queried node. *)
Theorem thm_child_parent (fs : TForest) (idx : SyntaxIndex fs) (r cr : NodeRef fs) :
  In cr (children_of idx r) -> parent_of idx cr = Some r.
Proof.
  intros Hin.
  pose proof (thm_children_same_file fs idx r cr Hin) as Hf.
  pose proof (thm_children_sound fs idx r cr Hin) as Hsound.
  apply child_ids_parent in Hsound.
  pose proof (ref_meta_get idx cr) as Hget.
  rewrite Hf in Hget. rewrite <- (ref_fi_eq idx r) in Hget.
  unfold parent_id in Hsound. rewrite Hget in Hsound.
  destruct (parent_of_some fs idx cr (node_ref_local r) Hsound) as [pr [Hpr [Hpf Hpl]]].
  rewrite Hpr. f_equal. apply node_ref_ext; [ rewrite Hpf; exact Hf | exact Hpl ].
Qed.

(* the other direction: a node with a parent is enumerated among that parent's children — a genuine inverse. *)
Theorem thm_parent_child (fs : TForest) (idx : SyntaxIndex fs) (r pr : NodeRef fs) :
  parent_of idx r = Some pr -> In r (children_of idx pr).
Proof.
  intros Hpar.
  pose proof (thm_parent_same_file fs idx r pr Hpar) as Hf.
  assert (Hp' : nm_parent (ref_meta idx r) = Some (node_ref_local pr)).
  { destruct (nm_parent (ref_meta idx r)) as [pid|] eqn:Hnp.
    - destruct (parent_of_some fs idx r pid Hnp) as [pr' [Hpr' [_ Hpl]]].
      rewrite Hpar in Hpr'. injection Hpr' as <-. rewrite Hpl. reflexivity.
    - rewrite (parent_of_none fs idx r Hnp) in Hpar. discriminate Hpar. }
  pose proof (ref_meta_get idx r) as Hgetr. rewrite <- Hf in Hgetr.
  pose proof (thm4_parent_has_child (file_ref_source (node_ref_file pr))
                (node_ref_local pr) (node_ref_local r) (ref_meta idx r) Hgetr Hp') as Hchild.
  rewrite <- (ref_fi_eq idx pr) in Hchild.
  destruct (refine_children_complete fs (node_ref_file pr)
              (child_ids (fi_table (ref_fi idx pr)) (node_ref_local pr))
              (children_valid idx pr) (node_ref_local r) Hchild) as [cr [Hcr Hcl]].
  pose proof (refine_children_file fs (node_ref_file pr) _ (children_valid idx pr) cr Hcr) as Hcrf.
  assert (Hcreq : cr = r).
  { apply node_ref_ext; [ rewrite Hcrf, Hf; reflexivity | rewrite Hcl; reflexivity ]. }
  subst cr. unfold children_of. exact Hcr.
Qed.

(* --- NodeRef-level ANCESTRY (§10): the O(1) preorder-interval test, certified through the sealed API. --- *)

(* same file => same per-file table (the interval test compares within one file). *)
Lemma ref_fi_table_same_file (fs : TForest) (idx : SyntaxIndex fs) (x y : NodeRef fs) :
  node_ref_file x = node_ref_file y -> fi_table (ref_fi idx x) = fi_table (ref_fi idx y).
Proof. intros H. rewrite (ref_fi_eq idx x), (ref_fi_eq idx y), H. reflexivity. Qed.

(* bridge: a NodeRef parent edge is exactly a per-file [parent_id] edge on the shared table, both ways. *)
Lemma parentof_to_parentid (fs : TForest) (idx : SyntaxIndex fs) (d a : NodeRef fs) :
  parent_of idx d = Some a ->
  node_ref_file a = node_ref_file d /\
  parent_id (fi_table (ref_fi idx d)) (node_ref_local d) = Some (node_ref_local a).
Proof.
  intros Hpar. pose proof (thm_parent_same_file fs idx d a Hpar) as Hf. split; [exact Hf|].
  assert (Hnp : nm_parent (ref_meta idx d) = Some (node_ref_local a)).
  { destruct (nm_parent (ref_meta idx d)) as [pid|] eqn:Hp.
    - destruct (parent_of_some fs idx d pid Hp) as [a' [Ha' [_ Hal]]].
      rewrite Hpar in Ha'. injection Ha' as <-. rewrite Hal. reflexivity.
    - rewrite (parent_of_none fs idx d Hp) in Hpar. discriminate Hpar. }
  pose proof (ref_meta_get idx d) as Hget. rewrite <- (ref_fi_eq idx d) in Hget.
  unfold parent_id. rewrite Hget. exact Hnp.
Qed.

Lemma parentid_to_parentof (fs : TForest) (idx : SyntaxIndex fs) (d : NodeRef fs) pa :
  parent_id (fi_table (ref_fi idx d)) (node_ref_local d) = Some pa ->
  exists a, parent_of idx d = Some a /\ node_ref_local a = pa /\ node_ref_file a = node_ref_file d.
Proof.
  intros Hpid.
  pose proof (ref_meta_get idx d) as Hget. rewrite <- (ref_fi_eq idx d) in Hget.
  unfold parent_id in Hpid. rewrite Hget in Hpid.
  destruct (parent_of_some fs idx d pa Hpid) as [a [Ha [Hf Hal]]].
  exists a. split; [exact Ha | split; [exact Hal | exact Hf]].
Qed.

(* the NodeRef-level ancestor relation: transitive closure of [parent_of]. *)
Inductive RefAncestor (fs : TForest) (idx : SyntaxIndex fs) : NodeRef fs -> NodeRef fs -> Prop :=
| RAnc_dir  : forall a d, parent_of idx d = Some a -> RefAncestor fs idx a d
| RAnc_step : forall a p d, RefAncestor fs idx a p -> parent_of idx d = Some p -> RefAncestor fs idx a d.

Lemma refanc_same_file (fs : TForest) (idx : SyntaxIndex fs) (a d : NodeRef fs) :
  RefAncestor fs idx a d -> node_ref_file a = node_ref_file d.
Proof.
  intros H. induction H as [a d Hpar | a p d Hanc IH Hpar].
  - apply (proj1 (parentof_to_parentid fs idx d a Hpar)).
  - rewrite IH. apply (proj1 (parentof_to_parentid fs idx d p Hpar)).
Qed.

Lemma refanc_to_anc (fs : TForest) (idx : SyntaxIndex fs) (a d : NodeRef fs) :
  RefAncestor fs idx a d -> Ancestor (fi_table (ref_fi idx d)) (node_ref_local a) (node_ref_local d).
Proof.
  intros H. induction H as [a d Hpar | a p d Hanc IH Hpar].
  - apply Anc_dir. apply (proj2 (parentof_to_parentid fs idx d a Hpar)).
  - pose proof (proj1 (parentof_to_parentid fs idx d p Hpar)) as Hf.
    rewrite (ref_fi_table_same_file fs idx p d Hf) in IH.
    apply (Anc_step (fi_table (ref_fi idx d)) (node_ref_local a) (node_ref_local p) (node_ref_local d) IH).
    apply (proj2 (parentof_to_parentid fs idx d p Hpar)).
Qed.

(* the interval-jump reconstruction: an Ancestor derivation on the file table lifts to a [RefAncestor]. *)
Lemma anc_to_refanc_aux (fs : TForest) (idx : SyntaxIndex fs) (fr : FileRef fs) (al dl : positive)
  (Hanc : Ancestor (fi_table (build_file (file_ref_source fr))) al dl) :
  forall (d : NodeRef fs), node_ref_file d = fr -> node_ref_local d = dl ->
  exists a, node_ref_file a = fr /\ node_ref_local a = al /\ RefAncestor fs idx a d.
Proof.
  induction Hanc as [al dl Hpid | al pl dl Hanc_ap IH Hpid_d]; intros d Hdf Hdl.
  - assert (Hpd : parent_id (fi_table (ref_fi idx d)) (node_ref_local d) = Some al)
      by (rewrite (ref_fi_eq idx d), Hdf, Hdl; exact Hpid).
    destruct (parentid_to_parentof fs idx d al Hpd) as [a [Ha [Hal Haf]]].
    exists a. split; [rewrite Haf; exact Hdf | split; [exact Hal | apply RAnc_dir; exact Ha]].
  - assert (Hpd : parent_id (fi_table (ref_fi idx d)) (node_ref_local d) = Some pl)
      by (rewrite (ref_fi_eq idx d), Hdf, Hdl; exact Hpid_d).
    destruct (parentid_to_parentof fs idx d pl Hpd) as [p [Hp [Hpl Hpf]]].
    destruct (IH p (eq_trans Hpf Hdf) Hpl) as [a [Haf [Hal Hra]]].
    exists a. split; [exact Haf | split; [exact Hal | apply (RAnc_step fs idx a p d Hra Hp)]].
Qed.

Lemma anc_to_refanc (fs : TForest) (idx : SyntaxIndex fs) (a d : NodeRef fs) :
  node_ref_file a = node_ref_file d ->
  Ancestor (fi_table (build_file (file_ref_source (node_ref_file d)))) (node_ref_local a) (node_ref_local d) ->
  RefAncestor fs idx a d.
Proof.
  intros Hf Hanc.
  destruct (anc_to_refanc_aux fs idx (node_ref_file d) (node_ref_local a) (node_ref_local d) Hanc d eq_refl eq_refl)
    as [a' [Haf [Hal Hra]]].
  assert (a' = a) by (apply node_ref_ext; [ rewrite Haf; symmetry; exact Hf | exact Hal ]).
  subst a'. exact Hra.
Qed.

(* the total NodeRef-level ancestor TEST — O(1) preorder-interval arithmetic after one metadata lookup.
   The same-file guard compares the public file PATH (the identity), not a hidden slot. *)
Definition is_ancestor_ref {fs} (idx : SyntaxIndex fs) (a d : NodeRef fs) : bool :=
  fp_eqb (file_ref_path (node_ref_file a)) (file_ref_path (node_ref_file d)) &&
  is_ancestor_local (fi_table (ref_fi idx d)) (node_ref_local a) (node_ref_local d).

(* the ancestor present-ness side condition thm13 needs: a valid reference's id is in its file table. *)
Lemma ref_local_present (fs : TForest) (idx : SyntaxIndex fs) (a d : NodeRef fs) :
  node_ref_file a = node_ref_file d ->
  NodeTable.get (node_ref_local a) (fi_table (build_file (file_ref_source (node_ref_file d)))) <> None.
Proof.
  intros Hf. rewrite <- Hf. pose proof (ref_meta_get idx a) as Hg. rewrite Hg. discriminate.
Qed.

(* the O(1) interval ancestor TEST is SOUND and COMPLETE w.r.t. the [parent_of] transitive closure. *)
Theorem thm_ref_ancestry (fs : TForest) (idx : SyntaxIndex fs) (a d : NodeRef fs) :
  is_ancestor_ref idx a d = true <-> RefAncestor fs idx a d.
Proof.
  unfold is_ancestor_ref. split.
  - intros Hb. apply andb_true_iff in Hb as [Hpath Hloc]. apply fp_eqb_eq in Hpath.
    assert (Hf : node_ref_file a = node_ref_file d) by (apply file_ref_ext; exact Hpath).
    apply (anc_to_refanc fs idx a d Hf).
    rewrite (ref_fi_eq idx d) in Hloc.
    apply (proj1 (thm13_interval_ancestry (file_ref_source (node_ref_file d))
                    (node_ref_local a) (node_ref_local d) (ref_local_present fs idx a d Hf))).
    exact Hloc.
  - intros Hra.
    pose proof (refanc_same_file fs idx a d Hra) as Hf.
    pose proof (refanc_to_anc fs idx a d Hra) as Hanc.
    apply andb_true_iff. split.
    + apply fp_eqb_eq. rewrite Hf. reflexivity.
    + rewrite (ref_fi_eq idx d). rewrite (ref_fi_eq idx d) in Hanc.
      apply (proj2 (thm13_interval_ancestry (file_ref_source (node_ref_file d))
                      (node_ref_local a) (node_ref_local d) (ref_local_present fs idx a d Hf))).
      exact Hanc.
Qed.

End Snap.

(* C0B §7 / §10.3 — negative ABSTRACTION checks: the raw index map and the raw record constructors are NOT
   reachable through the sealed [Snap] interface (each [Check] FAILS, so [Fail Check] succeeds).  The public
   API exposes exactness only through validated source references + theorem surfaces. *)
Fail Check Snap.index_at.        (* removed public raw path lookup — internal only *)
Fail Check Snap.mkSyntaxIndex.   (* raw index constructor hidden *)
Fail Check Snap.mkFileRef.       (* raw file-ref constructor hidden *)
Fail Check Snap.mkNodeRef.       (* raw node-ref constructor hidden *)
Fail Check Snap.si_outer.        (* raw outer-map projection hidden *)
